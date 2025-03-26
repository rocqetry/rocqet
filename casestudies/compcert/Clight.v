From Rocqet Require Import Loader.
From Rocqet Require Import LibTactics.

From Rocqet Require Import Coqlib.
From Rocqet Require Import Errors.
From Rocqet Require Import Values.
From Rocqet Require Import AST.
From Rocqet Require Import Integers. 
From Rocqet Require Import Floats.
From Rocqet Require Import Memory.
From Rocqet Require Import Globalenvs.
From Rocqet Require Import Smallstep.
From Rocqet Require Import Events.
From Rocqet Require Import Maps.
From Rocqet Require Import Linking.
Require Import Rocqet.CompCert.lib.Ctypes.
From Rocqet Require Import Cop.
From Rocqet Require Import Mon.
Require Import FSets.
Require Import FSetAVL.
Require Import Orders.
Require Import Mergesort.
Require Import Ordered.
Require Import Coq.ZArith.ZArith.
From Rocqet Require Import Prelude.
From Rocqet Require Import Op.


Trait Base. 

Family Clight.
FInductive expr : Type :=          
| Econst_int: int -> type -> expr(* integer literal *)
| Econst_float: float -> type -> expr(* double float literal *)
| Econst_single: float32 -> type -> expr(* single float literal *)
| Econst_long: int64 -> type -> expr(* long integer literal *)                                            
| Etempvar: ident -> type -> expr (* temporary variable *)          
| Esizeof: type -> type -> expr (* size of a type *)
| Ecast: expr -> type -> expr
| Ealignof: type -> type -> expr (* alignment of a type *)
| Eunop: Cop.unary_operation -> expr -> type -> expr (* unary operation *)
| Ebinop: Cop.binary_operation -> expr -> expr -> type -> expr. (* binary operation *)
       
FRecursion typeof about expr motive (fun (_ : expr) => type) by _rect. 
Case Econst_int i ty := ty. 
Case Econst_float f ty := ty. 
Case Econst_single s ty := ty. 
Case Econst_long l ty := ty. 
Case Etempvar v ty := ty.
Case Esizeof ty' ty := ty.
Case Ealignof ty' ty := ty.
Case Ecast e ty := ty.
Case Eunop op e ty := ty.
Case Ebinop op e0 e1 ty := ty.
FEnd typeof.
       
FDefinition label := ident.
FInductive stmt : Type :=                                        
| Sskip : stmt (* do nothing *)
| Sset : ident -> expr -> stmt (* assignment tempvar = rvalue *)
| Sseq : stmt -> stmt -> stmt (* sequence *)
| Sifthenelse : expr -> stmt -> stmt -> stmt (* conditional *)
| Sreturn : option expr -> stmt (* return statement *)
| Slabel : label -> stmt -> stmt
| Sgoto : label -> stmt
with lbl_stmts : Type :=(* cases of a switch *)
| LSnil: lbl_stmts
| LScons: option Z -> stmt -> lbl_stmts -> lbl_stmts.
              
MetaData function.
Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_temps: list (ident * type);
  fn_body: self__Clight.stmt
}.
FEnd function.

FDefinition var_names : list(ident * type) -> list ident :=
  fun vars => List.map (@fst ident type) vars.

FDefinition fundef := Ctypes.fundef function.
       
FDefinition type_of_function : function -> type := fun f => 
  Tfunction (type_of_params (self__Clight.fn_params f)) (self__Clight.fn_return f) (self__Clight.fn_callconv f).

FDefinition type_of_fundef : fundef -> type := fun f => 
  match f with
  | Internal fd => type_of_function fd
  | External id args res cc => Tfunction args res cc
  end.

FDefinition program := Ctypes.program function.
(* ------------------------------------------------ *)
(*                 Semantics for Clight             *)
(* ------------------------------------------------ *)
MetaData genv.
Record genv := { genv_genv :> Genv.t self__Clight.fundef type; genv_cenv :> composite_env }.
FEnd genv.
FDefinition globalenv : program -> genv := fun p => 
  {| self__Clight.genv_genv := Genv.globalenv p; self__Clight.genv_cenv := p.(prog_comp_env) |}.


FDefinition env := PTree.t (block * type).
FDefinition empty_env: env := (PTree.empty (block * type)).
FDefinition temp_env := PTree.t val.

MetaData alloc_variables.
Inductive alloc_variables: self__Clight.genv -> self__Clight.env -> mem ->
                           list (ident * type) ->
                           self__Clight.env -> mem -> Prop :=
| alloc_variables_nil:
  forall ge e m,
    alloc_variables ge e m nil e m
| alloc_variables_cons:
  forall (ge:genv) e m id ty vars m1 b1 m2 e2,
    Mem.alloc m 0 (sizeof ge ty) = (m1, b1) ->
    alloc_variables ge (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
    alloc_variables ge e m ((id, ty) :: vars) e2 m2.
FEnd alloc_variables.

MetaData create_undef_temps.
Fixpoint create_undef_temps (temps: list (ident * type)) : self__Clight.temp_env :=
  match temps with
  | nil => PTree.empty val
  | (id, t) :: temps' => PTree.set id Vundef (create_undef_temps temps')
  end.
FEnd create_undef_temps.

MetaData bind_parameters.
Fixpoint bind_parameter_temps (formals: list (ident * type)) (args: list val)
                              (le: self__Clight.temp_env) : option self__Clight.temp_env :=
 match formals, args with
 | nil, nil => Some le
 | (id, t) :: xl, v :: vl => bind_parameter_temps xl vl (PTree.set id v le)
 | _, _ => None
 end.
FEnd bind_parameters.

FInductive eval_expr : genv -> env -> temp_env -> mem -> expr -> val -> Prop :=
| eval_Econst_int: forall ge e le m i ty,
    eval_expr ge e le m (Econst_int i ty) (Vint i)
| eval_Econst_float: forall ge e le m f ty,
    eval_expr ge e le m (Econst_float f ty) (Vfloat f)
| eval_Econst_single: forall ge e le m f ty,
    eval_expr ge e le m (Econst_single f ty) (Vsingle f)
| eval_Econst_long: forall ge e le m i ty,
    eval_expr ge e le m (Econst_long i ty) (Vlong i)
| eval_Ecast: forall ge e le m a ty v1 v,
    eval_expr ge e le m a v1 ->
    Cop.sem_cast v1 (typeof a) ty m = Some v ->
    eval_expr ge e le m (Ecast a ty) v
| eval_Etempvar: forall ge e le m id ty v,
    PTree.get id le = Some v ->
    eval_expr ge e le m (Etempvar id ty) v.

FInductive cont: Type :=
| Kstop: cont
| Kseq: stmt -> cont -> cont. (* Kseq s2 k = after s1 in s1;s2 *)

FRecursion call_cont about cont motive (fun (c : cont) => cont) by _rect.       
Case Kstop := Kstop.
Case Kseq s k := (call_cont k).
FEnd call_cont.
            
FRecursion is_call_cont about cont motive (fun (c : cont) => Prop) by _rect.                   
Case Kstop := True.
Case Kseq s k := False.
FEnd is_call_cont.
            
FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont)) by _rect. 
Case Sskip := (fun lbl k => None). 
Case Sset id e := (fun lbl k => None).
Case Sseq s1 s2 := 
  (fun lbl k => 
    match find_label s1 lbl (Kseq s2 k) with
    | Some sk => Some sk
    | None => find_label s2 lbl k
    end). 
Case Sifthenelse a s1 s2 := 
 (fun lbl k => 
     match find_label s1 lbl k with
      | Some sk => Some sk
      | None => find_label s2 lbl k
      end).
Case Sreturn a := (fun lbl k => None).
Case Slabel lbl' s' :=  
  (fun lbl k =>  if ident_eq lbl lbl' then Some(s', k) else find_label s' lbl k).
Case Sgoto lbl' :=  (fun lbl k => None).
FEnd find_label.

MetaData state binds State, Callstate, Returnstate.
Inductive state: Type :=
  | State
      (f: function)
      (s: stmt)
      (k: cont)
      (e: env)
      (le: temp_env)
      (m: mem) : state
  | Callstate
      (fd: fundef)
      (args: list val)
      (k: cont)
      (m: mem) : state
  | Returnstate
      (res: val)
      (k: cont)
      (m: mem) : state.
FEnd state.

FDefinition block_of_binding := fun (ge: genv) (id_b_ty: ident * (block * type)) =>
  match id_b_ty with (id, (b, ty)) => (b, 0, Ctypes.sizeof (self__Clight.genv_cenv ge) ty) end.

FDefinition blocks_of_env : genv -> env -> list (block * Z * Z)  := fun ge e => 
  List.map (block_of_binding ge) (PTree.elements e).

MetaData function_entry2.
Inductive function_entry2 (ge: genv) (f: function) (vargs: list val) (m: mem) (e: env) (le: temp_env) (m': mem) : Prop :=
  | function_entry2_intro:
      list_norepet (var_names f.(fn_vars)) ->
      list_norepet (var_names f.(fn_params)) ->
      list_disjoint (var_names f.(fn_params)) (var_names f.(fn_temps)) ->
      alloc_variables ge empty_env m f.(fn_vars) e m' ->
      bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le ->
      function_entry2 ge f vargs m e le m'.
FEnd function_entry2.

(* FOverride Definition function_entry := function_entry2*)

(* To be overriden in SimplExpr & Cshmgen *)
FDefinition function_entry : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop := function_entry2.

FInductive step : genv -> state -> trace -> state -> Prop :=  
| step_skip_seq: forall ge f s k e le m,
  step ge (State f Sskip (Kseq s k) e le m)
    E0 (State f s k e le m)
| step_set: forall ge f id a k e le m v,
  eval_expr ge e le m a v ->
  step ge (State f (Sset id a) k e le m)
    E0 (State f Sskip k e (PTree.set id v le) m)
| step_seq: forall ge f s1 s2 k e le m,
  step ge (State f (Sseq s1 s2) k e le m)
    E0 (State f s1 (Kseq s2 k) e le m)
| step_ifthenelse: forall ge f a s1 s2 k e le m v1 b,
    eval_expr ge e le m a v1 ->
    Cop.bool_val v1 (typeof a) m = Some b ->
    step ge (State f (Sifthenelse a s1 s2) k e le m)
      E0 (State f (if b then s1 else s2) k e le m)      
| step_return_0: forall ge f k e le m m',
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    step ge (State f (Sreturn None) k e le m)
      E0 (Returnstate Vundef (call_cont k) m')
| step_return_1: forall ge f a k e le m v v' m',
    eval_expr ge e le m a v ->
    Cop.sem_cast v (typeof a) (self__Clight.fn_return f) m = Some v' ->
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    step ge (State f (Sreturn (Some a)) k e le m)
      E0 (Returnstate v' (call_cont k) m')      
| step_skip_call: forall ge f k e le m m',
    is_call_cont k ->
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    step ge (State f Sskip k e le m)
      E0 (Returnstate Vundef k m')
| step_label: forall ge f lbl s k e le m,
  step ge (State f (Slabel lbl s) k e le m)
    E0 (State f s k e le m)
| step_goto: forall ge f lbl k e le m s' k',
  find_label (self__Clight.fn_body f) lbl (call_cont k) = Some (s', k') ->
  step ge (self__Clight.State f (Sgoto lbl) k e le m)
    E0 (State f s' k' e le m)    
| step_internal_function: forall ge f vargs k m e le m1,
      function_entry ge f vargs m e le m1 ->
      step ge (Callstate (Internal f) vargs k m)
        E0 (State f (self__Clight.fn_body f) k e le m1).

MetaData initial_state.
Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      self__Clight.type_of_fundef f = Tfunction nil type_int32s cc_default ->
      initial_state p (Callstate f nil self__Clight.Kstop m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: self__Clight.state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (self__Clight.Returnstate (Vint r) self__Clight.Kstop m) r.
FEnd final_state.
FEnd Clight.

FEnd Base.

Trait Comp_Loops extends Base.

Trait Clight_Sloop extends Clight.
FInductive stmt : Type := 
  | Sloop: stmt -> stmt -> stmt (* infinite loop *)
  | Sbreak : stmt (* break statement *)
  | Scontinue : stmt. (* continue statement *)

FInductive cont: Type :=
| Kloop1: stmt -> stmt -> cont -> cont  (* Kloop1 s1 s2 k = after s1 in Sloop s1 s2 *)
| Kloop2: stmt -> stmt -> cont -> cont. (* Kloop2 s1 s2 k = after s2 in Sloop s1 s2 *)

FRecursion call_cont.
Case Kloop1 s1 s2 k := (call_cont k).
Case Kloop2 s1 s2 k := (call_cont k).
FEnd call_cont.

FRecursion is_call_cont.
Case _ := False.
FEnd is_call_cont.

FRecursion find_label.
Case Sloop s1 s2 :=
  (fun lbl k =>
     match find_label s1 lbl (Kloop1 s1 s2 k) with
     | Some sk => Some sk
     | None => find_label s2 lbl (Kloop2 s1 s2 k)
     end).
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_loop: forall ge f s1 s2 k e le m,
      step ge (State f (Sloop s1 s2) k e le m)
        E0 (State f s1 (Kloop1 s1 s2 k) e le m)        
| step_skip_or_continue_loop1: forall ge f s1 s2 k e le m x,
      x = Sskip \/ x = Scontinue ->
      step ge (State f x (Kloop1 s1 s2 k) e le m)
        E0 (State f s2 (Kloop2 s1 s2 k) e le m)
| step_break_loop1: forall ge f s1 s2 k e le m,
      step ge (State f Sbreak (Kloop1 s1 s2 k) e le m)
        E0 (State f Sskip k e le m)
| step_skip_loop2: forall ge f s1 s2 k e le m,
      step ge (State f Sskip (Kloop2 s1 s2 k) e le m)
        E0 (State f (Sloop s1 s2) k e le m)
| step_break_loop2: forall ge f s1 s2 k e le m,
      step ge (State f Sbreak (Kloop2 s1 s2 k) e le m)
        E0 (State f Sskip k e le m).
  
FEnd Clight_Sloop.

Family Clight extends Clight_Sloop.
FEnd Clight.

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family Clight.
FInductive stmt : Type :=
| Sbuiltin: option ident -> external_function -> list type -> list expr -> stmt. (* builtin invocation *)

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

Inherit eval_expr.

MetaData eval_exprlist binds eval_Enil, eval_Econs.
Inductive eval_exprlist: genv -> env -> temp_env -> mem -> list expr -> list type -> list val -> Prop :=
| eval_Enil: forall ge e le m,
    eval_exprlist ge e le m nil nil nil
| eval_Econs: forall ge e le m a bl ty tyl v1 v2 vl,
    eval_expr ge e le m a v1 ->
    Cop.sem_cast v1 (typeof a) ty m = Some v2 ->
    eval_exprlist ge e le m bl tyl vl ->
    eval_exprlist ge e le m (a :: bl) (ty :: tyl) (v2 :: vl).
FEnd eval_exprlist.

FDefinition set_opttemp := fun (optid: option ident) (v: val) (le: temp_env) =>
  match optid with
  | None => le
  | Some id => PTree.set id v le
  end.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_builtin: forall ge f optid ef tyargs al k e le m vargs t vres m',
      eval_exprlist ge e le m al tyargs vargs ->
      external_call ef (Genv.to_senv (self__Clight.genv_genv ge)) vargs m t vres m' ->
      step ge (State f (Sbuiltin optid ef tyargs al) k e le m)
         t (State f Sskip k e (set_opttemp optid vres le) m').
  
FEnd Clight.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Trait Clight_Lvalues extends Clight.
FInductive expr : Type :=
| Evar: ident -> type -> expr (* variable *)
| Ederef: expr -> type -> expr (* pointer dereference (unary *)                             
| Eaddrof: expr -> type -> expr. (* address-of operator (&) *)

FRecursion typeof.
Case Evar i t := t.
Case Eaddrof e t := t.
Case Ederef i t := t.
FEnd typeof.

MetaData deref_loc.
Inductive deref_loc (ty: type) (m: mem) (b: block) (ofs: ptrofs) :
                                             bitfield -> val -> Prop :=
  | deref_loc_value: forall chunk v,
      access_mode ty = By_value chunk ->
      Mem.loadv chunk m (Vptr b ofs) = Some v ->
      deref_loc ty m b ofs Full v
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ty m b ofs Full (Vptr b ofs)
  | deref_loc_copy:
      access_mode ty = By_copy ->
      deref_loc ty m b ofs Full (Vptr b ofs)
  | deref_loc_bitfield: forall sz sg pos width v,
      load_bitfield ty sz sg pos width m (Vptr b ofs) v ->
      deref_loc ty m b ofs (Bits sz sg pos width) v.
FEnd deref_loc.

FInductive eval_expr : genv -> env -> temp_env -> mem -> expr -> val -> Prop :=
| eval_Eaddrof: forall ge e le m a ty loc ofs,
   eval_lvalue ge e le m a loc ofs Ctypes.Full ->
   eval_expr ge e le m (Eaddrof a ty) (Vptr loc ofs)
| eval_Elvalue: forall ge e le m a loc ofs bf v,
      eval_lvalue ge e le m a loc ofs bf ->
      deref_loc (typeof a) m loc ofs bf v ->
      eval_expr ge e le m a v             
with eval_lvalue: genv -> env -> temp_env -> mem -> expr -> block -> ptrofs -> bitfield -> Prop :=
  | eval_Evar_local: forall ge e le m id l ty,
      e!id = Some(l, ty) ->
      eval_lvalue ge e le m (Evar id ty) l Ptrofs.zero Ctypes.Full                  
  | eval_Evar_global: forall ge e le m id l ty,
      e!id = None ->
      Genv.find_symbol (self__Clight_Lvalues.genv_genv ge) id = Some l ->
      eval_lvalue ge e le m (Evar id ty) l Ptrofs.zero Ctypes.Full
  | eval_Ederef: forall ge e le m a ty l ofs,
      eval_expr ge e le m a (Vptr l ofs) ->
      eval_lvalue ge e le m (Ederef a ty) l ofs Ctypes.Full.
             
FEnd Clight_Lvalues.

Trait Clight_Sassign extends Clight, Clight_Lvalues.
FInductive stmt : Type :=
| Sassign : expr -> expr -> stmt. (* assignment lvalue = rvalue *)

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

MetaData assign_loc.
Inductive assign_loc (ce: composite_env) (ty: type) (m: mem) (b: block) (ofs: ptrofs):
                                            bitfield -> val -> mem -> Prop :=
  | assign_loc_value: forall v chunk m',
      access_mode ty = By_value chunk ->
      Mem.storev chunk m (Vptr b ofs) v = Some m' ->
      assign_loc ce ty m b ofs Full v m'
  | assign_loc_copy: forall b' ofs' bytes m',
      access_mode ty = By_copy ->
      (sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs')) ->
      (sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs)) ->
      b' <> b \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs' + sizeof ce ty <= Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs + sizeof ce ty <= Ptrofs.unsigned ofs' ->
      Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ce ty) = Some bytes ->
      Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
      assign_loc ce ty m b ofs Full (Vptr b' ofs') m'
  | assign_loc_bitfield: forall sz sg pos width v m' v',
      store_bitfield ty sz sg pos width m (Vptr b ofs) v m' v' ->
      assign_loc ce ty m b ofs (Bits sz sg pos width) v m'.
FEnd assign_loc.

FInductive step : genv -> state -> trace -> state -> Prop :=  
| step_assign: forall ge f a1 a2 k e le m loc ofs bf v2 v m',
      eval_lvalue ge e le m a1 loc ofs bf ->
      eval_expr ge e le m a2 v2 ->
      Cop.sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
      assign_loc (self__Clight_Sassign.genv_cenv ge) (typeof a1) m loc ofs bf v m' ->
      step ge (State f (Sassign a1 a2) k e le m)
        E0 (State f Sskip k e le m').

FEnd Clight_Sassign.

Family Clight extends 
  Clight_Sassign,   
  Clight_Lvalues.
FEnd Clight.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

Family Clight.
FInductive expr : Type :=
| Efield: expr -> ident -> type -> expr. (* access to a member of a struct or union *)

FRecursion typeof.
Case Efield e i ty := ty.
FEnd typeof.

FInductive eval_expr : genv -> env -> temp_env -> mem -> expr -> val -> Prop := 
with eval_lvalue: genv -> env -> temp_env -> mem -> expr -> block -> ptrofs -> bitfield -> Prop :=
| eval_Efield_struct: forall ge e le m a i ty l ofs id co att delta bf,
      eval_expr ge e le m a (Vptr l ofs) ->
      typeof a = Tstruct id att ->
      (self__Clight.genv_cenv ge)!id = Some co ->
      field_offset (self__Clight.genv_cenv ge) i (co_members co) = OK (delta, bf) ->
      eval_lvalue ge e le m (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf                  
| eval_Efield_union: forall ge e le m a i ty l ofs id co att delta bf,
      eval_expr ge e le m a (Vptr l ofs) ->
      typeof a = Tunion id att ->
      (self__Clight.genv_cenv ge)!id = Some co ->
      union_field_offset (self__Clight.genv_cenv ge) i (co_members co) = OK (delta, bf) ->
      eval_lvalue ge e le m (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf.

FEnd Clight.

FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family Clight.
FInductive stmt : Type :=
| Scall: option ident -> expr -> list expr -> stmt. (* function call *)

FInductive cont: Type :=
| Kcall: option ident ->(* where to store result *)
           function ->(* calling function *)
           env ->(* local env of calling function *)
           temp_env ->(* temporary env of calling function *)
           cont -> cont.  

FRecursion call_cont.
Case Kcall a b c d k := (Kcall a b c d k).
FEnd call_cont.
            
FRecursion is_call_cont.
Case Kcall a b c d k := True.
FEnd is_call_cont.

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_call: forall ge f optid a al k e le m tyargs tyres cconv vf vargs fd,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
      eval_expr ge e le m a vf ->
      eval_exprlist ge e le m al tyargs vargs ->
      Genv.find_funct (self__Clight.genv_genv ge) vf = Some fd ->
      type_of_fundef fd = Tfunction tyargs tyres cconv ->
      step ge (State f (Scall optid a al) k e le m)
        E0 (Callstate fd vargs (Kcall optid f e le k) m)
| step_external_function: forall ge ef targs tres cconv vargs k m vres t m',
      external_call ef (Genv.to_senv (self__Clight.genv_genv ge)) vargs m t vres m' ->
      step ge (Callstate (External ef targs tres cconv) vargs k m)
         t (Returnstate vres k m')
| step_returnstate: forall ge v optid f e le k m,
      step ge (Returnstate v (Kcall optid f e le k) m)
        E0 (State f Sskip k e (set_opttemp optid v le) m).        

FEnd Clight.

FEnd Comp_Call.

(* small extension *)
Trait Comp_Switch extends Comp_Loops.

Family Clight.

FInductive stmt : Type := 
| Sswitch : expr -> lbl_stmts -> stmt. (* switch statement *)

FInductive cont: Type :=
| Kswitch: cont -> cont.

FRecursion call_cont.
Case Kswitch k := (call_cont k).
FEnd call_cont.
            
FRecursion is_call_cont.
Case Kswitch k := False.
FEnd is_call_cont.

FRecursion select_switch_default about lbl_stmts motive (fun (_ : lbl_stmts) => lbl_stmts) by _rect.
Case LSnil := LSnil.
Case LScons opt s sl' :=
  (match opt with
   | None => LScons opt s sl'
   | Some i => select_switch_default sl'
  end).
FEnd select_switch_default.

FRecursion select_switch_case about lbl_stmts motive (fun (_ : lbl_stmts) => Z -> option lbl_stmts) by _rect.
Case LSnil := (fun n => None).
Case LScons opt s sl' :=
  (fun n =>
     match opt with
     | None => select_switch_case sl' n
     | Some c => if zeq c n then Some (LScons opt s sl')  else select_switch_case sl' n
     end).
FEnd select_switch_case.

FDefinition select_switch := fun (n: Z) (sl: lbl_stmts) =>
  match select_switch_case sl n with
  | Some sl' => sl'
  | None => select_switch_default sl
  end.

FRecursion seq_of_labeled_statement about lbl_stmts motive (fun (_: lbl_stmts) => stmt) by _rect.
Case LSnil := Sskip.
Case LScons x s sl' := (Sseq s (seq_of_labeled_statement sl')).
FEnd seq_of_labeled_statement.

FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont))
with find_label_ls about lbl_stmts motive (fun (_ : lbl_stmts) => label -> cont -> option (stmt * cont)) by _rect.
Case Sswitch e sl := (fun lbl k => find_label_ls sl lbl (Kswitch k)).

Case LSnil := (fun lbl k => None).
Case LScons x s sl' :=
  (fun lbl k => 
      match find_label s lbl (Kseq (seq_of_labeled_statement sl') k) with
      | Some sk => Some sk
      | None => find_label_ls sl' lbl k
      end).
FEnd find_label with find_label_ls.      

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_switch: forall ge f a sl k e le m v n,
      eval_expr ge e le m a v ->
      Cop.sem_switch_arg v (typeof a) = Some n ->
      step ge (State f (Sswitch a sl) k e le m)
        E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le m)
| step_skip_break_switch: forall ge f x k e le m,
    x = Sskip \/ x = Sbreak ->
    step ge (State f x (Kswitch k) e le m)
      E0 (State f Sskip k e le m)
| step_continue_switch: forall ge f k e le m,
    step ge (State f Scontinue (Kswitch k) e le m)
      E0 (State f Scontinue k e le m).

FEnd Clight.

FEnd Comp_Switch.

(* Family Comp extends 
  Base,
  Comp_Switch,
  Comp_Loops,
  Comp_Heap, 
  Comp_Field, 
  Comp_Call,
  (* Comp_Float,*)
  Comp_Builtin. 

FEnd Comp.

Require Extraction.
Cd "extraction".

Separate Extraction Comp.Clight.*)
