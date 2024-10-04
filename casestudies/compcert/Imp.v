From NFPOP Require Import Loader.

Require Import Coq.ZArith.ZArith.
Require Import Coqlib.
Require Import Values.
Require Import AST.
Require Import Integers. 
Require Import Floats.
Require Import Errors.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Events.
Require Import Maps.
Require Import Linking.
Require Import FSets.
Require Import FSetAVL.
Require Import Orders.
Require Import Mergesort.
Require Import Ordered.


Axiom cheat : forall {X}, X.
Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Module VarOrder <: TotalLeBool.
  Definition t := (ident * Z)%type.
  Definition leb (v1 v2: t) : bool := zle (snd v1) (snd v2).
  Theorem leb_total: forall v1 v2, leb v1 v2 = true \/ leb v2 v1 = true.
  Proof.
    unfold leb; intros.
    assert (snd v1 <= snd v2 \/ snd v2 <= snd v1) by lia.
    unfold proj_sumbool. destruct H; [left|right]; apply zle_true; auto.
  Qed.
End VarOrder.

Module VarSort := Mergesort.Sort(VarOrder).


Family Imp.     
  MetaData type.
  Inductive intsize : Type :=
  | I8: intsize
  | I16: intsize
  | I32: intsize
  | IBool: intsize.

  
Inductive signedness : Type :=
  | Signed: signedness
  | Unsigned: signedness. 

Inductive bitfield : Type :=
  | Full
  | Bits (sz: intsize) (sg: signedness) (pos: Z) (width: Z).


   Record attr : Type := mk_attr {
   attr_volatile: bool;
   attr_alignas: option N(* log2 of required alignment *)
   }.

   Definition noattr := {| attr_volatile := false; attr_alignas := None |}.
     
  Inductive type : Type :=
      | Tvoid: type(* the void type *)
      | Tint: intsize -> signedness -> attr -> type(* integer types *)
      | Tlong: signedness -> attr -> type(* 64-bit integer types *)      
      | Tpointer: type -> attr -> type(* pointer types ty *)      
      | Tfunction: typelist -> type -> calling_convention -> type(* function types *)      
   with typelist : Type :=
      | Tnil: typelist
      | Tcons: type -> typelist -> typelist.  
  
  Definition type_int32s := Tint I32 Signed noattr.
  Definition type_bool := Tint IBool Signed noattr.

  Fixpoint type_of_params (params: list (ident * type)) : typelist :=
  match params with
  | nil => Tnil
  | (id, ty) :: rem => Tcons ty (type_of_params rem)
  end.
  FEnd type.

  (* C family languages *)
  Family Cfam.
       FInductive constant : Type :=
           | Ointconst: int -> constant (* integer constant *)
           | Ofloatconst: float -> constant (* double-precision floating-point constant *)
           | Osingleconst: float32 -> constant (* single-precision floating-point constant *)
           | Olongconst: int64 -> constant.

       FInductive expr : Type :=
          | Evar : ident -> expr (* reading a temporary variable *)            
          | Econst : constant -> expr. (* constants *)          

       FDefinition label := ident.
       FInductive stmt : Type :=
            | Sskip: stmt
            | Sset : ident -> expr -> stmt            
            | Sseq: stmt -> stmt -> stmt
            | Sifthenelse: expr -> stmt -> stmt -> stmt
            | Sloop: stmt -> stmt
            | Sblock: stmt -> stmt
            | Sexit: nat -> stmt            
            | Sreturn: option expr -> stmt
            | Slabel: label -> stmt -> stmt
            | Sgoto: label -> stmt.
       
       FOpaque Definition function : Type := cheat.
       FOpaque Definition function_body : function -> stmt := cheat.
       FOpaque Definition function_locals : function -> list ident := cheat.
       FOpaque Definition function_params : function -> list ident := cheat.       
       FOpaque Definition function_sig : function -> signature := cheat. 
       
       FDefinition fundef := AST.fundef function.       
       FDefinition program : Type := AST.program fundef unit.              
       
       FDefinition funsig := fun (fd: fundef) =>
         match fd with
         | Internal f => function_sig f
         | External ef => cheat (* No external functions *)
         end.
              
       FDefinition genv := Genv.t fundef unit.
       
       (* Function env/stack space *)
       FOpaque Definition fenv : Type := cheat.
       FOpaque Definition empty_fenv : fenv := cheat.
       
       FDefinition env := PTree.t val.            
       FDefinition empty_env : env := PTree.empty val.
       
       MetaData set_params.
       Fixpoint set_params (vl: list val) (il: list ident) {struct il} : self__Cfam.env :=
          match il, vl with
          | i1 :: is, v1 :: vs => PTree.set i1 v1 (set_params vs is)
          | i1 :: is, nil => PTree.set i1 Vundef (set_params nil is)
          | _, _ => PTree.empty val
          end.
       FEnd set_params.

       MetaData set_locals.
       Fixpoint set_locals (il: list ident) (e: self__Cfam.env) {struct il} : self__Cfam.env :=
         match il with
         | nil => e
         | i1 :: is => PTree.set i1 Vundef (set_locals is e)
         end.
       FEnd set_locals.
       
       FDefinition init_env : function -> list val -> env := fun f vargs => 
         set_locals (function_locals f) (set_params vargs (function_params f)).            

       (* Semantics for allocation of variables and binding of parameters at function entry. *)
       FOpaque Definition free_fenv : mem -> fenv -> function -> option mem := cheat.            
       FOpaque Definition alloc_fenv : fenv -> mem -> function -> fenv -> mem -> Prop := cheat.
       
       MetaData create_undef_temps.
       Fixpoint create_undef_temps (temps: list ident) : self__Cfam.env :=
        match temps with
        | nil => PTree.empty val
        | id :: temps' => PTree.set id Vundef (create_undef_temps temps')
       end.
       FEnd create_undef_temps.

       MetaData bind_parameters.
       Fixpoint bind_parameters (formals: list ident) (args: list val)
                    (le: self__Cfam.env) : option self__Cfam.env :=
           match formals, args with
           | nil, nil => Some le
           | id :: xl, v :: vl => bind_parameters xl vl (PTree.set id v le)
           | _, _ => None
           end.
       FEnd bind_parameters.
            
       FInductive cont: Type :=
          | Kstop: cont
          | Kseq: stmt -> cont -> cont
          | Kblock: cont -> cont.
                   
       MetaData state.
       Inductive state: Type :=
         | State :
             self__Cfam.function -> self__Cfam.stmt -> self__Cfam.cont ->
             self__Cfam.fenv -> self__Cfam.env -> mem -> state                 
         | Callstate: self__Cfam.fundef -> list val -> self__Cfam.cont -> mem -> state                    
         | Returnstate : val -> self__Cfam.cont -> mem -> state.
       FEnd state.
            
       FRecursion call_cont about cont motive (fun (_ : cont) => cont) by _rect.
             Case Kstop := Kstop.
             Case Kseq := (fun s c call_cont_c => call_cont_c).
             Case Kblock := (fun c call_cont_c => call_cont_c).
       FEnd call_cont.
               
       FRecursion is_call_cont about cont motive (fun (_ : cont) => Prop) by _rect.
           Case Kstop := True.                   
           Case Kseq := (fun s c call_cont_c => False).
           Case Kblock := (fun c call_cont_c => False).
       FEnd is_call_cont.
            
       FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont)) by _rect. 
           Case Sskip := (fun lbl k => None).
           Case Sset := (fun id e lbl k => None).
           Case Sseq := (fun s1 find_label_s1 s2 find_label_s2 => fun lbl k => 
                                    match find_label_s1 lbl (Kseq s2 k) with 
                                    | Some sk => Some sk 
                                    | None => find_label_s2 lbl k end).
           Case Sifthenelse := (fun e s1 find_label_s1 s2 find_label_s2 => fun lbl k => 
                                    match find_label_s1 lbl k with 
                                    | Some sk => Some sk 
                                    | None => find_label_s2 lbl k end).
           Case Sloop := (fun s1 find_label_s1 => fun lbl k => 
                                    find_label_s1 lbl (Kseq (Sloop s1) k)).                                         
           Case Sblock := (fun s1 find_label_s1 => fun lbl k => find_label_s1 lbl (Kblock k)).
           Case Sexit := (fun n lbl k => None).
           Case Sreturn := (fun _ lbl k => None).
           Case Slabel := (fun lbl' s find_label_s => fun lbl k => 
                                  if ident_eq lbl lbl' then 
                                  Some(s, k) else find_label_s lbl k).
           Case Sgoto := (fun label lbl k => None).
       FEnd find_label.
               
       FRecursion eval_constant about constant motive (fun (_ : constant) => option val) by _rect.
         Case Ointconst := (fun n => Some (Vint n)). 
         Case Ofloatconst := (fun n => Some (Vfloat n)).
         Case Osingleconst := (fun n => Some (Vsingle n)).
         Case Olongconst := (fun n => Some (Vlong n)).
       FEnd eval_constant.
               
       FInductive eval_expr : fenv -> env -> mem -> expr -> val -> Prop :=
           | eval_Evar: forall e le m id v,
               PTree.get id le = Some v ->
               eval_expr e le m (Evar id) v                  
           | eval_Econst: forall e le m cst v,
               eval_constant cst = Some v ->
               eval_expr e le m (Econst cst) v.
                           
       FInductive step : genv -> state -> trace -> state -> Prop :=
              | step_skip_seq: forall ge f s k e le m,
                  step ge (self__Cfam.State f Sskip (Kseq s k) e le m)
                    E0 (self__Cfam.State f s k e le m)
              | step_skip_block: forall ge f k e le m,
                  step ge (self__Cfam.State f Sskip (Kblock k) e le m)
                    E0 (self__Cfam.State f Sskip k e le m)
              | step_skip_call: forall ge f k e le m m',
                  is_call_cont k ->                       
                  free_fenv m e f = Some m' ->
                  step ge (self__Cfam.State f Sskip k e le m)
                    E0 (self__Cfam.Returnstate Vundef k m')
              | step_set: forall ge f id a k e le m v,
                  eval_expr e le m a v ->
                  step ge (self__Cfam.State f (Sset id a) k e le m)
                    E0 (self__Cfam.State f Sskip k e (PTree.set id v le) m)
              | step_seq: forall ge f s1 s2 k e le m,
                  step ge (self__Cfam.State f (Sseq s1 s2) k e le m)
                    E0 (self__Cfam.State f s1 (Kseq s2 k) e le m)
              | step_ifthenelse: forall ge f a s1 s2 k e le m v b,
                  eval_expr e le m a v ->
                  Val.bool_of_val v b ->
                  step ge (self__Cfam.State f (Sifthenelse a s1 s2) k e le m)
                    E0 (self__Cfam.State f (if b then s1 else s2) k e le m)
              | step_loop: forall ge f s k e le m,
                  step ge (self__Cfam.State f (Sloop s) k e le m)
                    E0 (self__Cfam.State f s (Kseq (Sloop s) k) e le m)        
              | step_block: forall ge f s k e le m,
                  step ge (self__Cfam.State f (Sblock s) k e le m)
                    E0 (self__Cfam.State f s (Kblock k) e le m)
              | step_return_0: forall ge f k e le m m',                       
                  free_fenv m e f = Some m' ->
                  step ge (self__Cfam.State f (Sreturn None) k e le m)
                    E0 (self__Cfam.Returnstate Vundef (call_cont k) m')            
              | step_return_1: forall ge f a k e le m v m',
                  eval_expr e le m a v ->
                  free_fenv m e f = Some m' ->
                  step ge (self__Cfam.State f (Sreturn (Some a)) k e le m)
                    E0 (self__Cfam.Returnstate v (call_cont k) m')            
              | step_label: forall ge f lbl s k e le m,
                  step ge (self__Cfam.State f (Slabel lbl s) k e le m)
                    E0 (self__Cfam.State f s k e le m)
              | step_goto: forall ge f lbl k e le m s' k',
                  find_label (function_body f) lbl (call_cont k) = Some(s', k') ->
                  step ge (self__Cfam.State f (Sgoto lbl) k e le m)
                    E0 (self__Cfam.State f s' k' e le m)
              | step_internal_function: forall ge f vargs k m m1 e le,                                               
                  alloc_fenv empty_fenv m f e m1 ->
                  init_env f vargs = le ->                        
                   step ge (self__Cfam.Callstate (Internal f) vargs k m)
                     E0 (self__Cfam.State f (function_body f) k e le m1).
       
       FOpaque Definition is_main_function : fundef -> Prop := cheat.
            
       MetaData initial_state.
       Inductive initial_state (p: self__Cfam.program): self__Cfam.state -> Prop :=
           | initial_state_intro: forall b f m0,
               let ge := Genv.globalenv p in
               Genv.init_mem p = Some m0 ->
               Genv.find_symbol ge p.(prog_main) = Some b ->
               Genv.find_funct_ptr ge b = Some f ->
               self__Cfam.is_main_function f ->
               initial_state p (self__Cfam.Callstate f nil self__Cfam.Kstop m0).
       FEnd initial_state.
            
       MetaData final_state.
       Inductive final_state: self__Cfam.state -> int -> Prop :=
           | final_state_intro: forall r m,
               final_state (self__Cfam.Returnstate (Vint r) self__Cfam.Kstop m) r.
       FEnd final_state.
  FEnd Cfam.

  (* A translation between C family languages *)
  Family Cfamtransl.
      Family Source extends Cfam.
      FEnd Source.

      Family Target extends Cfam.
      FEnd Target.
   
      FRecursion transl_expr about Source.expr motive (fun (_ : Source.expr) => res Target.expr) by _rect.
         Case Evar := (fun id => OK (Target.Evar id)).
         Case Econst := cheat.
      FEnd transl_expr.

      FRecursion transl_stmt about Source.stmt motive (fun (_ : Source.stmt) => res Target.stmt) by _rect.
          Case Sskip := (OK (Target.Sskip)).
          Case Sset := (fun id e =>
                       do te <- transl_expr e;
                       OK (Target.Sset id te)).
          Case Sseq := (fun s1 transl_stmt_s1 s2 transl_stmt_s2 =>                        
                          do ts1 <- transl_stmt_s1; 
                          do ts2 <- transl_stmt_s2; 
                          OK (Target.Sseq ts1 ts2)).
          Case Sifthenelse := (fun e s1 transl_stmt_s1 s2 transl_stmt_s2 =>                               
                                   do te <- transl_expr e;
                                   do ts1 <- transl_stmt_s1;
                                   do ts2 <- transl_stmt_s2;
                                   OK (Target.Sifthenelse te ts1 ts2)).
          Case Sloop := (fun s1 transl_stmt_s1 =>
                            do ts <- transl_stmt_s1;
                            OK (Target.Sloop ts)).
          Case Sblock := (fun s transl_stmt_s =>
                             do ts <- transl_stmt_s;
                             OK (Target.Sblock ts)).
          Case Sexit := (fun n => OK (Target.Sexit n)).
          Case Sreturn := (fun expr =>
                             match expr with
                             | None => OK (Target.Sreturn None)
                             | Some expr =>
                                  do te <- transl_expr expr;
                                  OK (Target.Sreturn (Some te))
                             end).
          Case Slabel := (fun lbl s transl_stmt_s =>                          
                            do ts <- transl_stmt_s;
                            OK (Target.Slabel lbl ts)).
          Case Sgoto := (fun lbl => OK (Target.Sgoto lbl)).
      FEnd transl_stmt.
      
      FOpaque Definition transl_function : Source.function -> res Target.function :=
        cheat.
      FOpaque Definition transl_fundef : Source.fundef -> res Target.fundef := 
        cheat.

      (* Simulation Proof *)      
      (* Invariant on abstract call stack *)
      MetaData frame.
      Inductive frame : Type :=
          Frame(tf: self__Cfamtransl.Target.function)
               (e: self__Cfamtransl.Source.fenv)
               (le: self__Cfamtransl.Source.env)
               (te: self__Cfamtransl.Target.env)
               (sp: self__Cfamtransl.Target.fenv)
               (lo hi: block).
      FEnd frame.

      FDefinition callstack : Type := list frame.
          
      (* This subsumes "match_env" for the C family lanauges *)
      FOpaque Definition match_callstack : 
         meminj -> mem -> mem ->
         callstack -> block -> block -> Prop := cheat.
          
      FOpaque Definition match_mem : meminj -> mem -> mem -> Prop := cheat.
      
      FInductive match_value : meminj -> val -> val -> Prop := 
        | match_value_refl : forall f v, match_value f v v
        | match_value_undef : forall f v, match_value f Vundef v.                                                     
        
      FInductive match_values : meminj -> list val -> list val -> Prop :=
        | match_values_nil : forall mi,
          match_values mi nil nil
        | match_values_cons : forall mi v v' vl vl' ,
            match_value mi v v' -> match_values mi vl vl'->
            match_values mi (v :: vl) (v' :: vl').
          
      FInductive match_cont: Source.cont -> Target.cont -> Prop :=
         | match_Kstop:
             match_cont Source.Kstop Target.Kstop
         | match_Kseq: forall s k ts tk,
             transl_stmt s = OK ts ->
             match_cont k tk ->
             match_cont (Source.Kseq s k) (Target.Kseq ts tk)
         | match_Kblock: forall k tk,
             match_cont k tk ->
             match_cont (Source.Kblock k) (Target.Kblock tk).
      
      MetaData match_states.
      Inductive match_states: 
         self__Cfamtransl.Source.state -> self__Cfamtransl.Target.state -> Prop :=
          | match_state:
              forall fn s k e le m tfn ts tk sp te tm f lo hi cs
              (TRF: self__Cfamtransl.transl_function fn = OK tfn)
              (TR: self__Cfamtransl.transl_stmt s = OK ts)
              (MINJ: self__Cfamtransl.match_mem f m tm)
              (MCS: self__Cfamtransl.match_callstack f m tm
                       (self__Cfamtransl.Frame tfn e le te sp lo hi :: cs)
                       (Mem.nextblock m) (Mem.nextblock tm))
              (MK: self__Cfamtransl.match_cont k tk),
              match_states (self__Cfamtransl.Source.State fn s k e le m)
                           (self__Cfamtransl.Target.State tfn ts tk sp te tm)
         | match_callstate:
              forall fd args k m tfd targs tk tm f cs
              (TR: self__Cfamtransl.transl_fundef fd = OK tfd)
              (MINJ: self__Cfamtransl.match_mem f m tm)
              (MCS: self__Cfamtransl.match_callstack f m tm cs (Mem.nextblock m) (Mem.nextblock tm))
              (MK: self__Cfamtransl.match_cont k tk)
              (ISCC: self__Cfamtransl.Source.is_call_cont k)
              (ARGSINJ: self__Cfamtransl.match_values f args targs),
              match_states (self__Cfamtransl.Source.Callstate fd args k m)
                           (self__Cfamtransl.Target.Callstate tfd targs tk tm)
          | match_returnstate:
              forall v k m tv tk tm f cs
              (MINJ: self__Cfamtransl.match_mem f m tm)
              (MCS: self__Cfamtransl.match_callstack f m tm cs (Mem.nextblock m) (Mem.nextblock tm))
              (MK: self__Cfamtransl.match_cont k tk)
              (RESINJ: self__Cfamtransl.match_value f v tv),
              match_states (self__Cfamtransl.Source.Returnstate v k m)
                           (self__Cfamtransl.Target.Returnstate tv tk tm).
      FEnd match_states.
             
      FInduction transl_expr_correct about Source.eval_expr motive 
         (fun  e le m a v (_ : Source.eval_expr e le m a v) => 
            forall f m tm tf te sp lo hi cs
                (MINJ: match_mem f m tm)
                (MATCH: match_callstack f m tm
                         (self__Cfamtransl.Frame tf e le te sp lo hi :: cs)
                         (Mem.nextblock m) (Mem.nextblock tm)),                
                    forall ta
                (TR: transl_expr a = OK ta),
              exists tv,
                 Target.eval_expr sp te tm ta tv
              /\ match_value f v tv).
      FProof.
        + intros. apply cheat.
        + intros. apply cheat.
      Qed. FEnd transl_expr_correct.
      
      (* call stack match even with set *)
      FLemma match_callstack_set_temp:
           forall f e le te sp lo hi cs bound tbound m tm tf id v tv,
           match_value f v tv ->
           match_callstack f m tm (self__Cfamtransl.Frame tf e le te sp lo hi :: cs) bound tbound ->
           match_callstack f m tm (self__Cfamtransl.Frame tf e (PTree.set id v le) (PTree.set id tv te) sp lo hi :: cs) bound tbound.
      FProofLemma.
      Admitted.
      CloseFLemma.
      
      (* Call cont lemma *)
      (*FInduction match_is_call_cont:
         forall tfn te sp tm k tk cenv xenv cs,
         match_cont k tk ->
         Source.is_call_cont k ->
         exists tk',
           star Target.step tge (Target.State tfn Sskip tk sp te tm)
                      E0 (Target.State tfn Sskip tk' sp te tm)
           /\ Target.is_call_cont tk'
           /\ Target.match_cont k tk' cenv nil cs.*)

      (* Preservation of match_callstack by freeing  function env allocated at function entry *)      
      FLemma match_callstack_freelist:
        forall f sf tf e le te sp lo hi cs m m' tm,
          match_mem f m tm ->          
          Source.free_fenv m e sf = Some m' -> 
          match_callstack f m tm (self__Cfamtransl.Frame tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
          exists tm',            
            Target.free_fenv tm sp tf = Some tm' 
          /\ match_callstack f m' tm' cs (Mem.nextblock m') (Mem.nextblock tm')
          /\  match_mem f m' tm'.
      FProofLemma.
        Admitted.
      CloseFLemma.

      (* Find label *)
      FInduction transl_find_label about Source.stmt motive
         (fun (s : Source.stmt) => forall k ts tk lbl,
              transl_stmt s = OK ts -> 
              match_cont k tk -> 
              match Source.find_label s lbl k with
              | None => Target.find_label ts lbl tk = None
              | Some(s', k') =>
                  exists ts', exists tk',
                    Target.find_label ts lbl tk = Some(ts', tk')
                 /\ transl_stmt s' = OK ts'
                 /\ match_cont k' tk'
              end).
      FProof.
      (* Skip *)
      + apply cheat.
      (* Set *)
      + apply cheat.
      (* Seq *)
      + apply cheat.
      (* Sifthenelse *)
      + apply cheat.
      (* Sloop *)
      + apply cheat.
      (* Sblock *)
      + apply cheat.
      (* Sexit *)
      + apply cheat.
       (* Sreturn *)
      + apply cheat.
       (* Slabel *)
      + apply cheat.
       (* Sgoto *)
      + apply cheat.
      Qed. FEnd transl_find_label.
     
      (*FInduction transl_find_label_body:
          forall cenv xenv size f tf k tk cs lbl s' k',
          transl_funbody cenv size f = OK tf ->
          match_cont k tk cenv xenv cs ->
          Csharpminor.find_label lbl f.(Csharpminor.fn_body) (Csharpminor.call_cont k) = Some (s', k') ->
          exists ts', exists tk', exists xenv',
             find_label lbl tf.(fn_body) (call_cont tk) = Some(ts', tk')
          /\ transl_stmt cenv xenv' s' = OK ts'
          /\ match_cont k' tk' cenv xenv' cs.*)
      
      FOpaque Definition measure : Source.state -> nat := cheat.

      FInduction transl_step_correct about Source.step motive
        (fun ge S1 t S2 (_ : Source.step ge S1 t S2) => 
        forall prog tprog tge, (* match_prog prog tprog -> *)
                Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->               
          forall T1, match_states S1 T1 -> 
          (exists T2, plus Target.step tge T1 t T2 /\ match_states S2 T2) \/
          (measure S2 < measure S1 /\ t = E0 /\ match_states S2 T1)%nat).
      FProof.
      
          (* skip seq *)
          + unfold self__Cfamtransl.__motiveTtransl_step_correct.
            intros ge f s k e le m prog tprog tge H G. 
            intros T1 MSTATE. inv MSTATE.
            rewrite -> self__Cfamtransl.transl_stmt_Sskip_eq in TR.
            unfold self__Cfamtransl.transl_stmtSskip in TR.
            monadInv TR. 
            left. econstructor. split. apply plus_one. 
            
            (* We need to somehow prove that *)
            (* match_cont (self__Cfamtransl.Source.Kseq s k) tk ==> tk = Kseq s' k' *)
            apply (* self__Cfamtransl.Target.step_skip_seq*) cheat.
            apply self__Cfamtransl.match_state with (f := f0) (lo := lo) (hi := hi) (cs := cs).            
            apply TRF.
            apply cheat. (* prove TR again?? *)
            apply MINJ.
            apply MCS.
            apply cheat. (* This is in a way a consequence of the call_cont theorem above *)
            
          (* skip block *)
          + unfold self__Cfamtransl.__motiveTtransl_step_correct.
            intros ge f k e le m prog tprog tge H G. 
            intros T1 MSTATE. inv MSTATE.
            rewrite -> self__Cfamtransl.transl_stmt_Sskip_eq in TR.
            unfold self__Cfamtransl.transl_stmtSskip in TR.
            monadInv TR.
            left. econstructor. split. apply plus_one. 
            (* Same as above, we need to show the cont is a Kblock *)
            apply (*self__Cfamtransl.Target.step_skip_block*) cheat.
            eapply self__Cfamtransl.match_state.
            apply TRF.
            rewrite -> self__Cfamtransl.transl_stmt_Sskip_eq.
            unfold self__Cfamtransl.transl_stmtSskip.
            reflexivity.
            apply MINJ.
            apply MCS.
            apply cheat. (* call_cont *)

          (* skip call *)
          + unfold self__Cfamtransl.__motiveTtransl_step_correct.
            intros ge f k e le m m' CC FENV prog tprog tge H G. 
            intros T1 MSTATE. inv MSTATE.
            rewrite -> self__Cfamtransl.transl_stmt_Sskip_eq in TR.
            unfold self__Cfamtransl.transl_stmtSskip in TR.
            monadInv TR. 
            left. econstructor. split. apply plus_one. 
            apply self__Cfamtransl.Target.step_skip_call.
            apply cheat. (* exploit match_is_call_cont *)
            apply cheat (*  exploit match_callstack_freelist *).
            apply self__Cfamtransl.match_returnstate with (f := f0) (cs := cs).
            apply cheat. (*  exploit match_callstack_freelist *)
            apply cheat. (* match call stack *)
            apply MK.
            apply self__Cfamtransl.match_value_refl.

          (* set *)
          + unfold self__Cfamtransl.__motiveTtransl_step_correct.
            intros ge f id a k e le m v EVAL prog tprog tge H G. 
            intros T1 MSTATE. inv MSTATE.                        
            rewrite -> self__Cfamtransl.transl_stmt_Sset_eq in TR.
            unfold self__Cfamtransl.transl_stmtSset in TR.            
            monadInv TR. 
            exploit self__Cfamtransl.transl_expr_correct; eauto.            
            intros H. destruct H as [tv [EV MV]].
            left. econstructor. split. apply plus_one.             
            eapply self__Cfamtransl.Target.step_set.
            apply EV.
            exploit self__Cfamtransl.match_callstack_set_temp; eauto.
            intros G.
            eapply self__Cfamtransl.match_state; eauto.
            rewrite -> self__Cfamtransl.transl_stmt_Sskip_eq.
            unfold self__Cfamtransl.transl_stmtSskip. reflexivity.            
          
          (* seq *)
          + unfold self__Cfamtransl.__motiveTtransl_step_correct.
            intros ge f s1 s2 k e le m prog tprog tge H G. 
            intros T1 MSTATE. inv MSTATE.                                    
            rewrite -> self__Cfamtransl.transl_stmt_Sseq_eq in TR.
            unfold self__Cfamtransl.transl_stmtSseq in TR.
            monadInv TR. 
            left. econstructor. split. apply plus_one. 
            apply self__Cfamtransl.Target.step_seq.
            eapply self__Cfamtransl.match_state; (try eassumption ;apply self__Cfamtransl.match_Kseq; eassumption).
              
          (* ifthenelse *)
          + unfold self__Cfamtransl.__motiveTtransl_step_correct.
            intros ge f a s1 s2 k e le m v b EV V prog tprog tge H G. 
            intros T1 MSTATE. inv MSTATE.
            rewrite -> self__Cfamtransl.transl_stmt_Sifthenelse_eq in TR.
            unfold self__Cfamtransl.transl_stmtSifthenelse in TR.            
            monadInv TR.
            exploit self__Cfamtransl.transl_expr_correct. apply EV. apply MINJ. apply MCS. apply EQ.
            intros TV.
            left. econstructor. split. apply plus_one. 
            eapply self__Cfamtransl.Target.step_ifthenelse.
            destruct TV as [tv [H1 H2]].
            assert (H_eq: tv = v). { apply cheat. }
            rewrite <- H_eq. apply H1. apply V. 
            destruct b.
            ++ eapply self__Cfamtransl.match_state; eassumption. 
            ++ eapply self__Cfamtransl.match_state. apply TRF. apply EQ0.
               apply MINJ. apply MCS. apply MK.

          (* loop *)
          + 
            unfold self__Cfamtransl.__motiveTtransl_step_correct.
            intros ge f s k e le m prog tprog tge H G. 
            intros T1 MSTATE. inv MSTATE.            
            rewrite -> self__Cfamtransl.transl_stmt_Sloop_eq in TR.
            unfold self__Cfamtransl.transl_stmtSloop in TR.            
            monadInv TR. 
            left. econstructor. split. apply plus_one. 
            apply self__Cfamtransl.Target.step_loop.            
            eapply self__Cfamtransl.match_state; eauto.            
            - apply self__Cfamtransl.match_Kseq.  
           rewrite -> self__Cfamtransl.transl_stmt_Sloop_eq.
            unfold self__Cfamtransl.transl_stmtSloop. 
            (* (do ts <- self__Cfamtransl.transl_stmt s; OK (self__Cfamtransl.Target.Sloop ts)) =
                OK (self__Cfamtransl.Target.Sloop x) *)
            apply cheat. apply MK.     
            
          (* block *)
          + unfold self__Cfamtransl.__motiveTtransl_step_correct.
            intros ge f s k e le m prog tprog tge H G. 
            intros T1 MSTATE. inv MSTATE. 
            rewrite -> self__Cfamtransl.transl_stmt_Sblock_eq in TR.
            unfold self__Cfamtransl.transl_stmtSblock in TR.
            monadInv TR. 
            left. econstructor. split. apply plus_one. 
            apply self__Cfamtransl.Target.step_block.
            apply self__Cfamtransl.match_state with (f := f0) (lo := lo) (hi := hi) (cs := cs).
            apply TRF. apply EQ. apply MINJ. apply MCS. apply self__Cfamtransl.match_Kblock.  apply MK.
            
          (* return none *)
          + unfold self__Cfamtransl.__motiveTtransl_step_correct.
            intros ge f k e le m m' F prog tprog tge H G. 
            intros T1 MSTATE. inv MSTATE. 
            rewrite -> self__Cfamtransl.transl_stmt_Sreturn_eq in TR.
            unfold self__Cfamtransl.transl_stmtSreturn in TR.
            monadInv TR.
            left. econstructor. split. apply plus_one. 
            apply self__Cfamtransl.Target.step_return_0.
            (* Some abstract lemma needed here  *)
            apply cheat. (* exploit match_callstack_freelist*)
            eapply self__Cfamtransl.match_returnstate.
            apply cheat. (* match_mem *)
            apply cheat. (* match_callstack *)
            apply cheat. (* match_cont (call_cont s) (call_cont tk) *)
            apply self__Cfamtransl.match_value_refl.
            
          (* return some *)
          + unfold self__Cfamtransl.__motiveTtransl_step_correct.
            intros ge f a k e le m v m' E F prog tprog tge H G. 
            intros T1 MSTATE. inv MSTATE. 
            rewrite -> self__Cfamtransl.transl_stmt_Sreturn_eq in TR.
            unfold self__Cfamtransl.transl_stmtSreturn in TR.
            monadInv TR.
            left. econstructor. split. apply plus_one. 
            apply self__Cfamtransl.Target.step_return_1.
            apply cheat. (* eval expr correct lemma *)
            apply cheat. (* free env lemma *)
            apply self__Cfamtransl.match_returnstate with (f := f0) (cs := cs).
            apply cheat. (* match mem *)
            apply cheat. (* match call stack *)
            apply cheat. (* match cont with call cont *)
            apply cheat. (* match value *)

          (* label *)
          + unfold self__Cfamtransl.__motiveTtransl_step_correct.
            intros ge f lbl s k e le m prog tprog tge H G. 
            intros T1 MSTATE. inv MSTATE. 
            rewrite -> self__Cfamtransl.transl_stmt_Slabel_eq in TR.
            unfold self__Cfamtransl.transl_stmtSlabel in TR.
            monadInv TR.
            left. econstructor. split. apply plus_one. 
            apply self__Cfamtransl.Target.step_label.
            apply self__Cfamtransl.match_state with (f := f0) (lo := lo) (hi := hi) (cs := cs).
            apply TRF. apply EQ. apply MINJ. apply MCS. apply MK.            
            
          (* goto *)
          + unfold self__Cfamtransl.__motiveTtransl_step_correct.
            intros ge f lbl k e le m s' k' FL prog tprog tge H G. 
            intros T1 MSTATE. inv MSTATE.
            exploit self__Cfamtransl.transl_find_label; eauto. intros.
            rewrite -> self__Cfamtransl.transl_stmt_Sgoto_eq in TR.
            unfold self__Cfamtransl.transl_stmtSgoto in TR.
            monadInv TR.            
            left. econstructor. split. apply plus_one.
            apply self__Cfamtransl.Target.step_goto.
            apply cheat. (* Use transl_find_label_body *)
            eapply self__Cfamtransl.match_state.
            apply TRF. apply cheat (* stmt used by find_label *). apply MINJ. apply MCS.
            apply cheat (* const used by find_label *).
                        
          (* internal function *)
          + 
            apply cheat.
            (*unfold self__Cfamtransl.__motiveTtransl_step_correct.
            intros ge f vargs k m m1 e le FENV ENV prog tprog tge H G. 
            intros T1 MSTATE. inv MSTATE.            
            left. econstructor. split. apply plus_one.
             apply self__Cfamtransl.Target.step_internal_function.*)            
        Qed.
      FEnd transl_step_correct.
    
     FLemma transl_initial_states:
          forall S prog tprog ge, Csharpminor.Sem.initial_state prog S ->
          transl_program prog = OK tprog ->
          exists R, Cminor.Sem.initial_state tprog R /\ match_states ge S R.
            FProofLemma.
              apply cheat.
            Qed.
     CloseFLemma.
        
     FLemma transl_final_states:
          forall S R r ge,
          match_states ge S R -> Csharpminor.Sem.final_state S r -> Cminor.Sem.final_state R r.
            FProofLemma.
              intros. inv H0. inv H. inv MK. inv RESINJ. constructor. Qed.            
     CloseFLemma.     
  FEnd Cfamtransl.
         
  Family C extends Cfam.
      
      FInductive expr : Type :=
        | Eval : val -> type -> expr (* constant *)
        | Evar : ident -> type -> expr (* variable *)        
        | Ecast : expr -> type -> expr (* type cast (ty)r *)
        | Eseqand : expr -> expr -> type -> expr (* sequential "and" r1 && r2 *)
        | Eseqor : expr -> expr -> type -> expr (* sequential "or" r1 || r2 *)
        | Econdition : expr -> expr -> expr -> type -> expr (* conditional r1 ? r2 : r3 *)
        | Esizeof : type -> type -> expr (* size of a type *)
        | Ealignof : type -> type -> expr (* natural alignment of a type *)        
        | Ecomma : expr -> expr -> type -> expr (* sequence expression r1, r2 *)                
        | Eparen : expr -> type -> type -> expr. 
        
        FRecursion typeof : (e : expr) -> type.
          Case Eval v ty := ty.
          Case Evar x ty := ty.          
          Case Ecast r ty := ty. 
          Case Eseqand r1 r2 ty := ty. 
          Case Eseqor r1 r2 ty := ty. 
          Case Econdition r1 r2 r3 ty := ty.
          Case Esizeof ty' ty := ty.
          Case Ealignof ty' ty := ty.          
          Case Ecomma r1 r2 ty := ty.
          Case Eparen e ty' ty := ty.
        FEnd typeof.

      FDefinition label := ident.
      
      FInductive statement : Type :=        
        | Sdo : expr -> statement(* evaluate expression for side effects *)        
        | Sifthenelse : expr -> statement -> statement -> statement(* conditional *)
        | Swhile : expr -> statement -> statement(* while loop *)
        | Sdowhile : expr -> statement -> statement(* do loop *)
        | Sfor: statement -> expr -> statement -> statement -> statement(* for loop *)
        | Sbreak : statement(* break statement *)
        | Scontinue : statement(* continue statement *)
        | Sreturn : option expr -> statement. (* return statement *)
      
      MetaData function.
      Record function : Type := mkfunction {
        fn_return: self__Imp.type;
        fn_callconv: calling_convention;
        fn_params: list (ident * self__Imp.type);
        fn_vars: list (ident * self__Imp.type);
        fn_body: self__C.statement
      }.
      FEnd function.

      FDefinition var_names := fun (vars: list(ident * type)) =>
        List.map (@fst ident type) vars.

      FDefinition fundef := AST.fundef function.

      FDefinition type_of_function : function -> type := fun f => 
         self__Imp.Tfunction (self__Imp.type_of_params (self__C.fn_params f)) 
           (self__C.fn_return f) (self__C.fn_callconv f).
       
       FDefinition type_of_fundef : fundef -> type := fun f =>
          match f with
          | Internal fd => type_of_function fd
          | _ => cheat (* TODO: We don't have External in the base compiler *)
          end.

      FDefinition program := AST.program fundef type.

      FOverride Definition fenv := PTree.t (block * Z).
      FOverride Definition empty_fenv := PTree.empty (block * Z).                    

      FDefinition block_of_binding := fun (id_b_sz: ident * (block * Z)) => 
           match id_b_sz with (id, (b, sz)) => (b, 0, sz) end.

      FDefinition blocks_of_env : fenv -> list (block * Z * Z) := fun e => 
          List.map block_of_binding (PTree.elements e).          

      FOverride Definition free_fenv := fun m e f =>
         Mem.free_list m (blocks_of_env e).                  

      FInductive cont: Type :=              
          | Kdo: cont -> cont(* Kdo k = after x in x; *)              
          | Kifthenelse: statement -> statement -> cont -> cont(* Kifthenelse s1 s2 k = after x in if (x) { s1 } else { s2 } *)
          | Kwhile1: expr -> statement -> cont -> cont(* Kwhile1 x s k = after x in while(x) s *)
          | Kwhile2: expr -> statement -> cont -> cont(* Kwhile x s k = after s in while (x) s *)
          | Kdowhile1: expr -> statement -> cont -> cont(* Kdowhile1 x s k = after s in do s while (x) *)
          | Kdowhile2: expr -> statement -> cont -> cont(* Kdowhile2 x s k = after x in do s while (x) *)
          | Kfor2: expr -> statement -> statement -> cont -> cont(* Kfor2 e2 e3 s k = after e2 in for(e1;e2;e3) s *)
          | Kfor3: expr -> statement -> statement -> cont -> cont(* Kfor3 e2 e3 s k = after s in for(e1;e2;e3) s *)
          | Kfor4: expr -> statement -> statement -> cont -> cont(* Kfor4 e2 e3 s k = after e3 in for(e1;e2;e3) s *)              
          | Kreturn: cont -> cont. (* Kreturn k = after e in return e; *)              

      FRecursion call_cont about cont motive (fun (c : cont) => cont) by _rect.            
          Case Kdo k := k.            
          Case Kifthenelse s1 s2 k := (call_cont k).
          Case Kwhile1 e s k := (call_cont k).
          Case Kwhile2 e s k := (call_cont k).
          Case Kdowhile1 e s k := (call_cont k).
          Case Kdowhile2 e s k := (call_cont k).
          Case Kfor2 e2 e3 s k := (call_cont k).
          Case Kfor3 e2 e3 s k := (call_cont k).
          Case Kfor4 e2 e3 s k := (call_cont k).
          Case Kreturn k := (call_cont k).            
      FEnd call_cont.

        FRecursion is_call_cont about cont motive (fun (c : cont) => Prop) by _rect.          
          Case Kdo k := False.          
          Case Kifthenelse s1 s2 k := False.
          Case Kwhile1 e s k := False.
          Case Kwhile2 e s k := False.
          Case Kdowhile1 e s k := False.
          Case Kdowhile2 e s k := False.
          Case Kfor2 e2 e3 s k := False.
          Case Kfor3 e2 e3 s k := False.
          Case Kfor4 e2 e3 s k := False.
          Case Kreturn k := False.          
        FEnd is_call_cont.

        FInductive state: Type :=          
          | ExprState : (* reduction of an expression *)
               function ->
               expr ->
               cont ->
               env ->
               mem -> state          
          | Stuckstate : state. (* undefined behavior occurred *)
        
        FRecursion find_label about statement motive (fun (_ : statement) => label -> cont -> option (statement * cont)) by _rect.          
          Case Sdo r := (fun lbl k => None).                    
          Case Swhile a s1 := (fun lbl k => find_label s1 lbl (Kwhile2 a s1 k)).
          Case Sdowhile a s1 := (fun lbl k => find_label s1 lbl (Kdowhile1 a s1 k)).
          Case Sfor a1 a2 a3 s1 := 
              (fun lbl k => match find_label a1 lbl (Kseq (Sfor Sskip a2 a3 s1) k) with 
                            | Some sk => Some sk 
                            | None => match find_label s1 lbl (Kfor3 a2 a3 s1 k) with 
                                      | Some sk => Some sk 
                                      | None => find_label a3 lbl (Kfor4 a2 a3 s1 k) end end).
          Case Sbreak := (fun lbl k => None).
          Case Scontinue := (fun lbl k => None).          
        FEnd find_label.
                
        MetaData bool_val.
        Axiom bool_val : val -> self__Imp.type -> mem -> option bool.
        FEnd bool_val.

        MetaData sizeof.
           Axiom sizeof : (* self__Sem.composite_env -> *) self__Imp.type -> Z. 
        FEnd sizeof.      
                
        MetaData alignof.
        Axiom alignof : (* self__Imp.Clight.Sem.composite_env ->*) self__Imp.type -> Z.
        FEnd alignof.

        MetaData sem_cast.
            Axiom sem_cast : val -> self__Imp.type -> self__Imp.type -> mem -> option val.
        FEnd sem_cast.                

        FInductive eval_simple_rvalue: genv -> env -> mem -> expr -> val -> Prop :=
           | esr_val: forall ge e m v ty,
               eval_simple_rvalue ge e m (Eval v ty) v                                   
           | esr_cast: forall ge e m ty r1 v1 v,
               eval_simple_rvalue ge e m r1 v1 ->
               sem_cast v1 (typeof r1) ty m = Some v ->
               eval_simple_rvalue ge e m (Ecast r1 ty) v
           | esr_sizeof: forall ge e m ty1 ty,
               eval_simple_rvalue ge e m (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (sizeof (* ge *) ty1)))                                  
           | esr_alignof: forall ge e m ty1 ty,
               eval_simple_rvalue ge e m (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (alignof (* ge *) ty1))).        
                
        FRecursion is_val about expr motive (fun (e : expr) => Prop) by _rect.
            Case Eval v ty := True.
            Case Evar x ty := False.
            Case Ecast r ty := False.
            Case Eseqand r1 r2 ty := False.
            Case Eseqor r1 r2 ty := False.
            Case Econdition r1 r2 r3 ty := False.
            Case Esizeof ty' ty := False.
            Case Ealignof ty' ty := True.
            Case Ecomma r1 r2 ty := False.
            Case Eparen e ty' ty := False.
        FEnd is_val.
        
        MetaData kind.
        Inductive kind : Type := LV | RV.
        FEnd kind.
        
        FInductive leftcontext: kind -> kind -> (expr -> expr) -> Prop :=
        | lctx_top: forall k,
            leftcontext k k (fun x => x)  
        | lctx_cast: forall k F ty,
            leftcontext k self__Sem.RV F -> leftcontext k self__Sem.RV (fun x => Ecast (F x) ty)
        | lctx_seqand: forall k F r2 ty,
            leftcontext k self__Sem.RV F -> leftcontext k self__Sem.RV (fun x => Eseqand (F x) r2 ty)
        | lctx_seqor: forall k F r2 ty,
            leftcontext k self__Sem.RV F -> leftcontext k self__Sem.RV (fun x => Eseqor (F x) r2 ty)
        | lctx_condition: forall k F r2 r3 ty,
            leftcontext k self__Sem.RV F -> leftcontext k self__Sem.RV (fun x => Econdition (F x) r2 r3 ty)
        | lctx_comma: forall k F e2 ty,
            leftcontext k self__Sem.RV F -> leftcontext k self__Sem.RV (fun x => Ecomma (F x) e2 ty)
        | lctx_paren: forall k F tycast ty,
            leftcontext k self__Sem.RV F -> leftcontext k self__Sem.RV (fun x => Eparen (F x) tycast ty).

        FInductive estep: genv -> state -> trace -> state -> Prop :=
             | step_expr: forall ge f r k e m v ty,
                 eval_simple_rvalue ge e m r v ->
                 is_val r ->
                 ty = typeof r ->
                 estep ge (ExprState f r k e m)
                    E0 (ExprState f (Eval v ty) k e m)               
             | step_seqand_true: forall ge f F r1 r2 ty k e m v,
                 leftcontext self__Sem.RV self__Sem.RV F ->
                 eval_simple_rvalue ge e m r1 v ->
                 bool_val v (typeof r1) m = Some true ->
                 estep ge (ExprState f (F (Eseqand r1 r2 ty)) k e m)
                    E0 (ExprState f (F (Eparen r2 self__Imp.type_bool ty)) k e m)
             | step_seqand_false: forall ge f F r1 r2 ty k e m v,
                 leftcontext self__Sem.RV self__Sem.RV F ->
                 eval_simple_rvalue ge e m r1 v ->
                 bool_val v (typeof r1) m = Some false ->
                 estep ge (ExprState f (F (Eseqand r1 r2 ty)) k e m)
                    E0 (ExprState f (F (Eval (Vint Int.zero) ty)) k e m)
             | step_seqor_true: forall ge f F r1 r2 ty k e m v,
                 leftcontext self__Sem.RV self__Sem.RV F ->
                 eval_simple_rvalue ge e m r1 v ->
                 bool_val v (typeof r1) m = Some true ->
                 estep ge (ExprState f (F (Eseqor r1 r2 ty)) k e m)
                    E0 (ExprState f (F (Eval (Vint Int.one) ty)) k e m)
             | step_seqor_false: forall ge f F r1 r2 ty k e m v,
                 leftcontext self__Sem.RV self__Sem.RV F ->
                 eval_simple_rvalue ge e m r1 v ->
                 bool_val v (typeof r1) m = Some false ->
                 estep ge (ExprState f (F (Eseqor r1 r2 ty)) k e m)
                    E0 (ExprState f (F (Eparen r2 self__Imp.type_bool ty)) k e m)
             | step_condition: forall ge f F r1 r2 r3 ty k e m v b,
                 leftcontext self__Sem.RV self__Sem.RV F ->
                 eval_simple_rvalue ge e m r1 v ->
                 bool_val v (typeof r1) m = Some b ->
                 estep ge (ExprState f (F (Econdition r1 r2 r3 ty)) k e m)
                    E0 (ExprState f (F (Eparen (if b then r2 else r3) ty ty)) k e m)
             | step_comma: forall ge f F r1 r2 ty k e m v,
                 leftcontext self__Sem.RV self__Sem.RV F ->
                 eval_simple_rvalue ge e m r1 v ->
                 ty = typeof r2 ->
                 estep ge (ExprState f (F (Ecomma r1 r2 ty)) k e m)
                    E0 (ExprState f (F r2) k e m)
             | step_paren: forall ge f F r tycast ty k e m v1 v,
                 leftcontext self__Sem.RV self__Sem.RV F ->
                 eval_simple_rvalue ge e m r v1 ->
                 sem_cast v1 (typeof r) tycast m = Some v ->
                 estep ge (ExprState f (F (Eparen r tycast ty)) k e m)
                    E0 (ExprState f (F (Eval v ty)) k e m).
        
        FInductive sstep: genv -> state -> trace -> state -> Prop :=
            | step_do_1: forall ge f x k e m,
                sstep ge (State f (Sdo x) k e m)
                  E0 (ExprState f x (Kdo k) e m)
            | step_do_2: forall ge f v ty k e m,
                sstep ge (ExprState f (Eval v ty) (Kdo k) e m)
                  E0 (State f Sskip k e m)
            | step_seq: forall ge f s1 s2 k e m,
                sstep ge (State f (Ssequence s1 s2) k e m)
                  E0 (State f s1 (Kseq s2 k) e m)
            | step_skip_seq: forall ge f s k e m,
                sstep ge (State f Sskip (Kseq s k) e m)
                  E0 (State f s k e m)
            | step_continue_seq: forall ge f s k e m,
                sstep ge (State f Scontinue (Kseq s k) e m)
                  E0 (State f Scontinue k e m)
            | step_break_seq: forall ge f s k e m,
                sstep ge (State f Sbreak (Kseq s k) e m)
                  E0 (State f Sbreak k e m)
            | step_ifthenelse_1: forall ge f a s1 s2 k e m,
                sstep ge (State f (Sifthenelse a s1 s2) k e m)
                  E0 (ExprState f a (Kifthenelse s1 s2 k) e m)
            | step_ifthenelse_2: forall ge f v ty s1 s2 k e m b,
                bool_val v ty m = Some b ->
                sstep ge (ExprState f (Eval v ty) (Kifthenelse s1 s2 k) e m)
                  E0 (State f (if b then s1 else s2) k e m)
            | step_while: forall ge f x s k e m,
                sstep ge (State f (Swhile x s) k e m)
                  E0 (ExprState f x (Kwhile1 x s k) e m)
            | step_while_false: forall ge f v ty x s k e m,
                bool_val v ty m = Some false ->
                sstep ge (ExprState f (Eval v ty) (Kwhile1 x s k) e m)
                  E0 (State f Sskip k e m)
            | step_while_true: forall ge f v ty x s k e m ,
                bool_val v ty m = Some true ->
                sstep ge (ExprState f (Eval v ty) (Kwhile1 x s k) e m)
                  E0 (State f s (Kwhile2 x s k) e m)
            | step_skip_or_continue_while: forall ge f s0 x s k e m,
                s0 = Sskip \/ s0 = Scontinue ->
                sstep ge (State f s0 (Kwhile2 x s k) e m)
                  E0 (State f (Swhile x s) k e m)
            | step_break_while: forall ge f x s k e m,
                sstep ge (State f Sbreak (Kwhile2 x s k) e m)
                  E0 (State f Sskip k e m)
            | step_dowhile: forall ge f a s k e m,
                sstep ge (State f (Sdowhile a s) k e m)
                  E0 (State f s (Kdowhile1 a s k) e m)
            | step_skip_or_continue_dowhile: forall ge f s0 x s k e m,
                s0 = Sskip \/ s0 = Scontinue ->
                sstep ge (State f s0 (Kdowhile1 x s k) e m)
                  E0 (ExprState f x (Kdowhile2 x s k) e m)
            | step_dowhile_false: forall ge f v ty x s k e m,
                bool_val v ty m = Some false ->
                sstep ge (ExprState f (Eval v ty) (Kdowhile2 x s k) e m)
                  E0 (State f Sskip k e m)
            | step_dowhile_true: forall ge f v ty x s k e m,
                bool_val v ty m = Some true ->
                sstep ge (ExprState f (Eval v ty) (Kdowhile2 x s k) e m)
                  E0 (State f (Sdowhile x s) k e m)
            | step_break_dowhile: forall ge f a s k e m,
                sstep ge (State f Sbreak (Kdowhile1 a s k) e m)
                  E0 (State f Sskip k e m)
            | step_for_start: forall ge f a1 a2 a3 s k e m,
                a1 <> Sskip ->
                sstep ge (State f (Sfor a1 a2 a3 s) k e m)
                  E0 (State f a1 (Kseq (Sfor Sskip a2 a3 s) k) e m)
            | step_for: forall ge f a2 a3 s k e m,
                sstep ge (State f (Sfor Sskip a2 a3 s) k e m)
                  E0 (ExprState f a2 (Kfor2 a2 a3 s k) e m)
            | step_for_false: forall ge f v ty a2 a3 s k e m,
                bool_val v ty m = Some false ->
                sstep ge (ExprState f (Eval v ty) (Kfor2 a2 a3 s k) e m)
                  E0 (State f Sskip k e m)
            | step_for_true: forall ge f v ty a2 a3 s k e m,
                bool_val v ty m = Some true ->
                sstep ge (ExprState f (Eval v ty) (Kfor2 a2 a3 s k) e m)
                  E0 (State f s (Kfor3 a2 a3 s k) e m)
            | step_skip_or_continue_for3: forall ge f x a2 a3 s k e m,
                x = Sskip \/ x = Scontinue ->
                sstep ge (State f x (Kfor3 a2 a3 s k) e m)
                  E0 (State f a3 (Kfor4 a2 a3 s k) e m)
            | step_break_for3: forall ge f a2 a3 s k e m,
                sstep ge (State f Sbreak (Kfor3 a2 a3 s k) e m)
                  E0 (State f Sskip k e m)
            | step_skip_for4: forall ge f a2 a3 s k e m,
                sstep ge (State f Sskip (Kfor4 a2 a3 s k) e m)
                  E0 (State f (Sfor Sskip a2 a3 s) k e m).                     

            FDefinition step :  genv -> state -> trace -> state -> Prop := fun ge S t S' => 
              estep ge S t S' \/ sstep ge S t S'.
                           
  FEnd C.
      
  Family Clight extends Cfam.
       
       FInductive expr : Type :=          
          | Econst_int: int -> type -> expr(* integer literal *)
          | Econst_float: float -> type -> expr(* double float literal *)
          | Econst_single: float32 -> type -> expr(* single float literal *)
          | Econst_long: int64 -> type -> expr(* long integer literal *)                                            
          | Etempvar: ident -> type -> expr (* temporary variable *)          
          | Esizeof: type -> type -> expr (* size of a type *)
          | Ecast: expr -> type -> expr
          | Ealignof: type -> type -> expr. (* alignment of a type *)                                         
       
       FRecursion typeof : (e : expr) -> type. 
          Case Econst_int i ty := ty. 
          Case Econst_float f ty := ty. 
          Case Econst_single s ty := ty. 
          Case Econst_long l ty := ty. 
          Case Etempvar v ty := ty.
          Case Esizeof ty' ty := ty.
          Case Ealignof ty' ty := ty.
          Case Ecast e ty := ty.
       FEnd typeof.
       
       FDefinition label := ident.
       FInductive stmt : Type :=                                            
           | Sloop: stmt -> stmt -> stmt (* infinite loop *)
           | Sbreak : stmt (* break stmt *)
           | Scontinue : stmt. (* continue stmt *)

       FDefinition Swhile := fun (e: expr) (s: stmt) =>
         Sloop (Ssequence (Sifthenelse e Sskip Sbreak) s) Sskip.

       FDefinition Sdowhile := fun (s: stmt) (e: expr) => 
         Sloop s (Sifthenelse e Sskip Sbreak).

       FDefinition Sfor := fun (s1: stmt) (e2: expr) (s3: stmt) (s4: stmt) =>
         Ssequence s1 (Sloop (Ssequence (Sifthenelse e2 Sskip Sbreak) s3) s4).
              
       MetaData function.
       Record function : Type := mkfunction {
         fn_return: self__Imp.type;
         fn_callconv: calling_convention;
         fn_params: list (ident * self__Imp.type);
         fn_vars: list (ident * self__Imp.type);
         fn_temps: list (ident * self__Imp.type);
         fn_body: self__Clight.stmt
       }.
       FEnd function.       
              
       FDefinition fundef := AST.fundef function.
       
       FDefinition type_of_function : function -> type := fun f => 
         self__Imp.Tfunction (self__Imp.type_of_params (self__Clight.fn_params f)) 
           (self__Clight.fn_return f) (self__Clight.fn_callconv f).
       
       FDefinition type_of_fundef : fundef -> type := fun f =>
          match f with
          | Internal fd => type_of_function fd
          | _ => cheat (* TODO: We don't have External in the base compiler *)
          end.              
              
       FOverride Definition fenv := PTree.t (block * Z).
       FOverride Definition empty_fenv := PTree.empty (block * Z).                    

       FDefinition block_of_binding := fun (id_b_sz: ident * (block * Z)) => 
           match id_b_sz with (id, (b, sz)) => (b, 0, sz) end.

       FDefinition blocks_of_env : fenv -> list (block * Z * Z) := fun e => 
          List.map block_of_binding (PTree.elements e).          

       FOverride Definition free_fenv := fun m e f =>
         Mem.free_list m (blocks_of_env e).       

       MetaData sem_cast.
       Axiom sem_cast : val -> self__Imp.type -> self__Imp.type -> mem -> option val.
       FEnd sem_cast.
                        
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
             sem_cast v1 (typeof a) ty m = Some v ->
             eval_expr ge e le m (Ecast a ty) v
          | eval_Etempvar: forall ge e le m id ty v,
              PTree.get id le = Some v ->
              eval_expr ge e le m (Etempvar id ty) v.

       FInductive cont: Type :=            
          | Kloop1: stmt -> stmt -> cont -> cont(* Kloop1 s1 s2 k = after s1 in Sloop s1 s2 *)
          | Kloop2: stmt -> stmt -> cont -> cont. (* Kloop2 s1 s2 k = after s2 in Sloop s1 s2 *)                

       FRecursion call_cont about cont motive (fun (c : cont) => cont) by _rect.       
            Case Kloop1 := (fun s1 s2 k call_cont_k => call_cont_k).
            Case Kloop2 := (fun s1 s2 k call_cont_k => call_cont_k). 
       FEnd call_cont.
            
       FRecursion is_call_cont about cont motive (fun (c : cont) => Prop) by _rect.                   
            Case Kloop1 s1 s2 k := False. 
            Case Kloop2 s1 s2 k := False.
       FEnd is_call_cont.                      
            
       FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont)) by _rect.            
            Case Sloop := (fun s1 find_label_s1 s2 find_label_s2 => 
                             fun lbl k =>
                             match find_label_s1 lbl (Kloop1 s1 s2 k) with 
                             | Some sk => Some sk 
                             | None => find_label_s2 lbl (Kloop2 s1 s2 k) end).            
            Case Sbreak := (fun lbl k => None).                
            Case Scontinue := (fun lbl k => None).
       FEnd find_label.

       MetaData bool_val.
       Axiom bool_val : val -> self__Imp.type -> mem -> option bool. 
       FEnd bool_val.

       MetaData sizeof.
       Axiom sizeof : (* self__Sem.composite_env -> *) self__Imp.type -> Z.
       FEnd sizeof.
             
       FDefinition block_of_binding := fun (id_b_ty: ident * (block * type)) =>
         match id_b_ty with (id, (b, ty)) => (b, 0, sizeof ty) end.

       FDefinition blocks_of_env : env -> list (block * Z * Z)  := fun e => 
         List.map block_of_binding (PTree.elements e).                      
                  
       FInductive step : genv -> state -> trace -> state -> Prop :=               
               | step_continue_seq: forall ge f s k e le m,
                   step ge (State f Scontinue (Kseq s k) e le m)
                     E0 (State f Scontinue k e le m)
               | step_break_seq: forall ge f s k e le m,
                   step ge (State f Sbreak (Kseq s k) e le m)
                     E0 (State f Sbreak k e le m)             
               | step_ifthenelse: forall ge f a s1 s2 k e le m v1 b,
                   eval_expr ge e le m a v1 ->
                   bool_val v1 (typeof a) m = Some b ->
                   step ge (State f (Sifthenelse a s1 s2) k e le m)
                     E0 (State f (if b then s1 else s2) k e le m)
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
  
  FEnd Clight.      
  
  Family Csharpminor extends Cfam.
       
       Inherit stmt.
       
       MetaData fn.
       Record fn : Type := mkfunction {
         fn_sig: signature;
         fn_params: list ident;
         fn_vars: list (ident * Z);
         fn_temps: list ident;
         fn_body: self__Csharpminor.stmt
       }.
       FEnd fn.
       
       FOverride Definition function := fn.
       FOverride Definition function_body := self__Csharpminor.fn_body.
       FOverride Definition function_locals := self__Csharpminor.fn_temps.
       FOverride Definition function_params := self__Csharpminor.fn_params.
       FOverride Definition function_sig := self__Csharpminor.fn_sig.
       
       FOverride Definition fenv := PTree.t (block * Z).
       FOverride Definition empty_fenv := PTree.empty (block * Z).                    

       FDefinition block_of_binding := fun (id_b_sz: ident * (block * Z)) => 
           match id_b_sz with (id, (b, sz)) => (b, 0, sz) end.

       FDefinition blocks_of_env : fenv -> list (block * Z * Z) := fun e => 
          List.map block_of_binding (PTree.elements e).          

       FOverride Definition free_fenv := fun m e f =>
         Mem.free_list m (blocks_of_env e).          
   
       MetaData alloc_variables.
         Inductive alloc_variables: self__Sem.fenv -> mem ->
                        list (ident * Z) ->
                        self__Sem.fenv -> mem -> Prop :=
         | alloc_variables_nil:
           forall e m,
             alloc_variables e m nil e m
         | alloc_variables_cons:
           forall e m id sz vars m1 b1 m2 e2,
             Mem.alloc m 0 sz = (m1, b1) ->
             alloc_variables (PTree.set id (b1, sz) e) m1 vars e2 m2 ->
             alloc_variables e m ((id, sz) :: vars) e2 m2.
       FEnd alloc_variables.
         
       FOverride Definition alloc_fenv := fun e m f e' m' => 
         list_norepet (map fst f.(self__Csharpminor.fn_vars)) /\
         list_norepet f.(self__Csharpminor.fn_params) /\
         list_disjoint f.(self__Csharpminor.fn_params) f.(self__Csharpminor.fn_temps) /\
         alloc_variables self__Sem.empty_fenv m (self__Csharpminor.fn_vars f) e m'.       

  FEnd Csharpminor.

  Family Cminor extends Cfam.
  
       Inherit stmt.
        
       MetaData fn.
          Record fn : Type := mkfunction {
             fn_sig: signature;
             fn_params: list ident;
             fn_vars: list ident;
             fn_stackspace: Z;
             fn_body: self__Cminor.stmt
          }.
       FEnd fn.

       FOverride Definition function := fn.
       FOverride Definition function_body := self__Cminor.fn_body.
       FOverride Definition function_locals := self__Cminor.fn_vars.
       FOverride Definition function_params := self__Cminor.fn_params.
       FOverride Definition function_sig := self__Cminor.fn_sig.
              
       (* stack pointer *)
       (* Vptr sp Ptrofs.zero *)
       FOverride Definition fenv := block.
   
       FOverride Definition free_fenv := fun m sp f =>
         Mem.free m sp 0 f.(self__Cminor.fn_stackspace).
          
       FOverride Definition alloc_fenv := fun sp m f sp' m' => 
          Mem.alloc m 0 f.(self__Cminor.fn_stackspace) = (m', sp).      
  FEnd Cminor.  
  
  (* RISC-V *)
  Family Asm.
      (* Operations *)
      FInductive condition : Type :=
        | Ccompuimm : comparison -> int -> condition. (**r unsigned integer comparison with a constant *)

     (** Arithmetic and logical operations.  In the descriptions, [rd] is the
       result of the operation and [r1], [r2], etc, are the arguments. *)

     FInductive operation : Type :=
        | Omove : operation                    (**r [rd = r1] *)
        | Ointconst : int -> operation       (**r [rd] is set to the given integer constant *)
        | Olongconst : int64 -> operation    (**r [rd] is set to the given integer constant *)
        | Ofloatconst : float -> operation   (**r [rd] is set to the given float constant *)
        | Osingleconst : float32 -> operation (**r [rd] is set to the given float constant *)
        (* | Oaddrsymbol : ident -> ptrofs -> operation*)  (**r [rd] is set to the address of the symbol plus the given offset *)
        | Oaddrstack : ptrofs -> operation (**r [rd] is set to the stack pointer plus the given offset *)        
          
        (*c 32-bit integer arithmetic: *)
        | Ocast8signed : operation             (**r [rd] is 8-bit sign extension of [r1] *)
        | Ocast16signed : operation            (**r [rd] is 16-bit sign extension of [r1] *)                             
                            
        | Osingleoffloat : operation           (**r [rd] is [r1] truncated to single-precision float *)
        | Ofloatofsingle : operation           (**r [rd] is [r1] extended to double-precision float *)
            
        (*c Conversions between int and float: *)
        | Ointoffloat : operation              (**r [rd = signed_int_of_float64(r1)] *)
        | Ointuoffloat : operation             (**r [rd = unsigned_int_of_float64(r1)] *)
        | Ofloatofint : operation              (**r [rd = float64_of_signed_int(r1)] *)
        | Ofloatofintu : operation             (**r [rd = float64_of_unsigned_int(r1)] *)
        | Ointofsingle : operation             (**r [rd = signed_int_of_float32(r1)] *)
        | Ointuofsingle : operation            (**r [rd = unsigned_int_of_float32(r1)] *)
        | Osingleofint : operation             (**r [rd = float32_of_signed_int(r1)] *)
        | Osingleofintu : operation            (**r [rd = float32_of_unsigned_int(r1)] *)
        | Olongoffloat : operation             (**r [rd = signed_long_of_float64(r1)] *)
        | Olonguoffloat : operation            (**r [rd = unsigned_long_of_float64(r1)] *)
        | Ofloatoflong : operation             (**r [rd = float64_of_signed_long(r1)] *)
        | Ofloatoflongu : operation            (**r [rd = float64_of_unsigned_long(r1)] *)
        | Olongofsingle : operation            (**r [rd = signed_long_of_float32(r1)] *)
        | Olonguofsingle : operation           (**r [rd = unsigned_long_of_float32(r1)] *)
        | Osingleoflong : operation            (**r [rd = float32_of_signed_long(r1)] *)
        | Osingleoflongu : operation           (**r [rd = float32_of_unsigned_int(r1)] *)
            
        (*c Boolean tests: *)
        | Ocmp : condition -> operation.  (**r [rd = 1] if condition holds, [rd = 0] otherwise. *)
      
     FRecursion eval_condition about condition motive (fun (_ : condition) => list val -> mem -> option bool) by _rect.
        Case Ccompuimm := (fun c n => fun vl m =>
                           match vl with 
                           | v1 :: nil => Val.cmpu_bool (Mem.valid_pointer m) c v1 (Vint n)
                           | _ => None end).
     FEnd eval_condition.

     FRecursion eval_operation about operation motive (fun (_ : operation) => forall F V, Genv.t F V -> val -> list val -> mem -> option val) by _rect.
        Case Omove := (fun F V ge sp vl m => 
                    match vl with 
                    | v1 :: nil => Some v1 
                    | _ => None end).
        Case Ointconst := (fun n => fun F V ge sp vl m =>  
                           match vl with 
                           | nil => Some (Vint n)
                           | _ => None end).
        Case Olongconst := (fun n => fun F V ge sp vl m =>  
                           match vl with 
                           | nil => Some (Vlong n)
                           | _ => None end).
        Case Ofloatconst := (fun n => fun F V ge sp vl m =>  
                           match vl with 
                           | nil => Some (Vfloat n)
                           | _ => None end).
        Case Osingleconst := (fun n => fun F V ge sp vl m =>  
                           match vl with 
                           | nil => Some (Vsingle n)
                           | _ => None end).                
        (* Case Oaddrsymbol := (fun s ofs => fun F V ge sp vl m =>
                           match vl with 
                           | nil => Some (Genv.symbol_address genv s ofs)
                           | _ => None end).*)
        Case Oaddrstack := (fun ofs => fun F V ge sp vl m =>
                           match vl with 
                           | nil => Some (Val.offset_ptr sp ofs)
                           | _ => None end).
        Case Ocast8signed := (fun F V ge sp vl m =>
                           match vl with 
                           | v1 :: nil => Some (Val.sign_ext 8 v1)
                           | _ => None end).
        Case Ocast16signed := (fun F V ge sp vl m =>
                           match vl with 
                           | v1 :: nil => Some (Val.sign_ext 16 v1)
                           | _ => None end).        
        Case Osingleoffloat := (fun F V ge sp vl m =>
                           match vl with 
                           | v1 :: nil => Some (Val.singleoffloat v1)
                           | _ => None end).        
        Case Ofloatofsingle := (fun F V ge sp vl m =>
                           match vl with 
                           | v1 :: nil => Some (Val.floatofsingle v1)
                           | _ => None end).
        Case Ointoffloat := (fun F V ge sp vl m => 
                           match vl with 
                           | v1 :: nil => (Val.intoffloat v1)
                           | _ => None end).
        Case Ointuoffloat := (fun F V ge sp vl m => 
                           match vl with 
                           | v1 :: nil => (Val.intuoffloat v1)
                           | _ => None end).
        Case Ofloatofint := (fun F V ge sp vl m => 
                           match vl with 
                           | v1 :: nil => (Val.floatofint v1)
                           | _ => None end).        
        Case Ofloatofintu := (fun F V ge sp vl m => 
                           match vl with 
                           | v1 :: nil => (Val.floatofintu v1)
                           | _ => None end).
        Case Ointofsingle := (fun F V ge sp vl m => 
                           match vl with 
                           | v1 :: nil => (Val.intofsingle v1)
                           | _ => None end).
        Case Ointuofsingle := (fun F V ge sp vl m => 
                           match vl with 
                           | v1 :: nil => (Val.intuofsingle v1)
                           | _ => None end).
        Case Osingleofint := (fun F V ge sp vl m => 
                            match vl with 
                            | v1 :: nil => (Val.singleofint v1)
                            | _ => None end).
        Case Osingleofintu := (fun F V ge sp vl m => 
                            match vl with 
                            | v1 :: nil => (Val.singleofintu v1)
                            | _ => None end).
        Case Olongoffloat := (fun F V ge sp vl m => 
                            match vl with 
                            | v1 :: nil => (Val.longoffloat v1)
                            | _ => None end).
        Case Olonguoffloat := (fun F V ge sp vl m => 
                            match vl with 
                            | v1 :: nil => (Val.longuoffloat v1)
                            | _ => None end).
        Case Ofloatoflong := (fun F V ge sp vl m => 
                            match vl with 
                            | v1 :: nil => (Val.floatoflong v1)
                            | _ => None end).
        Case Ofloatoflongu := (fun F V ge sp vl m => 
                            match vl with 
                            | v1 :: nil => (Val.floatoflongu v1)
                            | _ => None end).
        Case Olongofsingle := (fun F V ge sp vl m => 
                            match vl with 
                            | v1 :: nil => (Val.longofsingle v1)
                            | _ => None end).
        Case Olonguofsingle := (fun F V ge sp vl m => 
                            match vl with 
                            | v1 :: nil => (Val.longuofsingle v1)
                            | _ => None end).
        Case Osingleoflong := (fun F V ge sp vl m => 
                            match vl with 
                            | v1 :: nil => (Val.singleoflong v1)
                            | _ => None end).
        Case Osingleoflongu := (fun F V ge sp vl m => 
                            match vl with 
                            | v1 :: nil => (Val.singleoflongu v1)
                            | _ => None end).
        Case Ocmp := (fun c => fun F V ge sp vl m =>
                  match vl with 
                  | v1 :: v2 :: nil => Some (Val.of_optbool (eval_condition c vl m))
                  | _ => None end).
     FEnd eval_operation.

    (* FRecursion shift_stack_operation about operation motive (fun (_ : operation) => Z -> operation) by _rect.
        Case Omove := (fun delta => Omove).
        Case Ointconst := (fun delta n => Ointconst n).
        Case Olongconst := (fun delta n => Olongconst n).
        Case Oaddrsymbol := (fun delta s ofs => Oaddrsymbol s ofs).
        Case Oaddrstack := (fun delta ofs => Oaddrstack (Ptrofs.add ofs (Ptrofs.repr delta))).
        Case Ocast8signed := (fun delta => Ocast8signed).
        Case Ocast16signed := (fun delta => Ocast16signed).
        Case Oadd := (fun delta => Oadd).
        Case Oaddimm := (fun delta n => Oaddimm n).
        Case Oneg := (fun delta => Oneg).
        Case Osub := (fun delta => Osub).
        Case Omul := (fun delta => Omul).
        Case Odiv := (fun delta => Odiv).
        Case Ocmp := (fun delta c => Ocmp c).
    FEnd shift_stack_operation.*)
    
    MetaData ireg.
    Inductive ireg: Type :=
         | X1:  ireg | X2:  ireg | X3:  ireg | X4:  ireg | X5:  ireg
         | X6:  ireg | X7:  ireg | X8:  ireg | X9:  ireg | X10: ireg
         | X11: ireg | X12: ireg | X13: ireg | X14: ireg | X15: ireg
         | X16: ireg | X17: ireg | X18: ireg | X19: ireg | X20: ireg
         | X21: ireg | X22: ireg | X23: ireg | X24: ireg | X25: ireg
         | X26: ireg | X27: ireg | X28: ireg | X29: ireg | X30: ireg
         | X31: ireg.
    FEnd ireg.

    MetaData ireg0.
    Inductive ireg0: Type :=
        | X0: ireg0 | X: self__Asm.ireg -> ireg0.
    FEnd ireg0.
    
    MetaData freg.
    Inductive freg: Type :=
       | F0: freg  | F1: freg  | F2: freg  | F3: freg
       | F4: freg  | F5: freg  | F6: freg  | F7: freg
       | F8: freg  | F9: freg  | F10: freg | F11: freg
       | F12: freg | F13: freg | F14: freg | F15: freg
       | F16: freg | F17: freg | F18: freg | F19: freg
       | F20: freg | F21: freg | F22: freg | F23: freg
       | F24: freg | F25: freg | F26: freg | F27: freg
       | F28: freg | F29: freg | F30: freg | F31: freg.
    FEnd freg.
      
    (** We model the following registers of the RISC-V architecture. *)
    MetaData preg. 
    Inductive preg: Type :=
         | IR: self__Asm.ireg -> preg          (**r integer registers *)
         | FR: self__Asm.freg -> preg          (**r double-precision float registers *)
         | PC: preg.                           (**r program counter *)

    
    Lemma ireg_eq: forall (x y: self__Asm.ireg), {x=y} + {x<>y}.
    Proof. decide equality. Defined.

    Lemma ireg0_eq: forall (x y: self__Asm.ireg0), {x=y} + {x<>y}.
    Proof. decide equality. apply ireg_eq. Defined.
    
    Lemma freg_eq: forall (x y: self__Asm.freg), {x=y} + {x<>y}.
    Proof. decide equality. Defined.
    
    Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
    Proof. decide equality. apply ireg_eq. apply freg_eq. Defined.
    FEnd preg.
    
    (** Conventional names for stack pointer ([SP]) and return address ([RA]). *)
    (* Notation "'SP'" := X2 (only parsing) : asm.
     Notation "'RA'" := X1 (only parsing) : asm.*)
      
    MetaData offset.
    Inductive offset : Type :=
        | Ofsimm (ofs: ptrofs)
        | Ofslow (id: ident) (ofs: ptrofs).
    FEnd offset.    

    FDefinition label := positive.
    
    FInductive instruction : Type :=
      | Pmv : ireg -> ireg -> instruction                    (**r integer move *)
                  
      (* Loads and stores *)
      | Plb : ireg -> ireg -> offset -> instruction          (**r load signed int8 *)
      | Plbu : ireg -> ireg -> offset -> instruction         (**r load unsigned int8 *)
      | Plh : ireg -> ireg -> offset -> instruction          (**r load signed int16 *)
      | Plhu : ireg -> ireg -> offset -> instruction         (**r load unsigned int16 *)
      | Plw : ireg -> ireg -> offset -> instruction          (**r load int32 *)
      | Plw_a : ireg -> ireg -> offset -> instruction        (**r load any32 *)
      | Pld : ireg -> ireg -> offset -> instruction          (**r load int64 *)
      | Pld_a : ireg -> ireg -> offset -> instruction        (**r load any64 *)

      | Psb : ireg -> ireg -> offset -> instruction          (**r store int8 *)
      | Psh : ireg -> ireg -> offset -> instruction          (**r store int16 *)
      | Psw : ireg -> ireg -> offset -> instruction          (**r store int32 *)
      | Psw_a : ireg -> ireg -> offset -> instruction        (**r store any32 *)
      | Psd : ireg -> ireg -> offset -> instruction          (**r store int64 *)
      | Psd_a : ireg -> ireg -> offset -> instruction        (**r store any64 *)
            
      (* floating point register move *)
      | Pfmv : freg -> freg -> instruction                   (**r move *)
          
      (* 32-bit (single-precision) floating point *)
      | Pfls : freg -> ireg -> offset -> instruction         (**r load float *)
      | Pfss : freg -> ireg -> offset -> instruction         (**r store float *)
                      
      | Pfcvtws : ireg -> freg -> instruction                (**r float32 -> int32 conversion *)
      | Pfcvtwus : ireg -> freg -> instruction               (**r float32 -> unsigned int32 conversion *)
      | Pfcvtsw : freg -> ireg0 -> instruction               (**r int32 -> float32 conversion *)
      | Pfcvtswu : freg -> ireg0 -> instruction              (**r unsigned int32 -> float32 conversion *)
          
      | Pfcvtls : ireg -> freg -> instruction                (**r float32 -> int64 conversion *)
      | Pfcvtlus : ireg -> freg -> instruction               (**r float32 -> unsigned int64 conversion *)
      | Pfcvtsl : freg -> ireg0 -> instruction               (**r int64 -> float32 conversion *)
      | Pfcvtslu : freg -> ireg0 -> instruction              (**r unsigned int 64-> float32 conversion *)

      (* 64-bit (double-precision) floating point *)
      | Pfld : freg -> ireg -> offset -> instruction         (**r load 64-bit float *)
      | Pfld_a : freg -> ireg -> offset -> instruction       (**r load any64 *)
      | Pfsd : freg -> ireg -> offset -> instruction         (**r store 64-bit float *)
      | Pfsd_a : freg -> ireg -> offset -> instruction       (**r store any64 *)

      | Pfcvtwd : ireg -> freg -> instruction                (**r float -> int32 conversion *)
      | Pfcvtwud : ireg -> freg -> instruction               (**r float -> unsigned int32 conversion *)
      | Pfcvtdw : freg -> ireg0 -> instruction               (**r int32 -> float conversion *)
      | Pfcvtdwu : freg -> ireg0 -> instruction              (**r unsigned int32 -> float conversion *)
          
      | Pfcvtld : ireg -> freg -> instruction                (**r float -> int64 conversion *)
      | Pfcvtlud : ireg -> freg -> instruction               (**r float -> unsigned int64 conversion *)
      | Pfcvtdl : freg -> ireg0 -> instruction               (**r int64 -> float conversion *)
      | Pfcvtdlu : freg -> ireg0 -> instruction              (**r unsigned int64 -> float conversion *)
          
      | Pfcvtds : freg -> freg -> instruction                (**r float32 -> float   *)
      | Pfcvtsd : freg -> freg -> instruction                (**r float   -> float32 *)                  
          
      (* Unconditional jumps.  Links are always to X1/RA. *)
      | Pj_l : label -> instruction                          (**r jump to label *)
      | Pj_r : ireg -> signature -> instruction              (**r jump register *)
        
      (* Conditional branches, 32-bit comparisons *)
      | Pbeqw : ireg0 -> ireg0 -> label -> instruction       (**r branch-if-equal *)
      | Pbnew : ireg0 -> ireg0 -> label -> instruction       (**r branch-if-not-equal signed *)
      | Pbltw : ireg0 -> ireg0 -> label -> instruction       (**r branch-if-less signed *)
      | Pbltuw : ireg0 -> ireg0 -> label -> instruction      (**r branch-if-less unsigned *)
      | Pbgew : ireg0 -> ireg0 -> label -> instruction       (**r branch-if-greater-or-equal signed *)
      | Pbgeuw : ireg0 -> ireg0 -> label -> instruction      (**r branch-if-greater-or-equal unsigned *)
          
      | Pbeql : ireg0 -> ireg0 -> label -> instruction       (**r branch-if-equal *)
      | Pbnel : ireg0 -> ireg0 -> label -> instruction       (**r branch-if-not-equal signed *)
      | Pbltl : ireg0 -> ireg0 -> label -> instruction       (**r branch-if-less signed *)
      | Pbltul : ireg0 -> ireg0 -> label -> instruction      (**r branch-if-less unsigned *)
      | Pbgel : ireg0 -> ireg0 -> label -> instruction       (**r branch-if-greater-or-equal signed *)
      | Pbgeul : ireg0 -> ireg0 -> label -> instruction      (**r branch-if-greater-or-equal unsigned *)                 

      (* Pseudo-instructions *)
      | Plabel : label -> instruction                        (**r define a code label *)    
      | Pnop : instruction.                                   (**r nop instruction *)

     
                  
    FDefinition code := list instruction.
    MetaData function.
    Record function : Type := mkfunction { fn_sig: signature; fn_code: self__Asm.code }.
    FEnd function.
    FDefinition fundef := AST.fundef function.
    FDefinition program := AST.program fundef unit.    
    
    
    (* Operational Semantics *)
    Family Sem. 
          MetaData Pregmap.
              Module PregEq.
               Definition t  := self__Asm.preg.
               Definition eq := self__Asm.preg_eq.
             End PregEq.
             
             Module Pregmap := EMap(PregEq).
          FEnd Pregmap.
          FDefinition regset := Pregmap.t val.
          FDefinition genv := Genv.t fundef unit.
          
          FDefinition get0w : regset -> ireg0 -> val := fun rs r =>
            match r with
            | self__Asm.X0 => Vint Int.zero
            | self__Asm.X r => rs (self__Asm.IR r)
            end.

          FDefinition get0l : regset -> ireg0 -> val := fun rs r =>
            match r with
            | self__Asm.X0 => Vlong Int64.zero
            | self__Asm.X r => rs (self__Asm.IR r)
            end.

          (* Notation "a # b" := (a b) (at level 1, only parsing) : asm.
          Notation "a ## b" := (get0w a b) (at level 1) : asm.
          Notation "a ### b" := (get0l a b) (at level 1) : asm.
          Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level) : asm. *)
          
          MetaData undef_regs.
          Fixpoint undef_regs (l: list self__Asm.preg) (rs: self__Sem.regset) : self__Sem.regset :=
             match l with
             | nil => rs
             | r :: l' => undef_regs l' (self__Sem.Pregmap.set r Vundef rs)
             end.
          FEnd undef_regs.
          
          MetaData set_regs.
          Fixpoint set_regs (rl: list self__Asm.preg) (vl: list val) (rs: self__Sem.regset) : self__Sem.regset :=
             match rl, vl with
             | r1 :: rl', v1 :: vl' => set_regs rl' vl' (self__Sem.Pregmap.set r1 v1 rs)
             | _, _ => rs
             end.
          FEnd set_regs.

          MetaData find_instr.
          Fixpoint find_instr (pos: Z) (c: self__Asm.code) {struct c} : option self__Asm.instruction :=
             match c with
             | nil => None
             | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
             end.
          FEnd find_instr.

          (* FRecursion *)
          (* Definition is_label (lbl: label) (instr: instruction) : bool :=
            match instr with
            | Plabel lbl' => if peq lbl lbl' then true else false
            | _ => false
            end.*)          
          MetaData is_label.
          Axiom is_label : self__Asm.label -> self__Asm.instruction -> bool.
          FEnd is_label.
          
          MetaData label_pos.
          Fixpoint label_pos (lbl: self__Asm.label) (pos: Z) (c: self__Asm.code) {struct c} : option Z :=
            match c with
            | nil => None
            | instr :: c' =>
                if self__Sem.is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
            end.
          FEnd label_pos.
          
          MetaData outcome.
          Inductive outcome: Type :=
             | Next:  self__Sem.regset -> mem -> outcome
             | Stuck: outcome.
          FEnd outcome.
          
          FDefinition nextinstr := fun (rs: regset) =>
            Pregmap.set self__Asm.PC (Val.offset_ptr (rs self__Asm.PC) Ptrofs.one) rs.                    

          FDefinition goto_label := fun (f: self__Asm.function) (lbl: self__Asm.label) (rs: self__Sem.regset) (m: mem) =>
            match label_pos lbl 0 (self__Asm.fn_code f) with
            | None => self__Sem.Stuck
            | Some pos =>
                match (rs self__Asm.PC) with
                | Vptr b ofs => self__Sem.Next (Pregmap.set self__Asm.PC (Vptr b (Ptrofs.repr pos)) rs) m
                | _          => self__Sem.Stuck
                end
            end.

          MetaData low_half.
          Parameter low_half: self__Sem.genv -> ident -> ptrofs -> ptrofs.
          FEnd low_half.
          
          MetaData high_half.
          Parameter high_half: self__Sem.genv -> ident -> ptrofs -> val.
          FEnd high_half.
                    
          FDefinition eval_offset : self__Sem.genv -> self__Asm.offset -> ptrofs := fun ge ofs =>
             match ofs with
             | self__Asm.Ofsimm n => n
             | self__Asm.Ofslow id delta => low_half ge id delta
             end.          

          FDefinition exec_load := fun (ge : genv) (chunk: memory_chunk) (rs: regset) (m: mem)
                              (d: preg) (a: ireg) (ofs: offset) =>
            match Mem.loadv chunk m (Val.offset_ptr (rs (self__Asm.IR a)) (eval_offset ge ofs)) with
            | None => self__Sem.Stuck
            | Some v => self__Sem.Next (nextinstr (Pregmap.set d v rs)) m
            end.          
          
          FDefinition exec_store := fun (ge : genv) (chunk: memory_chunk) (rs: regset) (m: mem)
                                (s: preg) (a: ireg) (ofs: offset) =>
            match Mem.storev chunk m (Val.offset_ptr (rs (self__Asm.IR a)) (eval_offset ge ofs)) (rs s) with
            | None => self__Sem.Stuck
            | Some m' => self__Sem.Next (nextinstr rs) m'
            end.

          FDefinition eval_branch := fun (f: function) (l: label) (rs: regset) (m: mem) (res: option bool) =>
            match res with
              | Some true  => goto_label f l rs m
              | Some false => self__Sem.Next (nextinstr rs) m
              | None => self__Sem.Stuck
            end.
          
          FRecursion exec_instr about instruction motive (fun (_ : instruction) => genv -> function -> regset -> mem -> outcome) by _rect.
          Case Pmv := (fun d s ge f rs m => self__Sem.Next (nextinstr (Pregmap.set (self__Asm.IR d) (rs (self__Asm.IR s)) rs)) m).

          Case Plb := (fun d a ofs ge f rs m => exec_load ge Mint8signed rs m (self__Asm.IR d) a ofs).
          Case Plbu := (fun d a ofs ge f rs m => exec_load ge Mint8unsigned rs m (self__Asm.IR d) a ofs).
          Case Plh := (fun d a ofs ge f rs m => exec_load ge Mint16signed rs m (self__Asm.IR d) a ofs).
          Case Plhu := (fun d a ofs ge f rs m => exec_load ge Mint16unsigned rs m (self__Asm.IR d) a ofs).
          Case Plw := (fun d a ofs ge f rs m => exec_load ge Mint32 rs m (self__Asm.IR d) a ofs).
          Case Plw_a := (fun d a ofs ge f rs m => exec_load ge Many32 rs m (self__Asm.IR d) a ofs).
          Case Pld := (fun d a ofs ge f rs m => exec_load ge Mint64 rs m (self__Asm.IR d) a ofs).
          Case Pld_a := (fun d a ofs ge f rs m => exec_load ge Many64 rs m (self__Asm.IR d) a ofs).
          Case Psb := (fun s a ofs ge f rs m => exec_store ge Mint8unsigned rs m (self__Asm.IR s) a ofs).
          Case Psh := (fun s a ofs ge f rs m => exec_store ge Mint16unsigned rs m (self__Asm.IR s) a ofs).
          Case Psw := (fun s a ofs ge f rs m => exec_store ge Mint32 rs m (self__Asm.IR s) a ofs).
          Case Psw_a := (fun s a ofs ge f rs m => exec_store ge Many32 rs m (self__Asm.IR s) a ofs).
          Case Psd := (fun s a ofs ge f rs m => exec_store ge Mint64 rs m (self__Asm.IR s) a ofs).
          Case Psd_a := (fun s a ofs ge f rs m => exec_store ge Many64 rs m (self__Asm.IR s) a ofs).

          Case Pfmv := (fun d s ge f rs m => self__Sem.Next (nextinstr (Pregmap.set (self__Asm.FR d) (rs (self__Asm.FR s)) rs)) m).
          (* Pfmvxa, pfmvsx, pfmvxd, pfmvdx *)
          
          Case Pfls := (fun d a ofs ge f rs m => exec_load ge Mfloat32 rs m (self__Asm.FR d) a ofs).
          Case Pfss := (fun s a ofs ge f rs m => exec_store ge Mfloat32 rs m (self__Asm.FR s) a ofs).

          Case Pfcvtws := (fun d s ge f rs m => self__Sem.Next (nextinstr (Pregmap.set (self__Asm.IR d) (Val.maketotal (Val.intofsingle (rs (self__Asm.FR s)))) rs)) m).
          Case Pfcvtwus := (fun d s ge f rs m => self__Sem.Next (nextinstr (Pregmap.set (self__Asm.IR d) (Val.maketotal (Val.intuofsingle (rs (self__Asm.FR s)))) rs)) m).
          Case Pfcvtsw := (fun d s ge f rs m => self__Sem.Next (nextinstr (Pregmap.set (self__Asm.FR d) (Val.maketotal (Val.singleofint cheat (*rs s*))) rs)) m).
          Case Pfcvtswu := (fun d s ge f rs m => self__Sem.Next (nextinstr (Pregmap.set (self__Asm.FR d) (Val.maketotal (Val.singleofintu cheat (*rs s*))) rs)) m).
          
          Case Pfcvtls := (fun d s ge f rs m => self__Sem.Next (nextinstr (Pregmap.set (self__Asm.IR d) (Val.maketotal (Val.longofsingle (rs (self__Asm.FR s)))) rs)) m).
          Case Pfcvtlus := (fun d s ge f rs m => self__Sem.Next (nextinstr (Pregmap.set (self__Asm.IR d) (Val.maketotal (Val.longuofsingle (rs (self__Asm.FR s)))) rs)) m).
          Case Pfcvtsl := (fun d s ge f rs m => self__Sem.Next (nextinstr (Pregmap.set (self__Asm.FR d) (Val.maketotal (Val.singleoflong cheat (*rs s*))) rs)) m).
          Case Pfcvtslu := (fun d s ge f rs m => self__Sem.Next (nextinstr (Pregmap.set (self__Asm.FR d) (Val.maketotal (Val.singleoflongu cheat (*rs s*))) rs)) m).

          Case Pfld := (fun d a ofs ge f rs m => exec_load ge Mfloat64 rs m (self__Asm.FR d) a ofs).
          Case Pfld_a := (fun d a ofs ge f rs m => exec_load ge Many64 rs m (self__Asm.FR d) a ofs).
          Case Pfsd := (fun s a ofs ge f rs m => exec_store ge Mfloat64 rs m (self__Asm.FR s) a ofs).
          Case Pfsd_a := (fun s a ofs ge f rs m => exec_store ge Many64 rs m (self__Asm.FR s) a ofs).

          Case Pfcvtwd := (fun d s ge f rs m => self__Sem.Next (nextinstr (Pregmap.set (self__Asm.IR d) (Val.maketotal (Val.intoffloat (rs (self__Asm.FR s)))) rs)) m).
          Case Pfcvtwud := (fun d s ge f rs m => self__Sem.Next (nextinstr (Pregmap.set (self__Asm.IR d) (Val.maketotal (Val.intuoffloat (rs (self__Asm.FR s)))) rs)) m).
          Case Pfcvtdw := (fun d s ge f rs m => self__Sem.Next (nextinstr (Pregmap.set (self__Asm.FR d) (Val.maketotal (Val.floatofint (get0w rs s))) rs)) m).
          Case Pfcvtdwu := (fun d s ge f rs m => self__Sem.Next (nextinstr (Pregmap.set (self__Asm.FR d) (Val.maketotal (Val.floatofintu (get0w rs s))) rs)) m).

          Case Pfcvtld := (fun d s ge f rs m => self__Sem.Next (nextinstr (Pregmap.set (self__Asm.IR d) (Val.maketotal (Val.longoffloat (rs (self__Asm.FR s)))) rs)) m).
          Case Pfcvtlud := (fun d s ge f rs m => self__Sem.Next (nextinstr (Pregmap.set (self__Asm.IR d) (Val.maketotal (Val.longuoffloat (rs (self__Asm.FR s)))) rs)) m).
          Case Pfcvtdl := (fun d s ge f rs m => self__Sem.Next (nextinstr (Pregmap.set (self__Asm.FR d) (Val.maketotal (Val.floatoflong (get0l rs s))) rs)) m).
          Case Pfcvtdlu := (fun d s ge f rs m => self__Sem.Next (nextinstr (Pregmap.set (self__Asm.FR d) (Val.maketotal (Val.floatoflongu (get0l rs s))) rs)) m).

          Case Pfcvtds := (fun d s ge f rs m => self__Sem.Next (nextinstr (Pregmap.set (self__Asm.FR d) (Val.floatofsingle (rs (self__Asm.FR s))) rs)) m).
          Case Pfcvtsd := (fun d s ge f rs m => self__Sem.Next (nextinstr (Pregmap.set (self__Asm.FR d) (Val.singleoffloat (rs (self__Asm.FR s))) rs)) m).
          
          Case Pj_l := (fun lbl ge f rs m => goto_label f lbl rs m).
          Case Pj_r := (fun r sg ge f rs m => self__Sem.Next (Pregmap.set self__Asm.PC (rs (self__Asm.IR r)) rs)  m).
          
          Case Pbeqw := (fun s1 s2 l ge f rs m => eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Ceq cheat (*rs s1*) cheat (*rs s2*))).
          Case Pbnew := (fun s1 s2 l ge f rs m => eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Cne cheat (*rs s1*) cheat (*rs s2*))).
          Case Pbltw := (fun s1 s2 l ge f rs m => eval_branch f l rs m (Val.cmp_bool Clt cheat (*rs s1*) cheat (*rs s2*))).
          Case Pbltuw := (fun s1 s2 l ge f rs m => eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Clt cheat (*rs s1*) cheat (*rs s2*))).
          Case Pbgew := (fun s1 s2 l ge f rs m => eval_branch f l rs m (Val.cmp_bool Cge cheat (*rs s1*) cheat (*rs s2*))).          
          Case Pbgeuw := (fun s1 s2 l ge f rs m => eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Cge cheat (*rs s1*) cheat (*rs s2*))).
          
          Case Pbeql := (fun s1 s2 l ge f rs m => eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Ceq cheat (*rs s1*) cheat (*rs s2*))).
          Case Pbnel := (fun s1 s2 l ge f rs m => eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Cne cheat (*rs s1*) cheat (*rs s2*))).
          Case Pbltl := (fun s1 s2 l ge f rs m => eval_branch f l rs m (Val.cmpl_bool Clt cheat (*rs s1*) cheat (*rs s2*))).
          Case Pbltul := (fun s1 s2 l ge f rs m => eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Clt cheat (*rs s1*) cheat (*rs s2*))).
          Case Pbgel := (fun s1 s2 l ge f rs m => eval_branch f l rs m (Val.cmpl_bool Cge cheat (*rs s1*) cheat (*rs s2*))).
          Case Pbgeul := (fun s1 s2 l ge f rs m => eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Cge cheat (*rs s1*) cheat (*rs s2*))).

            
          Case Plabel := (fun lbl ge f rs m => self__Sem.Next (nextinstr rs) m).
          Case Pnop := (fun ge f rs m => self__Sem.Next (nextinstr rs) m).            

          FEnd exec_instr.



        (** Execution of the instruction at [rs PC]. *)

        MetaData state.
        Inductive state: Type :=
          | State: self__Sem.regset -> mem -> state.
        FEnd state.

        
        FInductive step: genv -> state -> trace -> state -> Prop :=
          | exec_step_internal:
              forall ge b ofs f i rs m rs' m',
              rs self__Asm.PC = Vptr b ofs ->
              Genv.find_funct_ptr ge b = Some (Internal f) ->
              find_instr (Ptrofs.unsigned ofs) (self__Asm.fn_code f) = Some i ->
              exec_instr i ge f rs m = self__Sem.Next rs' m' ->
              step ge (self__Sem.State rs m) E0 (self__Sem.State rs' m').        

        MetaData initial_state.
        Notation "a # b" := (a b) (at level 1, only parsing) : asm.
        Notation "a # b <- c" := (self__Sem.Pregmap.set b c a) (at level 1, b at next level) : asm.
        Open Scope asm.
        Inductive initial_state (p: self__Asm.program): self__Sem.state -> Prop :=
          | initial_state_intro: forall m0,
              let ge := Genv.globalenv p in
              let rs0 :=
                (self__Sem.Pregmap.init Vundef)
                # self__Asm.PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
                # (self__Asm.IR self__Asm.X2) <- Vnullptr
                # (self__Asm.IR self__Asm.X1) <- Vnullptr in
              Genv.init_mem p = Some m0 ->
              initial_state p (self__Sem.State rs0 m0).
        FEnd initial_state.

        MetaData final_state.
        Inductive final_state: self__Sem.state -> int -> Prop :=
          | final_state_intro: forall rs m r,
              rs self__Asm.PC = Vnullptr ->
              rs (self__Asm.IR (self__Asm.X10)) = Vint r ->
              final_state (self__Sem.State rs m) r.
        FEnd final_state.
      FEnd Sem.         
   FEnd Asm.

  (* Cminor with processor-dependent instructions *)
  Family CminorSel extends Cfam.
       FInductive expr : Type :=
          | Evar : ident -> expr          
          | Econdition : condexpr -> expr -> expr -> expr
          | Eop : Asm.operation -> exprlist -> expr
          | Elet : expr -> expr -> expr
          | Eletvar : nat -> expr
       with exprlist : Type :=
          | Enil: exprlist
          | Econs: expr -> exprlist -> exprlist
       with condexpr : Type :=
          | CEcond : Asm.condition -> exprlist -> condexpr
          | CEcondition : condexpr -> condexpr -> condexpr -> condexpr
          | CElet: expr -> condexpr -> condexpr.
       
       Inherit stmt.

       MetaData function.
       Record function : Type := mkfunction {
          fn_sig: signature;
          fn_params: list ident;
          fn_vars: list ident;
          fn_stackspace: Z;
          fn_body: self__CminorSel.stmt
       }.
       FEnd function.
       
       FDefinition letenv := list val.       
       (* stack pointer *)
       (* Vptr sp Ptrofs.zero *)
       FOverride Definition fenv := block.
   
       FOverride Definition free_fenv := fun m sp f =>
          Mem.free m sp 0 f.(self__Cminor.fn_stackspace).
          
       FOverride Definition alloc_fenv := fun sp m f sp' m' => 
          Mem.alloc m 0 f.(self__Cminor.fn_stackspace) = (m', sp).
          
       FDefinition eval_operation := fun op => Asm.eval_operation op fundef unit.                     
                    
       FInductive eval_expr: genv -> val -> env -> mem -> letenv -> expr -> val -> Prop :=
           | eval_Evar: forall ge sp e m le id v,
               PTree.get id e = Some v ->
               eval_expr ge sp e m le (Evar id) v
           | eval_Eop: forall ge sp e m le op al vl v,
               eval_exprlist ge sp e m le al vl ->
               Asm.eval_operation ge sp op vl m = Some v ->
               eval_expr ge sp e m le (Eop op al) v
           | eval_Econdition: forall ge sp e m le a b c va v,
               eval_condexpr ge sp e m le a va ->
               eval_expr ge sp e m le (if va then b else c) v ->
               eval_expr ge sp e m le (Econdition a b c) v
           | eval_Elet: forall ge sp e m le a b v1 v2,
               eval_expr ge sp e m le a v1 ->
               eval_expr ge sp e m (v1 :: le) b v2 ->
               eval_expr ge sp e m le (Elet a b) v2
           | eval_Eletvar: forall ge sp e m le n v,
               nth_error le n = Some v ->
               eval_expr ge sp e m le (Eletvar n) v
       with eval_exprlist: genv -> val -> env -> mem -> letenv -> self__CminorSel.exprlist -> list val -> Prop :=
          | eval_Enil: forall ge sp e m le,
              eval_exprlist ge sp e m le Enil nil
          | eval_Econs: forall ge sp e m le a1 al v1 vl,
              eval_expr ge sp e m le a1 v1 -> eval_exprlist ge sp e m le al vl ->
              eval_exprlist ge sp e m le (Econs a1 al) (v1 :: vl)
       with eval_condexpr: genv -> val -> env -> mem -> letenv -> self__CminorSel.condexpr -> bool -> Prop :=
          | eval_CEcond: forall ge sp e m le cond al vl vb,
              eval_exprlist ge sp e m le al vl ->
              Asm.eval_condition cond vl m = Some vb ->
              eval_condexpr ge sp e m le (CEcond cond al) vb
          | eval_CEcondition: forall ge sp e m le a b c va v,
              eval_condexpr ge sp e m le a va ->
              eval_condexpr ge sp e m le (if va then b else c) v ->
              eval_condexpr ge sp e m le (CEcondition a b c) v
          | eval_CElet: forall ge sp e m le a b v1 v2,
              eval_expr ge sp e m le a v1 ->
              eval_condexpr ge sp e m (v1 :: le) b v2 ->
              eval_condexpr ge sp e m le (CElet a b) v2.       
   FEnd CminorSel.

  (* C -> Clight *)
  Family SimplExpr.
      (* State and error monad *)
      MetaData monads.
        Record generator : Type := mkgenerator {
            gen_next: ident;
            gen_trail: list (ident * self__Imp.type)
        }.

      Inductive result (A: Type) (g: generator) : Type :=
        | Err: Errors.errmsg -> result A g
        | Res: A -> forall (g': generator), Ple (gen_next g) (gen_next g') -> result A g.

      Arguments Err [A g].
      Arguments Res [A g].

      Definition mon (A: Type) := forall (g: generator), result A g.

      Definition ret {A: Type} (x: A) : mon A :=
        fun g => Res x g (Ple_refl (gen_next g)).

      Definition error {A: Type} (msg: Errors.errmsg) : mon A :=
        fun g => Err msg.

      Definition bind {A B: Type} (x: mon A) (f: A -> mon B) : mon B :=
        fun g =>
          match x g with
            | Err msg => Err msg
            | Res a g' i =>
                match f a g' with
                | Err msg => Err msg
                | Res b g'' i' => Res b g'' (Ple_trans _ _ _ i i')
            end
          end.

      Definition bind2 {A B C: Type} (x: mon (A * B)) (f: A -> B -> mon C) : mon C :=
        bind x (fun p => f (fst p) (snd p)).

      Declare Scope gensym_monad_scope.
      Notation "'do' X <- A ; B" := (bind A (fun X => B))
         (at level 200, X ident, A at level 100, B at level 200)
         : gensym_monad_scope.
      Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
         (at level 200, X ident, Y ident, A at level 100, B at level 200)
         : gensym_monad_scope.

      Parameter first_unused_ident: unit -> ident.

      Definition initial_generator (x: unit) : generator :=
        mkgenerator (first_unused_ident x) nil.

      Definition gensym (ty: self__Imp.type): mon ident :=
        fun (g: generator) =>
          Res (gen_next g)
              (mkgenerator (Pos.succ (gen_next g)) ((gen_next g, ty) :: gen_trail g))
              (Ple_succ (gen_next g)).
      
      Fixpoint makeseq_rec (s: self__Imp.Clight.stmt) (l: list self__Imp.Clight.stmt) : self__Imp.Clight.stmt :=
         match l with
         | nil => s
         | s' :: l' => makeseq_rec (self__Imp.Clight.Ssequence s s') l'
          end.

      Definition makeseq (l: list self__Imp.Clight.stmt) : self__Imp.Clight.stmt :=
        makeseq_rec self__Imp.Clight.Sskip l.

      Local Open Scope gensym_monad_scope.
      FEnd monads.

      MetaData destination.
      Inductive set_destination : Type :=
          | SDbase (tycast ty: self__Imp.type) (tmp: ident)
          | SDcons (tycast ty: self__Imp.type) (tmp: ident) (sd: set_destination).

      Inductive destination : Type :=
        | For_val
        | For_effects
        | For_set (sd: set_destination).

      Fixpoint do_set (sd: set_destination) (a: self__Imp.Clight.expr) : list self__Imp.Clight.stmt :=
         match sd with
         | SDbase tycast ty tmp => self__Imp.Clight.Sset tmp (self__Imp.Clight.Ecast a tycast) :: nil
         | SDcons tycast ty tmp sd' => self__Imp.Clight.Sset tmp (self__Imp.Clight.Ecast a tycast) :: do_set sd' (self__Imp.Clight.Etempvar tmp ty)
         end.
      
      Definition finish (dst: destination) (sl: list self__Imp.Clight.stmt) (a: self__Imp.Clight.expr) :=
        match dst with
        | For_val => (sl, a)
        | For_effects => (sl, a)
        | For_set sd => (sl ++ do_set sd a, a)
        end.      
      
         Definition sd_temp (sd: set_destination) :=
           match sd with SDbase _ _ tmp => tmp | SDcons _ _ tmp _ => tmp end.
         
         Definition sd_head_type (sd: set_destination) :=
           match sd with SDbase _ ty _ => ty | SDcons _ ty _ _ => ty end.
         
         Definition temp_for_sd (ty: self__Imp.type) (sd: set_destination) : self__SimplExpr.mon ident :=
             (* if type_eq ty (sd_head_type sd) then ret (sd_temp sd) else gensym ty.*)
             cheat.
      FEnd destination.

      FDefinition dummy_expr := Clight.Econst_int Int.zero self__Imp.type_int32s.
      
      FRecursion eval_simpl_expr about Clight.expr motive (fun (_ : Clight.expr) => option val) by _rect.          
          Case Econst_float := (fun n ty => Some(Vfloat n)).
          Case Econst_int := (fun n ty => Some(Vint n)).
          Case Econst_single := (fun n ty => Some(Vsingle n)).
          Case Econst_long := (fun n ty => Some(Vlong n)).
          Case Ecast := (fun b eval_simpl_expr_b ty  => 
                            match eval_simpl_expr_b with
                            | None => None
                            | Some v => Clight.Sem.sem_cast v (Clight.typeof b) ty Mem.empty
                            end).
          Case Etempvar := (fun id ty => None).
          Case Esizeof := (fun _ _ => None).
          Case Ealignof := (fun _ _ => None).
      FEnd eval_simpl_expr.
      
      FDefinition makeif : Clight.expr -> Clight.stmt -> Clight.stmt -> Clight.stmt :=
        fun a s1 s2 =>
          match eval_simpl_expr a with
          | Some v =>
              match Clight.Sem.bool_val v (Clight.typeof a) Mem.empty with
              | Some b => if b then s1 else s2
              | None => Clight.Sifthenelse a s1 s2
              end
          | None => Clight.Sifthenelse a s1 s2
          end.      
      
      FRecursion transl_expr about C.expr motive (fun (_ : C.expr) => destination -> self__SimplExpr.mon (list Clight.stmt * Clight.expr)) by _rect.
          Case Evar := (fun id ty => fun dst => self__SimplExpr.ret (self__SimplExpr.finish dst nil (Clight.Etempvar id ty))).
          Case Eval := (fun v ty => fun dst => 
                             match v with 
                              | Vint n => self__SimplExpr.ret (self__SimplExpr.finish dst nil (Clight.Econst_int n ty)) 
                              | Vlong n => self__SimplExpr.ret (self__SimplExpr.finish dst nil (Clight.Econst_long n ty))
                              | Vfloat n => self__SimplExpr.ret (self__SimplExpr.finish dst nil (Clight.Econst_float n ty))
                              | Vsingle n => self__SimplExpr.ret (self__SimplExpr.finish dst nil (Clight.Econst_single n ty))
                              | _ =>  self__SimplExpr.error (msg "SimplExpr.transl_expr: Eval") end).
          Case Ecast := (fun r transl_expr_r ty => fun dst =>
                           self__SimplExpr.bind2 (transl_expr_r self__SimplExpr.For_val)
                               (fun sl1 a1 => match dst with
                            | self__SimplExpr.For_val | self__SimplExpr.For_set _ =>
                                self__SimplExpr.bind (self__SimplExpr.gensym ty)
                                   (fun t => self__SimplExpr.ret (self__SimplExpr.finish dst (sl1) (Clight.Ecast a1 ty)))
                            | self__SimplExpr.For_effects =>
                                transl_expr_r self__SimplExpr.For_effects end)).                    
          Case Ecomma := (fun r1 transl_expr_r1 r2 transl_expr_r2 ty => fun dst => 
                            self__SimplExpr.bind2 (transl_expr_r1 self__SimplExpr.For_effects)
                              (fun sl1 a1 => 
                                   self__SimplExpr.bind2 (transl_expr_r2 dst)
                                      (fun sl2 a2 => self__SimplExpr.ret (sl1 ++ sl2, a2)))).
          Case Econdition := (fun r1 transl_expr_r1 r2 transl_expr_r2 r3 transl_expr_r3 ty => 
                                fun dst => 
                                    self__SimplExpr.bind2 (transl_expr_r1 self__SimplExpr.For_val) 
                                       (fun sl1 a1 => 
                                           match dst with
                                          | self__SimplExpr.For_val =>
                                              self__SimplExpr.bind (self__SimplExpr.gensym ty) (fun t => 
                                                  let sd := self__SimplExpr.SDbase ty ty t in
                                                  self__SimplExpr.bind2 (transl_expr_r2 (self__SimplExpr.For_set sd)) 
                                                      (fun sl2 a2 => 
                                                          self__SimplExpr.bind2 (transl_expr_r3 (self__SimplExpr.For_set sd)) 
                                                              (fun sl3 a3 => 
                                                                  self__SimplExpr.ret (sl1 ++ makeif a1 (self__SimplExpr.makeseq sl2) (self__SimplExpr.makeseq sl3) :: nil, Clight.Etempvar t ty))))
                                          | self__SimplExpr.For_effects =>
                                              self__SimplExpr.bind2 (transl_expr_r2 self__SimplExpr.For_effects) (fun sl2 a2 => 
                                                  self__SimplExpr.bind2 (transl_expr_r3 self__SimplExpr.For_effects) (fun sl3 a3 => 
                                                      self__SimplExpr.ret (sl1 ++ makeif a1 (self__SimplExpr.makeseq sl2) (self__SimplExpr.makeseq sl3) :: nil, dummy_expr)))
                                          | self__SimplExpr.For_set sd =>
                                              self__SimplExpr.bind (self__SimplExpr.temp_for_sd ty sd) (fun t => 
                                                  let sd' := self__SimplExpr.SDcons ty ty t sd in
                                                  self__SimplExpr.bind2 (transl_expr_r2 (self__SimplExpr.For_set sd')) 
                                                      (fun sl2 a2 => 
                                                          self__SimplExpr.bind2 (transl_expr_r3 (self__SimplExpr.For_set sd')) 
                                                              (fun sl3 a3 => 
                                                                   self__SimplExpr.ret (sl1 ++ makeif a1 (self__SimplExpr.makeseq sl2) (self__SimplExpr.makeseq sl3) :: nil,
                                                                  dummy_expr))))
                                          end)).
          Case Eseqor := (fun r1 transl_expr_r1 r2 transl_expr_r2 ty => fun dst => 
                            self__SimplExpr.bind2 (transl_expr_r1 self__SimplExpr.For_val)
                               (fun sl1 a1 =>
                                    match dst with
                                    | self__SimplExpr.For_val =>
                                        self__SimplExpr.bind (self__SimplExpr.gensym ty)
                                             (fun t => 
                                                 let sd := self__SimplExpr.SDbase self__Imp.type_bool ty t in
                                                 self__SimplExpr.bind2 (transl_expr_r2 (self__SimplExpr.For_set sd))
                                                     (fun sl2 a2 => 
                                                    self__SimplExpr.ret (sl1 ++
                                                     makeif a1 (Clight.Sset t (Clight.Econst_int Int.one ty)) (self__SimplExpr.makeseq sl2) :: nil,
                                                     Clight.Etempvar t ty)))                             
                                    | self__SimplExpr.For_effects =>
                                        self__SimplExpr.bind2 (transl_expr_r2 self__SimplExpr.For_effects)
                                             (fun sl2 a2 => self__SimplExpr.ret (sl1 ++ makeif a1 Clight.Sskip (self__SimplExpr.makeseq sl2) :: nil, dummy_expr))                                        
                                    | self__SimplExpr.For_set sd =>
                                        self__SimplExpr.bind (self__SimplExpr.temp_for_sd ty sd)
                                            (fun t => 
                                               let sd' := self__SimplExpr.SDcons self__Imp.type_bool ty t sd in
                                               self__SimplExpr.bind2 (transl_expr_r2 (self__SimplExpr.For_set sd'))
                                                  (fun sl2 a2 => 
                                                      self__SimplExpr.ret (sl1 ++
                                                             makeif a1 (self__SimplExpr.makeseq (self__SimplExpr.do_set sd (Clight.Econst_int Int.one ty))) (self__SimplExpr.makeseq sl2) :: nil,
                                                          dummy_expr)))                                                                                                                        
                                    end)).
          Case Eseqand := (fun r1 transl_expr_r1 r2 transl_expr_r2 ty => fun dst => 
                               self__SimplExpr.bind2 (transl_expr_r1 self__SimplExpr.For_val)
                               (fun sl1 a1 =>
                                    match dst with
                                    | self__SimplExpr.For_val =>
                                        self__SimplExpr.bind (self__SimplExpr.gensym ty)
                                             (fun t => 
                                                 let sd := self__SimplExpr.SDbase self__Imp.type_bool ty t in
                                                 self__SimplExpr.bind2 (transl_expr_r2 (self__SimplExpr.For_set sd))
                                                     (fun sl2 a2 => 
                                                    self__SimplExpr.ret (sl1 ++
                                                           makeif a1 (self__SimplExpr.makeseq sl2) (Clight.Sset t (Clight.Econst_int Int.zero ty)) :: nil,
                                                        Clight.Etempvar t ty)))                      
                                    | self__SimplExpr.For_effects =>
                                        self__SimplExpr.bind2 (transl_expr_r2 self__SimplExpr.For_effects)
                                             (fun sl2 a2 => self__SimplExpr.ret (sl1 ++ makeif a1 Clight.Sskip (self__SimplExpr.makeseq sl2) :: nil, dummy_expr))                                        
                                    | self__SimplExpr.For_set sd =>
                                        self__SimplExpr.bind (self__SimplExpr.temp_for_sd ty sd)
                                            (fun t => 
                                               let sd' := self__SimplExpr.SDcons self__Imp.type_bool ty t sd in
                                               self__SimplExpr.bind2 (transl_expr_r2 (self__SimplExpr.For_set sd'))
                                                  (fun sl2 a2 => 
                                                      self__SimplExpr.ret (sl1 ++
                                                             makeif a1 (self__SimplExpr.makeseq sl2) (self__SimplExpr.makeseq (self__SimplExpr.do_set sd (Clight.Econst_int Int.zero ty))) :: nil,
                                                          dummy_expr)))                                                                                                                      
                                    end)).                            
          Case Esizeof := (fun ty' ty => fun dst => 
                            self__SimplExpr.ret (self__SimplExpr.finish dst nil (Clight.Esizeof ty' ty))).
          Case Ealignof := (fun ty' ty => fun dst => 
                            self__SimplExpr.ret (self__SimplExpr.finish dst nil (Clight.Ealignof ty' ty))).          
          Case Eparen := (fun e tycast ty => fun dst => fun _ => self__SimplExpr.error (msg "SimplExpr.transl_expr: paren")).
      FEnd transl_expr.

      FDefinition transl_expression : C.expr -> self__SimplExpr.mon (Clight.stmt * Clight.expr) := fun r =>
          self__SimplExpr.bind2 (transl_expr r self__SimplExpr.For_val) (fun sl a => self__SimplExpr.ret (self__SimplExpr.makeseq sl, a)).

      FDefinition transl_expr_stmt : C.expr -> self__SimplExpr.mon Clight.stmt := fun r =>
          self__SimplExpr.bind2 (transl_expr r self__SimplExpr.For_effects) (fun sl a => self__SimplExpr.ret (self__SimplExpr.makeseq sl)).          

      FDefinition transl_if : C.expr -> Clight.stmt -> Clight.stmt -> self__SimplExpr.mon Clight.stmt  := fun r s1 s2 => 
          self__SimplExpr.bind2 (transl_expr r self__SimplExpr.For_val) (fun sl a => self__SimplExpr.ret (self__SimplExpr.makeseq (sl ++ makeif a s1 s2 :: nil))).          

      FLemma is_Sskip:
        forall s, {s = Clight.Sskip} + {s <> Clight.Sskip}.
      FProofLemma.
      apply cheat. Qed.
      CloseFLemma.
      
      FRecursion transl_stmt about C.statement motive (fun (_ : C.statement) => self__SimplExpr.mon Clight.stmt) by _rect.
          Case Sskip :=  (self__SimplExpr.ret Clight.Sskip).
          Case Sdo := (fun e => transl_expr_stmt e).
          Case Ssequence := (fun s1 transl_stmt_s1 s2 transl_stmt_s2 => 
                              self__SimplExpr.bind (transl_stmt_s1) (fun ts1 => 
                                  self__SimplExpr.bind (transl_stmt_s2) (fun ts2 => 
                                      self__SimplExpr.ret (Clight.Ssequence ts1 ts2)))).
          Case Sifthenelse := (fun e s1 transl_stmt_s1 s2 transl_stmt_s2 =>
                                self__SimplExpr.bind (transl_stmt_s1) (fun ts1 => 
                                  self__SimplExpr.bind (transl_stmt_s2) (fun ts2 => 
                                      self__SimplExpr.bind2 (transl_expression e) (fun s' a => 
                                          if is_Sskip ts1 && is_Sskip ts2 then
                                              self__SimplExpr.ret (Clight.Ssequence s' Clight.Sskip)
                                          else
                                              self__SimplExpr.ret (Clight.Ssequence s' (Clight.Sifthenelse a ts1 ts2)))))).
          Case Swhile := (fun e s1 transl_stmt_s1 =>
                           self__SimplExpr.bind (transl_if e Clight.Sskip Clight.Sbreak) (fun s' => 
                               self__SimplExpr.bind (transl_stmt_s1) (fun ts1 => 
                                   self__SimplExpr.ret (Clight.Sloop (Clight.Ssequence s' ts1) Clight.Sskip)))).
          Case Sdowhile := (fun e s1 transl_stmt_s1 =>
                              self__SimplExpr.bind (transl_if e Clight.Sskip Clight.Sbreak) (fun s' => 
                                  self__SimplExpr.bind (transl_stmt_s1) (fun ts1 => 
                                      self__SimplExpr.ret (Clight.Sloop ts1 s')))).
          Case Sfor := (fun s1 transl_stmt_s1 e2 s3 transl_stmt_s3 s4 transl_stmt_s4 =>
                          self__SimplExpr.bind (transl_stmt_s1) (fun ts1 => 
                              self__SimplExpr.bind (transl_if e2 Clight.Sskip Clight.Sbreak) (fun s' => 
                                  self__SimplExpr.bind (transl_stmt_s3) (fun ts3 => 
                                      self__SimplExpr.bind (transl_stmt_s4) (fun ts4 => 
                                          if is_Sskip ts1 then
                                              self__SimplExpr.ret (Clight.Sloop (Clight.Ssequence s' ts4) ts3)
                                          else
                                              self__SimplExpr.ret (Clight.Ssequence ts1 (Clight.Sloop (Clight.Ssequence s' ts4) ts3))))))).
          Case Sbreak := (self__SimplExpr.ret Clight.Sbreak).
          Case Scontinue := (self__SimplExpr.ret Clight.Scontinue).
          Case Sreturn := (fun e =>
                            match e with
                            | None => self__SimplExpr.ret (Clight.Sreturn None)
                            | Some e => 
                                self__SimplExpr.bind2 (transl_expression e) (fun s' a => 
                                    self__SimplExpr.ret (Clight.Ssequence s' (Clight.Sreturn (Some a))))
                            end).
          Case Slabel := (fun lbl s1 transl_stmt_s1 => 
                            self__SimplExpr.bind transl_stmt_s1 (fun ts1 => 
                                self__SimplExpr.ret (Clight.Slabel lbl ts1))).
          Case Sgoto := (fun lbl => self__SimplExpr.ret (Clight.Sgoto lbl)).
      FEnd transl_stmt.

      FDefinition transl_function : C.function -> res Clight.function := fun f => 
          match transl_stmt f.(self__Imp.C.fn_body) (self__SimplExpr.initial_generator tt) with
          | self__SimplExpr.Err msg =>
              Error msg
          | self__SimplExpr.Res tbody g i =>
              OK (Clight.mkfunction
                      f.(self__Imp.C.fn_return)
                      f.(self__Imp.C.fn_callconv)
                      f.(self__Imp.C.fn_params)
                      f.(self__Imp.C.fn_vars)
                      g.(self__SimplExpr.gen_trail)
                      tbody)
          end.      

     FDefinition transl_fundef : C.fundef -> res Clight.fundef := fun fd =>
          match fd with
          | Internal f =>
              bind (transl_function f) (fun tf => OK (Internal tf))              
          | _ => cheat (* No external yet *)              
          end.
     
     FDefinition transl_program : C.program -> res Clight.program := fun p =>     
       do p1 <- AST.transform_partial_program (transl_fundef) p; OK p1.

     (* Relational specification of translation *)
     Family Spec.
          FDefinition final : self__SimplExpr.destination -> Clight.expr -> list Clight.stmt := fun dst a => 
              match dst with
              | self__SimplExpr.For_val => nil
              | self__SimplExpr.For_effects => nil
              | self__SimplExpr.For_set sd => self__SimplExpr.do_set sd a
              end.

          FInductive tr_expr : 
                  Clight.Sem.temp_env -> 
                  self__SimplExpr.destination -> C.expr -> list Clight.stmt -> 
                  Clight.expr -> list ident -> Prop :=              
             | tr_val_effect: forall le v ty any tmp,
                 tr_expr le self__SimplExpr.For_effects (C.Eval v ty) nil any tmp
             | tr_val_value: forall le v ty a tmp,
                 Clight.typeof a = ty ->
                 (forall tge e le' m,
                   (forall id, In id tmp -> le'!id = le!id) ->
                   Clight.Sem.eval_expr tge e le' m a v) ->
                 tr_expr le self__SimplExpr.For_val (C.Eval v ty) nil a tmp
             | tr_val_set: forall le sd v ty a any tmp,
                 Clight.typeof a = ty ->
                 (forall tge e le' m,
                   (forall id, In id tmp -> le'!id = le!id) ->
                   Clight.Sem.eval_expr tge e le' m a v) ->
                 tr_expr le (self__SimplExpr.For_set sd) (C.Eval v ty)
                             (self__SimplExpr.do_set sd a) any tmp
             | tr_sizeof: forall le dst ty' ty tmp,
                 tr_expr le dst (C.Esizeof ty' ty)
                             (final dst (Clight.Esizeof ty' ty))
                             (Clight.Esizeof ty' ty) tmp
             | tr_alignof: forall le dst ty' ty tmp,
                 tr_expr le dst (C.Ealignof ty' ty)
                             (final dst (Clight.Ealignof ty' ty))
                             (Clight.Ealignof ty' ty) tmp
             | tr_cast_effects: forall le e1 ty sl1 a1 any tmp,
                 tr_expr le self__SimplExpr.For_effects e1 sl1 a1 tmp ->
                 tr_expr le self__SimplExpr.For_effects (C.Ecast e1 ty)
                             sl1
                             any tmp
             | tr_cast_val: forall le dst e1 ty sl1 a1 tmp,
                 tr_expr le self__SimplExpr.For_val e1 sl1 a1 tmp ->
                 tr_expr le dst (C.Ecast e1 ty)
                             (sl1 ++ final dst (Clight.Ecast a1 ty))
                             (Clight.Ecast a1 ty) tmp
             | tr_seqand_val: forall le e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp,
                 tr_expr le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
                 tr_expr le (self__SimplExpr.For_set (self__SimplExpr.SDbase self__Imp.type_bool ty t)) e2 sl2 a2 tmp2 ->
                 list_disjoint tmp1 tmp2 ->
                 incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
                 tr_expr le self__SimplExpr.For_val (C.Eseqand e1 e2 ty)
                               (sl1 ++ makeif a1 (self__SimplExpr.makeseq sl2)
                                                 (Clight.Sset t (Clight.Econst_int Int.zero ty)) :: nil)
                               (Clight.Etempvar t ty) tmp
             | tr_seqand_effects: forall le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
                 tr_expr le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
                 tr_expr le self__SimplExpr.For_effects e2 sl2 a2 tmp2 ->
                 list_disjoint tmp1 tmp2 ->
                 incl tmp1 tmp -> incl tmp2 tmp ->
                 tr_expr le self__SimplExpr.For_effects (C.Eseqand e1 e2 ty)
                               (sl1 ++ makeif a1 (self__SimplExpr.makeseq sl2) Clight.Sskip :: nil)
                               any tmp
             | tr_seqand_set: forall le sd e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 any tmp,
                 tr_expr le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
                 tr_expr le (self__SimplExpr.For_set (self__SimplExpr.SDcons self__Imp.type_bool ty t sd)) e2 sl2 a2 tmp2 ->
                 list_disjoint tmp1 tmp2 ->
                 incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
                 tr_expr le (self__SimplExpr.For_set sd) (C.Eseqand e1 e2 ty)
                               (sl1 ++ makeif a1 (self__SimplExpr.makeseq sl2)
                                                 (self__SimplExpr.makeseq (self__SimplExpr.do_set sd (Clight.Econst_int Int.zero ty))) :: nil)
                               any tmp
             | tr_seqor_val: forall le e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp,
                 tr_expr le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
                 tr_expr le (self__SimplExpr.For_set (self__SimplExpr.SDbase self__Imp.type_bool ty t)) e2 sl2 a2 tmp2 ->
                 list_disjoint tmp1 tmp2 ->
                 incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
                 tr_expr le self__SimplExpr.For_val (C.Eseqor e1 e2 ty)
                               (sl1 ++ makeif a1 (Clight.Sset t (Clight.Econst_int Int.one ty))
                                                 (self__SimplExpr.makeseq sl2) :: nil)
                               (Clight.Etempvar t ty) tmp
             | tr_seqor_effects: forall le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
                 tr_expr le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
                 tr_expr le self__SimplExpr.For_effects e2 sl2 a2 tmp2 ->
                 list_disjoint tmp1 tmp2 ->
                 incl tmp1 tmp -> incl tmp2 tmp ->
                 tr_expr le self__SimplExpr.For_effects (C.Eseqor e1 e2 ty)
                               (sl1 ++ makeif a1 Clight.Sskip (self__SimplExpr.makeseq sl2) :: nil)
                               any tmp
             | tr_seqor_set: forall le sd e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 any tmp,
                 tr_expr le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
                 tr_expr le (self__SimplExpr.For_set (self__SimplExpr.SDcons self__Imp.type_bool ty t sd)) e2 sl2 a2 tmp2 ->
                 list_disjoint tmp1 tmp2 ->
                 incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
                 tr_expr le (self__SimplExpr.For_set sd) (C.Eseqor e1 e2 ty)
                               (sl1 ++ makeif a1 (self__SimplExpr.makeseq (self__SimplExpr.do_set sd (Clight.Econst_int Int.one ty)))
                               (self__SimplExpr.makeseq sl2) :: nil)
                               any tmp
             | tr_condition_val: forall le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t tmp,
                 tr_expr le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
                 tr_expr le (self__SimplExpr.For_set (self__SimplExpr.SDbase ty ty t)) e2 sl2 a2 tmp2 ->
                 tr_expr le (self__SimplExpr.For_set (self__SimplExpr.SDbase ty ty t)) e3 sl3 a3 tmp3 ->
                 list_disjoint tmp1 tmp2 ->
                 list_disjoint tmp1 tmp3 ->
                 incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp -> In t tmp ->
                 tr_expr le self__SimplExpr.For_val (C.Econdition e1 e2 e3 ty)
                                 (sl1 ++ makeif a1 (self__SimplExpr.makeseq sl2) (self__SimplExpr.makeseq sl3) :: nil)
                                 (Clight.Etempvar t ty) tmp
             | tr_condition_effects: forall le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp,
                 tr_expr le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
                 tr_expr le self__SimplExpr.For_effects e2 sl2 a2 tmp2 ->
                 tr_expr le self__SimplExpr.For_effects e3 sl3 a3 tmp3 ->
                 list_disjoint tmp1 tmp2 ->
                 list_disjoint tmp1 tmp3 ->
                 incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp ->
                 tr_expr le self__SimplExpr.For_effects (C.Econdition e1 e2 e3 ty)
                                 (sl1 ++ makeif a1 (self__SimplExpr.makeseq sl2) (self__SimplExpr.makeseq sl3) :: nil)
                                 any tmp
             | tr_condition_set: forall le sd t e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp,
                 tr_expr le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
                 tr_expr le (self__SimplExpr.For_set (self__SimplExpr.SDcons ty ty t sd)) e2 sl2 a2 tmp2 ->
                 tr_expr le (self__SimplExpr.For_set (self__SimplExpr.SDcons ty ty t sd)) e3 sl3 a3 tmp3 ->
                 list_disjoint tmp1 tmp2 ->
                 list_disjoint tmp1 tmp3 ->
                 incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp -> In t tmp ->
                 tr_expr le (self__SimplExpr.For_set sd) (C.Econdition e1 e2 e3 ty)
                                 (sl1 ++ makeif a1 (self__SimplExpr.makeseq sl2) (self__SimplExpr.makeseq sl3) :: nil)
                                 any tmp                    
             | tr_comma: forall le dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp,
                 tr_expr le self__SimplExpr.For_effects e1 sl1 a1 tmp1 ->
                 tr_expr le dst e2 sl2 a2 tmp2 ->
                 list_disjoint tmp1 tmp2 ->
                 incl tmp1 tmp -> incl tmp2 tmp ->
                 tr_expr le dst (C.Ecomma e1 e2 ty) (sl1 ++ sl2) a2 tmp.
                (*
                Variable ge: genv.
                Variable e: env.
                Variable le: temp_env.
                Variable m: mem. *)

             MetaData tr_top.
             Inductive tr_top: 
               self__Imp.Clight.Sem.genv -> 
               self__Imp.Clight.Sem.env -> 
               self__Imp.Clight.Sem.temp_env -> 
               mem -> 
               self__SimplExpr.destination -> 
               self__Imp.C.expr -> 
               list self__Imp.Clight.stmt -> 
               self__Imp.Clight.expr -> list ident -> Prop :=
                  | tr_top_val_val: forall ge e le m v ty a tmp,
                      self__Imp.Clight.typeof a = ty -> self__Imp.Clight.Sem.eval_expr ge e le m a v ->
                      tr_top ge e le m self__SimplExpr.For_val (self__Imp.C.Eval v ty) nil a tmp
                  | tr_top_base: forall ge e le m dst r sl a tmp,
                      self__Spec.tr_expr le dst r sl a tmp ->
                      tr_top ge e le m dst r sl a tmp.
             FEnd tr_top.

             MetaData tr_expression.
             Inductive tr_expression: self__Imp.C.expr -> self__Imp.Clight.stmt -> self__Imp.Clight.expr -> Prop :=
                  | tr_expression_intro: forall r sl a tmps,
                      (forall ge e le m, self__Spec.tr_top ge e le m self__SimplExpr.For_val r sl a tmps) ->
                      tr_expression r (self__SimplExpr.makeseq sl) a.
             FEnd tr_expression.
             
             MetaData tr_expr_stmt.
             Inductive tr_expr_stmt: self__Imp.C.expr -> self__Imp.Clight.stmt -> Prop :=
                  | tr_expr_stmt_intro: forall r sl a tmps,
                      (forall ge e le m, self__Spec.tr_top ge e le m self__SimplExpr.For_effects r sl a tmps) ->
                      tr_expr_stmt r (self__SimplExpr.makeseq sl).
             FEnd tr_expr_stmt.

             MetaData tr_if.
             Inductive tr_if: self__Imp.C.expr -> self__Imp.Clight.stmt -> self__Imp.Clight.stmt -> self__Imp.Clight.stmt  -> Prop :=
                  | tr_if_intro: forall r s1 s2 sl a tmps,
                      (forall ge e le m, self__Spec.tr_top ge e le m self__SimplExpr.For_val r sl a tmps) ->
                      tr_if r s1 s2 (self__SimplExpr.makeseq (sl ++ self__SimplExpr.makeif a s1 s2 :: nil)).
             FEnd tr_if.

             FInductive tr_stmt: C.statement -> Clight.stmt -> Prop :=
                | tr_skip:
                    tr_stmt C.Sskip Clight.Sskip
                | tr_do: forall r s,
                    tr_expr_stmt r s ->
                    tr_stmt (C.Sdo r) s
                | tr_seq: forall s1 s2 ts1 ts2,
                   tr_stmt s1 ts1 -> tr_stmt s2 ts2 ->
                   tr_stmt (C.Ssequence s1 s2) (Clight.Ssequence ts1 ts2)
                | tr_ifthenelse_empty: forall r s' a,
                    tr_expression r s' a ->
                    tr_stmt (C.Sifthenelse r C.Sskip C.Sskip) (Clight.Ssequence s' Clight.Sskip)
                | tr_ifthenelse: forall r s1 s2 s' a ts1 ts2,
                    tr_expression r s' a ->
                    tr_stmt s1 ts1 -> tr_stmt s2 ts2 ->
                    tr_stmt (C.Sifthenelse r s1 s2) (Clight.Ssequence s' (Clight.Sifthenelse a ts1 ts2))
                | tr_while: forall r s1 s' ts1,
                    tr_if r Clight.Sskip Clight.Sbreak s' ->
                    tr_stmt s1 ts1 ->
                    tr_stmt (C.Swhile r s1)
                            (Clight.Sloop (Clight.Ssequence s' ts1) Clight.Sskip)
                | tr_dowhile: forall r s1 s' ts1,
                    tr_if r Clight.Sskip Clight.Sbreak s' ->
                    tr_stmt s1 ts1 ->
                    tr_stmt (C.Sdowhile r s1)
                            (Clight.Sloop ts1 s')
                | tr_for_1: forall r s3 s4 s' ts3 ts4,
                    tr_if r Clight.Sskip Clight.Sbreak s' ->
                    tr_stmt s3 ts3 ->
                    tr_stmt s4 ts4 ->
                    tr_stmt (C.Sfor C.Sskip r s3 s4)
                            (Clight.Sloop (Clight.Ssequence s' ts4) ts3)
                | tr_for_2: forall s1 r s3 s4 s' ts1 ts3 ts4,
                    tr_if r Clight.Sskip Clight.Sbreak s' ->
                    s1 <> C.Sskip ->
                    tr_stmt s1 ts1 ->
                    tr_stmt s3 ts3 ->
                    tr_stmt s4 ts4 ->
                    tr_stmt (C.Sfor s1 r s3 s4)
                            (Clight.Ssequence ts1 (Clight.Sloop (Clight.Ssequence s' ts4) ts3))
                | tr_break:
                    tr_stmt C.Sbreak Clight.Sbreak
                | tr_continue:
                    tr_stmt C.Scontinue Clight.Scontinue
                | tr_return_none:
                    tr_stmt (C.Sreturn None) (Clight.Sreturn None)
                | tr_return_some: forall r s' a,
                    tr_expression r s' a ->
                    tr_stmt (C.Sreturn (Some r)) (Clight.Ssequence s' (Clight.Sreturn (Some a)))
                | tr_label: forall lbl s ts,
                    tr_stmt s ts ->
                    tr_stmt (C.Slabel lbl s) (Clight.Slabel lbl ts)
                | tr_goto: forall lbl,
                    tr_stmt (C.Sgoto lbl) (Clight.Sgoto lbl).
             
                (* Translation meets spec *)
                (*
                    Lemma transl_meets_spec:
                     (forall r dst g sl a g' I,
                      transl_expr ce dst r g = Res (sl, a) g' I ->
                      dest_below dst g ->
                      exists tmps, (forall le, tr_expr le dst r sl a (add_dest dst tmps)) /\ contained tmps g g')
                    /\
                     (forall rl g sl al g' I,
                      transl_exprlist ce rl g = Res (sl, al) g' I ->
                      exists tmps, (forall le, tr_exprlist le rl sl al tmps) /\ contained tmps g g').
                  Proof.
                  
                  Lemma transl_expr_meets_spec:
                     forall r dst g sl a g' I,
                     transl_expr ce dst r g = Res (sl, a) g' I ->
                     dest_below dst g ->
                     exists tmps, forall ge e le m, tr_top ge e le m dst r sl a tmps.
                  Proof.
                  
                  Lemma transl_expression_meets_spec:
                    forall r g s a g' I,
                    transl_expression ce r g = Res (s, a) g' I ->
                    tr_expression r s a.
                  Proof.
                  
                  Lemma transl_expr_stmt_meets_spec:
                    forall r g s g' I,
                    transl_expr_stmt ce r g = Res s g' I ->
                    tr_expr_stmt r s.
                  Proof.
                  
                  Lemma transl_if_meets_spec:
                    forall r s1 s2 g s g' I,
                    transl_if ce r s1 s2 g = Res s g' I ->
                    tr_if r s1 s2 s.
                  Proof.
                  
                  Lemma transl_stmt_meets_spec:
                    forall s g ts g' I, transl_stmt ce s g = Res ts g' I -> tr_stmt s ts
                  with transl_lblstmt_meets_spec:
                    forall s g ts g' I, transl_lblstmt ce s g = Res ts g' I -> tr_lblstmts s ts.
                  Proof.
                *)
             
                MetaData tr_function.
                Inductive tr_function: self__Imp.C.function -> self__Imp.Clight.function -> Prop :=
                     | tr_function_intro: forall f tf,
                         self__Spec.tr_stmt f.(self__Imp.C.fn_body) tf.(self__Imp.Clight.fn_body) ->
                         self__Imp.Clight.fn_return tf = self__Imp.C.fn_return f ->
                         self__Imp.Clight.fn_callconv tf = self__Imp.C.fn_callconv f ->
                         self__Imp.Clight.fn_params tf = self__Imp.C.fn_params f ->
                         self__Imp.Clight.fn_vars tf = self__Imp.C.fn_vars f ->
                         tr_function f tf.
                FEnd tr_function.

                (* Lemma transl_function_spec:
                    forall f tf,
                    transl_function ce f = OK tf ->
                    tr_function f tf. *)
                
                MetaData tr_fundef.
                Inductive tr_fundef (p: self__Imp.C.program): self__Imp.C.fundef -> self__Imp.Clight.fundef -> Prop :=
                    | tr_internal: forall f tf,
                        self__Spec.tr_function (* p.(prog_comp_env)*) f tf ->
                        tr_fundef p (Internal f) (Internal tf).                    
                FEnd tr_fundef.
                
                (* Lemma transl_fundef_spec:
                   forall p fd tfd,
                   transl_fundef p.(prog_comp_env) fd = OK tfd ->
                   tr_fundef p fd tfd.*)
          FEnd Spec.
          
          (* Correctness of the pass *)
          Family Proof.
              FDefinition match_prog : C.program -> Clight.program -> Prop := fun p tp => cheat.
              
              FInductive match_cont : (* composite_env ->*) C.Sem.cont -> Clight.Sem.cont -> Prop :=
                   | match_Kstop: 
                       match_cont C.Sem.Kstop Clight.Sem.Kstop
                   | match_Kseq: forall s k ts tk,
                       Spec.tr_stmt s ts ->
                       match_cont k tk ->
                       match_cont (C.Sem.Kseq s k) (Clight.Sem.Kseq ts tk)
                   | match_Kwhile2: forall r s k s' ts tk,
                       Spec.tr_if r Clight.Sskip Clight.Sbreak s' ->
                       Spec.tr_stmt s ts ->
                       match_cont k tk ->
                       match_cont (C.Sem.Kwhile2 r s k)
                                  (Clight.Sem.Kloop1 (Clight.Ssequence s' ts) Clight.Sskip tk)
                   | match_Kdowhile1: forall r s k s' ts tk,
                       Spec.tr_if r Clight.Sskip Clight.Sbreak s' ->
                       Spec.tr_stmt s ts ->
                       match_cont k tk ->
                       match_cont (C.Sem.Kdowhile1 r s k)
                                  (Clight.Sem.Kloop1 ts s' tk)
                   | match_Kfor3: forall r s3 s k ts3 s' ts tk,
                       Spec.tr_if r Clight.Sskip Clight.Sbreak s' ->
                       Spec.tr_stmt s3 ts3 ->
                       Spec.tr_stmt s ts ->
                       match_cont k tk ->
                       match_cont (C.Sem.Kfor3 r s3 s k)
                                  (Clight.Sem.Kloop1 (Clight.Ssequence s' ts) ts3 tk)
                   | match_Kfor4: forall r s3 s k ts3 s' ts tk,
                       Spec.tr_if r Clight.Sskip Clight.Sbreak s' ->
                       Spec.tr_stmt s3 ts3 ->
                       Spec.tr_stmt s ts ->
                       match_cont k tk ->
                       match_cont (C.Sem.Kfor4 r s3 s k)
                                  (Clight.Sem.Kloop2 (Clight.Ssequence s' ts) ts3 tk)                   
              with match_cont_exp : (* composite_env*) destination -> Clight.expr -> C.Sem.cont -> Clight.Sem.cont -> Prop :=
                   | match_Kdo: forall k a tk,
                       match_cont k tk ->
                       match_cont_exp self__SimplExpr.For_effects a (C.Sem.Kdo k) tk
                   | match_Kifthenelse_empty: forall a k tk,
                       match_cont k tk ->
                       match_cont_exp self__SimplExpr.For_val a (C.Sem.Kifthenelse C.Sskip C.Sskip k) (Clight.Sem.Kseq Clight.Sskip tk)
                   | match_Kifthenelse_1: forall a s1 s2 k ts1 ts2 tk,
                       Spec.tr_stmt s1 ts1 -> Spec.tr_stmt s2 ts2 ->
                       match_cont k tk ->
                       match_cont_exp self__SimplExpr.For_val a (C.Sem.Kifthenelse s1 s2 k) (Clight.Sem.Kseq (Clight.Sifthenelse a ts1 ts2) tk)
                   | match_Kwhile1: forall r s k s' a ts tk,
                       Spec.tr_if r Clight.Sskip Clight.Sbreak s' ->
                       Spec.tr_stmt s ts ->
                       match_cont k tk ->
                       match_cont_exp self__SimplExpr.For_val a
                          (C.Sem.Kwhile1 r s k)
                          (Clight.Sem.Kseq (makeif a Clight.Sskip Clight.Sbreak)
                            (Clight.Sem.Kseq ts (Clight.Sem.Kloop1 (Clight.Ssequence s' ts) Clight.Sskip tk)))
                   | match_Kdowhile2: forall r s k s' a ts tk,
                       Spec.tr_if r Clight.Sskip Clight.Sbreak s' ->
                       Spec.tr_stmt s ts ->
                        match_cont k tk ->
                        match_cont_exp self__SimplExpr.For_val a
                          (C.Sem.Kdowhile2 r s k)
                          (Clight.Sem.Kseq (makeif a Clight.Sskip Clight.Sbreak) (Clight.Sem.Kloop2 ts s' tk))
                   | match_Kfor2: forall r s3 s k s' a ts3 ts tk,
                       Spec.tr_if r Clight.Sskip Clight.Sbreak s' ->
                       Spec.tr_stmt s3 ts3 ->
                       Spec.tr_stmt s ts ->
                       match_cont k tk ->
                       match_cont_exp self__SimplExpr.For_val a
                         (C.Sem.Kfor2 r s3 s k)
                         (Clight.Sem.Kseq (makeif a Clight.Sskip Clight.Sbreak)
                           (Clight.Sem.Kseq ts (Clight.Sem.Kloop1 (Clight.Ssequence s' ts) ts3 tk)))
                   | match_Kreturn: forall k a tk,
                       match_cont k tk ->
                       match_cont_exp self__SimplExpr.For_val a (C.Sem.Kreturn k) (Clight.Sem.Kseq (Clight.Sreturn (Some a)) tk).

              MetaData Kseqlist.
                 Fixpoint Kseqlist (sl: list self__Imp.Clight.stmt) (k: self__Imp.Clight.Sem.cont) :=
                 match sl with
                 | nil => k
                 | s :: l => self__Imp.Clight.Sem.Kseq s (Kseqlist l k)
                 end.
              FEnd Kseqlist.
              
              MetaData match_states.
              Inductive match_states: self__Imp.C.Sem.state -> self__Imp.Clight.Sem.state -> Prop :=
                  | match_exprstates: forall tge f r k e m tf sl tk le dest a tmps (* cu *)
                      (* (LINK: linkorder cu prog)*)
                      (TRF: self__SimplExpr.Spec.tr_function (* cu.(prog_comp_env) *) f tf)
                      (TR: self__SimplExpr.Spec.tr_top (* cu.(prog_comp_env)*) tge e le m dest r sl a tmps)
                      (MK: self__Proof.match_cont_exp (* cu.(prog_comp_env)*) dest a k tk),
                      match_states (self__Imp.C.Sem.ExprState f r k e m)
                                   (self__Imp.Clight.Sem.State tf self__Imp.Clight.Sskip (self__Proof.Kseqlist sl tk) e le m)
                  | match_regularstates: forall f s k e m tf ts tk le (* cu*)
                      (* (LINK: linkorder cu prog) *)
                      (TRF: self__SimplExpr.Spec.tr_function (* cu.(prog_comp_env)*) f tf)
                      (TR: self__SimplExpr.Spec.tr_stmt (* cu.(prog_comp_env)*) s ts)
                      (MK: self__Proof.match_cont (* cu.(prog_comp_env)*) k tk),
                      match_states (self__Imp.C.Sem.State f s k e m)
                                   (self__Imp.Clight.Sem.State tf ts tk e le m)
                  | match_callstates: forall fd args k m tfd tk cu
                      (* (LINK: linkorder cu prog)*)
                      (TR: self__SimplExpr.Spec.tr_fundef cu fd tfd)
                      (MK: (* forall ce,*) self__Proof.match_cont (* ce*) k tk),
                      match_states (self__Imp.C.Sem.Callstate fd args k m)
                                   (self__Imp.Clight.Sem.Callstate tfd args tk m)
                  | match_returnstates: forall res k m tk
                      (MK: (* forall ce,*) self__Proof.match_cont (* ce*) k tk),
                      match_states (self__Imp.C.Sem.Returnstate res k m)
                                   (self__Imp.Clight.Sem.Returnstate res tk m)
                  | match_stuckstate: forall S,
                      match_states self__Imp.C.Sem.Stuckstate S.
              FEnd match_states.

              (* Write esize as an FRecursion *)
              FRecursion esize about C.expr motive (fun (_ : C.expr) => nat) by _rect.                  
                  Case Evar := (fun _ _ => 1%nat).                                    
                  Case Eval := (fun _ _ => 0%nat).                                                      
                  Case Ecast r1 ty := (S(esize r1)).
                  Case Eseqand r1 r2 ty := (S(esize r1)).
                  Case Eseqor r1 r2 ty := (S(esize r1)).
                  Case Econdition r1 r2 r3 ty := (S(esize r1)).
                  Case Esizeof ty' ty := 1%nat.
                  Case Ealignof ty' ty:= 1%nat.                                    
                  Case Ecomma r1 r2 ty := (S(esize r1 + esize r2)%nat).                                    
                  Case Eparen r1 tycast ty := (S(esize r1)).
              FEnd esize.

              FRecursion measure_stmt about C.statement motive (fun (_ : C.statement) => nat) by _rect.
                  Case Sskip := 0%nat.
                  Case Sdo r := ((esize r + 2)%nat).
                  Case Sifthenelse r s1 s2 := ((esize r + 2)%nat).                                                      
                  Case Slabel lbl s := 0%nat.
                  Case Sgoto lbl := 0%nat. 
                  Case Ssequence s1 s2 := 0%nat.
                  Case Swhile e s1 := 0%nat. 
                  Case Sdowhile e s1 := 0%nat.
                  Case Sfor s1 e s2 s3 := 0%nat.
                  Case Sbreak := 0%nat. 
                  Case Scontinue := 0%nat. 
                  Case Sreturn e := 0%nat.                   
              FEnd measure_stmt.
              
              FRecursion measure about C.Sem.state motive (fun (_ : C.Sem.state) => nat) by _rect.
                  Case ExprState f r k e m := ((esize r + 1)%nat).
                  Case State f s k e m := (measure_stmt s).
                  Case Callstate f vs k m := 0%nat. 
                  Case Returnstate v k m := 0%nat.
                  Case Stuckstate := 0%nat.
              FEnd measure.
              
              FInduction estep_simulation about C.Sem.estep 
                 motive (fun ge S1 t S2 (_ : C.Sem.estep ge S1 t S2) => 
                            forall prog tprog tge, match_prog prog tprog -> Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
                            forall T1 (MS : match_states S1 T1),
                      exists T2,
                       (plus Clight.Sem.step tge T1 t T2 \/
                         (star Clight.Sem.step tge T1 t T2 /\ measure S2 < measure S1)%nat)
                    /\ match_states S2 T2).
              FProof.                                  
                 (* expr *)
                 + intros. apply cheat.                 
                 (* seqand true *)                  
                 + intros. apply cheat.
                 (* seqand false *)                 
                 + intros. apply cheat.
                 (* seqor true *)
                 + intros. apply cheat.
                 (* seqor false *)
                 + apply cheat.
                 (* condition *)
                 + apply cheat.
                 (* comma *)
                 + apply cheat.
                 (* paren *)
                 + apply cheat.   
              Qed.
              FEnd estep_simulation.
              
              FInduction sstep_simulation about C.Sem.sstep 
                   motive (fun ge S1 t S2 (_ : C.Sem.sstep ge S1 t S2) => 
                            forall prog tprog tge, match_prog prog tprog -> Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
                            forall T1 (MS : match_states S1 T1),
                      exists T2,
                       (plus Clight.Sem.step tge T1 t T2 \/
                         (star Clight.Sem.step tge T1 t T2 /\ measure S2 < measure S1)%nat)
                    /\ match_states S2 T2).
              FProof.                  
                  (* do 1 *)
                  + apply cheat.
                  (* do 2 *)
                  + apply cheat.
                  (* seq *)
                  + intros. apply cheat.
                  (* skip seq *)
                  + intros. apply cheat.
                  (* continue seq *)
                  + apply cheat.
                  (* break seq *)
                  + apply cheat.
                  (* ifthenelse empty *)
                  + apply cheat.
                  (* ifthenelse non empty *)
                  + apply cheat.
                  (* while *)
                  + apply cheat.
                  (* while false *)
                  + apply cheat.
                  (* while true *)
                  + apply cheat.
                   (* skip-or-continue while *)
                  + apply cheat.
                  (* break while *)
                  + apply cheat.
                  (* dowhile *)
                  + apply cheat.
                  (* skip-or-continue dowhile *)
                  + apply cheat.
                  (* dowhile false *)
                  + apply cheat.
                  (* dowhile true *)
                  + apply cheat.
                  (* break dowhile *)
                  + apply cheat.
                  (* for start *)
                  + apply cheat.
                  (* for *)
                  + apply cheat.
                  (* for false *)
                  + apply cheat.
                  (* for true *)
                  + apply cheat.
                  (* skip-or-continue for3 *)
                  + apply cheat.
                  (* break for3 *)
                  + apply cheat.
                  (* skip for4 *)
                  + apply cheat.
                  (* return none *)
                  + apply cheat.
                  (* return some 1 *)
                  + apply cheat.
                  (* return some 2 *)
                  + intros. apply cheat.
                  (* skip return *)
                  + apply cheat.
                  (* label *)
                  + apply cheat.
                  (* goto *)
                  + apply cheat.
                  (* internal function *)
                  + apply cheat.
              Qed.
              FEnd sstep_simulation.                    
              
              FLemma simulation :
                   (forall ge S1 t S2 (_ : C.Sem.step ge S1 t S2),
                        forall prog tprog tge, match_prog prog tprog -> Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
                        forall T1 (MS : match_states S1 T1),
                      exists T2,
                       (plus Clight.Sem.step tge T1 t T2 \/
                         (star Clight.Sem.step tge T1 t T2 /\ measure S2 < measure S1)%nat)
                    /\ match_states S2 T2).
              FProofLemma.
                  intros ge S1 t S2 STEP. destruct STEP.
                  - apply self__Proof.estep_simulation; auto.
                  - apply self__Proof.sstep_simulation; auto.
                Qed.
              CloseFLemma.
              
              FLemma transl_initial_states:
                 forall S prog tprog (_ : match_prog prog tprog),                 
                 C.Sem.initial_state prog S ->
                 exists T, Clight.Sem.initial_state tprog T /\ match_states S T.
              FProofLemma.
                 apply cheat.
              Qed.
              CloseFLemma.
              
              FLemma transl_final_states:
                   forall S T r,
                   match_states S T -> C.Sem.final_state S r -> Clight.Sem.final_state T r.
              FProofLemma.
                  apply cheat.
                  (* intros. inv H0. inv H. (* specialize (MK (PTree.empty _)).*) apply cheat.*)
              Qed.
              CloseFLemma.
          FEnd Proof.
  FEnd SimplExpr.
  
  (* Clight -> Csharpminor *)
  Family Cshmgen.
      FDefinition make_intconst := fun (n: int) => Csharpminor.Econst (Csharpminor.Ointconst n).
      FDefinition make_longconst := fun (f: int64) => Csharpminor.Econst (Csharpminor.Olongconst f).
      FDefinition make_floatconst := fun (f: float) => Csharpminor.Econst (Csharpminor.Ofloatconst f).
      FDefinition make_singleconst := fun (f: float32) => Csharpminor.Econst (Csharpminor.Osingleconst f).            

      FDefinition make_ptrofsconst := fun (n: Z) =>
        if Archi.ptr64 then make_longconst (Int64.repr n) else make_intconst (Int.repr n).
      
      (* Definition sizeof (ce: composite_env) (t: type) : res Z := *)
      MetaData sizeof.
      Axiom sizeof : (* self__Imp.Clight.Sem.composite_env -> *)self__Imp.type -> res Z.
      FEnd sizeof.
      
      MetaData alignof.
      Axiom alignof : (* self__Imp.Clight.Sem.composite_env ->*) self__Imp.type -> res Z.
      FEnd alignof.

      (* Definition make_cast (from to: type) (e: expr) :=*)
      MetaData make_cast.
      Axiom make_cast : self__Imp.type -> self__Imp.type -> self__Imp.Csharpminor.expr -> res self__Imp.Csharpminor.expr.
      FEnd make_cast.
      
      FRecursion transl_expr about Clight.expr motive (fun (_ : Clight.expr) => res Csharpminor.expr) by _rect.
          Case Econst_int := (fun n type => OK(make_intconst n)). 
          Case Econst_float := (fun n type => OK(make_floatconst n)).
          Case Econst_single := (fun n type => OK(make_singleconst n)).
          Case Econst_long := (fun n type => OK(make_longconst n)).        
          Case Etempvar := (fun id ty => OK(Csharpminor.Evar id)). 
          Case Esizeof := (fun ty _ =>
                               do sz <- sizeof ty; OK(make_ptrofsconst sz)).
          Case Ealignof := (fun ty _ => 
                               do al <- alignof ty; OK(make_ptrofsconst al)).
          Case Ecast := (fun b transl_expr_b ty => 
                                do tb <- transl_expr_b;
                                make_cast (Clight.typeof b) ty tb).
      FEnd transl_expr.

       (* (nbrk : nat) -> if Clight.stmt terminates on break return Csharpminor.exit nbrk
          (ncnt : nat) -> if Clight.smt terminates on continue return Csharpminor.exit ncnt
        *)
      
      (* Definition make_boolean (e: expr) (ty: type) := *)
      MetaData make_boolean.
      Axiom make_boolean : self__Imp.Csharpminor.expr -> self__Imp.type -> self__Imp.Csharpminor.expr.
      FEnd make_boolean.            
      
      FRecursion transl_statement about Clight.stmt motive (fun (_ : Clight.stmt) => type -> nat -> nat -> res Csharpminor.stmt) by _rect.
           Case Sskip := (fun tyret nbrk ncnt => OK Csharpminor.Sskip).   
           Case Sset := (fun x b => fun tyret nbrk ncnt => 
                            do tb <- transl_expr b;
                            OK (Csharpminor.Sset x tb)).
           Case Ssequence := (fun s1 transl_s1 s2 transl_s2 =>
                              fun tyret nbrk ncnt => 
                             do ts1 <- transl_s1 tyret nbrk ncnt;
                             do ts2 <- transl_s2 tyret nbrk ncnt;
                             OK (Csharpminor.Sseq ts1 ts2)).
           Case Sifthenelse := (fun e s1 transl_s1 s2 transl_s2 => 
                                  fun tyret nbrk ncnt => 
                                do te <- transl_expr e;
                                do ts1 <- transl_s1 tyret nbrk ncnt;
                                do ts2 <- transl_s2 tyret nbrk ncnt;
                                OK (Csharpminor.Sifthenelse (make_boolean te (Clight.typeof e)) ts1 ts2)).
           Case Sloop := (fun s1 transl_s1 s2 transl_s2 => 
                          fun tyret nbrk ncnt =>
                             do ts1 <- transl_s1 tyret 1%nat 0%nat;
                             do ts2 <- transl_s2 tyret 0%nat (S ncnt);
                             OK (Csharpminor.Sblock (Csharpminor.Sloop (Csharpminor.Sseq (Csharpminor.Sblock ts1) ts2)))).
           Case Sbreak := (fun tyret nbrk ncnt => OK (Csharpminor.Sexit nbrk)).
           Case Scontinue := (fun tyret nbrk ncnt => OK (Csharpminor.Sexit ncnt)).
           Case Sreturn := (fun e => fun tyret nbrk ncnt =>
                              match e with
                              | None => OK (Csharpminor.Sreturn None)
                              | Some e => 
                                  do te <- transl_expr e;
                                  do te' <- make_cast (Clight.typeof e) tyret te;
                                  OK (Csharpminor.Sreturn (Some te'))
                              end).
           Case Slabel := (fun lbl s transl_s =>
                           fun tyret nbrk ncnt => 
                             do ts <- transl_s tyret nbrk ncnt;
                             OK (Csharpminor.Slabel lbl ts)).
           Case Sgoto := (fun lbl =>  
                            fun tyret nbrk ncnt =>  
                              OK (Csharpminor.Sgoto lbl)).
      FEnd transl_statement.     

      (* Translation of functions *)
      FDefinition transl_var := fun (v: ident * type) =>
        do sz <- sizeof (snd v); OK (fst v, sz).

      (* Definition typ_of_type (t: type) : AST.typ :=*)
      MetaData typ_of_type.
      Axiom typ_of_type : self__Imp.type -> typ.
      FEnd typ_of_type.

      (* Definition rettype_of_type (t: type) : AST.rettype :=*)
      MetaData rettype_of_type.
      Axiom rettype_of_type : self__Imp.type -> typ.
      FEnd rettype_of_type.
      
      FDefinition signature_of_function := fun (f: Clight.function) =>
        {| sig_args := map typ_of_type (map snd (Clight.fn_params f));
          sig_res  := rettype_of_type (Clight.fn_return f);
          sig_cc   := Clight.fn_callconv f |}.
      
      FDefinition transl_function : Clight.function -> res Csharpminor.function := fun f =>
        do tbody <- transl_statement (Clight.fn_body f) f.(self__Imp.Clight.fn_return) 1%nat 0%nat;
        do tvars <- mmap (transl_var) (self__Imp.Clight.fn_vars f);
        OK (self__Imp.Csharpminor.mkfunction
              (signature_of_function f)
              (map fst (Clight.fn_params f))
              tvars
              (map fst (Clight.fn_temps f))
              tbody).      

     FDefinition transl_fundef : ident -> Clight.fundef -> res Csharpminor.fundef := fun id f =>
       match f with
       | Internal g =>
           do tg <- transl_function g; OK(AST.Internal tg)
       | _ =>
           cheat (* no external*)
       end.

     (** ** Translation of programs *)

     FDefinition transl_globvar := fun (id: ident) (ty: type) => OK tt.

     FDefinition transl_program : Clight.program -> res Csharpminor.program := fun p => 
       transform_partial_program2 (transl_fundef) transl_globvar p.
     
     Family Proof.
          FInductive match_fundef :  Clight.fundef -> Csharpminor.fundef -> Prop :=
            | match_fundef_internal: forall f tf,
                transl_function f = OK tf ->
                match_fundef (Internal f) (Internal tf).

          FDefinition match_varinfo : self__Imp.type -> unit -> Prop := fun v tb => True.

          FDefinition match_prog : Clight.program -> Csharpminor.program -> Prop := fun p tp => 
            (* match_program_gen match_fundef match_varinfo p p tp.*) cheat.

     
          FInductive match_cont : type -> nat -> nat -> Clight.Sem.cont -> Csharpminor.Sem.cont -> Prop :=
              | match_Kstop: forall tyret nbrk ncnt,
                  match_cont tyret nbrk ncnt
                    Clight.Sem.Kstop
                    Csharpminor.Sem.Kstop
              | match_Kseq: forall tyret nbrk ncnt s k ts tk,
                  transl_statement s tyret nbrk ncnt = OK ts ->
                  match_cont tyret nbrk ncnt k tk ->
                  match_cont tyret nbrk ncnt
                             (Clight.Sem.Kseq s k)
                             (Csharpminor.Sem.Kseq ts tk)
              | match_Kloop1: forall tyret s1 s2 k ts1 ts2 nbrk ncnt tk,
                  transl_statement s1 tyret 1%nat 0%nat = OK ts1 ->
                  transl_statement s2 tyret 0%nat (S ncnt) = OK ts2 ->
                  match_cont tyret nbrk ncnt k tk ->
                  match_cont tyret 1%nat 0%nat
                             (Clight.Sem.Kloop1 s1 s2 k)
                             (Csharpminor.Sem.Kblock
                                (Csharpminor.Sem.Kseq ts2
                                   (Csharpminor.Sem.Kseq
                                      (Csharpminor.Sloop
                                         (Csharpminor.Sseq
                                            (Csharpminor.Sblock ts1) ts2))
                                      (Csharpminor.Sem.Kblock tk))))
              | match_Kloop2: forall tyret s1 s2 k ts1 ts2 nbrk ncnt tk,
                  transl_statement s1 tyret 1%nat 0%nat = OK ts1 ->
                  transl_statement s2 tyret 0%nat (S ncnt) = OK ts2 ->
                  match_cont tyret nbrk ncnt k tk ->
                  match_cont tyret 0%nat (S ncnt)
                             (Clight.Sem.Kloop2 s1 s2 k)
                             (Csharpminor.Sem.Kseq
                                (Csharpminor.Sloop
                                   (Csharpminor.Sseq
                                      (Csharpminor.Sblock ts1) ts2))
                                (Csharpminor.Sem.Kblock tk)).          
          
          MetaData match_states.
          Record match_env (e: self__Imp.Clight.Sem.env) (te: self__Imp.Csharpminor.Sem.env) : Prop :=
           mk_match_env {
             me_local:
               forall id b ty,
               e!id = Some (b, ty) -> te!id = Some(b, self__Imp.Clight.Sem.sizeof ty);
             me_local_inv:
               forall id b sz,
               te!id = Some (b, sz) -> exists ty, e!id = Some(b, ty)
           }.

          Inductive match_transl
            : self__Imp.Csharpminor.stmt -> self__Imp.Csharpminor.Sem.cont ->
              self__Imp.Csharpminor.stmt -> self__Imp.Csharpminor.Sem.cont -> Prop :=
          | match_transl_0: forall ts tk,
              match_transl ts tk ts tk
          | match_transl_1: forall ts tk,
              match_transl (self__Imp.Csharpminor.Sblock ts) tk ts (self__Imp.Csharpminor.Sem.Kblock tk).
          
          Inductive match_states: self__Imp.Clight.Sem.state -> self__Imp.Csharpminor.Sem.state -> Prop :=
              | match_state:
                  forall f nbrk ncnt s k e le m tf ts tk te ts' tk'
                      (* (LINK: linkorder cu prog)*)
                      (TRF: self__Cshmgen.transl_function f = OK tf)
                      (TR: self__Cshmgen.transl_statement s (self__Imp.Clight.fn_return f) nbrk ncnt = OK ts)
                      (MTR: match_transl ts tk ts' tk')
                      (MENV: match_env e te)
                      (MK: self__Proof.match_cont (self__Imp.Clight.fn_return f) nbrk ncnt k tk),
                  match_states (self__Imp.Clight.Sem.State f s k e le m)
                               (self__Imp.Csharpminor.Sem.State tf ts' tk' te le m)
              | match_callstate:
                  forall fd args k m tfd tk targs tres cconv 
                      (* (LINK: linkorder cu prog)*)
                      (TR: self__Proof.match_fundef fd tfd)
                      (MK: self__Proof.match_cont tres 0%nat 0%nat k tk)
                      (ISCC: self__Imp.Clight.Sem.is_call_cont k)
                      (TY: self__Imp.Clight.type_of_fundef fd = self__Imp.Tfunction targs tres cconv),
                  match_states (self__Imp.Clight.Sem.Callstate fd args k m)
                               (self__Imp.Csharpminor.Sem.Callstate tfd args tk m)
              | match_returnstate:
                  forall res tres k m tk 
                      (MK: self__Proof.match_cont tres 0%nat 0%nat k tk),
                      (* (WT: wt_val res tres),*)
                  match_states (self__Imp.Clight.Sem.Returnstate res k m)
                    (self__Imp.Csharpminor.Sem.Returnstate res tk m).
          FEnd match_states.
                 
          FInduction transl_step about Clight.Sem.step
            motive (fun ge S1 t S2 (_ : Clight.Sem.step ge S1 t S2) => 
             forall prog tprog tge, match_prog prog tprog -> Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
            forall T1, self__Proof.match_states S1 T1 -> 
            exists T2, plus Csharpminor.Sem.step tge T1 t T2 /\ match_states S2 T2).            
          FProof.              
              (* set *)
              + apply cheat.
              (* seq *)
              + intros. unfold self__Proof.__motiveTtransl_step. intros.
                econstructor; split.
                - apply plus_one. apply self__Imp.Csharpminor.Sem.step_seq.
                - econstructor; eauto. apply cheat.
              (* skip seq *)
              + apply cheat.
              (* continue seq *)
              + apply cheat.
              (* break seq *)
              + apply cheat.
              (* ifthenelse *)
              + apply cheat.
              (* loop *)
              + apply cheat.
              (* skip-or-continue loop *)
              + apply cheat.
              (* break loop1 *)
              + intros. apply cheat.
              (* skip loop2 *)
              + apply cheat.
              (* break loop2 *)
              + apply cheat.
              (* return none *)
              + apply cheat.
              (* return some *)
              + intros. apply cheat.
              (* skip call *)
              + apply cheat.
              (* label *)
              + apply cheat.
              (* goto *)
              + intros. apply cheat.
              (* internal function *)
              + intros. apply cheat.
          Qed.
          FEnd transl_step.
                
          FLemma transl_initial_states:
            forall S prog tprog, Clight.Sem.initial_state prog S -> transl_program prog = OK tprog ->
            exists R, Csharpminor.Sem.initial_state tprog R /\ match_states S R.
          FProofLemma.
              apply cheat. Qed.
          CloseFLemma.

          FDisplay PluginScope.
          
          FLemma transl_final_states:
            forall S R r,
            match_states S R -> Clight.Sem.final_state S r -> Csharpminor.Sem.final_state R r.
          FProofLemma.
             intros. inv H0. inv H. inv MK. constructor. Qed.
          CloseFLemma.
     FEnd Proof.
  FEnd Cshmgen.             

   (* Csharpminor -> Cminor *)
  Family Cminorgen.
      FDefinition compilenv := PTree.t Z.

      FRecursion translate_constant about
         Csharpminor.constant motive (fun (_ : Csharpminor.constant) => Cminor.constant) by _rect.
           Case Ointconst := (fun n => Cminor.Ointconst n).
           Case Ofloatconst := (fun n => Cminor.Ofloatconst n).
           Case Osingleconst := (fun n => Cminor.Osingleconst n).
           Case Olongconst := (fun n => Cminor.Olongconst n).
      FEnd translate_constant.
   
      FRecursion transl_expr about Csharpminor.expr motive (fun (_ : Csharpminor.expr) => compilenv -> res Cminor.expr) by _rect.
           Case Evar := (fun id => fun cenv => OK (Cminor.Evar id)).
           Case Econst := (fun cst => fun cenv => OK (Cminor.Econst (translate_constant cst))).
      FEnd transl_expr.

      FDefinition exit_env := list bool.

      MetaData shift_exit.
      Fixpoint shift_exit (e: self__Cminorgen.exit_env) (n: nat) {struct e} : nat :=
        match e, n with
        | nil, _ => n
        | false :: e', _ => S (shift_exit e' n)
        | true :: e', O => O
        | true :: e', S m => S (shift_exit e' m)
        end.
      FEnd shift_exit.
    
      FRecursion transl_stmt about Csharpminor.stmt motive (fun (_ : Csharpminor.stmt) => compilenv -> exit_env -> res Cminor.stmt) by _rect.
            Case Sskip := (fun cenv xenv => OK (Cminor.Sskip)).
            Case Sset := (fun id e => fun cenv xenv =>
                         do te <- transl_expr e cenv;
                         OK (Cminor.Sassign id te)).
            Case Sseq := (fun s1 transl_stmt_s1 s2 transl_stmt_s2 =>
                          fun cenv xenv =>
                            do ts1 <- transl_stmt_s1 cenv xenv;
                            do ts2 <- transl_stmt_s2 cenv xenv;
                            OK (Cminor.Sseq ts1 ts2)).
            Case Sifthenelse := (fun e s1 transl_stmt_s1 s2 transl_stmt_s2 =>
                                 fun cenv xenv =>
                                     do te <- transl_expr e cenv;
                                     do ts1 <- transl_stmt_s1 cenv xenv;
                                     do ts2 <- transl_stmt_s2 cenv xenv;
                                     OK (Cminor.Sifthenelse te ts1 ts2)).
            Case Sloop := (fun s1 transl_stmt_s1 =>
                           fun cenv xenv =>
                              do ts <- transl_stmt_s1 cenv xenv;
                              OK (Cminor.Sloop ts)).
            Case Sblock := (fun s transl_stmt_s =>
                            fun cenv xenv =>
                               do ts <- transl_stmt_s cenv (true :: xenv);
                               OK (Cminor.Sblock ts)).
            Case Sexit := (fun n => fun cenv xenv =>  OK (Cminor.Sexit (shift_exit xenv n))).
            Case Sreturn := (fun expr => fun cenv xenv =>
                               match expr with
                               | None => OK (Cminor.Sreturn None)
                               | Some expr =>
                                    do te <- transl_expr expr cenv;
                                    OK (Cminor.Sreturn (Some te))
                               end).
            Case Slabel := (fun lbl s transl_stmt_s =>
                            fun cenv xenv =>
                              do ts <- transl_stmt_s cenv xenv;
                              OK (Cminor.Slabel lbl ts)).
            Case Sgoto := (fun lbl => fun cenv xenv => OK (Cminor.Sgoto lbl)).
      FEnd transl_stmt.

      (* Stack layout *)
      FDefinition block_alignment : Z -> Z := fun sz =>
          if zlt sz 2 then 1
          else if zlt sz 4 then 2
          else if zlt sz 8 then 4 else 8.

      FDefinition assign_variable : compilenv * Z -> ident * Z -> compilenv * Z := 
          fun cenv_stacksize id_sz => 
          let (id, sz) := id_sz in
          let (cenv, stacksize) := cenv_stacksize in
          let ofs := align stacksize (block_alignment sz) in
          (PTree.set id ofs cenv, ofs + Z.max 0 sz).

      FDefinition assign_variables : compilenv * Z -> list (ident * Z) -> compilenv * Z :=
          fun cenv_stacksize vars => List.fold_left assign_variable vars cenv_stacksize.

      FDefinition build_compilenv : Csharpminor.function -> compilenv * Z :=
          fun f => assign_variables (PTree.empty Z, 0) (VarSort.sort (Csharpminor.fn_vars f)).

      (* Translate Function, Fundef, Program *)
      FDefinition transl_funbody := 
      fun (cenv: compilenv) (stacksize: Z) (f: Csharpminor.function) =>
        do tbody <- transl_stmt f.(self__Imp.Csharpminor.fn_body) cenv nil ;
        OK (Cminor.mkfunction
              (Csharpminor.fn_sig f)
              (Csharpminor.fn_params f)
              (Csharpminor.fn_temps f)
              stacksize
              tbody).

      FDefinition transl_function := fun (f: Csharpminor.function) => 
        let (cenv, stacksize) := build_compilenv f in
        if zle stacksize Ptrofs.max_unsigned
        then transl_funbody cenv stacksize f
        else Error(msg "Cminorgen: too many local variables, stack size exceeded").

      FDefinition transl_fundef : Csharpminor.fundef -> res Cminor.fundef := fun f => 
        transf_partial_fundef transl_function f.

      FDefinition transl_program : Csharpminor.program -> res Cminor.program := fun p => 
        transform_partial_program transl_fundef p.

      Family Proof.
        FDefinition match_prog : Csharpminor.program -> Cminor.program -> Prop :=
          fun p tp =>
          match_program (fun cu f tf => transl_fundef f = OK tf) eq p tp.

        MetaData is_reachable_from_env.
        Inductive is_reachable_from_env (f: meminj) (e: self__Imp.Csharpminor.Sem.env) (sp: block) (ofs: Z) : Prop :=
          | is_reachable_intro: forall id b sz delta,
              e!id = Some(b, sz) ->
              f b = Some(sp, delta) ->
              delta <= ofs < delta + sz ->
              is_reachable_from_env f e sp ofs.
        FEnd is_reachable_from_env.

        FDefinition padding_freeable : meminj -> Csharpminor.Sem.env -> mem -> block -> Z -> Prop :=
          fun f e tm sp sz =>
          forall ofs,
          0 <= ofs < sz -> Mem.perm tm sp ofs Cur Freeable \/ is_reachable_from_env f e sp ofs.
        
        FDefinition match_temps : meminj -> Csharpminor.Sem.temp_env -> Cminor.Sem.env -> Prop :=
            fun f le te =>
            forall id v, le!id = Some v -> exists v', te!(id) = Some v' /\ Val.inject f v v'.

        MetaData match_var.
        Inductive match_var (f: meminj) (sp: block): option (block * Z) -> option Z -> Prop :=
          | match_var_local: forall b sz ofs,
              Val.inject f (Vptr b Ptrofs.zero) (Vptr sp (Ptrofs.repr ofs)) ->
              match_var f sp (Some(b, sz)) (Some ofs)
          | match_var_global:
              match_var f sp None None.
        FEnd match_var.

        MetaData match_env.
        Record match_env (f: meminj) (cenv: self__Cminorgen.compilenv)
                        (e: self__Imp.Csharpminor.Sem.env) (sp: block)
                        (lo hi: block) : Prop :=
          mk_match_env {
            me_vars:
              forall id, self__Proof.match_var f sp (e!id) (cenv!id);

            me_low_high:
              Ple lo hi;

            me_bounded:
              forall id b sz, PTree.get id e = Some(b, sz) -> Ple lo b /\ Plt b hi;

            me_inv:
              forall b delta,
              f b = Some(sp, delta) ->
              exists id, exists sz, PTree.get id e = Some(b, sz);
              
            me_incr:
              forall b tb delta,
              f b = Some(tb, delta) -> Plt b lo -> Plt tb sp
        }.
        FEnd match_env.

        FDefinition match_bounds : Csharpminor.Sem.env -> mem -> Prop := 
          fun e m => forall id b sz ofs p, 
             PTree.get id e = Some(b, sz) -> Mem.perm m b ofs Max p -> 0 <= ofs < sz.  

        MetaData frame.
        Inductive frame : Type :=
          Frame(cenv: self__Cminorgen.compilenv)
              (tf: self__Imp.Cminor.function)
              (e: self__Imp.Csharpminor.Sem.env)
              (le: self__Imp.Csharpminor.Sem.temp_env)
              (te: self__Imp.Cminor.Sem.env)
              (sp: block)
              (lo hi: block).
        FEnd frame.

        FDefinition callstack : Type := list frame.

        MetaData match_globalenvs.
        Inductive match_globalenvs (ge: self__Imp.Csharpminor.Sem.genv) (f: meminj) (bound: block): Prop :=
        | mk_match_globalenvs
            (DOMAIN: forall b, Plt b bound -> f b = Some(b, 0))
            (IMAGE: forall b1 b2 delta, f b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)
            (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
            (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
            (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound).
        FEnd match_globalenvs.
        
        MetaData match_callstack.
        Inductive match_callstack (ge: self__Imp.Csharpminor.Sem.genv) (f: meminj) (m: mem) (tm: mem):
                          self__Proof.callstack -> block -> block -> Prop :=
          | mcs_nil:
              forall hi bound tbound,
              self__Proof.match_globalenvs ge f hi ->
              Ple hi bound -> Ple hi tbound ->
              match_callstack ge f m tm nil bound tbound
          | mcs_cons:
              forall cenv tf e le te sp lo hi cs bound tbound
                (BOUND: Ple hi bound)
                (TBOUND: Plt sp tbound)
                (MTMP: self__Proof.match_temps f le te)
                (MENV: self__Proof.match_env f cenv e sp lo hi)
                (BOUND: self__Proof.match_bounds e m)
                (PERM: self__Proof.padding_freeable f e tm sp tf.(self__Imp.Cminor.fn_stackspace))
                (MCS: match_callstack ge f m tm cs lo sp),
              match_callstack ge f m tm (self__Proof.Frame cenv tf e le te sp lo hi :: cs) bound tbound.
        FEnd match_callstack.

        FInductive match_cont: Csharpminor.Sem.cont -> Cminor.Sem.cont -> compilenv -> exit_env -> callstack -> Prop :=
          | match_Kstop: forall cenv xenv,
              match_cont Csharpminor.Sem.Kstop Cminor.Sem.Kstop cenv xenv nil
          | match_Kseq: forall s k ts tk cenv xenv cs,
              transl_stmt s cenv xenv = OK ts ->
              match_cont k tk cenv xenv cs ->
              match_cont (Csharpminor.Sem.Kseq s k) (Cminor.Sem.Kseq ts tk) cenv xenv cs
          | match_Kseq2: forall s1 s2 k ts1 tk cenv xenv cs,
              transl_stmt s1 cenv xenv = OK ts1 ->
              match_cont (Csharpminor.Sem.Kseq s2 k) tk cenv xenv cs ->
              match_cont (Csharpminor.Sem.Kseq (Csharpminor.Sseq s1 s2) k)
                        (Cminor.Sem.Kseq ts1 tk) cenv xenv cs
          | match_Kblock: forall k tk cenv xenv cs,
              match_cont k tk cenv xenv cs ->
              match_cont (Csharpminor.Sem.Kblock k) (Cminor.Sem.Kblock tk) cenv (true :: xenv) cs
          | match_Kblock2: forall k tk cenv xenv cs,
              match_cont k tk cenv xenv cs ->
              match_cont k (Cminor.Sem.Kblock tk) cenv (false :: xenv) cs.

          MetaData match_states.
          Inductive match_states (ge: self__Imp.Csharpminor.Sem.genv) : self__Imp.Csharpminor.Sem.state -> self__Imp.Cminor.Sem.state -> Prop :=
              | match_state:
                  forall fn s k e le m tfn ts tk sp te tm cenv xenv f lo hi cs sz
                  (TRF: self__Cminorgen.transl_funbody cenv sz fn = OK tfn)
                  (TR: self__Cminorgen.transl_stmt s cenv xenv = OK ts)
                  (MINJ: Mem.inject f m tm)
                  (MCS: self__Proof.match_callstack ge f m tm
                          (self__Proof.Frame cenv tfn e le te sp lo hi :: cs)
                          (Mem.nextblock m) (Mem.nextblock tm))
                  (MK: self__Proof.match_cont k tk cenv xenv cs),
                  match_states ge (self__Imp.Csharpminor.Sem.State fn s k e le m)
                              (self__Imp.Cminor.Sem.State tfn ts tk (Vptr sp Ptrofs.zero) te tm)
              | match_state_seq:
                  forall fn s1 s2 k e le m tfn ts1 tk sp te tm cenv xenv f lo hi cs sz
                  (TRF: self__Cminorgen.transl_funbody cenv sz fn = OK tfn)
                  (TR: self__Cminorgen.transl_stmt s1 cenv xenv = OK ts1)
                  (MINJ: Mem.inject f m tm)
                  (MCS: self__Proof.match_callstack ge f m tm
                          (self__Proof.Frame cenv tfn e le te sp lo hi :: cs)
                          (Mem.nextblock m) (Mem.nextblock tm))
                  (MK: self__Proof.match_cont (self__Imp.Csharpminor.Sem.Kseq s2 k) tk cenv xenv cs),
                  match_states ge (self__Imp.Csharpminor.Sem.State fn (self__Imp.Csharpminor.Sseq s1 s2) k e le m)
                              (self__Imp.Cminor.Sem.State tfn ts1 tk (Vptr sp Ptrofs.zero) te tm)
              | match_callstate:
                  forall fd args k m tfd targs tk tm f cs cenv
                  (TR: self__Cminorgen.transl_fundef fd = OK tfd)
                  (MINJ: Mem.inject f m tm)
                  (MCS: self__Proof.match_callstack ge f m tm cs (Mem.nextblock m) (Mem.nextblock tm))
                  (MK: self__Proof.match_cont k tk cenv nil cs)
                  (ISCC: self__Imp.Csharpminor.Sem.is_call_cont k)
                  (ARGSINJ: Val.inject_list f args targs),
                  match_states ge (self__Imp.Csharpminor.Sem.Callstate fd args k m)
                              (self__Imp.Cminor.Sem.Callstate tfd targs tk tm)
              | match_returnstate:
                  forall v k m tv tk tm f cs cenv
                  (MINJ: Mem.inject f m tm)
                  (MCS: self__Proof.match_callstack ge f m tm cs (Mem.nextblock m) (Mem.nextblock tm))
                  (MK: self__Proof.match_cont k tk cenv nil cs)
                  (RESINJ: Val.inject f v tv),
                  match_states ge (self__Imp.Csharpminor.Sem.Returnstate v k m)
                              (self__Imp.Cminor.Sem.Returnstate tv tk tm).
          FEnd match_states.
        (*
          Variable prog: Csharpminor.program.
          Variable tprog: program.
          Hypothesis TRANSL: match_prog prog tprog.
          Let ge : Csharpminor.genv := Genv.globalenv prog.
          Let tge: genv := Genv.globalenv tprog. 
        *)

        FRecursion seq_left_depth about Csharpminor.stmt motive (fun (_ : Csharpminor.stmt) => nat) by _rect.
              Case Sskip := O.
              Case Sset := (fun _ _ => O).
              Case Sseq := (fun s1 seq_left_depth_s1 s2 _ => S (seq_left_depth_s1)).
              Case Sifthenelse := (fun _ s1 _ s2 _ => O).
              Case Sloop := (fun s _ => O).
              Case Sblock := (fun s _ => O).
              Case Sexit := (fun _ => O).
              Case Sreturn := (fun e => O).
              Case Slabel := (fun _ s _ => O).
              Case Sgoto := (fun _ => O).
        FEnd seq_left_depth.

        FRecursion measure about Csharpminor.Sem.state motive (fun (_ : Csharpminor.Sem.state) => nat) by _rect.
              Case State := (fun fn s k e le m => seq_left_depth s).
              Case Callstate := (fun f args k m => O).
              Case Returnstate := (fun res k m => O).
        FEnd measure.

        FInduction transl_step_correct about Csharpminor.Sem.step motive
          (fun ge S1 t S2 (_ : Csharpminor.Sem.step ge S1 t S2) => 
             forall prog tprog tge, match_prog prog tprog -> Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->               
          forall T1, match_states ge S1 T1 -> 
          (exists T2, plus Cminor.Sem.step tge T1 t T2 /\ match_states ge S2 T2) 
          \/ (measure S2 < measure S1 /\ t = E0 /\ match_states ge S2 T1)%nat).
        FProof.
          finduction.
          (* skip seq *)
          + intros. apply cheat.
          (* skip block *)
          + intros. apply cheat.
          (* skip call *)
          + intros. apply cheat.
          (* set *)
          + intros. apply cheat.
          (* seq *)
          + intros. apply cheat.
          (* ifthenelse *)
          + intros. apply cheat.
          (* loop *)
          + apply cheat.
          (* block *)
          + apply cheat.
          (* return none *)
          + apply cheat.
          (* return some *)
          + apply cheat.
          (* label *)
          + apply cheat.
          (* goto *)
          + apply cheat.
          (* internal function *)
          + intros. apply cheat.
        Qed.
        FEnd transl_step_correct.
        
        FLemma transl_initial_states:
          forall S prog tprog ge, Csharpminor.Sem.initial_state prog S ->
          transl_program prog = OK tprog ->
          exists R, Cminor.Sem.initial_state tprog R /\ match_states ge S R.
            FProofLemma.
              apply cheat.
            Qed.
        CloseFLemma.
        
        FLemma transl_final_states:
          forall S R r ge,
          match_states ge S R -> Csharpminor.Sem.final_state S r -> Cminor.Sem.final_state R r.
            FProofLemma.
              intros. inv H0. inv H. inv MK. inv RESINJ. constructor. Qed.            
        CloseFLemma.
      FEnd Proof.
  FEnd Cminorgen.     

   (* Cminor -> CminorSel *)
   Family Selection.
       FDefinition longconst : int64 -> expr := fun n =>
          if Archi.splitlong then SplitLong.longconst n else CminorSel.Eop (Asm.Olongconst n) CminorSel.Enil.

       FRecurcion sel_constant about Cminor.constant motive (fun (_ : Cminor.constant) => CminorSel.expr).
           Case Ointconst := (fun n => CminorSel.Eop (Asm.Ointconst n) CminorSel.Enil).
           Case Ofloatconst := (fun n => CminorSel.Eop (Asm.Ofloatconst f) CminorSel.Enil).
           Case Osingleconst := (fun n =>  CminorSel.Eop (Asm.Osingleconst f) CminorSel.Enil).
           Case Olongconst := (fun n => longconst n).
       FEnd sel_constant.

       FRecursion sel_expr about Cminor.expr motive (fun (_ : Cminor.expr) => CminorSel.expr).          
           Case Evar := (fun id => CminorSel.Evar id).
           Case Econst := (fun cst => sel_constant cst).           
       FEnd sel_expr.
       
       FRecursion select_condition about Asm.operation motive (fun (_ : Asm.operation) => CminorSel.exprlist -> condition) by _rect.
           Case Ocmp := (fun c args => CminorSel.CEcond c args).
       FEnd select_condition.
       
       FRecursion condexpr_of_expr about CminorSel.expr motive (fun (_ : Cminor.expr) => CminorSel.condexpr) by _rect.
           Case Eop op args := select_condition op args.
           Case Econdition a b c := (CminorSel.CEcondition a (condexpr_of_expr b) (condexpr_of_expr c))
           Case Elet a b := (CElet a (condexpr_of_expr b)).
           Case Eletvar n := (CminorSel.CEcond (Asm.Ccompuimm Cne Int.zero) (CminorSel.Econs e Cminor.Enil)).
           Case Evar i := (CminorSel.CEcond (Asm.Ccompuimm Cne Int.zero) (CminorSel.Econs e Cminor.Enil)).
       FEnd condexpr_of_expr.

       Function condexpr_of_expr (e: expr) : condexpr :=
           match e with
           | Eop (Ocmp c) el => CEcond c el
           | Econdition a b c => CEcondition a (condexpr_of_expr b) (condexpr_of_expr c)
           | Elet a b => CElet a (condexpr_of_expr b)
           | _ => CEcond (Ccompuimm Cne Int.zero) (e ::: Enil)
           end.
       
       FRecursion sel_stmt about Cminor.stmt 
                            motive (fun (_ : Cminor.stmt) => res CminorSel.stmt) by _rect.
          Case Sskip := (OK CminorSel.Sskip).
          Case Sassign id e := (OK (CminorSel.Sassign id (sel_expr e))).
          Case Sseq s1 s2 := (
                 do s1' <- sel_stmt s1 ; 
                 do s2' <- sel_stmt s2 ;
                 OK (CminorSel.Sseq s1' s2')).
          Case Sifthenelse e ifso ifnot := (
               (* For simplicity, don't use the
                  "if conversion heuristics" present in CompCert *)                      
                 do ifso' <- sel_stmt ifso ;
                 do ifnot' <- sel_stmt ifnot ;
                 OK (Sifthenelse (condexpr_of_expr (sel_expr e)) ifso' ifnot')).
          Case Sloop body := (do body' <- sel_stmt body; OK (CminorSel.Sloop body')).
          Case Sblock s := (do body' <- sel_stmt body; OK (CminorSel.Sblock body')). 
          Case Sexit := (OK (CminorSel.Sexit n)).
          Case Sreturn e := (match e with 
                             | None => OK (CminorSel.Sreturn None) 
                             | Some e => OK (CminorSel.Sreturn (Some (sel_expr e)))).
          Case Slabel lbl body := (do body' <- sel_stmt body; OK (CminorSel.Slabel lbl body')) 
          Case Sgoto := (OK (CminorSel.Sgoto lbl)).
        FEnd sel_stmt.

       FDefinition sel_function : Cminor.function -> res function := fun f =>             
             do body' <- sel_stmt f.(self__Imp.Cminor.fn_body);
             OK (self__Imp.CminorSel.mkfunction
                   f.(self__Imp.Cminor.fn_sig)
                   f.(self__Imp.Cminor.fn_params)
                   f.(self__Imp.Cminor.fn_vars)
                   f.(self__Imp.Cminor.fn_stackspace)
                   body').

       FDefinition sel_fundef : Cminor.fundef -> res fundef := fun f =>
         transf_partial_fundef (sel_function) f.

       FDefinition sel_program : Cminor.program -> res program := fun p =>         
        transform_partial_program (sel_fundef) p.       
       
       Family Proof. 
           Inductive match_cont: Cminor.program -> helper_functions -> known_idents -> typenv -> Cminor.cont -> CminorSel.cont -> Prop :=
               | match_cont_seq: forall cunit hf ki env s s' k k',
                   sel_stmt (prog_defmap cunit) ki env s = OK s' ->
                   match_cont cunit hf ki env k k' ->
                   match_cont cunit hf ki env (Cminor.Kseq s k) (Kseq s' k')
               | match_cont_block: forall cunit hf ki env k k',
                   match_cont cunit hf ki env k k' ->
                   match_cont cunit hf ki env (Cminor.Kblock k) (Kblock k')
               | match_cont_other: forall cunit hf ki env k k',
                   match_call_cont k k' ->
                   match_cont cunit hf ki env k k'
           with match_call_cont: Cminor.cont -> CminorSel.cont -> Prop :=
             | match_cont_stop:
                 match_call_cont Cminor.Kstop Kstop
             | match_cont_call: forall cunit hf env id f sp e k f' e' k',
                 linkorder cunit prog ->
                 helper_functions_declared cunit hf ->
                 sel_function (prog_defmap cunit) hf f = OK f' ->
                 type_function f = OK env ->
                 match_cont cunit hf (known_id f) env k k' ->
                 env_lessdef e e' ->
                 match_call_cont (Cminor.Kcall id f sp e k) (Kcall id f' sp e' k').

       Inductive match_states: Cminor.state -> CminorSel.state -> Prop :=
         | match_state: forall cunit hf f f' s k s' k' sp e m e' m' env
               (LINK: linkorder cunit prog)
               (HF: helper_functions_declared cunit hf)
               (TF: sel_function (prog_defmap cunit) hf f = OK f')
               (TYF: type_function f = OK env)
               (TS: sel_stmt (prog_defmap cunit) (known_id f) env s = OK s')
               (MC: match_cont cunit hf (known_id f) env k k')
               (LD: env_lessdef e e')
               (ME: Mem.extends m m'),
             match_states
               (Cminor.State f s k sp e m)
               (State f' s' k' sp e' m')
         | match_callstate: forall cunit f f' args args' k k' m m'
               (LINK: linkorder cunit prog)
               (TF: match_fundef cunit f f')
               (MC: match_call_cont k k')
               (LD: Val.lessdef_list args args')
               (ME: Mem.extends m m'),
             match_states
               (Cminor.Callstate f args k m)
               (Callstate f' args' k' m')
         | match_returnstate: forall v v' k k' m m'
               (MC: match_call_cont k k')
               (LD: Val.lessdef v v')
               (ME: Mem.extends m m'),
             match_states
               (Cminor.Returnstate v k m)
               (Returnstate v' k' m')
         | match_builtin_1: forall cunit hf ef args optid f sp e k m al f' e' k' m' env
               (LINK: linkorder cunit prog)
               (HF: helper_functions_declared cunit hf)
               (TF: sel_function (prog_defmap cunit) hf f = OK f')
               (TYF: type_function f = OK env)
               (MC: match_cont cunit hf (known_id f) env k k')
               (EA: Cminor.eval_exprlist ge sp e m al args)
               (LDE: env_lessdef e e')
               (ME: Mem.extends m m'),
             match_states
               (Cminor.Callstate (External ef) args (Cminor.Kcall optid f sp e k) m)
               (State f' (sel_builtin optid ef al) k' sp e' m')
         | match_builtin_2: forall cunit hf v v' optid f sp e k m f' e' m' k' env
               (LINK: linkorder cunit prog)
               (HF: helper_functions_declared cunit hf)
               (TF: sel_function (prog_defmap cunit) hf f = OK f')
               (TYF: type_function f = OK env)
               (MC: match_cont cunit hf (known_id f) env k k')
               (LDV: Val.lessdef v v')
               (LDE: env_lessdef (set_optvar optid v e) e')
               (ME: Mem.extends m m'),
             match_states
               (Cminor.Returnstate v (Cminor.Kcall optid f sp e k) m)
               (State f' Sskip k' sp e' m').

           Definition measure (s: Cminor.state) : nat :=
              match s with
              | Cminor.Callstate _ _ _ _ => 0%nat
              | Cminor.State _ _ _ _ _ _ => 1%nat
              | Cminor.Returnstate _ _ _ => 2%nat
              end.

           Lemma sel_step_correct:
             forall S1 t S2, Cminor.step ge S1 t S2 ->
             forall T1, match_states S1 T1 -> wt_state S1 ->
             (exists T2, plus step tge T1 t T2 /\ match_states S2 T2)
             \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 T1)%nat
             \/ (exists T2 n, step tge T1 t T2 /\ eventually n S2 (fun S3 => match_states S3 T2)).
           Proof.
           
           Lemma sel_initial_states:
             forall S, Cminor.initial_state prog S ->
             exists R, initial_state tprog R /\ match_states S R.
           Proof.
           
           Lemma sel_final_states:
             forall S R r,
             match_states S R -> Cminor.final_state S r -> final_state R r.
           Proof.
       FEnd Proof.

  FEnd Selection.

   
   Family RTL.
       Definition node := positive.
      
       FInductive instruction: Type :=
          | Inop: node -> instruction
          | Iop: Asm.operation -> list reg -> reg -> node -> instruction          
          | Icond: condition -> list reg -> node -> node -> instruction
          | Ireturn: option reg -> instruction.

      FDefinition code: Type := PTree.t instruction.

      Record function: Type := mkfunction {
        fn_sig: signature;
        fn_params: list reg;
        fn_stacksize: Z;
        fn_code: code;
        fn_entrypoint: node
      }.
       
      Family Sem. 
          Definition genv := Genv.t fundef unit.
          Definition regset := Regmap.t val.
           
          FInductive stackframe : Type :=
             | Stackframe : reg -> function -> val -> node -> regset -> stackframe.
           
          FInductive state : Type :=
             | State : list stackframe -> function -> val -> noce -> regset -> mem -> state
             | Callstate : list stackframe -> fundef -> list val -> mem -> state
             | Returnstate : list stackframe -> val -> mem -> state.
           
          FInductive step: genv -> state -> trace -> state -> Prop :=
               | exec_Inop:
                   forall s f sp pc rs m pc',
                   (fn_code f)!pc = Some(Inop pc') ->
                   step (State s f sp pc rs m)
                     E0 (State s f sp pc' rs m)
               | exec_Iop:
                   forall s f sp pc rs m op args res pc' v,
                   (fn_code f)!pc = Some(Iop op args res pc') ->
                   Asm.eval_operation ge sp op rs##args m = Some v ->
                   step (State s f sp pc rs m)
                     E0 (State s f sp pc' (rs#res <- v) m)
               | exec_Icond:
                   forall s f sp pc rs m cond args ifso ifnot b pc',
                   (fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
                   Asm.eval_condition cond rs##args m = Some b ->
                   pc' = (if b then ifso else ifnot) ->
                   step (State s f sp pc rs m)
                     E0 (State s f sp pc' rs m)
               | exec_Ireturn:
                   forall s f stk pc rs m or m',
                   (fn_code f)!pc = Some(Ireturn or) ->
                   Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
                   step (State s f (Vptr stk Ptrofs.zero) pc rs m)
                     E0 (Returnstate s (regmap_optget or Vundef rs) m')  
               | exec_return:
                   forall res f sp pc rs s vres m,
                   step (Returnstate (Stackframe res f sp pc rs :: s) vres m)
                     E0 (State s f sp pc (rs#res <- vres) m).

               Inductive initial_state (p: program): state -> Prop :=
                  | initial_state_intro: forall b f m0,
                      let ge := Genv.globalenv p in
                      Genv.init_mem p = Some m0 ->
                      Genv.find_symbol ge p.(prog_main) = Some b ->
                      Genv.find_funct_ptr ge b = Some f ->
                      funsig f = signature_main ->
                      initial_state p (Callstate nil f nil m0).

                 Inductive final_state: state -> int -> Prop :=
                    | final_state_intro: forall r m,
                        final_state (Returnstate nil (Vint r) m) r.
      FEnd Sem.
  FEnd RTL.

  (* CminorSel -> RTL *)
  Family RTLgen.
        FRecursion transl_expr about CminorSel.expr motive (fun (_ : CminorSel.expr) => mapping -> reg -> node -> node).
            Case Evar := (fun id => fun map rd nd => 
                             do r <- find_var map v; 
                                add_move r rd nd).
            Case Eop := (fun op al => fun map rd nd => 
                            do rl <- alloc_regs map al;
                            do no <- add_instr (Iop op rl rd nd);
                            transl_exprlist map al rl no).
            Case Econdition := (fun a b transl_b c transl_c => fun map rd nd => 
                                     do nfalse <- transl_expr map c rd nd;
                                    do ntrue <- transl_expr map b rd nd;
                                      transl_condexpr map a ntrue nfalse).
            Case Elet := (fun b c => fun map rd nd => 
                                       do r <- new_reg;
                                      do nc <- transl_expr (add_letvar map r) c rd nd;
                                        transl_expr map b r nc).
            Case Eletvar := (fun n => fun map rd nd => 
                                      do r <- find_letvar map n; add_move r rd nd).            
        FEnd transl_expr.        
        (* with transl_exprlist about CminorSel.exprlist motive (fun (_ : CminorSel.exprlist) => mapping -> list reg -> node -> node).
              Case Enil := (fun map al rl nd => match rl with nil => ret nd | _ => error (Errors.msg "RTLgen.transl_exprlist") end).
              Case Econs := (fun fun b bs transl_bs => map al rl nd => 
                                  match rl with 
                                  | r :: rs =>  
                                      do no <- transl_exprlist map bs rs nd; 
                                      transl_expr map b r no 
                                | _ => error (Errors.msg "RTLgen.transl_exprlist") end).
         *)
        (* with transl_condexpr about CminorSel.condexpr (fun (_ : CminorSel.condexpr) => mapping  -> node -> node -> node)
              Case CEcond := (fun c al => fun map ntrue nfalse => 
                              do rl <- alloc_regs map al;
                              do nt <- add_instr (Icond c rl ntrue nfalse);
                                transl_exprlist map al rl nt).
              Case CEcondition := (fun a b transl_b c transl_c => fun map ntrue nfalse => 
                                     do nc <- transl_c map ntrue nfalse;
                                    do nb <- transl_b map ntrue nfalse;
                                      transl_condexpr map a nb nc).
              Case CElet := (fun b c transl_c => fun map ntrue nfalse => 
                             do r <- new_reg;
                            do nc <- transl_condexpr (add_letvar map r) c ntrue nfalse;
                                transl_expr map b r nc).              
        FEnd transl_expr. *)      

        Definition transl_exit (nexits: list node) (n: nat) : mon node :=
          match nth_error nexits n with
          | None => error (Errors.msg "RTLgen: wrong exit")
          | Some ne => ret ne
          end.

        Definition labelmap : Type := PTree.t node.
        
        FRecursion transl_stmt about CminorSel.stmt
          motive (fun (_ : CminorSel.stmt) => 
                    mapping -> node -> list node -> labelmap -> node -> option reg -> node).
             Case Sskip := (fun map nd nexits ngoto nret rret => ret nd).
             Case Sassign := (fun id e => fun map nd nexits ngoto nret rret => 
                                  do r <- find_var map v;
                                  transl_expr map b r nd). 
             Case Sseq := (fun s1 transl_s1 s2 transl_s2 => fun map nd nexits ngoto nret rret =>  
                         do ns <- transl_s2 map nd nexits ngoto nret rret;
                         transl_s1 map ns nexits ngoto nret rret).
             Case Sifthenelse := (fun c strue transl_strue sfalse transl_sfalse =>
                                     fun map nd nexits ngoto nret rret => 
                            (* Don't use "more likely" heuristic *)
                            do ntrue <- transl_strue map nd nexits ngoto nret rret;
                            do nfalse <- transl_sfalse map nd nexits ngoto nret rret;
                            transl_condexpr map c ntrue nfalse).
             Case Sloop := (fun s tranl_s => fun map nd nexits ngoto nret rret => 
                                do n1 <- reserve_instr;
                                do n2 <- transl_s map n1 nexits ngoto nret rret;
                                do xx <- update_instr n1 (Inop n2);
                                add_instr (Inop n2)).
             Case Sblock := (fun s tranl_s => fun map nd nexits ngoto nret rret => 
                                   transl_s map nd (nd :: nexits) ngoto nret rret).
             Case Sexit := (fun n => fun map nd nexits ngoto nret rret =>  transl_exit nexits n).
             Case Sreturn := (fun opt_a => fun map nd nexits ngoto nret rret => 
                                match opt_a, rret with
                                | None, _ => ret nret
                                | Some a, Some r => transl_expr map a r nret
                                | _, _ => error (Errors.msg "RTLgen: type mismatch on return")
                                end).
             Case Slabel := (fun lbl s transl_s => fun map nd nexits ngoto nret rret => 
                               do ns <- transl_stmt map s' nd nexits ngoto nret rret;
                               (* Some eror handling stuff about labels *)
                               ret ns).
             Case Sgoto := (fun lbl => fun map nd nexits ngoto nret rret => 
                              match ngoto!lbl with
                              | None => error (Errors.MSG "Undefined defined label " ::
                                              Errors.CTX lbl :: nil)
                              | Some n => ret n
                              end).
        FEnd transl_stmt.

        (* Non executable relation spec for transl_stmt, defined via an Inductive type *)
        Family Spec.
             (* tr_move c ns rs nd rd holds if the graph c, between nodes ns and nd, contains 
                instructions that move the value of register rs to register rd. *)
             Inductive tr_move (c: code):
                    node -> reg -> node -> reg -> Prop :=
                | tr_move_0: forall n r,
                    tr_move c n r n r
                | tr_move_1: forall ns rs nd rd,
                    c!ns = Some (RTL.Iop Asm.Omove (rs :: nil) rd nd) ->
                    tr_move c ns rs nd rd.

              Inductive reg_map_ok: mapping -> reg -> option ident -> Prop :=
                | reg_map_ok_novar: forall map rd,
                    ~reg_in_map map rd ->
                    reg_map_ok map rd None
                | reg_map_ok_somevar: forall map rd id,
                    map.(map_vars)!id = Some rd ->
                    reg_map_ok map rd (Some id).
 
                 
              FInductive tr_expr (c: code):
                      mapping -> list reg -> expr -> node -> node -> reg -> option ident -> Prop :=
                  | tr_Evar: forall map pr id ns nd r rd dst,
                      map.(map_vars)!id = Some r ->
                      ((rd = r /\ dst = None) \/ (reg_map_ok map rd dst /\ ~In rd pr)) ->
                      tr_move c ns r nd rd ->
                      tr_expr c map pr (Evar id) ns nd rd dst
                  | tr_Eop: forall map pr op al ns nd rd n1 rl dst,
                      tr_exprlist c map pr al ns n1 rl ->
                      c!n1 = Some (Iop op rl rd nd) ->
                      reg_map_ok map rd dst -> ~In rd pr ->
                      tr_expr c map pr (Eop op al) ns nd rd dst
                  | tr_Eload: forall map pr chunk addr al ns nd rd n1 rl dst,
                      tr_exprlist c map pr al ns n1 rl ->
                      c!n1 = Some (Iload chunk addr rl rd nd) ->
                      reg_map_ok map rd dst -> ~In rd pr ->
                      tr_expr c map pr (Eload chunk addr al) ns nd rd dst
                  | tr_Econdition: forall map pr a ifso ifnot ns nd rd ntrue nfalse dst,
                      tr_condition c map pr a ns ntrue nfalse ->
                      tr_expr c map pr ifso ntrue nd rd dst ->
                      tr_expr c map pr ifnot nfalse nd rd dst ->
                      tr_expr c map pr (Econdition a ifso ifnot) ns nd rd dst
                  | tr_Elet: forall map pr b1 b2 ns nd rd n1 r dst,
                      ~reg_in_map map r ->
                      tr_expr c map pr b1 ns n1 r None ->
                      tr_expr c (add_letvar map r) pr b2 n1 nd rd dst ->
                      tr_expr c map pr (Elet b1 b2) ns nd rd dst
                  | tr_Eletvar: forall map pr n ns nd rd r dst,
                      List.nth_error map.(map_letvars) n = Some r ->
                      ((rd = r /\ dst = None) \/ (reg_map_ok map rd dst /\ ~In rd pr)) ->
                      tr_move c ns r nd rd ->
                      tr_expr c map pr (Eletvar n) ns nd rd dst
                  with tr_condition (c: code):
                        mapping -> list reg -> condexpr -> node -> node -> node -> Prop :=
                    | tr_CEcond: forall map pr cond bl ns ntrue nfalse n1 rl,
                        tr_exprlist c map pr bl ns n1 rl ->
                        c!n1 = Some (Icond cond rl ntrue nfalse) ->
                        tr_condition c map pr (CEcond cond bl) ns ntrue nfalse
                    | tr_CEcondition: forall map pr a1 a2 a3 ns ntrue nfalse n2 n3,
                        tr_condition c map pr a1 ns n2 n3 ->
                        tr_condition c map pr a2 n2 ntrue nfalse ->
                        tr_condition c map pr a3 n3 ntrue nfalse ->
                        tr_condition c map pr (CEcondition a1 a2 a3) ns ntrue nfalse
                    | tr_CElet: forall map pr a b ns ntrue nfalse r n1,
                        ~reg_in_map map r ->
                        tr_expr c map pr a ns n1 r None ->
                        tr_condition c (add_letvar map r) pr b n1 ntrue nfalse ->
                        tr_condition c map pr (CElet a b) ns ntrue nfalse
                  with tr_exprlist (c: code):
                          mapping -> list reg -> exprlist -> node -> node -> list reg -> Prop :=
                      | tr_Enil: forall map pr n,
                          tr_exprlist c map pr Enil n n nil
                      | tr_Econs: forall map pr a1 al ns nd r1 rl n1,
                          tr_expr c map pr a1 ns n1 r1 None ->
                          tr_exprlist c map (r1 :: pr) al n1 nd rl ->
                          tr_exprlist c map pr (Econs a1 al) ns nd (r1 :: rl).
    
              FInductive tr_stmt (c: code) (map: mapping):
                    CminorSel.stmt -> node -> node -> list node -> labelmap -> node -> option reg -> Prop :=
                  | tr_Sskip: forall ns nexits ngoto nret rret,
                    tr_stmt c map Sskip ns ns nexits ngoto nret rret
                  | tr_Sassign: forall id a ns nd nexits ngoto nret rret r,
                    map.(map_vars)!id = Some r ->
                    tr_expr c map nil a ns nd r (Some id) ->
                    tr_stmt c map (Sassign id a) ns nd nexits ngoto nret rret
                  | tr_Sseq: forall s1 s2 ns nd nexits ngoto nret rret n,
                    tr_stmt c map s2 n nd nexits ngoto nret rret ->
                    tr_stmt c map s1 ns n nexits ngoto nret rret ->
                    tr_stmt c map (Sseq s1 s2) ns nd nexits ngoto nret rret
                  | tr_Sifthenelse: forall a strue sfalse ns nd nexits ngoto nret rret ntrue nfalse,
                    tr_stmt c map strue ntrue nd nexits ngoto nret rret ->
                    tr_stmt c map sfalse nfalse nd nexits ngoto nret rret ->
                    tr_condition c map nil a ns ntrue nfalse ->
                    tr_stmt c map (Sifthenelse a strue sfalse) ns nd nexits ngoto nret rret
                  | tr_Sloop: forall sbody ns nd nexits ngoto nret rret nloop nend,
                    tr_stmt c map sbody nloop nend nexits ngoto nret rret ->
                    c!ns = Some(Inop nloop) ->
                    c!nend = Some(Inop nloop) ->
                    tr_stmt c map (Sloop sbody) ns nd nexits ngoto nret rret
                  | tr_Sblock: forall sbody ns nd nexits ngoto nret rret,
                    tr_stmt c map sbody ns nd (nd :: nexits) ngoto nret rret ->
                    tr_stmt c map (Sblock sbody) ns nd nexits ngoto nret rret
                  | tr_Sexit: forall n ns nd nexits ngoto nret rret,
                    nth_error nexits n = Some ns ->
                    tr_stmt c map (Sexit n) ns nd nexits ngoto nret rret
                  | tr_Sreturn_none: forall nret nd nexits ngoto rret,
                    tr_stmt c map (Sreturn None) nret nd nexits ngoto nret rret
                  | tr_Sreturn_some: forall a ns nd nexits ngoto nret rret,
                    tr_expr c map nil a ns nret rret None ->
                    tr_stmt c map (Sreturn (Some a)) ns nd nexits ngoto nret (Some rret)
                  | tr_Slabel: forall lbl s ns nd nexits ngoto nret rret n,
                    ngoto!lbl = Some n ->
                    c!n = Some (Inop ns) ->
                    tr_stmt c map s ns nd nexits ngoto nret rret ->
                    tr_stmt c map (Slabel lbl s) ns nd nexits ngoto nret rret
                  | tr_Sgoto: forall lbl ns nd nexits ngoto nret rret,
                    ngoto!lbl = Some ns ->
                    tr_stmt c map (Sgoto lbl) ns nd nexits ngoto nret rret.   

                Inductive tr_function: CminorSel.function -> RTL.function -> Prop :=
                    | tr_function_intro:
                        forall f code rparams map1 s0 s1 i1 rvars map2 s2 i2 nentry ngoto nret rret orret,
                        add_vars init_mapping f.(CminorSel.fn_params) s0 = OK (rparams, map1) s1 i1 ->
                        add_vars map1 f.(CminorSel.fn_vars) s1 = OK (rvars, map2) s2 i2 ->
                        orret = ret_reg f.(CminorSel.fn_sig) rret ->
                        tr_stmt code map2 f.(CminorSel.fn_body) nentry nret nil ngoto nret orret ->
                        code!nret = Some(Ireturn orret) ->
                        tr_function f (RTL.mkfunction
                                        f.(CminorSel.fn_sig)
                                        rparams
                                        f.(CminorSel.fn_stackspace)
                                        code
                                        nentry).

                (* Proof that the translation proof meets the specification *)    
                       
        FEnd Spec.
   FEnd RTLgen.

  Family LTL.
      Definition node := positive.

      FInductive instruction: Type :=
        | Lop : Asm.operation -> list mreg -> mreg -> instruction     
        | Lgetstack : slot -> Z -> typ -> mreg -> instruction
        | Lsetstack : mreg -> slot -> Z -> typ -> instruction 
        | Lbranch : node -> instruction
        | Lcond : Asm.condition -> list mreg -> node -> node -> instruction
        | Lreturn : instruction.
       
      Definition bblock := list instruction.
      Definition code: Type := PTree.t bblock.

      Record function: Type := mkfunction {
        fn_sig: signature;
        fn_stacksize: Z;
        fn_code: code;
        fn_entrypoint: node
      }.
       
      Family Sem.
          Definition genv := Genv.t fundef unit.
          Definition locset := Locmap.t.
           
          FInductive stackframe : Type :=
             | Stackframe : function -> val -> locset -> bblock -> stackframe.               

          FInductive state : Type :=
             | State : list stackframe -> function -> val -> node -> locset -> mem -> state                 
             | Block : list stackframe -> function -> val -> bblock -> locset -> mem -> state               
             | Callstate : list stackframe -> fundef -> locset -> mem -> state.               
             | Returnstate : list stackframe -> locset -> mem -> state.
             
          FInductive step: state -> trace -> state -> Prop :=
             | exec_start_block: forall s f sp pc rs m bb,
                 (fn_code f)!pc = Some bb ->
                 step (State s f sp pc rs m)
                   E0 (Block s f sp bb rs m)
             | exec_Lop: forall s f sp op args res bb rs m v rs',
                 eval_operation ge sp op (reglist rs args) m = Some v ->
                 rs' = Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs) ->
                 step (Block s f sp (Lop op args res :: bb) rs m)
                   E0 (Block s f sp bb rs' m)  
             | exec_Lgetstack: forall s f sp sl ofs ty dst bb rs m rs',
                 rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (undef_regs (destroyed_by_getstack sl) rs) ->
                 step (Block s f sp (Lgetstack sl ofs ty dst :: bb) rs m)
                   E0 (Block s f sp bb rs' m)
             | exec_Lsetstack: forall s f sp src sl ofs ty bb rs m rs',
                 rs' = Locmap.set (S sl ofs ty) (rs (R src)) (undef_regs (destroyed_by_setstack ty) rs) ->
                 step (Block s f sp (Lsetstack src sl ofs ty :: bb) rs m)
                   E0 (Block s f sp bb rs' m)
             | exec_Lbranch: forall s f sp pc bb rs m,
                 step (Block s f sp (Lbranch pc :: bb) rs m)
                   E0 (State s f sp pc rs m)
             | exec_Lcond: forall s f sp cond args pc1 pc2 bb rs b pc rs' m,
                 eval_condition cond (reglist rs args) m = Some b ->
                 pc = (if b then pc1 else pc2) ->
                 rs' = undef_regs (destroyed_by_cond cond) rs ->
                 step (Block s f sp (Lcond cond args pc1 pc2 :: bb) rs m)
                   E0 (State s f sp pc rs' m)
             | exec_Lreturn: forall s f sp bb rs m m',
                 Mem.free m sp 0 f.(fn_stacksize) = Some m' ->
                 step (Block s f (Vptr sp Ptrofs.zero) (Lreturn :: bb) rs m)
                   E0 (Returnstate s (return_regs (parent_locset s) rs) m')
             | exec_return: forall f sp rs1 bb s rs m,
                 step (Returnstate (Stackframe f sp rs1 bb :: s) rs m)
                   E0 (Block s f sp bb rs m).

          Inductive initial_state (p: program): state -> Prop :=
            | initial_state_intro: forall b f m0,
                let ge := Genv.globalenv p in
                Genv.init_mem p = Some m0 ->
                Genv.find_symbol ge p.(prog_main) = Some b ->
                Genv.find_funct_ptr ge b = Some f ->
                funsig f = signature_main ->
                initial_state p (Callstate nil f (Locmap.init Vundef) m0).

          Inductive final_state: state -> int -> Prop :=
              | final_state_intro: forall rs m retcode,
                  Locmap.getpair (map_rpair R (loc_result signature_main)) rs = Vint retcode ->
                  final_state (Returnstate nil rs m) retcode.
       FEnd Sem.
   FEnd LTL.

   Family Linear.
       FInductive instruction: Type :=
          | Lgetstack: slot -> Z -> typ -> mreg -> instruction
          | Lsetstack: mreg -> slot -> Z -> typ -> instruction
          | Lop: Asm.operation -> list mreg -> mreg -> instruction          
          | Llabel: label -> instruction
          | Lgoto: label -> instruction
          | Lcond: Asm.condition -> list mreg -> label -> instruction
          | Lreturn: instruction.

       Definition code: Type := list instruction.

       Record function: Type := mkfunction {
         fn_sig: signature;
         fn_stacksize: Z;
         fn_code: code
       }.
       
       Family Sem.
          Definition genv := Genv.t fundef unit.
          Definition locset := Locmap.t.

          FInductive stackframe: Type :=
               | Stackframe : function -> val -> locset -> code -> stackframe.                   

          FInductive state: Type :=
             | State : list stackframe -> function -> val -> code -> locset -> mem -> state      
             | Callstate : list stackframe -> fundef -> locset -> mem -> state      
             | Returnstate : list stackframe -> locset -> mem -> state.

          FInductive step: state -> trace -> state -> Prop :=
             | exec_Lgetstack:
               forall s f sp sl ofs ty dst b rs m rs',
                 rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (undef_regs (destroyed_by_getstack sl) rs) ->
                 step (State s f sp (Lgetstack sl ofs ty dst :: b) rs m)
                   E0 (State s f sp b rs' m)
             | exec_Lsetstack:
               forall s f sp src sl ofs ty b rs m rs',
                 rs' = Locmap.set (S sl ofs ty) (rs (R src)) (undef_regs (destroyed_by_setstack ty) rs) ->
                 step (State s f sp (Lsetstack src sl ofs ty :: b) rs m)
                   E0 (State s f sp b rs' m)
             | exec_Lop:
               forall s f sp op args res b rs m v rs',
                 Asm.eval_operation ge sp op (reglist rs args) m = Some v ->
                 rs' = Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs) ->
                 step (State s f sp (Lop op args res :: b) rs m)
                   E0 (State s f sp b rs' m)  
             | exec_Llabel:
               forall s f sp lbl b rs m,
                 step (State s f sp (Llabel lbl :: b) rs m)
                   E0 (State s f sp b rs m)
             | exec_Lgoto:
               forall s f sp lbl b rs m b',
                 find_label lbl f.(fn_code) = Some b' ->
                 step (State s f sp (Lgoto lbl :: b) rs m)
                   E0 (State s f sp b' rs m)
             | exec_Lcond_true:
               forall s f sp cond args lbl b rs m rs' b',
                 eval_condition cond (reglist rs args) m = Some true ->
                 rs' = undef_regs (destroyed_by_cond cond) rs ->
                 find_label lbl f.(fn_code) = Some b' ->
                 step (State s f sp (Lcond cond args lbl :: b) rs m)
                   E0 (State s f sp b' rs' m)
             | exec_Lcond_false:
               forall s f sp cond args lbl b rs m rs',
                 eval_condition cond (reglist rs args) m = Some false ->
                 rs' = undef_regs (destroyed_by_cond cond) rs ->
                 step (State s f sp (Lcond cond args lbl :: b) rs m)
                   E0 (State s f sp b rs' m)
             | exec_Lreturn:
               forall s f stk b rs m m',
                 Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
                 step (State s f (Vptr stk Ptrofs.zero) (Lreturn :: b) rs m)
                   E0 (Returnstate s (return_regs (parent_locset s) rs) m')  
             | exec_return:
               forall s f sp rs0 c rs m,
                 step (Returnstate (Stackframe f sp rs0 c :: s) rs m)
                   E0 (State s f sp c rs m).
          
          Inductive initial_state (p: program): state -> Prop :=
              | initial_state_intro: forall b f m0,
                  let ge := Genv.globalenv p in
                  Genv.init_mem p = Some m0 ->
                  Genv.find_symbol ge p.(prog_main) = Some b ->
                  Genv.find_funct_ptr ge b = Some f ->
                  funsig f = signature_main ->
                  initial_state p (Callstate nil f (Locmap.init Vundef) m0).

          Inductive final_state: state -> int -> Prop :=
              | final_state_intro: forall rs m retcode,
                  Locmap.getpair (map_rpair R (loc_result signature_main)) rs = Vint retcode ->
                  final_state (Returnstate nil rs m) retcode.
       FEnd Sem.
   FEnd Linear.

   Family Mach.
        FInductive instruction: Type :=
            | Mgetstack: ptrofs -> typ -> mreg -> instruction
            | Mgetparam: ptrofs -> typ -> mreg -> instruction
            | Msetstack: mreg -> ptrofs -> typ -> instruction
            | Mop: Asm.operation -> list mreg -> mreg -> instruction            
            | Mlabel: label -> instruction
            | Mgoto: label -> instruction
            | Mcond: Asm.condition -> list mreg -> label -> instruction
            | Mreturn: instruction.

        Definition code := list instruction.
        
        Record function: Type := mkfunction
            { fn_sig: signature;
              fn_code: code;
              fn_stacksize: Z;
              fn_link_ofs: ptrofs;
              fn_retaddr_ofs: ptrofs }.

        Family Sem.
            Definition genv := Genv.t fundef unit.
            Definition locset := Locmap.t.
            
            FInductive stackframe: Type :=
                | Stackframe: block -> val -> val -> code -> stackframe.
            
            FInductive state: Type :=
                | State: list stackframe -> block -> val -> code -> regset -> mem -> state
                | Callstate: list stackframe -> block -> regset -> mem -> state
                | Returnstate: list stackframe -> regset -> mem -> state.
            
            FInductive step:  state -> trace -> state -> Prop :=
                | exec_Mlabel:
                      forall s f sp lbl c rs m,
                      step (State s f sp (Mlabel lbl :: c) rs m)
                        E0 (State s f sp c rs m)
                | exec_Mgetstack:
                      forall s f sp ofs ty dst c rs m v,
                      load_stack m sp ty ofs = Some v ->
                      step (State s f sp (Mgetstack ofs ty dst :: c) rs m)
                        E0 (State s f sp c (rs#dst <- v) m)
                | exec_Msetstack:
                      forall s f sp src ofs ty c rs m m' rs',
                      store_stack m sp ty ofs (rs src) = Some m' ->
                      rs' = undef_regs (destroyed_by_setstack ty) rs ->
                      step (State s f sp (Msetstack src ofs ty :: c) rs m)
                        E0 (State s f sp c rs' m')
                | exec_Mgetparam:
                      forall s fb f sp ofs ty dst c rs m v rs',
                      Genv.find_funct_ptr ge fb = Some (Internal f) ->
                      load_stack m sp Tptr f.(fn_link_ofs) = Some (parent_sp s) ->
                      load_stack m (parent_sp s) ty ofs = Some v ->
                      rs' = (rs # temp_for_parent_frame <- Vundef # dst <- v) ->
                      step (State s fb sp (Mgetparam ofs ty dst :: c) rs m)
                        E0 (State s fb sp c rs' m)
                | exec_Mop:
                    forall s f sp op args res c rs m v rs',
                    eval_operation ge sp op rs##args m = Some v ->
                    rs' = ((undef_regs (destroyed_by_op op) rs)#res <- v) ->
                    step (State s f sp (Mop op args res :: c) rs m)
                      E0 (State s f sp c rs' m)
                | exec_Mgoto:
                    forall s fb f sp lbl c rs m c',
                    Genv.find_funct_ptr ge fb = Some (Internal f) ->
                    find_label lbl f.(fn_code) = Some c' ->
                    step (State s fb sp (Mgoto lbl :: c) rs m)
                      E0 (State s fb sp c' rs m)
                | exec_Mcond_true:
                    forall s fb f sp cond args lbl c rs m c' rs',
                    eval_condition cond rs##args m = Some true ->
                    Genv.find_funct_ptr ge fb = Some (Internal f) ->
                    find_label lbl f.(fn_code) = Some c' ->
                    rs' = undef_regs (destroyed_by_cond cond) rs ->
                    step (State s fb sp (Mcond cond args lbl :: c) rs m)
                      E0 (State s fb sp c' rs' m)
                | exec_Mcond_false:
                      forall s f sp cond args lbl c rs m rs',
                      eval_condition cond rs##args m = Some false ->
                      rs' = undef_regs (destroyed_by_cond cond) rs ->
                      step (State s f sp (Mcond cond args lbl :: c) rs m)
                        E0 (State s f sp c rs' m)
                | exec_Mreturn:
                     forall s fb stk soff c rs m f m',
                     Genv.find_funct_ptr ge fb = Some (Internal f) ->
                     load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) = Some (parent_sp s) ->
                     load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra s) ->
                     Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
                     step (State s fb (Vptr stk soff) (Mreturn :: c) rs m)
                       E0 (Returnstate s rs m').                

            Inductive initial_state (p: program): state -> Prop :=
                  | initial_state_intro: forall fb m0,
                      let ge := Genv.globalenv p in
                      Genv.init_mem p = Some m0 ->
                      Genv.find_symbol ge p.(prog_main) = Some fb ->
                      initial_state p (Callstate nil fb (Regmap.init Vundef) m0).

            Inductive final_state: state -> int -> Prop :=
                  | final_state_intro: forall rs m r retcode,
                      loc_result signature_main = One r ->
                      rs r = Vint retcode ->
                      final_state (Returnstate nil rs m) retcode.
        FEnd Sem.
  FEnd Mach.  
   
  Family Renumber.
      MetaData _renum_pc. 
          Definition renum_pc (pc: node) : node :=
          match pnum!pc with
          | Some pc' => pc'
          | None => 1%positive(* impossible case, never exercised *)
          end.
      FEnd _renum_pc.

      FRecursion renum_instr : (i : RTL.instruction) -> RTL.instruction. 
          Case Inop (s) := Inop (renum_pc s). 
          Case Iop (op, args, res, s) := Iop op args res (renum_pc s).
          Case Icond (cond, args, s1, s2) := Icond cond args (renum_pc s1) (renum_pc s2).
          Case Ireturn (or) := Ireturn or.
      FEnd renum_instr.

      MetaData _renum_cfg.
          Definition renum_node (c': code) (pc: node) (i: RTL.instruction) : RTL.code :=
          match pnum!pc with
          | None => c'
          | Some pc' => PTree.set pc' (renum_instr i) c'
          end.

          Definition renum_cfg (c: code) : code :=
            PTree.fold renum_node c (PTree.empty instruction).
      FEnd _renum_cfg.
   FEnd Renumber.
   
   (* Nanopasses: 
   1. Replace ops which have all arguments known to a single constant load operation 
   2. Replace ops which have some arguments known to simpler ops (strength reduction)
   3. Cast operators that have no effect are removed 
   4. Conditional branches and multi-way branches are statically resolved into Inop instructions when possible.
   *)
  Family Constprop.  
         FRecursion transf_instr : 
             (instr: instruction) -> (f: RTL.function) -> 
             (an: PMap.t VA.t) -> 
            (rm: romem) -> 
            (pc: RTL.node) -> RTL.instruction. 
           Case Iop (op, args, res, s) := 
              (let aargs := aregs ae args in
              let a := eval_static_operation op aargs in
              let s' := successor f (AE.set res a ae) s in
              match const_for_result a with
              | Some cop =>
                  Iop cop nil res s'
              | None =>
                  let (op', args') := op_strength_reduction op args aargs in
                  Iop op' args' res s'
              end.)
           Case Inop (s) := Inop s.
           Case Icond (cond, args, s1, s2) := 
              (let aargs := aregs ae args in
              match resolve_branch (eval_static_condition cond aargs) with
              | Some b =>
                  if b then Inop s1 else Inop s2
              | None =>
                  let (cond', args') := cond_strength_reduction cond args aargs in
                  Icond cond' args' s1 s2
              end).
           Case Ireturn (or) := Ireturn or.
         FEnd transf_instr.
   FEnd Constprop.
   
   (* Nanopasses: 
     1. Combine op 
     2. Combine cond
     3. Combine address
   *)
  Family CSE.
      FRecursion transfer : (i : instruction) -> (f: function) -> (approx: PMap.t VA.t) -> (before: numbering) -> instruction.
          Case Inop (s) := Inop (s).
          Case Iop (op, args, res, s) := (
                if is_trivial_op op then instr else
                let (n1, vl) := valnum_regs n args in
                match find_rhs n1 (Op op vl) with
                | Some r =>
                    Iop Omove (r :: nil) res s
                | None =>
                    let (op', args') := reduce _ combine_op n1 op args vl in
                    Iop op' args' res s
                end
          ).
          Case Icond (cond, args, ifso, ifnot) := (
            let (n1, vl) := valnum_regs n args in
            match combine_cond' cond vl with
            | Some b => Inop (if b then s1 else s2)
            | None =>
                let (cond', args') := reduce _ combine_cond n1 cond args vl in
                Icond cond' args' s1 s2
            end
          ).
          Case Ireturn (optarg) := Ireturn (optarg). 
      FEnd transfer.
  FEnd CSE.
   
  Family Deadcode.
      FRecursion trnasf_instr : (i : instruction) -> (f: function) -> (approx: PMap.t VA.t) -> (an: PMap.t NA.t) -> (pc: RTL.node) -> RTL.instruction.
          Case Inop (s) := Inop (s).
          Case Iop (op, args, res, s) := (
              let nres := nreg (fst an!!pc) res in
              if is_dead nres then Inop s else
              if is_int_zero nres then Iop (Ointconst Int.zero) nil res s else
              if operation_is_redundant op nres then
                  match args with
                  | arg :: _ => Iop Omove (arg :: nil) res s
                  | nil => instr
                  end
              else Iop (op, args, res, s)
          ).
          Case Icond (cond, args, s1, s2) := (
              if peq s1 s2 then Inop s1 else Icond cond args s1 s2
          ).
          Case Ireturn(v) := Ireturn(v).
  FEnd Deadcode.

   Family Unusedglob.
      (* Checks the ids referenced by an instruction *)
      FRecursion ref_instruction : (i : instruction) -> list ident.
          Case Inop (s) := nil.
          Case Iop (op, args, res, s) := globals_operation op.
          Case Icond (cond, args, s1, s2) := nil.
          Case Ireturn (or) := nil.
   FEnd Unusedglob.
   
   (* RTL -> LTL *)
   (* Allocation is written in OCaml, hence this is a translation validation *)
   (* The correctness is the correctness of the translation validator *)
   Family Allocation.
        Family Proof.
        FEnd Proof.
   FEnd Allocation.

  (* RTL -> RTL *)
  Family Tunneling.
      Module U := UnionFind.UF(PTree).
      
    FRecursion record_branch : (i : instruction) -> (uf: U.t) -> (pc: node) -> (b: bblock) -> U.t.
          Case Lbranch s := U.union uf pc s.
          Case Lgetstack sl ofs ty r := uf.
          Case Lsetstack r sl ofs ty := uf.
          Case Lop op args res := uf.
          Case Lcond cond args s1 s2 := uf.
          Case Lreturn := uf.
    FEnd record_branch.

    FRecursion tunnel_instr : (i : instruction) -> (uf: U.t) -> instruction.
        Case Lbranch s := Lbranch (U.repr uf s).
        Case Lcond cond args s1 s2 := 
            let s1' := U.repr uf s1 in let s2' := U.repr uf s2 in
            if peq s1' s2'
            then Lbranch s1'
            else Lcond cond args s1' s2'.
        Case Ljumptable arg tbl := Ljumptable arg (List.map (U.repr uf) tbl).
        Case Lop op args res := Lop op args res.
        Case Lgetstack sl ofs ty r := Lgetstack sl ofs ty r.
        Case Lsetstack r sl ofs ty := Lsetstack r sl ofs ty.
        Case Lreturn := Lreturn.
    FEnd tunnel_instr.
  FEnd Tunneling.

   (* LTL -> Linear *)
  Family Linearize.
       FRecursion starts_with_label about Linear.instruction motive (fun (_ : Linear.instruction) => label -> bool).
            Case Llabel := (fun lbl' => fun lbl => peq lbl lbl').
            Case Lop := (fun op args res => fun lbl => false).
            Case Lgetstack := (fun sl ofs ty r => fun lbl => false).
            Case Lsetstack := (fun r sl ofs ty => fun lbl => false).
            Case Lbranch := (fun lbl => fun lbl => false).
            Case Lcond := (fun cond args lbl => fun lbl => false).
            Case Lreturn := (fun lbl => false).
            Case Ljumptable := (fun arg tbl => fun lbl => false).
       FEnd starts_with_label.

       Metadata _starts_with.
       Fixpoint starts_with (lbl: label) (k: code) {struct k} : bool :=
            match k with
            | i :: k' => if starts_with_label i then true else starts_with lbl k'
            | _ => false
            end.
       FEnd _starts_with.
              
       FDefinition add_branch (s: label) (k: code) : code :=
          if starts_with s k then k else Lgoto s :: k.

       FRecursion translate_instr about LTL.instruction motive (fun (_ : LTL.instruction) -> Linear.code -> Linear.instruction).
          Case Lop := (fun op args res => fun k => Lop op args res).
          Case Lgetstack := (fun sl ofs ty r => fun => Lgetstack sl ofs ty r).
          Case Lsetstack := (fun r sl ofs ty => fun k => Lsetstack r sl ofs ty).
          Case Lbranch := (fun lbl => fun k => add_branch s k).
          Case Lcond := (fun cond args lbl => fun k => 
                              if starts_with s1 k then
                                  Lcond (Asm.negate_condition cond) args s2 :: add_branch s1 k
                                else
                                  Lcond cond args s1 :: add_branch s2 k).
          Case Lreturn := (fun k => Lreturn).
       FEnd transl_instr.
       
       MetaData _linearize_block.
       Fixpoint linearize_block (b: LTL.bblock) (k: code) : code :=
          match b with
          | nil => k
          | i :: b' => linearize_block b' (transl_instr i k)
          end.
       FEnd _linearize_block.
   FEnd Linearize.

   (* Linear -> Linear *)
   Family Debugvar.
   FEnd Debugvar.
   
   (* Linear -> Mach *)
  Family Stacking.
        Definition transl_op (fe: frame_env) (op: operation) :=
            Asm.shift_stack_operation fe.(fe_stack_data) op.

        Fixpoint restore_callee_save_rec (rl: list mreg) (ofs: Z) (k: Mach.code) :=
          match rl with
          | nil => k
          | r :: rl =>
              let ty := mreg_type r in
              let sz := AST.typesize ty in
              let ofs1 := align ofs sz in
              Mgetstack (Ptrofs.repr ofs1) ty r :: restore_callee_save_rec rl (ofs1 + sz) k
          end.

        Definition restore_callee_save (fe: frame_env) (k: Mach.code) :=
          restore_callee_save_rec fe.(fe_used_callee_save) fe.(fe_ofs_callee_save) k.

        FRecursion transl_instr about Linear.instruction motive (fun (_ : Linear.instruction) => frame_env -> Mach.code -> Mach.code).
             Case Lgetstack := (fun sl ofs ty r => fun fe k => 
                      match sl with
                      | Local =>
                          Mach.Mgetstack (Ptrofs.repr (offset_local fe ofs)) ty r :: k
                      | Incoming =>
                          Mach.Mgetparam (Ptrofs.repr (offset_arg ofs)) ty r :: k
                      | Outgoing =>
                          Mach.Mgetstack (Ptrofs.repr (offset_arg ofs)) ty r :: k
                      end).
             Case Lsetstack := (fun r sl ofs ty => fun fe k => 
                      match sl with
                      | Local =>
                          Mach.Msetstack r (Ptrofs.repr (offset_local fe ofs)) ty :: k
                      | Incoming =>
                          k
                      | Outgoing =>
                          Mach.Msetstack r (Ptrofs.repr (offset_arg ofs)) ty :: k
                      end). 
             Case Lop := (fun op args res => fun fe k =>  Mach.Mop (transl_op fe op) args res :: k).
             Case Llabel := (fun lbl => fun fe k => Mach.Mlabel lbl :: k).
             Case Lgoto := (fun lbl => fun fe k => Mach.Mgoto lbl :: k).
             Case Lcond := (fun cond args lbl => fun fe k => Mach.Mcond cond args lbl :: k).
             Case Lreturn := (fun fe k =>  restore_callee_save fe (Mreturn :: k)).
        FEnd transl_instr.

        Definition transl_code
            (fe: frame_env) (il: list Linear.instruction) : Mach.code :=
          list_fold_right (transl_instr fe) il nil.
  FEnd Stacking.

   (* Mach -> Asm *)
  Family Asmgen.
    FRecursion transl_op about Linear.operation motive (fun (_ : Linear.operation) => list mreg -> mreg -> Asm.code -> Asm.code).
        Case Omove := (fun a1 res k => 
            match preg_of res, preg_of a1 with
            | IR r, IR a => Pmv r a :: k
            | FR r, FR a => Pfmv r a :: k
            |  _  ,  _   => error (Errors.msg "Asmgen.Omove")
            end).
        Case Ointconst := (fun n res k => 
            match ireg_of res with
            | None => error (Errors.msg "Asmgen.Ointconst")
            | Some rd => loadimm32 rd n k
            end).
        Case Olongconst := (fun n res k => 
            match ireg_of res with
            | None => error (Errors.msg "Asmgen.Olongconst")
            | Some rd => loadimm64 rd n k
            end).
        Case Ofloatconst := (fun f res k => 
            match freg_of res with
            | None => error (Errors.msg "Asmgen.Ofloatconst")
            | Some rd => 
                if Float.eq_dec f Float.zero
                then Pfcvtdw rd X0 :: k
                else Ploadfi rd f :: k
            end).
        Case Osingleconst := (fun f res k => 
            match freg_of res with
            | None => error (Errors.msg "Asmgen.Osingleconst")
            | Some rd => 
                if Float32.eq_dec f Float32.zero
                then Pfcvtsw rd X0 :: k
                else Ploadsi rd f :: k
            end).
        Case Oaddrsymbol := (fun s ofs res k => 
            match ireg_of res with
            | None => error (Errors.msg "Asmgen.Oaddrsymbol")
            | Some rd => 
                if Archi.pic_code tt && negb (Ptrofs.eq ofs Ptrofs.zero)
                then Ploadsymbol rd s Ptrofs.zero :: addptrofs rd rd ofs k
                else Ploadsymbol rd s ofs :: k
            end).
        Case Oaddrstack := (fun n res k => 
            match ireg_of res with
            | None => error (Errors.msg " Asmgen.Oaddrstack")
            | Some rd => addptrofs rd SP n k
            end).
    FEnd transl_op.

    FRecursion transl_cbranch about condition motive (fun (_ : condition) => list mreg -> label -> Asm.code -> Asm.code).
        Case Ccomp := (fun c => fun args lbl k => 
            match args with
            | a1 :: a2 :: nil =>
                do r1 <- ireg_of a1; do r2 <- ireg_of a2;
                OK (transl_cbranch_int32s c r1 r2 lbl :: k)
            | _ => error (Errors.msg "Asmgen.transl_cbranch")
            end).
        Case Ccompu := (fun c => fun args lbl k => 
            match args with
            | a1 :: a2 :: nil =>
                do r1 <- ireg_of a1; do r2 <- ireg_of a2;
                OK (transl_cbranch_int32u c r1 r2 lbl :: k)
            | _ => error (Errors.msg "Asmgen.transl_cbranch")
            end).
        Case Ccompimm := (fun c n => fun args lbl k => 
            match args with
            | a1 :: nil =>
                do r1 <- ireg_of a1;
                OK (if Int.eq n Int.zero then
                        transl_cbranch_int32s c r1 X0 lbl :: k
                    else loadimm32 X31 n (transl_cbranch_int32s c r1 X31 lbl :: k))
            | _ => error (Errors.msg "Asmgen.transl_cbranch")
            end).
        Case Ccompuimm := (fun c n => fun args lbl k => 
            match args with
            | a1 :: nil =>
                do r1 <- ireg_of a1;
                OK (if Int.eq n Int.zero then
                        transl_cbranch_int32u c r1 X0 lbl :: k
                    else loadimm32 X31 n (transl_cbranch_int32u c r1 X31 lbl :: k))
            | _ => error (Errors.msg "Asmgen.transl_cbranch")
            end).
        Case Ccompl := (fun c => fun args lbl k => 
            match args with
            | a1 :: a2 :: nil =>
                do r1 <- ireg_of a1; do r2 <- ireg_of a2;
                OK (transl_cbranch_int64s c r1 r2 lbl :: k)
            | _ => error (Errors.msg "Asmgen.transl_cbranch")
            end).
        Case Ccomplu := (fun c => fun args lbl k => 
            match args with
            | a1 :: a2 :: nil =>
                do r1 <- ireg_of a1; do r2 <- ireg_of a2;
                OK (transl_cbranch_int64u c r1 r2 lbl :: k)
            | _ => error (Errors.msg "Asmgen.transl_cbranch")
            end).
        Case Ccomplimm := (fun c n => fun args lbl k => 
            match args with
            | a1 :: nil =>
                do r1 <- ireg_of a1;
                OK (if Int64.eq n Int64.zero then
                        transl_cbranch_int64s c r1 X0 lbl :: k
                    else loadimm64 X31 n (transl_cbranch_int64s c r1 X31 lbl :: k))
            | _ => error (Errors.msg "Asmgen.transl_cbranch")
            end).
        Case Ccompluimm := (fun c n => fun args lbl k => 
            match args with
            | a1 :: nil =>
                do r1 <- ireg_of a1;
                OK (if Int64.eq n Int64.zero then
                        transl_cbranch_int64u c r1 X0 lbl :: k
                    else loadimm64 X31 n (transl_cbranch_int64u c r1 X31 lbl :: k))
            | _ => error (Errors.msg "Asmgen.transl_cbranch")
            end).
        Case Ccompf := (fun c => fun args lbl k => 
            match args with
            | f1 :: f2 :: nil =>
                do r1 <- freg_of f1; do r2 <- freg_of f2;
                let (insn, normal) := transl_cond_float c X31 r1 r2 in
                OK (insn :: (if normal then Pbnew X31 X0 lbl else Pbeqw X31 X0 lbl) :: k)
            | _ => error (Errors.msg "Asmgen.transl_cbranch")
            end).
        Case Cnotcompf := (fun c => fun args lbl k => 
            match args with
            | f1 :: f2 :: nil =>
                do r1 <- freg_of f1; do r2 <- freg_of f2;
                let (insn, normal) := transl_cond_float c X31 r1 r2 in
                OK (insn :: (if normal then Pbeqw X31 X0 lbl else Pbnew X31 X0 lbl) :: k)
            | _ => error (Errors.msg "Asmgen.transl_cbranch")
            end).
        Case Ccompfs := (fun c => fun args lbl k => 
            match args with
            | f1 :: f2 :: nil =>
                do r1 <- freg_of f1; do r2 <- freg_of f2;
                let (insn, normal) := transl_cond_single c X31 r1 r2 in
                OK (insn :: (if normal then Pbnew X31 X0 lbl else Pbeqw X31 X0 lbl) :: k)
            | _ => error (Errors.msg "Asmgen.transl_cbranch")
            end).
    FEnd transl_cbranch.

    FRecursion translate_instr about Mach.instruction motive (fun (_ : Mach.instruction) => Mach.function -> bool -> Asm.code -> Asm.code).
       Case Mgetstack := (fun ofs ty dst => fun f ep k => loadind SP ofs ty dst k).
       Case Msetstack := (fun src ofs ty => fun f ep k => storeind SP src ofs ty k).
       Case Mgetparam := (fun ofs ty dst => fun f ep k => 
                         do c <- loadind X30 ofs ty dst k;
                        OK (if ep then c
                                  else loadind_ptr SP f.(fn_link_ofs) X30 c).
      Case Mop := (fun op args res => fun f ep k => transl_op op args res k).
      Case Mlabel := (fun lbl => fun f ep k => Asm.Plabel lbl :: k).
      Case Mgoto := (fun lbl => fun f ep k => Asm.Pj_l lbl :: k).
      Case Mcond := (fun cond args lbl => fun f ep k => transl_cbranch cond args lbl k).
      Case Mreturn := (fun f ep k => make_epilogue f (Pj_r RA f.(Mach.fn_sig) :: k)).
    FEnd translate_instr.
   FEnd Asmgen.
FEnd Imp.
