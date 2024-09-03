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

Axiom cheat : forall {X}, X.
Local Open Scope string_scope.
Local Open Scope error_monad_scope.


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

  Fixpoint type_of_params (params: list (ident * type)) : typelist :=
  match params with
  | nil => Tnil
  | (id, ty) :: rem => Tcons ty (type_of_params rem)
  end.
  FEnd type.

  Family ClightVariant. 
  FEnd ClightVariant.
  
  Family CminorVariant.
  FEnd CminorVariant.
  
  Family CFGLike. 
  FEnd CFGLike.
  
  Family LinearLike.
  FEnd LinearLike.
         
  Family C.
      FInductive expr : Type :=
        | Eval : val -> type -> expr (* constant *)
        | Evar : ident -> type -> expr (* variable *)        
        | Ecast : expr -> type -> expr (* type cast (ty)r *)
        | Eseqand : expr -> expr -> type -> expr (* sequential "and" r1 && r2 *)
        | Eseqor : expr -> expr -> type -> expr (* sequential "or" r1 || r2 *)
        | Econdition : expr -> expr -> expr -> type -> expr (* conditional r1 ? r2 : r3 *)
        | Esizeof : type -> type -> expr (* size of a type *)
        | Ealignof : type -> type -> expr (* natural alignment of a type *)
        | Eassign : expr -> expr -> type -> expr (* assignment l = r *)                
        | Ecomma : expr -> expr -> type -> expr. (* sequence expression r1, r2 *)                
        
        FRecursion typeof : (e : expr) -> type.
          Case Eval v ty := ty.
          Case Evar x ty := ty.          
          Case Ecast r ty := ty. 
          Case Eseqand r1 r2 ty := ty. 
          Case Eseqor r1 r2 ty := ty. 
          Case Econdition r1 r2 r3 ty := ty.
          Case Esizeof ty' ty := ty.
          Case Ealignof ty' ty := ty. 
          Case Eassign l r ty := ty.                    
          Case Ecomma r1 r2 ty := ty.
        FEnd typeof.      

      FDefinition label := ident.
      
      FInductive statement : Type :=
        | Sskip : statement(* do nothing *)
        | Sdo : expr -> statement(* evaluate expression for side effects *)
        | Ssequence : statement -> statement -> statement(* sequence *)
        | Sifthenelse : expr -> statement -> statement -> statement(* conditional *)
        | Swhile : expr -> statement -> statement(* while loop *)
        | Sdowhile : expr -> statement -> statement(* do loop *)
        | Sfor: statement -> expr -> statement -> statement -> statement(* for loop *)
        | Sbreak : statement(* break statement *)
        | Scontinue : statement(* continue statement *)
        | Sreturn : option expr -> statement(* return statement *)
        | Slabel : label -> statement -> statement
        | Sgoto : label -> statement.

      
      MetaData function.
      Record function : Type := mkfunction {
        fn_return: self__Imp.type;
        fn_callconv: calling_convention;
        fn_params: list (ident * self__Imp.type);
        fn_vars: list (ident * self__Imp.type);
        fn_body: self__C.statement
      }.
      FEnd function.

      Family Semantics.                        
      FEnd Semantics.
  FEnd C.
      
   Family Clight.
       FInductive expr : Type :=          
          | Econst_int: int -> type -> expr(* integer literal *)
          | Econst_float: float -> type -> expr(* double float literal *)
          | Econst_single: float32 -> type -> expr(* single float literal *)
          | Econst_long: int64 -> type -> expr(* long integer literal *)                                            
          | Etempvar: ident -> type -> expr (* temporary variable *)          
          | Esizeof: type -> type -> expr (* size of a type *)
          | Ealignof: type -> type -> expr. (* alignment of a type *)                                         
       
       FRecursion typeof : (e : expr) -> type. 
          Case Econst_int i ty := ty. 
          Case Econst_float f ty := ty. 
          Case Econst_single s ty := ty. 
          Case Econst_long l ty := ty. 
          Case Etempvar v ty := ty.
          Case Esizeof ty' ty := ty.
          Case Ealignof ty' ty := ty.
       FEnd typeof.
       
       FDefinition label := ident.
       FInductive stmt : Type :=
           | Sskip : stmt(* do nothing *)           
           | Sset : ident -> expr -> stmt(* assignment tempvar = rvalue *)           
           | Ssequence : stmt -> stmt -> stmt(* sequence *)
           | Sifthenelse : expr -> stmt -> stmt -> stmt(* conditional *)
           | Sloop: stmt -> stmt -> stmt(* infinite loop *)
           | Sbreak : stmt(* break stmt *)
           | Scontinue : stmt(* continue stmt *)
           | Sreturn : option expr -> stmt(* return stmt *)           
           | Slabel : label -> stmt -> stmt
           | Sgoto : label -> stmt.       

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

       FDefinition var_names : list(ident * type) -> list ident := fun vars => 
         List.map (@fst ident type) vars.
              
       FDefinition fundef := AST.fundef function.
       
       FDefinition type_of_function : function -> type := fun f => 
         self__Imp.Tfunction (self__Imp.type_of_params (self__Clight.fn_params f)) 
           (self__Clight.fn_return f) (self__Clight.fn_callconv f).
       
       FDefinition type_of_fundef : fundef -> type := fun f =>
          match f with
          | Internal fd => type_of_function fd
          | _ => cheat (* TODO: We don't have External in the base compiler *)
          end.
       
       FDefinition program : Type := AST.program fundef unit.                     
       
       Family Semantics.                                                          
            FDefinition env := PTree.t (block * type).                                     
            FDefinition empty_env: env := (PTree.empty (block * type)).

            FDefinition temp_env := PTree.t val.
                        
           FInductive eval_expr : env -> temp_env -> mem -> expr -> val -> Prop :=
               | eval_Econst_int: forall e le m i ty,
                   eval_expr e le m (Econst_int i ty) (Vint i)
               | eval_Econst_float: forall e le m f ty,
                   eval_expr e le m (Econst_float f ty) (Vfloat f)
               | eval_Econst_single: forall e le m f ty,
                   eval_expr e le m (Econst_single f ty) (Vsingle f)
               | eval_Econst_long: forall e le m i ty,
                   eval_expr e le m (Econst_long i ty) (Vlong i)
               | eval_Etempvar: forall e le m id ty v,
                   PTree.get id le = Some v ->
                   eval_expr e le m (Etempvar id ty) v.

           FInductive cont: Type :=
                | Kstop: cont
                | Kseq: stmt -> cont -> cont(* Kseq s2 k = after s1 in s1;s2 *)
                | Kloop1: stmt -> stmt -> cont -> cont(* Kloop1 s1 s2 k = after s1 in Sloop s1 s2 *)
                | Kloop2: stmt -> stmt -> cont -> cont. (* Kloop2 s1 s2 k = after s2 in Sloop s1 s2 *)                

           FRecursion call_cont about cont motive (fun (c : cont) => cont) by _rect.
           (* FRecursion call_cont : (c : cont) -> cont.*)
                Case Kstop := Kstop.
                Case Kseq := ( fun s k call_cont_k => call_cont_k).
                Case Kloop1 := (fun s1 s2 k call_cont_k => call_cont_k).
                Case Kloop2 := (fun s1 s2 k call_cont_k => call_cont_k). 
           FEnd call_cont.
            
           (* FRecursion is_call_cont about cont motive (fun (c : cont) => Prop) by _rect.
           FRecursion is_call_cont : (c : cont) -> Prop.
                Case Kstop := True.
                Case Kseq s k := False. 
                Case Kloop1 s1 s2 k := False. 
                Case Kloop2 s1 s2 k := False.
           FEnd is_call_cont.*)
           (* There is a bug which doesn't allow more than one FRecursion on a type *)
           MetaData is_call_cont.
           Axiom is_call_cont : self__Semantics.cont -> Prop.
           FEnd is_call_cont.

           FInductive state: Type :=
                | State : function -> stmt -> cont -> env -> temp_env -> mem -> state                    
                | Callstate : fundef -> list val -> cont -> mem -> state                    
                | Returnstate : val -> cont -> mem -> state.                      
            
           FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont)) by _rect.
           (* FRecursion find_label : (s : stmt) -> (lbl: label) -> (k: cont) -> option (stmt * cont).*)
                Case Sskip := (fun lbl k => None).
                Case Sset := (fun id e => fun lbl k => None).
                Case Ssequence := (fun s1 find_label_s1 s2 find_label_s2 => 
                                        fun lbl k =>
                                        match find_label_s1 lbl (Kseq s2 k) with 
                                        | Some sk => Some sk 
                                        | None => find_label_s2 lbl k end).                
                Case Sifthenelse := (fun e s1 find_label_s1 s2 find_label_s2 => 
                                         fun lbl k =>
                                         match find_label_s1 lbl k with 
                                         | Some sk => Some sk 
                                         | None => find_label_s2 lbl k end).
                Case Sloop := (fun s1 find_label_s1 s2 find_label_s2 => 
                                 fun lbl k =>
                                 match find_label_s1 lbl (Kloop1 s1 s2 k) with 
                                 | Some sk => Some sk 
                                 | None => find_label_s2 lbl (Kloop2 s1 s2 k) end).                
                Case Sreturn := (fun e => fun lbl k => None).
                Case Slabel := (fun lbl' s find_label_s => fun lbl k => if ident_eq lbl lbl' then 
                                      Some(s, k) else find_label_s lbl k).
                Case Sgoto := (fun label => fun lbl k => None).
                Case Sbreak := (fun lbl k => None).                
                Case Scontinue := (fun lbl k => None).
           FEnd find_label.
           MetaData bool_val.
           Axiom bool_val : val -> self__Imp.type -> mem -> option bool. 
           FEnd bool_val.

           MetaData sizeof.
           Axiom sizeof : (* self__Semantics.composite_env -> *) self__Imp.type -> Z. 
           FEnd sizeof.      
           
           MetaData create_undef_temps.
             Fixpoint create_undef_temps (temps: list (ident * self__Imp.type)) : self__Semantics.temp_env :=
              match temps with
              | nil => PTree.empty val
              | (id, t) :: temps' => PTree.set id Vundef (create_undef_temps temps')
             end.
           FEnd create_undef_temps.

           MetaData bind_parameter_temps.
           Fixpoint bind_parameter_temps (formals: list (ident * self__Imp.type)) (args: list val)
                              (le: self__Semantics.temp_env) : option self__Semantics.temp_env :=
                match formals, args with
                | nil, nil => Some le
                | (id, t) :: xl, v :: vl => bind_parameter_temps xl vl (PTree.set id v le)
                | _, _ => None
                end.
           FEnd bind_parameter_temps.
             
           FDefinition block_of_binding := fun (id_b_ty: ident * (block * type)) =>
             match id_b_ty with (id, (b, ty)) => (b, 0, sizeof ty) end.

           FDefinition blocks_of_env : env -> list (block * Z * Z)  := fun e => 
             List.map block_of_binding (PTree.elements e).                      
           
           (* Definition sem_cast (v: val) (t1 t2: type) (m: mem): option val := *)
           MetaData sem_cast.
           Axiom sem_cast : val -> self__Imp.type -> self__Imp.type -> mem -> option val.
           FEnd sem_cast.

           MetaData alloc_variables.
           Inductive alloc_variables: self__Semantics.env -> mem ->
                           list (ident * self__Imp.type) ->
                           self__Semantics.env -> mem -> Prop :=
               | alloc_variables_nil:
                   forall e m,
                   alloc_variables e m nil e m
               | alloc_variables_cons:
                   forall e m id ty vars m1 b1 m2 e2,
                   Mem.alloc m 0 (self__Semantics.sizeof ty) = (m1, b1) ->
                   alloc_variables (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
                   alloc_variables e m ((id, ty) :: vars) e2 m2.
           FEnd alloc_variables.


           MetaData function_entry.
           Inductive function_entry              
             (f: self__Clight.function) (vargs: list val) (m: mem) 
             (e: self__Semantics.env) (le: self__Semantics.temp_env) (m': mem) : Prop :=
              | function_entry2_intro:
                  list_norepet (self__Clight.var_names f.(self__Clight.fn_vars)) ->
                  list_norepet (self__Clight.var_names f.(self__Clight.fn_params)) ->
                  list_disjoint (self__Clight.var_names f.(self__Clight.fn_params)) (self__Clight.var_names f.(self__Clight.fn_temps)) ->
                  self__Semantics.alloc_variables self__Semantics.empty_env m f.(self__Clight.fn_vars) e m' ->
                  self__Semantics.bind_parameter_temps f.(self__Clight.fn_params) vargs (self__Semantics.create_undef_temps f.(self__Clight.fn_temps)) = Some le ->
                  function_entry f vargs m e le m'.
           FEnd function_entry.
          
           (* (e : env) (le : temp_env) (m : mem) *)
           FInductive step : state -> trace -> state -> Prop :=
               | step_set: forall f id a k e le m v,
                   eval_expr e le m a v ->
                   step (State f (Sset id a) k e le m)
                     E0 (State f Sskip k e (PTree.set id v le) m)                  
               | step_seq: forall f s1 s2 k e le m,
                   step (State f (Ssequence s1 s2) k e le m)
                     E0 (State f s1 (Kseq s2 k) e le m)
               | step_skip_seq: forall f s k e le m,
                   step (State f Sskip (Kseq s k) e le m)
                     E0 (State f s k e le m)
               | step_continue_seq: forall f s k e le m,
                   step (State f Scontinue (Kseq s k) e le m)
                     E0 (State f Scontinue k e le m)
               | step_break_seq: forall f s k e le m,
                   step (State f Sbreak (Kseq s k) e le m)
                     E0 (State f Sbreak k e le m)             
               | step_ifthenelse: forall f a s1 s2 k e le m v1 b,
                   eval_expr e le m a v1 ->
                   bool_val v1 (typeof a) m = Some b ->
                   step (State f (Sifthenelse a s1 s2) k e le m)
                     E0 (State f (if b then s1 else s2) k e le m)
               | step_loop: forall f s1 s2 k e le m,
                   step (State f (Sloop s1 s2) k e le m)
                     E0 (State f s1 (Kloop1 s1 s2 k) e le m)
               | step_skip_or_continue_loop1: forall f s1 s2 k e le m x,
                   x = Sskip \/ x = Scontinue ->
                   step (State f x (Kloop1 s1 s2 k) e le m)
                     E0 (State f s2 (Kloop2 s1 s2 k) e le m)
               | step_break_loop1: forall f s1 s2 k e le m,
                   step (State f Sbreak (Kloop1 s1 s2 k) e le m)
                     E0 (State f Sskip k e le m)
               | step_skip_loop2: forall f s1 s2 k e le m,
                   step (State f Sskip (Kloop2 s1 s2 k) e le m)
                     E0 (State f (Sloop s1 s2) k e le m)
               | step_break_loop2: forall f s1 s2 k e le m,
                   step (State f Sbreak (Kloop2 s1 s2 k) e le m)
                     E0 (State f Sskip k e le m)
               | step_return_0: forall f k e le m m',
                   Mem.free_list m (blocks_of_env e) = Some m' ->
                   step (State f (Sreturn None) k e le m)
                     E0 (Returnstate Vundef (call_cont k) m')
               | step_return_1: forall f a k e le m v v' m',
                   eval_expr e le m a v ->
                   sem_cast v (typeof a) f.(self__Clight.fn_return) m = Some v' ->
                   Mem.free_list m (blocks_of_env e) = Some m' ->
                   step (State f (Sreturn (Some a)) k e le m)
                     E0 (Returnstate v' (call_cont k) m')
               | step_skip_call: forall f k e le m m',
                   is_call_cont k ->
                   Mem.free_list m (blocks_of_env e) = Some m' ->
                   step (State f Sskip k e le m)
                     E0 (Returnstate Vundef k m')                          
               | step_label: forall f lbl s k e le m,
                   step (State f (Slabel lbl s) k e le m)
                     E0 (State f s k e le m)             
               | step_goto: forall f lbl k e le m s' k',
                   find_label f.(self__Clight.fn_body) lbl (call_cont k) = Some (s', k') ->
                   step (State f (Sgoto lbl) k e le m)
                     E0 (State f s' k' e le m)
               | step_internal_function: forall f vargs k m e le m1,
                     function_entry f vargs m e le m1 ->
                     step (Callstate (Internal f) vargs k m)
                       E0 (State f f.(self__Clight.fn_body) k e le m1).
           
               MetaData initial_state.
               Inductive initial_state (p: self__Clight.program): self__Semantics.state -> Prop :=
                  | initial_state_intro: forall b f m0,
                      let ge := Genv.globalenv p in
                      Genv.init_mem p = Some m0 ->
                      Genv.find_symbol ge p.(prog_main) = Some b ->
                      Genv.find_funct_ptr ge b = Some f ->
                      self__Clight.type_of_fundef f = self__Imp.Tfunction self__Imp.Tnil self__Imp.type_int32s cc_default ->
                      initial_state p (self__Semantics.Callstate f nil self__Semantics.Kstop m0).
               FEnd initial_state.
               
               MetaData final_state.
               Inductive final_state: self__Semantics.state -> int -> Prop :=
                  | final_state_intro: forall r m,
                      final_state (self__Semantics.Returnstate (Vint r) self__Semantics.Kstop m) r.
               FEnd final_state.
       FEnd Semantics.
  FEnd Clight.

  Family Csharpminor.
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

       
       MetaData function.
       Record function : Type := mkfunction {
         fn_sig: signature;
         fn_params: list ident;
         fn_vars: list (ident * Z);
         fn_temps: list ident;
         fn_body: self__Csharpminor.stmt
       }.
       FEnd function.
       
       FDefinition fundef := AST.fundef function.       
       FDefinition program : Type := AST.program fundef unit.       
         
       Family Semantics.            
            FDefinition env := PTree.t (block * Z).
            FDefinition temp_env := PTree.t val.
            FDefinition empty_env : env := PTree.empty (block * Z).
            FDefinition empty_temp_env : temp_env := PTree.empty val.
            
            FInductive cont: Type :=
               | Kstop: cont
               | Kseq: stmt -> cont -> cont
               | Kblock: cont -> cont.
            
            FInductive state: Type :=
                | State: function -> stmt -> cont -> env -> temp_env -> mem -> state 
                | Callstate: fundef -> list val -> cont -> mem -> state                    
                | Returnstate : val -> cont -> mem -> state.
            
            FRecursion call_cont about cont motive (fun (_ : cont) => cont) by _rect.
                   Case Kstop := Kstop.
                   Case Kseq := (fun s c call_cont_c => call_cont_c).
                   Case Kblock := (fun c call_cont_c => call_cont_c).
               FEnd call_cont.
               
            (* FRecursion is_call_cont about cont motive (fun (_ : cont) => Prop) by _rect.
                   Case Kstop := True.                   
                   Case Kseq := (fun s c call_cont_c => False).
                   Case Kblock := (fun c call_cont_c => False).
            FEnd is_call_cont. *)
            MetaData is_call_cont.
            Axiom is_call_cont : self__Semantics.cont -> Prop.
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
               
            FInductive eval_expr : env -> temp_env -> mem -> expr -> val -> Prop :=
                | eval_Evar: forall e le m id v,
                    PTree.get id le = Some v ->
                    eval_expr e le m (Evar id) v                  
                | eval_Econst: forall e le m cst v,
                    eval_constant cst = Some v ->
                    eval_expr e le m (Econst cst) v.
            
            
            FDefinition block_of_binding := fun (id_b_sz: ident * (block * Z)) => 
              match id_b_sz with (id, (b, sz)) => (b, 0, sz) end.
            
            FDefinition blocks_of_env : env -> list (block * Z * Z) := fun (e: env) =>
              List.map block_of_binding (PTree.elements e).

               
            (* (e : env) -> (le : temp_env) -> (m : mem) -> *)
            FInductive step :  state -> trace -> state -> Prop :=
                   | step_skip_seq: forall f s k e le m,
                       step (State f Sskip (Kseq s k) e le m)
                         E0 (State f s k e le m)
                   | step_skip_block: forall f k e le m,
                       step (State f Sskip (Kblock k) e le m)
                         E0 (State f Sskip k e le m)
                   | step_skip_call: forall f k e le m m',
                       is_call_cont k ->
                       Mem.free_list m (blocks_of_env e) = Some m' ->
                       step (State f Sskip k e le m)
                         E0 (Returnstate Vundef k m')
                   | step_set: forall f id a k e le m v,
                       eval_expr e le m a v ->
                       step (State f (Sset id a) k e le m)
                         E0 (State f Sskip k e (PTree.set id v le) m)
                   | step_seq: forall f s1 s2 k e le m,
                       step (State f (Sseq s1 s2) k e le m)
                         E0 (State f s1 (Kseq s2 k) e le m)
                   | step_ifthenelse: forall f a s1 s2 k e le m v b,
                       eval_expr e le m a v ->
                       Val.bool_of_val v b ->
                       step (State f (Sifthenelse a s1 s2) k e le m)
                         E0 (State f (if b then s1 else s2) k e le m)
                   | step_loop: forall f s k e le m,
                       step (State f (Sloop s) k e le m)
                         E0 (State f s (Kseq (Sloop s) k) e le m)        
                   | step_block: forall f s k e le m,
                       step (State f (Sblock s) k e le m)
                         E0 (State f s (Kblock k) e le m)
                   | step_return_0: forall f k e le m m',
                       Mem.free_list m (blocks_of_env e) = Some m' ->
                       step (State f (Sreturn None) k e le m)
                         E0 (Returnstate Vundef (call_cont k) m')
                   | step_return_1: forall f a k e le m v m',
                       eval_expr e le m a v ->
                       Mem.free_list m (blocks_of_env e) = Some m' ->
                       step (State f (Sreturn (Some a)) k e le m)
                         E0 (Returnstate v (call_cont k) m')
                   | step_label: forall f lbl s k e le m,
                       step (State f (Slabel lbl s) k e le m)
                         E0 (State f s k e le m)
                   | step_goto: forall f lbl k e le m s' k',
                       find_label f.(self__Csharpminor.fn_body) lbl (call_cont k) = Some(s', k') ->
                       step (State f (Sgoto lbl) k e le m)
                         E0 (State f s' k' e le m).           
            
            (*MetaData initial_state.
            Inductive initial_state (p: self__Csharpminor.program): state -> Prop :=
                | initial_state_intro: forall b f m0,
                    let ge := Genv.globalenv p in
                    Genv.init_mem p = Some m0 ->
                    Genv.find_symbol ge p.(prog_main) = Some b ->
                    Genv.find_funct_ptr ge b = Some f ->
                    funsig f = signature_main ->
                    initial_state p (Callstate f nil Kstop m0).
            FEnd initial_state. *)
            
            MetaData final_state.
            Inductive final_state: self__Semantics.state -> int -> Prop :=
                | final_state_intro: forall r m,
                    final_state (self__Semantics.Returnstate (Vint r) self__Semantics.Kstop m) r.
            FEnd final_state.
       FEnd Semantics.
   FEnd Csharpminor.

   
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
      Axiom sizeof : self__Imp.Clight.Semantics.composite_env -> self__Imp.type -> res Z.
      FEnd sizeof.
      
      MetaData alignof.
      Axiom alignof : self__Imp.Clight.Semantics.composite_env -> self__Imp.type -> res Z.
      FEnd alignof.
      
      FRecursion transl_expr about Clight.expr motive (fun (_ : Clight.expr) => Clight.Semantics.composite_env -> res Csharpminor.expr) by _rect.
          Case Econst_int := (fun n type => fun ce => OK(make_intconst n)). 
          Case Econst_float := (fun n type => fun ce => OK(make_floatconst n)).
          Case Econst_single := (fun n type => fun ce => OK(make_singleconst n)).
          Case Econst_long := (fun n type => fun ce => OK(make_longconst n)).        
          Case Etempvar := (fun id ty => fun ce => OK(Csharpminor.Evar id)). 
          Case Esizeof := (fun ty _ => fun ce => 
                               do sz <- sizeof ce ty; OK(make_ptrofsconst sz)).                           
          Case Ealignof := (fun ty _ => fun ce => 
                               do al <- alignof ce ty; OK(make_ptrofsconst al)).
      FEnd transl_expr.

       (* (nbrk : nat) -> if Clight.stmt terminates on break return Csharpminor.exit nbrk
          (ncnt : nat) -> if Clight.smt terminates on continue return Csharpminor.exit ncnt
        *)

      (* Definition make_boolean (e: expr) (ty: type) := *)
      MetaData make_boolean.
      Axiom make_boolean : self__Imp.Csharpminor.expr -> self__Imp.type -> self__Imp.Csharpminor.expr.
      FEnd make_boolean.
      
      (* Definition make_cast (from to: type) (e: expr) :=*)
      MetaData make_cast.
      Axiom make_cast : self__Imp.type -> self__Imp.type -> self__Imp.Csharpminor.expr -> res self__Imp.Csharpminor.expr.
      FEnd make_cast.
      
      FRecursion transl_statement about Clight.stmt motive (fun (_ : Clight.stmt) => Clight.Semantics.composite_env -> type -> nat -> nat -> res Csharpminor.stmt) by _rect.
           Case Sskip := (fun ce tyret nbrk ncnt => OK Csharpminor.Sskip).   
           Case Sset := (fun x b => fun ce tyret nbrk ncnt => 
                            do tb <- transl_expr b ce;
                            OK (Csharpminor.Sset x tb)).
           Case Ssequence := (fun s1 transl_s1 s2 transl_s2 =>
                              fun ce tyret nbrk ncnt => 
                             do ts1 <- transl_s1 ce tyret nbrk ncnt;
                             do ts2 <- transl_s2 ce tyret nbrk ncnt;
                             OK (Csharpminor.Sseq ts1 ts2)).
           Case Sifthenelse := (fun e s1 transl_s1 s2 transl_s2 => 
                                  fun ce tyret nbrk ncnt => 
                                do te <- transl_expr e ce;
                                do ts1 <- transl_s1 ce tyret nbrk ncnt;
                                do ts2 <- transl_s2 ce tyret nbrk ncnt;
                                OK (Csharpminor.Sifthenelse (make_boolean te (Clight.typeof e)) ts1 ts2)).
           Case Sloop := (fun s1 transl_s1 s2 transl_s2 => 
                          fun ce tyret nbrk ncnt =>
                             do ts1 <- transl_s1 ce tyret 1%nat 0%nat;
                             do ts2 <- transl_s2 ce tyret 0%nat (S ncnt);
                             OK (Csharpminor.Sblock (Csharpminor.Sloop (Csharpminor.Sseq (Csharpminor.Sblock ts1) ts2)))).
           Case Sbreak := (fun ce tyret nbrk ncnt => OK (Csharpminor.Sexit nbrk)).
           Case Scontinue := (fun ce tyret nbrk ncnt => OK (Csharpminor.Sexit ncnt)).
           Case Sreturn := (fun e => fun ce tyret nbrk ncnt =>
                              match e with
                              | None => OK (Csharpminor.Sreturn None)
                              | Some e => 
                                  do te <- transl_expr e ce;
                                  do te' <- make_cast (Clight.typeof e) tyret te;
                                  OK (Csharpminor.Sreturn (Some te'))
                              end).           
           Case Slabel := (fun lbl s transl_s =>
                           fun ce tyret nbrk ncnt => 
                             do ts <- transl_s ce tyret nbrk ncnt;
                             OK (Csharpminor.Slabel lbl ts)).
           Case Sgoto := (fun lbl =>  
                            fun ce tyret nbrk ncnt =>  
                              OK (Csharpminor.Sgoto lbl)).
      FEnd transl_statement.
            
      
      Definition transl_var (ce: composite_env) (v: ident * type) :=
        do sz <- sizeof ce (snd v); OK (fst v, sz).

      Definition signature_of_function (f: Clight.function) :=
        {| sig_args := map typ_of_type (map snd (Clight.fn_params f));
          sig_res  := rettype_of_type (Clight.fn_return f);
          sig_cc   := Clight.fn_callconv f |}.

      Definition transl_function (ce: composite_env) (f: Clight.function) : res function :=
        do tbody <- transl_statement ce f.(Clight.fn_return) 1%nat 0%nat (Clight.fn_body f);
        do tvars <- mmap (transl_var ce) (Clight.fn_vars f);
        OK (mkfunction
              (signature_of_function f)
              (map fst (Clight.fn_params f))
              tvars
              (map fst (Clight.fn_temps f))
              tbody).

     Definition transl_fundef (ce: composite_env) (id: ident) (f: Clight.fundef) : res fundef :=
       match f with
       | Internal g =>
           do tg <- transl_function ce g; OK(AST.Internal tg)
       | External ef args res cconv =>
           if signature_eq (ef_sig ef) (signature_of_type args res cconv)
           then OK(AST.External ef)
           else Error(msg "Cshmgen.transl_fundef: wrong external signature")
       end.

     (** ** Translation of programs *)

     Definition transl_globvar (id: ident) (ty: type) := OK tt.

     Definition transl_program (p: Clight.program) : res program :=
       transform_partial_program2 (transl_fundef p.(prog_comp_env)) transl_globvar p.
       
     Family Correctness.            
          FInduction transl_step:
            forall S1 t S2, Clight.step ge S1 t S2 ->
            forall T1, match_states S1 T1 ->
            exists T2, plus step tge T1 t T2 /\ match_states S2 T2.
          FProof.
          
          Closing Fact transl_initial_states:
            forall S, Clight.initial_state prog S ->
            exists R, initial_state tprog R /\ match_states S R.
          FProof.
          
          Closing Fact transl_final_states:
            forall S R r,
            match_states S R -> Clight.final_state S r -> final_state R r.
          FProof.
      FEnd Correctness.
   FEnd Cshmgen.
          
   Family Cminor.
       FInductive constant : Type :=
           | Ointconst: int -> constant(* integer constant *)
           | Ofloatconst: float -> constant(* double-precision floating-point constant *)
           | Osingleconst: float32 -> constant(* single-precision floating-point constant *)
           | Olongconst: int64 -> constant(* long integer constant *)
           | Oaddrsymbol: ident -> ptrofs -> constant(* address of the symbol plus the offset *)
           | Oaddrstack: ptrofs -> constant.(* stack pointer plus the given offset *)       

       FInductive expr : Type :=
          | Evar : ident -> expr
          | Econst : constant -> expr.          

       FInductive stmt : Type :=
          | Sskip: stmt
          | Sassign : ident -> expr -> stmt          
          | Sseq: stmt -> stmt -> stmt
          | Sifthenelse: expr -> stmt -> stmt -> stmt
          | Sloop: stmt -> stmt
          | Sblock: stmt -> stmt
          | Sexit: nat -> stmt
          | Sreturn: option expr -> stmt
          | Slabel: label -> stmt -> stmt
          | Sgoto: label -> stmt.

       Record function : Type := mkfunction {
          fn_sig: signature;
          fn_params: list ident;
          fn_vars: list ident;
          fn_stackspace: Z;
          fn_body: stmt
       }.

        Family Semantics.
              Definition genv := Genv.t fundef unit.
              Definition env := PTree.t val.

              FInductive cont: Type :=
                   | Kstop: cont
                   | Kseq: stmt -> cont -> cont
                   | Kblock: cont -> cont.                   
               
              FInductive state: Type :=
                   | State: function -> stmt -> cont -> val -> env -> mem -> state  
                   | Callstate:  fundef -> list val -> cont -> mem -> state                                 
                   | Returnstate: val -> cont -> mem -> state.
               
              FRecursion eval_constant about constant motive (fun (_ : constant) => val -> option val) by _rect.
                  Case Ointconst := (fun n => fun sp => Some (Vint n)). 
                  Case Olongconst := (fun n => fun sp => Some (Vlong n)).
                  Case Ofloatconst := (fun n => fun sp => Some (Vfloat n)).
                  Case Osingleconst := (fun n => fun sp => Some (Vsingle n)).
                  Case Oaddrsymbol := (fun id ofs => fun sp => Some (Genv.symbol_address ge s ofs)).
                  Case Oaddrstack := (fun ofs => fun sp => Some (Val.offset_ptr sp ofs)).
              FEnd eval_constant.                                
               
              FInductive eval_expr : (sp : val) -> (e : env) -> (m : mem) -> expr -> val -> Prop :=
                  | eval_Evar: forall id v,
                        PTree.get id e = Some v ->
                        eval_expr (Evar id) v
                  | eval_Econst: forall cst v,
                        eval_constant sp cst = Some v ->
                        eval_expr (Econst cst) v.              
                  
              FInductive eval_exprlist: list expr -> list val -> Prop :=
                  | eval_Enil:
                      eval_exprlist nil nil
                  | eval_Econs: forall a1 al v1 vl,
                      eval_expr a1 v1 -> eval_exprlist al vl ->
                      eval_exprlist (a1 :: al) (v1 :: vl).
               
               FRecursion call_cont about cont motive (fun (_ : cont) => cont).
                   Case Kstop := Kstop
                   Case Kseq := (fun s c call_cont_c => call_cont_c)
                   Case Kblock := (fun s c call_cont_c => call_cont_c)                   
               FEnd call_cont.
               
               FRecursion is_call_cont about cont motive (fun (_ : cont) => Prop).
                   Case Kstop := True                   
                   Case Kseq := (fun s c call_cont_c => False)
                   Case Kblock := (fun s c call_cont_c => False)                   
               FEnd is_call_cont.
                   
               FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont)). 
                    Case Sskip := (fun lbl k => None).         
                    Case Sassign := (fun id e lbl k => None).
                    Case Sseq := := (fun s1 find_label_s1 s2 find_label_s2 => fun lbl k => 
                                         match find_label_s1 lbl (Kseq s2 k) with 
                                         | Some sk => Some sk 
                                         | None => find_label_s2 lbl k end).
                    Case Sifthenelse := (fun e s1 _ s2 _ lbl k => fun lbl k => 
                                         match find_label_s1 lbl k with 
                                         | Some sk => Some sk 
                                         | None => find_label_s2 lbl k end).
                    Case Sloop := (fun s _ lbl k => fun lbl k => find_label_s lbl (Kseq (Sloop s) k)).
                    Case Sblock := (fun s _ lbl k => find_label_s1 lbl (Kblock k)).
                    Case Slabel := (fun lbl' s find_label_s => fun lbl k => 
                                       if ident_eq lbl lbl' then 
                                       Some(s, k) else find_label_s lbl k).
                    Case Sexit := (fun n lbl k => None)
                    Case Sreturn := (fun _ lbl k => None).
                    Case Sgoto := (fun label lbl k => None).
               FEnd find_label.
               
               (* (sp : val) -> (e : env) -> (m : mem) -> *)
              FInductive step : state -> trace -> state -> Prop :=
                 | step_skip_seq: forall f s k sp e m,
                     step (State f Sskip (Kseq s k) sp e m)
                       E0 (State f s k sp e m)
                 | step_skip_block: forall f k sp e m,
                     step (State f Sskip (Kblock k) sp e m)
                       E0 (State f Sskip k sp e m)
                 | step_skip_call: forall f k sp e m m',
                     is_call_cont k ->
                     Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
                     step (State f Sskip k (Vptr sp Ptrofs.zero) e m)
                       E0 (Returnstate Vundef k m')
                 | step_assign: forall f id a k sp e m v,
                     eval_expr sp e m a v ->
                     step (State f (Sassign id a) k sp e m)
                       E0 (State f Sskip k sp (PTree.set id v e) m)
                 | step_seq: forall f s1 s2 k sp e m,
                     step (State f (Sseq s1 s2) k sp e m)
                       E0 (State f s1 (Kseq s2 k) sp e m)
                 | step_ifthenelse: forall f a s1 s2 k sp e m v b,
                     eval_expr sp e m a v ->
                     Val.bool_of_val v b ->
                     step (State f (Sifthenelse a s1 s2) k sp e m)
                       E0 (State f (if b then s1 else s2) k sp e m)
                 | step_loop: forall f s k sp e m,
                     step (State f (Sloop s) k sp e m)
                       E0 (State f s (Kseq (Sloop s) k) sp e m)
                 | step_block: forall f s k sp e m,
                     step (State f (Sblock s) k sp e m)
                       E0 (State f s (Kblock k) sp e m)
                 | step_exit_seq: forall f n s k sp e m,
                     step (State f (Sexit n) (Kseq s k) sp e m)
                       E0 (State f (Sexit n) k sp e m)
                 | step_exit_block_0: forall f k sp e m,
                     step (State f (Sexit O) (Kblock k) sp e m)
                       E0 (State f Sskip k sp e m)
                 | step_exit_block_S: forall f n k sp e m,
                     step (State f (Sexit (S n)) (Kblock k) sp e m)
                       E0 (State f (Sexit n) k sp e m)
                 | step_return_0: forall f k sp e m m',
                    Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
                    step (State f (Sreturn None) k (Vptr sp Ptrofs.zero) e m)
                      E0 (Returnstate Vundef (call_cont k) m')
                 | step_return_1: forall f a k sp e m v m',
                     eval_expr (Vptr sp Ptrofs.zero) e m a v ->
                     Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
                     step (State f (Sreturn (Some a)) k (Vptr sp Ptrofs.zero) e m)
                      E0 (Returnstate v (call_cont k) m')
                 | step_label: forall f lbl s k sp e m,
                    step (State f (Slabel lbl s) k sp e m)
                      E0 (State f s k sp e m)
                 | step_goto: forall f lbl k sp e m s' k',
                    find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
                    step (State f (Sgoto lbl) k sp e m)
                      E0 (State f s' k' sp e m).
          FEnd Semantics.
   FEnd Cminor.

    (* RISC-V *)
   Family Asm.
      (* Operations *)
      FInductive condition : Type :=
        | Ccomp : comparison -> condition.       (**r signed integer comparison *)

(** Arithmetic and logical operations.  In the descriptions, [rd] is the
  result of the operation and [r1], [r2], etc, are the arguments. *)

     FInductive operation : Type :=
        | Omove                    (**r [rd = r1] *)
        | Ointconst (n: int)       (**r [rd] is set to the given integer constant *)
        | Olongconst (n: int64)    (**r [rd] is set to the given integer constant *)
        | Oaddrsymbol (id: ident) (ofs: ptrofs)  (**r [rd] is set to the address of the symbol plus the given offset *)
        | Oaddrstack (ofs: ptrofs) (**r [rd] is set to the stack pointer plus the given offset *)
      (*c 32-bit integer arithmetic: *)
        | Ocast8signed             (**r [rd] is 8-bit sign extension of [r1] *)
        | Ocast16signed            (**r [rd] is 16-bit sign extension of [r1] *)
        | Oadd                     (**r [rd = r1 + r2] *)
        | Oaddimm (n: int)         (**r [rd = r1 + n] *)
        | Oneg                     (**r [rd = - r1]   *)                     
        | Osub                     (**r [rd = r1 - r2] *)
        | Omul                     (**r [rd = r1 * r2] *)
        | Odiv                     (**r [rd = r1 / r2] (signed) *)
      (*c Boolean tests: *)
        | Ocmp (cond: condition).  (**r [rd = 1] if condition holds, [rd = 0] otherwise. *) 

      
      FRecursion eval_operation about operation motive (fun (_ : operation) => condition -> list val -> mem -> option val) by _rect.
          Case Ccomp := (fun c => fun ge sp vl m => 
                        match vl with 
                        | v1 :: v2 :: nil => Val.cmp_bool c v1 v2
                        | _ => None end).
      FEnd eval_operation.

     FRecursion eval_operation about operation motive (fun (_ : operation) => Genv.t -> val -> list val -> mem -> option val) by _rect.
        Case Omove := (fun ge sp vl m => 
                    match vl with 
                    | v1 :: nil => Some v1 
                    | _ => None end).
        Case Ointconst := (fun n => fun ge sp vl m =>  
                           match vl with 
                           | nil => (Some (Vint n)
                           | _ => None end).
        Case Olongconst := (fun n => fun ge sp vl m =>  
                           match vl with 
                           | nil => (Some (Vlong n)
                           | _ => None end).
        Case Oaddrsymbol := (fun s ofs => fun ge sp vl m =>
                           match vl with 
                           | nil => Some (Genv.symbol_address genv s ofs)
                           | _ => None end).
        Case Oaddrstack := (fun ofs => fun ge sp vl m =>
                           match vl with 
                           | nil => Some (Val.offset_ptr sp ofs)
                           | _ => None end)
        Case Ocast8signed := (fun ge sp vl m =>
                           match vl with 
                           | v1 :: nil => Some (Val.sign_ext 8 v1)
                           | _ => None end).
        Case Ocast16signed := (fun ge sp vl m =>
                           match vl with 
                           | v1 :: nil => Some (Val.sign_ext 16 v1)
                           | _ => None end)
        Case Oadd := (fun ge sp vl m =>
                  match vl with 
                  | v1 :: v2 :: nil => Some(Val.add v1 v2)
                  | _ => None end).
        Case Oaddimm := (fun n => fun ge sp vl m =>
                  match vl with 
                  | v1 :: nil => Some(Val.add v1 (Vint n))
                  | _ => None end).
        Case Oneg := (fun ge sp vl m =>
                  match vl with 
                  | v1 :: nil => Some(Val.neg v1)
                  | _ => None end).
        Case Osub := (fun ge sp vl m =>
                  match vl with 
                  | v1 :: v2 :: nil => Some(Val.sub v1 v2)
                  | _ => None end).
        Case Omul := (fun ge sp vl m =>
                  match vl with 
                  | v1 :: v2 :: nil => Some(Val.mul v1 v2)
                  | _ => None end).
        Case Odiv := (fun ge sp vl m =>
                  match vl with 
                  | v1 :: v2 :: nil => Some(Val.divs v1 v2)
                  | _ => None end).
        Case Ocmp := (fun c => fun ge sp vl m =>
                  match vl with 
                  | v1 :: v2 :: nil =>  Some (Val.of_optbool (eval_condition c vl m))
                  | _ => None end).
     FEnd eval_operation.

    FRecursion shift_stack_operation about operation motive (fun (_ : operation) => Z -> operation) by _rect.
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
    FEnd shift_stack_operation.
      
     Inductive ireg: Type :=
         | X1:  ireg | X2:  ireg | X3:  ireg | X4:  ireg | X5:  ireg
         | X6:  ireg | X7:  ireg | X8:  ireg | X9:  ireg | X10: ireg
         | X11: ireg | X12: ireg | X13: ireg | X14: ireg | X15: ireg
         | X16: ireg | X17: ireg | X18: ireg | X19: ireg | X20: ireg
         | X21: ireg | X22: ireg | X23: ireg | X24: ireg | X25: ireg
         | X26: ireg | X27: ireg | X28: ireg | X29: ireg | X30: ireg
         | X31: ireg.

     Inductive ireg0: Type :=
        | X0: ireg0 | X: ireg -> ireg0.
      
      (* Non-extensible inductive *)
     Inductive preg: Type :=
         | IR: ireg -> preg                    (**r integer registers *)
         | FR: freg -> preg                    (**r double-precision float registers *)
         | PC: preg.                           (**r program counter *)
      
     Notation "'SP'" := X2 (only parsing) : asm.
     Notation "'RA'" := X1 (only parsing) : asm.
      
      (* Non-extensible inductive *)
     Inductive offset : Type :=
        | Ofsimm (ofs: ptrofs)
        | Ofslow (id: ident) (ofs: ptrofs).

     Definition label := positive.

     FInductive instruction : Type :=
         | Pmv     (rd: ireg) (rs: ireg)                    (**r integer move *)
       
       (** 32-bit integer register-immediate instructions *)
         | Paddiw  (rd: ireg) (rs: ireg0) (imm: int)        (**r add immediate *)
         | Psltiw  (rd: ireg) (rs: ireg0) (imm: int)        (**r set-less-than immediate *)
         | Psltiuw (rd: ireg) (rs: ireg0) (imm: int)        (**r set-less-than unsigned immediate *)
         | Pandiw  (rd: ireg) (rs: ireg0) (imm: int)        (**r and immediate *)
         | Poriw   (rd: ireg) (rs: ireg0) (imm: int)        (**r or immediate *)
         | Pxoriw  (rd: ireg) (rs: ireg0) (imm: int)        (**r xor immediate *)
         | Pslliw  (rd: ireg) (rs: ireg0) (imm: int)        (**r shift-left-logical immediate *)
         | Psrliw  (rd: ireg) (rs: ireg0) (imm: int)        (**r shift-right-logical immediate *)
         | Psraiw  (rd: ireg) (rs: ireg0) (imm: int)        (**r shift-right-arith immediate *)
         | Pluiw   (rd: ireg)             (imm: int)        (**r load upper-immediate *)
       (** 32-bit integer register-register instructions *)
         | Paddw   (rd: ireg) (rs1 rs2: ireg0)              (**r integer addition *)
         | Psubw   (rd: ireg) (rs1 rs2: ireg0)              (**r integer subtraction *)
                   
         | Pmulw   (rd: ireg) (rs1 rs2: ireg0)              (**r integer multiply low *)
         | Pmulhw  (rd: ireg) (rs1 rs2: ireg0)              (**r integer multiply high signed *)
         | Pmulhuw (rd: ireg) (rs1 rs2: ireg0)              (**r integer multiply high unsigned *)
         | Pdivw   (rd: ireg) (rs1 rs2: ireg0)              (**r integer division *)
         | Pdivuw  (rd: ireg) (rs1 rs2: ireg0)              (**r unsigned integer division *)
         | Premw   (rd: ireg) (rs1 rs2: ireg0)              (**r integer remainder *)
         | Premuw  (rd: ireg) (rs1 rs2: ireg0)              (**r unsigned integer remainder *)
         | Psltw   (rd: ireg) (rs1 rs2: ireg0)              (**r set-less-than *)
         | Psltuw  (rd: ireg) (rs1 rs2: ireg0)              (**r set-less-than unsigned *)
         | Pseqw   (rd: ireg) (rs1 rs2: ireg0)              (**r [rd <- rs1 == rs2] (pseudo) *)
         | Psnew   (rd: ireg) (rs1 rs2: ireg0)              (**r [rd <- rs1 != rs2] (pseudo) *)
         | Pandw   (rd: ireg) (rs1 rs2: ireg0)              (**r bitwise and *)
         | Porw    (rd: ireg) (rs1 rs2: ireg0)              (**r bitwise or *)
         | Pxorw   (rd: ireg) (rs1 rs2: ireg0)              (**r bitwise xor *)
         | Psllw   (rd: ireg) (rs1 rs2: ireg0)              (**r shift-left-logical *)
         | Psrlw   (rd: ireg) (rs1 rs2: ireg0)              (**r shift-right-logical *)
         | Psraw   (rd: ireg) (rs1 rs2: ireg0)              (**r shift-right-arith *)    


        (* Loads and stores *)
        | Plb     (rd: ireg) (ra: ireg) (ofs: offset)     (**r load signed int8 *)
        | Plbu    (rd: ireg) (ra: ireg) (ofs: offset)     (**r load unsigned int8 *)
        | Plh     (rd: ireg) (ra: ireg) (ofs: offset)     (**r load signed int16 *)
        | Plhu    (rd: ireg) (ra: ireg) (ofs: offset)     (**r load unsigned int16 *)
        | Plw     (rd: ireg) (ra: ireg) (ofs: offset)     (**r load int32 *)
        | Plw_a   (rd: ireg) (ra: ireg) (ofs: offset)     (**r load any32 *)
        | Pld     (rd: ireg) (ra: ireg) (ofs: offset)     (**r load int64 *)
        | Pld_a   (rd: ireg) (ra: ireg) (ofs: offset)     (**r load any64 *)

        | Psb     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store int8 *)
        | Psh     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store int16 *)
        | Psw     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store int32 *)
        | Psw_a   (rs: ireg) (ra: ireg) (ofs: offset)     (**r store any32 *)
        | Psd     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store int64 *)
        | Psd_a   (rs: ireg) (ra: ireg) (ofs: offset)     (**r store any64 *)                         
      
      (* Unconditional jumps.  Links are always to X1/RA. *)
       | Pj_l    (l: label)                              (**r jump to label *)
       | Pj_r    (r: ireg)     (sg: signature)           (**r jump register *)
     
       (* Conditional branches, 32-bit comparisons *)
       | Pbeqw   (rs1 rs2: ireg0) (l: label)             (**r branch-if-equal *)
       | Pbnew   (rs1 rs2: ireg0) (l: label)             (**r branch-if-not-equal signed *)
       | Pbltw   (rs1 rs2: ireg0) (l: label)             (**r branch-if-less signed *)
       | Pbltuw  (rs1 rs2: ireg0) (l: label)             (**r branch-if-less unsigned *)
       | Pbgew   (rs1 rs2: ireg0) (l: label)             (**r branch-if-greater-or-equal signed *)
       | Pbgeuw  (rs1 rs2: ireg0) (l: label)             (**r branch-if-greater-or-equal unsigned *)

      (* Pseudo-instructions *)
       | Plabel  (lbl: label)                            (**r define a code label *)    
       | Pnop : instruction                             (**r nop instruction *)       
                  
     Definition code := list instruction.
     Record function : Type := mkfunction { fn_sig: signature; fn_code: code }.
      
     Family Semantics. 
          Definition regset := Pregmap.t val.
          Definition genv := Genv.t fundef unit.
          
          Inductive outcome: Type :=
             | Next:  regset -> mem -> outcome
             | Stuck: outcome.
          
          Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
            match c with
            | nil => None
            | instr :: c' =>
                if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
            end.

          Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
            match label_pos lbl 0 (fn_code f) with
            | None => Stuck
            | Some pos =>
                match rs#PC with
                | Vptr b ofs => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
                | _          => Stuck
                end
            end.

          Definition eval_branch (f: function) (l: label) (rs: regset) (m: mem) (res: option bool) : outcome :=
            match res with
              | Some true  => goto_label f l rs m
              | Some false => Next (nextinstr rs) m
              | None => Stuck
            end.

          Definition exec_load (chunk: memory_chunk) (rs: regset) (m: mem)
                              (d: preg) (a: ireg) (ofs: offset) :=
            match Mem.loadv chunk m (Val.offset_ptr (rs a) (eval_offset ofs)) with
            | None => Stuck
            | Some v => Next (nextinstr (rs#d <- v)) m
            end.

          Definition exec_store (chunk: memory_chunk) (rs: regset) (m: mem)
                                (s: preg) (a: ireg) (ofs: offset) :=
            match Mem.storev chunk m (Val.offset_ptr (rs a) (eval_offset ofs)) (rs s) with
            | None => Stuck
            | Some m' => Next (nextinstr rs) m'
            end.
          
          FRecursion exec_instr about instruction motive (fun (_ : instruction) => function -> regset -> mem -> outcome).
              Case Pmv := (fun d s => fun f rs m =>  Next (nextinstr (rs#d <- (rs#s))) m).
              Case Paddiw := (fun d s i => fun f rs m =>  Next (nextinstr (rs#d <- (Val.add rs##s (Vint i)))) m).
              Case Psltiw := (fun d s i => fun f rs m => Next (nextinstr (rs#d <- (Val.cmp Clt rs##s (Vint i)))) m).
              Case Psltiuw := (fun d s i => fun f rs m =>  Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Clt rs##s (Vint i)))) m).
              Case Pandiw := (fun d s i => fun f rs m =>  Next (nextinstr (rs#d <- (Val.and rs##s (Vint i))) m).
              Case Poriw := (fun d s i => fun f rs m =>  Next (nextinstr (rs#d <- (Val.or rs##s (Vint i))) m).
              Case Pxoriw := (fun d s i => fun f rs m =>  Next (nextinstr (rs#d <- (Val.xor rs##s (Vint i))) m).
              Case Pslliw := (fun d s i => fun f rs m =>  Next (nextinstr (rs#d <- (Val.shl rs##s (Vint i))) m).
              Case Psrliw := (fun d s i => fun f rs m =>  Next (nextinstr (rs#d <- (Val.shru rs##s (Vint i))) m).
              Case Psraiw := (fun d s i => fun f rs m =>  Next (nextinstr (rs#d <- (Val.shr rs##s (Vint i))) m).
              Case Pluiw := (fun d i => fun f rs m =>  Next (nextinstr (rs#d <- (Vint (Int.shl i (Int.repr 12))))) m).

              Case Paddw := (fun d s1 s2 => fun f rs m =>  Next (nextinstr (rs#d <- (Val.add rs##s1 rs##s2)) m).
              Case Psubw := (fun d s1 s2 => fun f rs m =>  Next (nextinstr (rs#d <- (Val.sub rs##s1 rs##s2)) m).
              Case Pmulw := (fun d s1 s2 => fun f rs m =>  Next (nextinstr (rs#d <- (Val.mul rs##s1 rs##s2)) m).
              Case Pmulhw := (fun d s1 s2 => fun f rs m =>  Next (nextinstr (rs#d <- (Val.mulhs rs##s1 rs##s2)) m).
              Case Pmulhuw := (fun d s1 s2 => fun f rs m =>  Next (nextinstr (rs#d <- (Val.mulhu rs##s1 rs##s2)) m).
              Case Pdivw := (fun d s1 s2 => fun f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.divs rs##s1 rs##s2)))) m).
              Case Pdivuw := (fun d s1 s2 => fun f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.divu rs##s1 rs##s2))) m).
              Case Premw := (fun d s1 s2 => fun f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.mods rs##s1 rs##s2))) m).
              Case Premuw := (fun d s1 s2 => fun f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.modu rs##s1 rs##s2))) m).
              Case Psltw := (fun d s1 s2 => fun f rs m =>  Next (nextinstr (rs#d <- (Val.cmp Clt rs##s1 rs##s2)) m).
              Case Psltuw := (fun d s1 s2 => fun f rs m =>  Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Clt rs##s1 rs##s2)) m).
              Case Pseqw := (fun d s1 s2 => fun f rs m =>  Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Ceq rs##s1 rs##s2))) m).
              Case Psnew := (fun d s1 s2 => fun f rs m =>  Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Cne rs##s1 rs##s2))) m).
              Case Pandw := (fun d s1 s2 => fun f rs m =>  Next (nextinstr (rs#d <- (Val.and rs##s1 rs##s2)) m).
              Case Porw := (fun d s1 s2 => fun f rs m =>  Next (nextinstr (rs#d <- (Val.or rs##s1 rs##s2)) m).
              Case Pxorw := (fun d s1 s2 => fun f rs m =>  Next (nextinstr (rs#d <- (Val.xor rs##s1 rs##s2)) m).
              Case Psllw := (fun d s1 s2 => fun f rs m =>  Next (nextinstr (rs#d <- (Val.shl rs##s1 rs##s2)) m).
              Case Psrlw := (fun d s1 s2 => fun f rs m =>  Next (nextinstr (rs#d <- (Val.shru rs##s1 rs##s2)) m).
              Case Psraw := (fun d s1 s2 => fun f rs m =>  Next (nextinstr (rs#d <- (Val.shr rs##s1 rs##s2)) m).

              Case Pbeqw := (fun s1 s2 l => fun f rs m => 
                              eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Ceq rs##s1 rs##s2)).
              Case Pbnew := (fun s1 s2 l => fun f rs m => 
                              eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Cne rs##s1 rs##s2)).
              Case Pbltw := (fun s1 s2 l => fun f rs m => 
                              eval_branch f l rs m (Val.cmp_bool Clt rs##s1 rs##s2)).
              Case Pbltuw := (fun s1 s2 l => fun f rs m => 
                              eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Clt rs##s1 rs##s2)).
              Case Pbgew := (fun s1 s2 l => fun f rs m => 
                              eval_branch f l rs m (Val.cmp_bool Cge rs##s1 rs##s2)).
              Case Pbgeuw := (fun s1 s2 l => fun f rs m => 
                              eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Cge rs##s1 rs##s2)).
              Case Plabel := (fun lbl => fun f rs m =>  Next (nextinstr rs) m).

              (* Loads and Stores *)
              Case Plb := (fun d a ofs => fun f rs m => 
                             exec_load Mint8signed rs m d a ofs).
              Case Plbu := (fun d a ofs => fun f rs m => 
                             exec_load Mint8unsigned rs m d a ofs).
              Case Plh := (fun d a ofs => fun f rs m => 
                             exec_load Mint16signed rs m d a ofs).
              Case Plhu := (fun d a ofs => fun f rs m => 
                             exec_load Mint16unsigned rs m d a ofs).
              Case Plw := (fun d a ofs => fun f rs m => 
                             exec_load Mint32 rs m d a ofs).
              Case Plw_a := (fun d a ofs => fun f rs m => 
                             exec_load Many32 rs m d a ofs).
              Case Pld := (fun d a ofs => fun f rs m => 
                             exec_load Mint64 rs m d a ofs).
              Case Pld_a := (fun d a ofs => fun f rs m => 
                             exec_load Many64 rs m d a ofs).
              Case Psb := (fun s a ofs => fun f rs m => 
                             exec_store Mint8signed rs m s a ofs).
              Case Psh := (fun s a ofs => fun f rs m => 
                             exec_store Mint16signed rs m s a ofs).
              Case Psw := (fun s a ofs => fun f rs m => 
                             exec_store Mint32 rs m s a ofs).
              Case Psw_a := (fun s a ofs => fun f rs m => 
                             exec_store Many32 rs m s a ofs).
              Case Psd := (fun s a ofs => fun f rs m => 
                             exec_store Mint64 rs m s a ofs).
              Case Psd_a := (fun s a ofs => fun f rs m => 
                             exec_store Many64 rs m s a ofs).

              Case Pj_l := (fun l => fun f rs m =>  goto_label f l rs m).
              (* Jump to a regiser *)
              Case Pj_r := (fun r sg => fun f rs m => Next (rs#PC <- (rs#r)) m).

              (** The following instructions and directives are not generated directly by Asmgen,
                   so we do not model them. *)
              Case Pnop := (fun f rs m => Stuck).
          FEnd exec_instr.

          (** Execution of the instruction at [rs PC]. *)

        Inductive state: Type :=
          | State: regset -> mem -> state.

        FInductive step: state -> trace -> state -> Prop :=
          | exec_step_internal:
              forall b ofs f i rs m rs' m',
              rs PC = Vptr b ofs ->
              Genv.find_funct_ptr ge b = Some (Internal f) ->
              find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
              exec_instr f i rs m = Next rs' m' ->
              step (State rs m) E0 (State rs' m'). 
        
        Inductive initial_state (p: program): state -> Prop :=
          | initial_state_intro: forall m0,
              let ge := Genv.globalenv p in
              let rs0 :=
                (Pregmap.init Vundef)
                # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
                # SP <- Vnullptr
                # RA <- Vnullptr in
              Genv.init_mem p = Some m0 ->
              initial_state p (State rs0 m0).

        Inductive final_state: state -> int -> Prop :=
          | final_state_intro: forall rs m r,
              rs PC = Vnullptr ->
              rs X10 = Vint r ->
              final_state (State rs m) r.

      FEnd Semantics.                   
   FEnd Asm.

   (* Processor dependent intermediate representations *)

   Family CminorSel.
       FInductive expr : Type :=
          | Evar : ident -> expr          
          | Econdition : condexpr -> expr -> expr -> expr
          | Eop : operation -> exprlist -> expr
          | Elet : expr -> expr -> expr
          | Eletvar : nat -> expr          
       with exprlist : Type :=
         | Enil: exprlist
         | Econs: expr -> exprlist -> exprlist
       with condexpr : Type :=
         | CEcond : Asm.condition -> exprlist -> condexpr
         | CEcondition : condexpr -> condexpr -> condexpr -> condexpr
         | CElet: expr -> condexpr -> condexpr.
       
       FInductive stmt : Type :=
          | Sskip: stmt
          | Sassign : ident -> expr -> stmt          
          | Sseq: stmt -> stmt -> stmt
          | Sifthenelse: condexpr -> stmt -> stmt -> stmt
          | Sloop: stmt -> stmt
          | Sblock: stmt -> stmt
          | Sexit: nat -> stmt
          | Sreturn: option expr -> stmt
          | Slabel: label -> stmt -> stmt
          | Sgoto: label -> stmt.
       
        Record function : Type := mkfunction {
          fn_sig: signature;
          fn_params: list ident;
          fn_vars: list ident;
          fn_stackspace: Z;
          fn_body: stmt
        }.

       Family Semantics. 
          Definition genv := Genv.t fundef unit.
          Definition letenv := list val.
           
          FInductive cont : Type := 
             | Kstop: cont
             | Kseq: stmt -> cont -> cont
             | Kblock: cont -> cont.             

          FRecursion call_cont about cont motive (fun (_ : cont) => cont).
              Case Kstop := Kstop.
              Case Kseq := (fun s k call_cont_k => call_cont_k).                
              Case Kblock := (fun k call_cont_k => call_cont_k).              
          FEnd call_cont.
            
          FRecursion is_call_cont about cont motive (fun (_ : cont) => Prop).
             Case Kstop := True.
             Case Kseq := (fun s k _ => False).                
             Case Kblock := (fun k _ => False).              
          FEnd is_call_cont.

          FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont)). 
              Case Sskip := (fun lbl k => None)
              Case Sassign := (fun id e lbl k => None)
              Case Sseq := (fun s1 find_label_s1 s2 find_label_s2 => fun lbl k => 
                                       match find_label_s1 lbl (Kseq s2 k) with 
                                       | Some sk => Some sk 
                                       | None => find_label_s2 lbl k end).
              Case Sifthenelse := (fun e s1 _ s2 _ => fun lbl k => 
                                       match find_label_s1 lbl k with 
                                       | Some sk => Some sk 
                                       | None => find_label_s2 lbl k end).
              Case Sloop := (fun s1 find_label_s1 => fun lbl k => 
                                       find_label_s1 lbl (Kseq (Sloop s1) k)).
              Case Sblock := (fun s find_label_s1  => fun lbl k => find_label_s1 lbl (Kblock k)).
              Case Sexit := (fun n lbl k => None).                
              Case Sreturn := (fun _ lbl k => None).
              Case Slabel := (fun lbl' s find_label_s => fun lbl k => 
                                     if ident_eq lbl lbl' then 
                                     Some(s, k) else find_label_s lbl k).
              Case Sgoto := (fun label lbl k => None).
          FEnd find_label.
           
          FInductive state: Type :=
               | State : function -> stmt -> cont -> val -> env -> mem -> state                   
               | Callstate : fundef -> list val -> cont -> mem -> state                   
               | Returnstate : val -> cont -> mem -> state.
           
          FInductive eval_expr: letenv -> expr -> val -> Prop :=
              | eval_Evar: forall le id v,
                  PTree.get id e = Some v ->
                  eval_expr le (Evar id) v              
              | eval_Econdition: forall le a b c va v,
                  eval_condexpr le a va ->
                  eval_expr le (if va then b else c) v ->
                  eval_expr le (Econdition a b c) v
              | eval_Elet: forall le a b v1 v2,
                  eval_expr le a v1 ->
                  eval_expr (v1 :: le) b v2 ->
                  eval_expr le (Elet a b) v2
              | eval_Eletvar: forall le n v,
                  nth_error le n = Some v ->
                  eval_expr le (Eletvar n) v              
          with eval_exprlist: letenv -> exprlist -> list val -> Prop :=
             | eval_Enil: forall le,
                 eval_exprlist le Enil nil
             | eval_Econs: forall le a1 al v1 vl,
                 eval_expr le a1 v1 -> eval_exprlist le al vl ->
                 eval_exprlist le (Econs a1 al) (v1 :: vl)
          with eval_condexpr: letenv -> condexpr -> bool -> Prop :=
             | eval_CEcond: forall le cond al vl vb,
                 eval_exprlist le al vl ->
                 Asm.eval_condition cond vl m = Some vb ->
                 eval_condexpr le (CEcond cond al) vb
             | eval_CEcondition: forall le a b c va v,
                 eval_condexpr le a va ->
                 eval_condexpr le (if va then b else c) v ->
                 eval_condexpr le (CEcondition a b c) v
             | eval_CElet: forall le a b v1 v2,
                 eval_expr le a v1 ->
                 eval_condexpr (v1 :: le) b v2 ->
                 eval_condexpr le (CElet a b) v2.
           
          FInductive step: state -> trace -> state -> Prop :=
             | step_skip_seq: forall f s k sp e m,
                   step (State f Sskip (Kseq s k) sp e m)
                     E0 (State f s k sp e m)
             | step_skip_block: forall f k sp e m,
                   step (State f Sskip (Kblock k) sp e m)
                     E0 (State f Sskip k sp e m)
             | step_skip_call: forall f k sp e m m',
                   is_call_cont k ->
                   Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
                   step (State f Sskip k (Vptr sp Ptrofs.zero) e m)
                     E0 (Returnstate Vundef k m')

             | step_assign: forall f id a k sp e m v,
                   eval_expr sp e m nil a v ->
                   step (State f (Sassign id a) k sp e m)
                     E0 (State f Sskip k sp (PTree.set id v e) m)

             | step_seq: forall f s1 s2 k sp e m,
                   step (State f (Sseq s1 s2) k sp e m)
                     E0 (State f s1 (Kseq s2 k) sp e m)

             | step_ifthenelse: forall f c s1 s2 k sp e m b,
                   eval_condexpr sp e m nil c b ->
                   step (State f (Sifthenelse c s1 s2) k sp e m)
                     E0 (State f (if b then s1 else s2) k sp e m)

             | step_loop: forall f s k sp e m,
                   step (State f (Sloop s) k sp e m)
                     E0 (State f s (Kseq (Sloop s) k) sp e m)

             | step_block: forall f s k sp e m,
                   step (State f (Sblock s) k sp e m)
                     E0 (State f s (Kblock k) sp e m)

             | step_exit_seq: forall f n s k sp e m,
                   step (State f (Sexit n) (Kseq s k) sp e m)
                     E0 (State f (Sexit n) k sp e m)
             | step_exit_block_0: forall f k sp e m,
                   step (State f (Sexit O) (Kblock k) sp e m)
                     E0 (State f Sskip k sp e m)
             | step_exit_block_S: forall f n k sp e m,
                   step (State f (Sexit (S n)) (Kblock k) sp e m)
                     E0 (State f (Sexit n) k sp e m)

             | step_return_0: forall f k sp e m m',
                   Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
                   step (State f (Sreturn None) k (Vptr sp Ptrofs.zero) e m)
                     E0 (Returnstate Vundef (call_cont k) m')
             | step_return_1: forall f a k sp e m v m',
                   eval_expr (Vptr sp Ptrofs.zero) e m nil a v ->
                   Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
                   step (State f (Sreturn (Some a)) k (Vptr sp Ptrofs.zero) e m)
                     E0 (Returnstate v (call_cont k) m')

             | step_label: forall f lbl s k sp e m,
                   step (State f (Slabel lbl s) k sp e m)
                     E0 (State f s k sp e m)

             | step_goto: forall f lbl k sp e m s' k',
                   find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
                   step (State f (Sgoto lbl) k sp e m)
                     E0 (State f s' k' sp e m).
       FEnd Semantics.
    FEnd CminorSel.   

   Family RTL.
       Definition node := positive.
      
       FInductive instruction: Type :=
          | Inop: node -> instruction
          | Iop:Asm.operation -> list reg -> reg -> node -> instruction          
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
       
      Family Semantics. 
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
      FEnd Semantics.
   FEnd RTL.

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
       
      Family Semantics.
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
       FEnd Semantics.
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
       
       Family Semantics.
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
       FEnd Semantics.
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

        Family Semantics.
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
        FEnd Semantics.
   FEnd Mach.

  (* C -> Clight *)
   Family SimplExpr.
      Inductive destination : Type :=
        | For_val
        | For_effects
        | For_set (sd: set_destination).

      Definition finish (dst: destination) (sl: list statement) (a: expr) :=
        match dst with
        | For_val => (sl, a)
        | For_effects => (sl, a)
        | For_set sd => (sl ++ do_set sd a, a)
        end.
     
      FRecursion transl_expr about C.expr motive (fun (_ : C.expr) => destination -> mon (list Clight.statement * Clight.expr)). 
          Case Etempvar := (fun id ty => fun dst => ret (finish dst nil (Clight.Etempvar id ty))).
          Case EVal := (fun v ty => fun dst => 
                             match v with 
                              | Vint n => ret (finish dst nil (Clight.Econst_int n ty)) 
                              | Vlong n => ret (finish dst nil (Clight.Econst_long n ty))
                              | Vfloat n => ret (finish dst nil (Clight.Econst_float n ty))
                              | Vsingle n => ret (finish dst nil (Clight.Econst_single n ty))
                              | _ =>  error (msg "SimplExpr.transl_expr: Eval"))
          Case Ecast := (fun r ty => fun dst => 
                            do (sl1, a1) <- transl_expr For_val r;
                            match dst with
                            | For_val | For_set _ =>
                                do t <- gensym ty;
                                ret (finish dst (sl1) (Clight.Ecast a1 ty))
                            | For_effects =>
                                transl_expr For_effects r
                            end).
          Case Eassign := (fun l r ty => fun dst => 
                            do (sl1, a1) <- transl_expr For_val l;
                            do (sl2, a2) <- transl_expr For_val r;
                            do bf <- is_bitfield_access a1;
                            let ty1 := C.typeof l in
                            let ty2 := C.typeof r in
                            match dst with
                            | For_val | For_set _ =>
                                do t <- gensym ty1;
                                ret (finish dst
                                        (sl1 ++ sl2 ++ Clight.Sset t (Clight.Ecast a2 ty1) :: make_assign bf a1 (Clight.Etempvar t ty1) :: nil)
                                        (make_assign_value bf (Clight.Etempvar t ty1)))
                            | For_effects =>
                                ret (sl1 ++ sl2 ++ make_assign bf a1 a2 :: nil,
                                    dummy_expr)
                            end).
          Case Eassignop := (fun op l r tyres ty => fun dst => 
                            let ty1 := C.typeof l in
                            do (sl1, a1) <- transl_expr For_val l;
                            do (sl2, a2) <- transl_expr For_val r;
                            do (sl3, a3) <- transl_valof ty1 a1;
                            do bf <- is_bitfield_access a1;
                            match dst with
                            | For_val | For_set _ =>
                                do t <- gensym ty1;
                                ret (finish dst
                                        (sl1 ++ sl2 ++ sl3 ++
                                        Clight.Sset t (Clight.Ecast (Clight.Ebinop op a3 a2 tyres) ty1) ::
                                        make_assign bf a1 (Clight.Etempvar t ty1) :: nil)
                                        (make_assign_value bf (Clight.Etempvar t ty1)))
                            | For_effects =>
                                ret (sl1 ++ sl2 ++ sl3 ++ make_assign bf a1 (Clight.Ebinop op a3 a2 tyres) :: nil,
                                    dummy_expr)
                            end).
          Case Epostincr := (fun id l ty => fun dst => 
                            let ty1 := C.typeof l in
                            do (sl1, a1) <- transl_expr For_val l;
                            do bf <- is_bitfield_access a1;
                            match dst with
                            | For_val | For_set _ =>
                                do t <- gensym ty1;
                                ret (finish dst
                                        (sl1 ++ make_set bf t a1 ::
                                        make_assign bf a1 (transl_incrdecr id (Clight.Etempvar t ty1) ty1) :: nil)
                                        (Clight.Etempvar t ty1))
                            | For_effects =>
                                do (sl2, a2) <- transl_valof ty1 a1;
                                ret (sl1 ++ sl2 ++ make  assign bf a1 (transl_incrdecr id a2 ty1) :: nil,
                                    dummy_expr) 
                            end).
          Case Ecomma := (fun r1 r2 ty => fun dst => 
                            do (sl1, a1) <- transl_expr For_effects r1;
                            do (sl2, a2) <- transl_expr dst r2;
                            ret (sl1 ++ sl2, a2)).
          Case Econdition := (fun r1 r2 r3 ty => fun dst => 
                            do (sl1, a1) <- transl_expr For_val r1;
                            match dst with
                            | For_val =>
                                do t <- gensym ty;
                                let sd := SDbase ty ty t in
                                do (sl2, a2) <- transl_expr (For_set sd) r2;
                                do (sl3, a3) <- transl_expr (For_set sd) r3;
                                ret (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil,
                                    Clight.Etempvar t ty)
                            | For_effects =>
                                do (sl2, a2) <- transl_expr For_effects r2;
                                do (sl3, a3) <- transl_expr For_effects r3;
                                ret (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil,
                                    dummy_expr)
                            | For_set sd =>
                                do t <- temp_for_sd ty sd;
                                let sd' := SDcons ty ty t sd in
                                do (sl2, a2) <- transl_expr (For_set sd') r2;
                                do (sl3, a3) <- transl_expr (For_set sd') r3;
                                ret (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil,
                                    dummy_expr)
                            end).
          Case Eseqor := (fun r1 r2 ty => fun dst => 
                            do (sl1, a1) <- transl_expr For_val r1;
                            match dst with
                            | For_val =>
                                do t <- gensym ty;
                                let sd := SDbase type_bool ty t in
                                do (sl2, a2) <- transl_expr (For_set sd) r2;
                                ret (sl1 ++
                                    makeif a1 (Clight.Sset t (Clight.Econst_int Int.one ty)) (makeseq sl2) :: nil,
                                    Clight.Etempvar t ty)
                            | For_effects =>
                                do (sl2, a2) <- transl_expr For_effects r2;
                                ret (sl1 ++ makeif a1 Clight.Sskip (makeseq sl2) :: nil, dummy_expr)
                            | For_set sd =>
                                do t <- temp_for_sd ty sd;
                                let sd' := SDcons type_bool ty t sd in
                                do (sl2, a2) <- transl_expr (For_set sd') r2;
                                ret (sl1 ++
                                    makeif a1 (makeseq (do_set sd (Clight.Econst_int Int.one ty))) (makeseq sl2) :: nil,
                                    dummy_expr)
                            end).
          Case Eseqand := (fun r1 r2 ty => fun dst => 
                            do (sl1, a1) <- transl_expr For_val r1;
                            match dst with
                            | For_val =>
                                do t <- gensym ty;
                                let sd := SDbase type_bool ty t in
                                do (sl2, a2) <- transl_expr (For_set sd) r2;
                                ret (sl1 ++
                                    makeif a1 (makeseq sl2) (Clight.Sset t (Clight.Econst_int Int.zero ty)) :: nil,
                                    Clight.Etempvar t ty)
                            | For_effects =>
                                do (sl2, a2) <- transl_expr For_effects r2;
                                ret (sl1 ++ makeif a1 Clight.Sskip (makeseq sl2) :: nil, dummy_expr)
                            | For_set sd =>
                                do t <- temp_for_sd ty sd;
                                let sd' := SDcons type_bool ty t sd in
                                do (sl2, a2) <- transl_expr (For_set sd') r2;
                                ret (sl1 ++
                                    makeif a1 (makeseq sl2) (makeseq (do_set sd (Clight.Econst_int Int.zero ty))) :: nil,
                                    dummy_expr)
                            end).
          Case Esizeof := (fun ty' ty => fun dst => 
                            ret (finish dst nil (Clight.Esizeof ty' ty))).
          Case Ealignof := (fun ty' ty => fun dst => 
                            ret (finish dst nil (Clight.Ealignof ty' ty))).
          Case Evalof := (fun l ty => fun dst => 
                            do (sl1, a1) <- transl_expr For_val l;
                            do (sl2, a2) <- transl_valof (C.typeof l) a1;
                            ret (finish dst (sl1 ++ sl2) a2)).
      FEnd transl_expr.

      Definition transl_expression (r: C.expr) : mon (statement * expr) :=
          do (sl, a) <- transl_expr For_val r; ret (makeseq sl, a).

      Definition transl_expr_stmt (r: C.expr) : mon statement :=
          do (sl, a) <- transl_expr For_effects r; ret (makeseq sl).

      Definition transl_if (r: C.expr) (s1 s2: statement) : mon statement :=
          do (sl, a) <- transl_expr For_val r;
          ret (makeseq (sl ++ makeif a s1 s2 :: nil)).

      FRecursion transl_stmt about C.statement motive (fun (_ : C.statement) => mon Clight.statement).
          Case Sskip :=  ret Clight.Sskip.
          Case Sdo := (fun e => transl_expr_stmt e).
          Case Ssequence := (fun s1 trans_stmt_s1 s2 transl_stmt_s2 => 
                              do ts1 <- transl_stmt_s1;
                              do ts2 <- transl_stmt_s2;
                              ret (Clight.Ssequence ts1 ts2)).
          Case Sifthenelse := (fun e s1 transl_stmt_s1 s2 transl_stmt_s2 =>
                                do ts1 <- transl_stmt_s1;
                                do ts2 <- transl_stmt_s2;
                                do (s', a) <- transl_expression e;
                                if is_Sskip s1 && is_Sskip s2 then
                                  ret (Clight.Ssequence s' Clight.Sskip)
                                else
                                  ret (Clight.Ssequence s' (Clight.Sifthenelse a ts1 ts2))).
          Case Swhile := (fun e s1 transl_stmt_s1 =>
                            do s' <- transl_if e Clight.Sskip Clight.Sbreak;
                            do ts1 <- transl_stmt_s1;
                            ret (Clight.Sloop (Clight.Ssequence s' ts1) Clight.Sskip)).
          Case Sdowhile := (fun e s1 transl_stmt_s1 =>
                              do s' <- transl_if e Clight.Sskip Clight.Sbreak;
                              do ts1 <- transl_stmt s1;
                              ret (Clight.Sloop ts1 s')).
          Case Sfor := (fun s1 transl_stmt_s1 e2 s3 transl_stmt_s3 s4 transl_stmt_s4 =>
                          do ts1 <- transl_stmt s1;
                          do s' <- transl_if e2 Clight.Sskip Clight.Sbreak;
                          do ts3 <- transl_stmt s3;
                          do ts4 <- transl_stmt s4;
                          if is_Sskip s1 then
                            ret (Clight.Sloop (Clight.Ssequence s' ts4) ts3)
                          else
                            ret (Clight.Ssequence ts1 (Clight.Sloop (Clight.Ssequence s' ts4) ts3))).
          Case Sbreak := ret Clight.Sbreak.
          Case Scontinue := ret Clight.Scontinue.
          Case Sreturn := (fun e =>
                            match e with
                            | None => ret (Clight.Sreturn None)
                            | Some e => do (s', a) <- transl_expression e;
                                        ret (Clight.Ssequence s' (Clight.Sreturn (Some a)))
                            end).
          Case Slabel := (fun lbl s1 transl_stmt_s1 => 
                            do ts1 <- transl_stmt_s1;
                            ret (Clight.Slabel lbl ts1)).
          Case Sgoto := (fun lbl => ret (Clight.Sgoto lbl)).
      FEnd transl_stmt.

      Definition transl_function (f: C.function) : res function :=
          match transl_stmt f.(C.fn_body) (initial_generator tt) with
          | Err msg =>
              Error msg
          | Res tbody g i =>
              OK (mkfunction
                      f.(C.fn_return)
                      f.(C.fn_callconv)
                      f.(C.fn_params)
                      f.(C.fn_vars)
                      g.(gen_trail)
                      tbody)
          end.

          (* Relational specification of translation *)
          Family Specification.
                FInductive tr_expr: temp_env -> destination -> Csyntax.expr -> list statement -> expr -> list ident -> Prop :=
                    | tr_var: forall le dst id ty tmp,
                        tr_expr le dst (Csyntax.Evar id ty)
                                (final dst (Evar id ty)) (Evar id ty) tmp
                    | tr_deref: forall le dst e1 ty sl1 a1 tmp,
                        tr_expr le For_val e1 sl1 a1 tmp ->
                        tr_expr le dst (Csyntax.Ederef e1 ty)
                                (sl1 ++ final dst (Ederef' a1 ty)) (Ederef' a1 ty) tmp
                    | tr_field: forall le dst e1 f ty sl1 a1 tmp,
                        tr_expr le For_val e1 sl1 a1 tmp ->
                        tr_expr le dst (Csyntax.Efield e1 f ty)
                                (sl1 ++ final dst (Efield a1 f ty)) (Efield a1 f ty) tmp
                    | tr_val_effect: forall le v ty any tmp,
                        tr_expr le For_effects (Csyntax.Eval v ty) nil any tmp
                    | tr_val_value: forall le v ty a tmp,
                        typeof a = ty ->
                        (forall tge e le' m,
                          (forall id, In id tmp -> le'!id = le!id) ->
                          eval_expr tge e le' m a v) ->
                        tr_expr le For_val (Csyntax.Eval v ty)
                                            nil a tmp
                    | tr_val_set: forall le sd v ty a any tmp,
                        typeof a = ty ->
                        (forall tge e le' m,
                          (forall id, In id tmp -> le'!id = le!id) ->
                          eval_expr tge e le' m a v) ->
                        tr_expr le (For_set sd) (Csyntax.Eval v ty)
                                    (do_set sd a) any tmp
                    | tr_sizeof: forall le dst ty' ty tmp,
                        tr_expr le dst (Csyntax.Esizeof ty' ty)
                                    (final dst (Esizeof ty' ty))
                                    (Esizeof ty' ty) tmp
                    | tr_alignof: forall le dst ty' ty tmp,
                        tr_expr le dst (Csyntax.Ealignof ty' ty)
                                    (final dst (Ealignof ty' ty))
                                    (Ealignof ty' ty) tmp
                    | tr_cast_effects: forall le e1 ty sl1 a1 any tmp,
                        tr_expr le For_effects e1 sl1 a1 tmp ->
                        tr_expr le For_effects (Csyntax.Ecast e1 ty)
                                    sl1
                                    any tmp
                    | tr_cast_val: forall le dst e1 ty sl1 a1 tmp,
                        tr_expr le For_val e1 sl1 a1 tmp ->
                        tr_expr le dst (Csyntax.Ecast e1 ty)
                                    (sl1 ++ final dst (Ecast a1 ty))
                                    (Ecast a1 ty) tmp
                    | tr_seqand_val: forall le e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp,
                        tr_expr le For_val e1 sl1 a1 tmp1 ->
                        tr_expr le (For_set (SDbase type_bool ty t)) e2 sl2 a2 tmp2 ->
                        list_disjoint tmp1 tmp2 ->
                        incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
                        tr_expr le For_val (Csyntax.Eseqand e1 e2 ty)
                                      (sl1 ++ makeif a1 (makeseq sl2)
                                                        (Sset t (Econst_int Int.zero ty)) :: nil)
                                      (Etempvar t ty) tmp
                    | tr_seqand_effects: forall le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
                        tr_expr le For_val e1 sl1 a1 tmp1 ->
                        tr_expr le For_effects e2 sl2 a2 tmp2 ->
                        list_disjoint tmp1 tmp2 ->
                        incl tmp1 tmp -> incl tmp2 tmp ->
                        tr_expr le For_effects (Csyntax.Eseqand e1 e2 ty)
                                      (sl1 ++ makeif a1 (makeseq sl2) Sskip :: nil)
                                      any tmp
                    | tr_seqand_set: forall le sd e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 any tmp,
                        tr_expr le For_val e1 sl1 a1 tmp1 ->
                        tr_expr le (For_set (SDcons type_bool ty t sd)) e2 sl2 a2 tmp2 ->
                        list_disjoint tmp1 tmp2 ->
                        incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
                        tr_expr le (For_set sd) (Csyntax.Eseqand e1 e2 ty)
                                      (sl1 ++ makeif a1 (makeseq sl2)
                                                        (makeseq (do_set sd (Econst_int Int.zero ty))) :: nil)
                                      any tmp
                    | tr_seqor_val: forall le e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp,
                        tr_expr le For_val e1 sl1 a1 tmp1 ->
                        tr_expr le (For_set (SDbase type_bool ty t)) e2 sl2 a2 tmp2 ->
                        list_disjoint tmp1 tmp2 ->
                        incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
                        tr_expr le For_val (Csyntax.Eseqor e1 e2 ty)
                                      (sl1 ++ makeif a1 (Sset t (Econst_int Int.one ty))
                                                        (makeseq sl2) :: nil)
                                      (Etempvar t ty) tmp
                    | tr_seqor_effects: forall le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
                        tr_expr le For_val e1 sl1 a1 tmp1 ->
                        tr_expr le For_effects e2 sl2 a2 tmp2 ->
                        list_disjoint tmp1 tmp2 ->
                        incl tmp1 tmp -> incl tmp2 tmp ->
                        tr_expr le For_effects (Csyntax.Eseqor e1 e2 ty)
                                      (sl1 ++ makeif a1 Sskip (makeseq sl2) :: nil)
                                      any tmp
                    | tr_seqor_set: forall le sd e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 any tmp,
                        tr_expr le For_val e1 sl1 a1 tmp1 ->
                        tr_expr le (For_set (SDcons type_bool ty t sd)) e2 sl2 a2 tmp2 ->
                        list_disjoint tmp1 tmp2 ->
                        incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
                        tr_expr le (For_set sd) (Csyntax.Eseqor e1 e2 ty)
                                      (sl1 ++ makeif a1 (makeseq (do_set sd (Econst_int Int.one ty)))
                                      (makeseq sl2) :: nil)
                                      any tmp
                    | tr_condition_val: forall le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t tmp,
                        tr_expr le For_val e1 sl1 a1 tmp1 ->
                        tr_expr le (For_set (SDbase ty ty t)) e2 sl2 a2 tmp2 ->
                        tr_expr le (For_set (SDbase ty ty t)) e3 sl3 a3 tmp3 ->
                        list_disjoint tmp1 tmp2 ->
                        list_disjoint tmp1 tmp3 ->
                        incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp -> In t tmp ->
                        tr_expr le For_val (Csyntax.Econdition e1 e2 e3 ty)
                                        (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil)
                                        (Etempvar t ty) tmp
                    | tr_condition_effects: forall le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp,
                        tr_expr le For_val e1 sl1 a1 tmp1 ->
                        tr_expr le For_effects e2 sl2 a2 tmp2 ->
                        tr_expr le For_effects e3 sl3 a3 tmp3 ->
                        list_disjoint tmp1 tmp2 ->
                        list_disjoint tmp1 tmp3 ->
                        incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp ->
                        tr_expr le For_effects (Csyntax.Econdition e1 e2 e3 ty)
                                        (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil)
                                        any tmp
                    | tr_condition_set: forall le sd t e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp,
                        tr_expr le For_val e1 sl1 a1 tmp1 ->
                        tr_expr le (For_set (SDcons ty ty t sd)) e2 sl2 a2 tmp2 ->
                        tr_expr le (For_set (SDcons ty ty t sd)) e3 sl3 a3 tmp3 ->
                        list_disjoint tmp1 tmp2 ->
                        list_disjoint tmp1 tmp3 ->
                        incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp -> In t tmp ->
                        tr_expr le (For_set sd) (Csyntax.Econdition e1 e2 e3 ty)
                                        (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil)
                                        any tmp
                    | tr_assign_effects: forall le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 bf any tmp,
                        tr_expr le For_val e1 sl1 a1 tmp1 ->
                        tr_expr le For_val e2 sl2 a2 tmp2 ->
                        list_disjoint tmp1 tmp2 ->
                        incl tmp1 tmp -> incl tmp2 tmp ->
                        tr_is_bitfield_access a1 bf ->
                        tr_expr le For_effects (Csyntax.Eassign e1 e2 ty)
                                        (sl1 ++ sl2 ++ make_assign bf a1 a2 :: nil)
                                        any tmp
                    | tr_assign_val: forall le dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 t tmp ty1 ty2 bf,
                        tr_expr le For_val e1 sl1 a1 tmp1 ->
                        tr_expr le For_val e2 sl2 a2 tmp2 ->
                        incl tmp1 tmp -> incl tmp2 tmp ->
                        list_disjoint tmp1 tmp2 ->
                        In t tmp -> ~In t tmp1 -> ~In t tmp2 ->
                        ty1 = Csyntax.typeof e1 ->
                        ty2 = Csyntax.typeof e2 ->
                        tr_is_bitfield_access a1 bf ->
                        tr_expr le dst (Csyntax.Eassign e1 e2 ty)
                                    (sl1 ++ sl2 ++
                                      Sset t (Ecast a2 ty1) ::
                                      make_assign bf a1 (Etempvar t ty1) ::
                                      final dst (make_assign_value bf (Etempvar t ty1)))
                                    (make_assign_value bf (Etempvar t ty1)) tmp
                    | tr_assignop_effects: forall le op e1 e2 tyres ty ty1 sl1 a1 tmp1 sl2 a2 tmp2 bf sl3 a3 tmp3 any tmp,
                        tr_expr le For_val e1 sl1 a1 tmp1 ->
                        tr_expr le For_val e2 sl2 a2 tmp2 ->
                        ty1 = Csyntax.typeof e1 ->
                        tr_rvalof ty1 a1 sl3 a3 tmp3 ->
                        list_disjoint tmp1 tmp2 -> list_disjoint tmp1 tmp3 -> list_disjoint tmp2 tmp3 ->
                        incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp ->
                        tr_is_bitfield_access a1 bf ->
                        tr_expr le For_effects (Csyntax.Eassignop op e1 e2 tyres ty)
                                        (sl1 ++ sl2 ++ sl3 ++ make_assign bf a1 (Ebinop op a3 a2 tyres) :: nil)
                                        any tmp
                    | tr_assignop_val: forall le dst op e1 e2 tyres ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t bf tmp ty1,
                        tr_expr le For_val e1 sl1 a1 tmp1 ->
                        tr_expr le For_val e2 sl2 a2 tmp2 ->
                        tr_rvalof ty1 a1 sl3 a3 tmp3 ->
                        list_disjoint tmp1 tmp2 -> list_disjoint tmp1 tmp3 -> list_disjoint tmp2 tmp3 ->
                        incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp ->
                        In t tmp -> ~In t tmp1 -> ~In t tmp2 -> ~In t tmp3 ->
                        ty1 = Csyntax.typeof e1 ->
                        tr_is_bitfield_access a1 bf ->
                        tr_expr le dst (Csyntax.Eassignop op e1 e2 tyres ty)
                                    (sl1 ++ sl2 ++ sl3 ++
                                      Sset t (Ecast (Ebinop op a3 a2 tyres) ty1) ::
                                      make_assign bf a1 (Etempvar t ty1) ::
                                      final dst (make_assign_value bf (Etempvar t ty1)))
                                    (make_assign_value bf (Etempvar t ty1)) tmp
                    | tr_postincr_effects: forall le id e1 ty ty1 sl1 a1 tmp1 sl2 a2 tmp2 bf any tmp,
                        tr_expr le For_val e1 sl1 a1 tmp1 ->
                        tr_rvalof ty1 a1 sl2 a2 tmp2 ->
                        ty1 = Csyntax.typeof e1 ->
                        incl tmp1 tmp -> incl tmp2 tmp ->
                        list_disjoint tmp1 tmp2 ->
                        tr_is_bitfield_access a1 bf ->
                        tr_expr le For_effects (Csyntax.Epostincr id e1 ty)
                                        (sl1 ++ sl2 ++ make_assign bf a1 (transl_incrdecr id a2 ty1) :: nil)
                                        any tmp
                    | tr_postincr_val: forall le dst id e1 ty sl1 a1 tmp1 bf t ty1 tmp,
                        tr_expr le For_val e1 sl1 a1 tmp1 ->
                        incl tmp1 tmp -> In t tmp -> ~In t tmp1 ->
                        ty1 = Csyntax.typeof e1 ->
                        tr_is_bitfield_access a1 bf ->
                        tr_expr le dst (Csyntax.Epostincr id e1 ty)
                                    (sl1 ++ make_set bf t a1 ::
                                      make_assign bf a1 (transl_incrdecr id (Etempvar t ty1) ty1) ::
                                      final dst (Etempvar t ty1))
                                    (Etempvar t ty1) tmp
                    | tr_comma: forall le dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp,
                        tr_expr le For_effects e1 sl1 a1 tmp1 ->
                        tr_expr le dst e2 sl2 a2 tmp2 ->
                        list_disjoint tmp1 tmp2 ->
                        incl tmp1 tmp -> incl tmp2 tmp ->
                        tr_expr le dst (Csyntax.Ecomma e1 e2 ty) (sl1 ++ sl2) a2 tmp
                    | tr_paren_val: forall le e1 tycast ty sl1 a1 t tmp,
                        tr_expr le (For_set (SDbase tycast ty t)) e1 sl1 a1 tmp ->
                        In t tmp ->
                        tr_expr le For_val (Csyntax.Eparen e1 tycast ty)
                                        sl1
                                        (Etempvar t ty) tmp.
                (*
                Variable ge: genv.
                Variable e: env.
                Variable le: temp_env.
                Variable m: mem. *)

                Inductive tr_top: destination -> Csyntax.expr -> list statement -> expr -> list ident -> Prop :=
                  | tr_top_val_val: forall v ty a tmp,
                      typeof a = ty -> eval_expr ge e le m a v ->
                      tr_top For_val (Csyntax.Eval v ty) nil a tmp
                  | tr_top_base: forall dst r sl a tmp,
                      tr_expr le dst r sl a tmp ->
                      tr_top dst r sl a tmp.

                Inductive tr_expression: Csyntax.expr -> statement -> expr -> Prop :=
                  | tr_expression_intro: forall r sl a tmps,
                      (forall ge e le m, tr_top ge e le m For_val r sl a tmps) ->
                      tr_expression r (makeseq sl) a.

                Inductive tr_expr_stmt: Csyntax.expr -> statement -> Prop :=
                  | tr_expr_stmt_intro: forall r sl a tmps,
                      (forall ge e le m, tr_top ge e le m For_effects r sl a tmps) ->
                      tr_expr_stmt r (makeseq sl).

                Inductive tr_if: Csyntax.expr -> statement -> statement -> statement -> Prop :=
                  | tr_if_intro: forall r s1 s2 sl a tmps,
                      (forall ge e le m, tr_top ge e le m For_val r sl a tmps) ->
                      tr_if r s1 s2 (makeseq (sl ++ makeif a s1 s2 :: nil)).

                FInductive tr_stmt: C.statement -> Clight.statement -> Prop :=
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
                        tr_stmt (C.Sifthenelse r Csyntax.Sskip Csyntax.Sskip) (Clight.Ssequence s' Sskip)
                    | tr_ifthenelse: forall r s1 s2 s' a ts1 ts2,
                        tr_expression r s' a ->
                        tr_stmt s1 ts1 -> tr_stmt s2 ts2 ->
                        tr_stmt (C.Sifthenelse r s1 s2) (Clight.Ssequence s' (Clight.Sifthenelse a ts1 ts2))
                    | tr_while: forall r s1 s' ts1,
                        tr_if r Sskip Sbreak s' ->
                        tr_stmt s1 ts1 ->
                        tr_stmt (C.Swhile r s1)
                                (Clight.Sloop (Ssequence s' ts1) Sskip)
                    | tr_dowhile: forall r s1 s' ts1,
                        tr_if r Sskip Sbreak s' ->
                        tr_stmt s1 ts1 ->
                        tr_stmt (C.Sdowhile r s1)
                                (Clight.Sloop ts1 s')
                    | tr_for_1: forall r s3 s4 s' ts3 ts4,
                        tr_if r Sskip Sbreak s' ->
                        tr_stmt s3 ts3 ->
                        tr_stmt s4 ts4 ->
                        tr_stmt (C.Sfor C.Sskip r s3 s4)
                                (Clight.Sloop (Clight.Ssequence s' ts4) ts3)
                    | tr_for_2: forall s1 r s3 s4 s' ts1 ts3 ts4,
                        tr_if r Sskip Sbreak s' ->
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

                (* Proof of correctness of translation wrt the specification *)
          FEnd Specification.
   FEnd SimplExpr.     
   
   (* Csharpminor -> Cminor *)
   Family Cminorgen.
      FRecursion translate_constant about
         Csharpminor.constant motive (fun (_ : Csharpminor.constant) => Cminor.constant) by _rect.
           Case Ointconst := (fun n => Cminor.Ointconst n).
           Case Ofloatconst := (fun n => Cminor.Ofloatconst n).
           Case Osingleconst := (fun n => Cminor.Osingleconst n).
           Case Olongconst := (fun n => Cminor.Olongconst n).
      FEnd translate_constant.
   
      FRecursion translate_expr about Csharpminor.expr motive (fun (_ : Csharpminor.expr) => Cminor.expr) by _rect.
           Case Evar := (fun id => Cminor.Evar id).
           Case Econst := (fun cst => Cminor.Econst (translate_constant cst)).
      FEnd translate_expr.

      Definition exit_env := list bool.

      Fixpoint shift_exit (e: exit_env) (n: nat) {struct e} : nat :=
        match e, n with
        | nil, _ => n
        | false :: e', _ => S (shift_exit e' n)
        | true :: e', O => O
        | true :: e', S m => S (shift_exit e' m)
        end.
    
      FRecursion translate_stmt about Csharpminor.stmt motive (fun (_ : Csharpminor.stmt) => compilenv -> exit_env -> Cminor.stmt) by _rect.
            Case Sskip := (fun cenv xenv => Cminor.Sskip).
            Case Sset := (fun id e => fun cenv xenv => Cminor.Sassign id (translate_expr e)).
            Case Sseq := (fun s1 translate_stmt_s1 s2 translate_stmt_s2 => fun cenv xenv => Cminor.Sseq translate_stmt_s1 translate_stmt_s2).
            Case Sifthenelse := (fun e s1 translate_stmt_s1 s2 translate_stmt_s2 => fun cenv xenv =>
                                   Cminor.Sifthenelse (translate_expr e) translate_stmt_s1 translate_stmt_s2).
            Case Sloop := (fun s1 translate_stmt_s1 => fun cenv xenv => Cminor.Sloop translate_stmt_s1).
            Case Sblock := (fun s translate_stmt_s => fun cenv xenv => Cminor.Sblock translate_stmt_s).
            Case Sexit := (fun cenv xenv => Sexit (shift_exit xenv n)).
            Case Sreturn := (fun expr => fun cenv xenv =>
                               match expr with
                               | None => Cminor.Sreturn None
                               | Some expr => Cminor.Sreturn (Some (translate_expr expr)) end).
            Case Slabel := (fun lbl s translate_stmt_s => fun cenv xenv => Cminor.Slabel lbl translate_stmt_s).
            Case Sgoto := (fun lbl => fun cenv xenv => Cminor.Sgoto lbl).
      FEnd translate_stmt.


       (* Translate Function, Fundef, Program *)


      Family Correctness.
      FEnd Correctness.
  FEnd Cminorgen.    
   
   (* Cminor -> CminorSel *)
   Family Selection.
       Definition longconst (n: int64) : expr :=
          if Archi.splitlong then SplitLong.longconst n else Eop (Olongconst n) Enil.

       FRecurcion sel_constant about Cminor.constant motive (fun (_ : Cminor.constant) => CminorSel.constant).
           Case Ointconst := (fun n => CminorSel.Eop (Asm.Ointconst n) Enil).
           Case Ofloatconst := (fun n => CminorSel.Eop (Asm.Ofloatconst f) Enil).
           Case Osingleconst := (fun n =>  Eop (Osingleconst f) Enil).
           Case Olongconst := (fun n => longconst n).
        FEnd sel_constant.

        FRecursion sel_expr about Cminor.expr motive (fun (_ : Cminor.expr) => CminorSel.expr).          
           Case Evar := (fun id => CminorSel.Evar id).
           Case Econst := (fun cst => sel_constant cst).
        FEnd sel_expr.        
       
        FRecursion sel_stmt about Cminor.stmt 
                            motive (fun (_ : Cminor.stmt) => known_idents -> typeenv -> CminorSel.stmt).
          Case Sskip := (fun ki env => CminorSel.Sskip).
          Case Sassign := (fun id e => fun ki env => CminorSel.Sassign id (sel_expr e)).
          Case Sseq := (fun s1 sel_s1 s2 sel_s2 => fun ki env => CminorSel.Sseq (sel_s1 ki env) (sel_s1 ki env)).
          Case Sifthenelse := 
                (fun e ifso sel_ifso ifnot sel_ifnot => fun ki env => 
                      (* Don't use the if conversion heuristics *)
                      do ifso' <- sel_ifso ki env; do ifnot' <- sel_ifnot ki env;
                      OK (Sifthenelse (condexpr_of_expr (sel_expr e)) ifso' ifnot')).
          Case Sloop := (fun s sel_s1 => fun ki env => CminorSel.Sloop (sel_s1 ki env)).
          Case Sblock := (fun s sel_s1 => fun ki env => CminorSel.Sblock (sel_s1 ki env)).
          Case Sexit := (fun n => fun ki env => CminorSel.Sexit n).
          Case Sreturn := (fun e => fun ki env => 
                               match e with 
                               | None => CminorSel.Sreturn None 
                               | Some e => CminorSel.Sreturn (Some (sel_expr e))).
          Case Slabel := (fun lbl s sel_s => fun ki env => CminorSel.Slabel (sel_s ki env)).
          Case Sgoto := (fun lbl => fun ki env => CminorSel.Sgoto lbl).
        FEnd sel_stmt.
   FEnd Selection.

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
        Family Specification. 
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
                       
        FEnd Specification.
   FEnd RTLgen.   
   
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
        Family Correctness.
        FEnd Correctness.
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


(* Family ImpOperators { }*)
(* 
Inductive binarith_cases: Type :=
                | bin_case_i (s: signedness)(* at int type *)
                | bin_case_l (s: signedness)(* at long int type *)                
                | bin_default.(* error *)

            Definition classify_binarith (ty1: type) (ty2: type) : binarith_cases :=
                match ty1, ty2 with
                | Tint I32 Unsigned _, Tint _ _ _ => bin_case_i Unsigned
                | Tint _ _ _, Tint I32 Unsigned _ => bin_case_i Unsigned
                | Tint _ _ _, Tint _ _ _ => bin_case_i Signed
                | Tlong Signed _, Tlong Signed _ => bin_case_l Signed
                | Tlong _ _, Tlong _ _ => bin_case_l Unsigned
                | Tlong sg _, Tint _ _ _ => bin_case_l sg
                | Tint _ _ _, Tlong sg _ => bin_case_l sg                
                | _, _ => bin_default
                end.
            
            Definition binarith_type (c: binarith_cases) : type :=
                match c with
                | bin_case_i sg => Tint I32 sg noattr
                | bin_case_l sg => Tlong sg noattr                
                | bin_default => Tvoid
                end.
            
            Definition sem_binarith
                  (sem_int: signedness -> int -> int -> option val)
                  (sem_long: signedness -> int64 -> int64 -> option val)                  
                  (v1: val) (t1: type) (v2: val) (t2: type) (m: mem): option val :=
            let c := classify_binarith t1 t2 in
            let t := binarith_type c in
            match sem_cast v1 t1 t m with
            | None => None
            | Some v1' =>
            match sem_cast v2 t2 t m with
            | None => None
            | Some v2' =>
            match c with
            | bin_case_i sg =>
                match v1', v2' with
                | Vint n1, Vint n2 => sem_int sg n1 n2
                | _, _ => None
                end            
            | bin_case_l sg =>
                match v1', v2' with
                | Vlong n1, Vlong n2 => sem_long sg n1 n2
                | _, _ => None
                end
            | bin_default => None
            end end end.
            
            (* Addition *)
            Inductive classify_add_cases : Type :=
              | add_case_pi (ty: type) (si: signedness)(* pointer, int *)
              | add_case_pl (ty: type)(* pointer, long *)
              | add_case_ip (si: signedness) (ty: type)(* int, pointer *)
              | add_case_lp (ty: type)(* long, pointer *)
              | add_default.(* numerical type, numerical type *)
            
            Definition classify_add (ty1: type) (ty2: type) :=
              match typeconv ty1, typeconv ty2 with
              | Tpointer ty _, Tint _ si _ => add_case_pi ty si
              | Tpointer ty _, Tlong _ _ => add_case_pl ty
              | Tint _ si _, Tpointer ty _ => add_case_ip si ty
              | Tlong _ _, Tpointer ty _ => add_case_lp ty
              | _, _ => add_default
              end.
            
            Definition ptrofs_of_int (si: signedness) (n: int) : ptrofs :=
              match si with
              | Signed => Ptrofs.of_ints n
              | Unsigned => Ptrofs.of_intu n
              end.
            
            Definition sem_add_ptr_int (cenv: composite_env) (ty: type) (si: signedness) (v1 v2: val): option val :=
              match v1, v2 with
              | Vptr b1 ofs1, Vint n2 =>
                  let n2 := ptrofs_of_int si n2 in
                  Some (Vptr b1 (Ptrofs.add ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
              | Vint n1, Vint n2 =>
                  if Archi.ptr64 then None else Some (Vint (Int.add n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
              | Vlong n1, Vint n2 =>
                  let n2 := cast_int_long si n2 in
                  if Archi.ptr64 then Some (Vlong (Int64.add n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))) else None
              | _, _ => None
              end.
            
            Definition sem_add_ptr_long (cenv: composite_env) (ty: type) (v1 v2: val): option val :=
              match v1, v2 with
              | Vptr b1 ofs1, Vlong n2 =>
                  let n2 := Ptrofs.of_int64 n2 in
                  Some (Vptr b1 (Ptrofs.add ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
              | Vint n1, Vlong n2 =>
                  let n2 := Int.repr (Int64.unsigned n2) in
                  if Archi.ptr64 then None else Some (Vint (Int.add n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
              | Vlong n1, Vlong n2 =>
                  if Archi.ptr64 then Some (Vlong (Int64.add n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))) else None
              | _, _ => None
              end.
            
            Definition sem_add (cenv: composite_env) (v1:val) (t1:type) (v2: val) (t2:type) (m: mem): option val :=
              match classify_add t1 t2 with
              | add_case_pi ty si =>(* pointer plus integer *)
                  sem_add_ptr_int cenv ty si v1 v2
              | add_case_pl ty =>(* pointer plus long *)
                  sem_add_ptr_long cenv ty v1 v2
              | add_case_ip si ty =>(* integer plus pointer *)
                  sem_add_ptr_int cenv ty si v2 v1
              | add_case_lp ty =>(* long plus pointer *)
                  sem_add_ptr_long cenv ty v2 v1
              | add_default =>
                  sem_binarith
                    (fun sg n1 n2 => Some(Vint(Int.add n1 n2)))
                    (fun sg n1 n2 => Some(Vlong(Int64.add n1 n2)))                    
                    v1 t1 v2 t2 m
              end.
            
            (* Subtraction *)
            Inductive classify_sub_cases : Type :=
               | sub_case_pi (ty: type) (si: signedness)(* pointer, int *)
               | sub_case_pp (ty: type)(* pointer, pointer *)
               | sub_case_pl (ty: type)(* pointer, long *)
               | sub_default.(* numerical type, numerical type *)

            Definition classify_sub (ty1: type) (ty2: type) :=
              match typeconv ty1, typeconv ty2 with
              | Tpointer ty _, Tint _ si _ => sub_case_pi ty si
              | Tpointer ty _ , Tpointer _ _ => sub_case_pp ty
              | Tpointer ty _, Tlong _ _ => sub_case_pl ty
              | _, _ => sub_default
              end.

            Definition sem_sub (cenv: composite_env) (v1:val) (t1:type) (v2: val) (t2:type) (m:mem): option val :=
              match classify_sub t1 t2 with
              | sub_case_pi ty si =>(* pointer minus integer *)
                  match v1, v2 with
                  | Vptr b1 ofs1, Vint n2 =>
                      let n2 := ptrofs_of_int si n2 in
                      Some (Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
                  | Vint n1, Vint n2 =>
                      if Archi.ptr64 then None else Some (Vint (Int.sub n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
                  | Vlong n1, Vint n2 =>
                      let n2 := cast_int_long si n2 in
                      if Archi.ptr64 then Some (Vlong (Int64.sub n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))) else None
                  | _, _ => None
                  end
              | sub_case_pl ty =>(* pointer minus long *)
                  match v1, v2 with
                  | Vptr b1 ofs1, Vlong n2 =>
                      let n2 := Ptrofs.of_int64 n2 in
                      Some (Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
                  | Vint n1, Vlong n2 =>
                      let n2 := Int.repr (Int64.unsigned n2) in
                      if Archi.ptr64 then None else Some (Vint (Int.sub n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
                  | Vlong n1, Vlong n2 =>
                      if Archi.ptr64 then Some (Vlong (Int64.sub n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))) else None
                  | _, _ => None
                  end
              | sub_case_pp ty =>(* pointer minus pointer *)
                  match v1,v2 with
                  | Vptr b1 ofs1, Vptr b2 ofs2 =>
                      if eq_block b1 b2 then
                        let sz := sizeof cenv ty in
                        if zlt 0 sz && zle sz Ptrofs.max_signed
                        then Some (Vptrofs (Ptrofs.divs (Ptrofs.sub ofs1 ofs2) (Ptrofs.repr sz)))
                        else None
                      else None
                  | _, _ => None
                  end
              | sub_default =>
                  sem_binarith
                    (fun sg n1 n2 => Some(Vint(Int.sub n1 n2)))
                    (fun sg n1 n2 => Some(Vlong(Int64.sub n1 n2)))                    
                    v1 t1 v2 t2 m
              end.
            
            (* Multiplication *)
            Definition sem_mul (v1:val) (t1:type) (v2: val) (t2:type) (m:mem) : option val :=
                sem_binarith
                  (fun sg n1 n2 => Some(Vint(Int.mul n1 n2)))
                  (fun sg n1 n2 => Some(Vlong(Int64.mul n1 n2)))
                  (fun n1 n2 => Some(Vfloat(Float.mul n1 n2)))
                  (fun n1 n2 => Some(Vsingle(Float32.mul n1 n2)))
                  v1 t1 v2 t2 m.
            
            (* Division *)
            Definition sem_div (v1:val) (t1:type) (v2: val) (t2:type) (m:mem) : option val :=
                 sem_binarith
                   (fun sg n1 n2 =>
                     match sg with
                     | Signed =>
                         if Int.eq n2 Int.zero
                         || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
                         then None else Some(Vint(Int.divs n1 n2))
                     | Unsigned =>
                         if Int.eq n2 Int.zero
                         then None else Some(Vint(Int.divu n1 n2))
                     end)
                   (fun sg n1 n2 =>
                     match sg with
                     | Signed =>
                         if Int64.eq n2 Int64.zero
                         || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
                         then None else Some(Vlong(Int64.divs n1 n2))
                     | Unsigned =>
                         if Int64.eq n2 Int64.zero
                         then None else Some(Vlong(Int64.divu n1 n2))
                     end)                   
                   v1 t1 v2 t2 m.
            
            Inductive classify_cmp_cases : Type :=
                | cmp_case_pp(* pointer, pointer *)
                | cmp_case_pi (si: signedness)(* pointer, int *)
                | cmp_case_ip (si: signedness)(* int, pointer *)
                | cmp_case_pl(* pointer, long *)
                | cmp_case_lp(* long, pointer *)
                | cmp_default.(* numerical, numerical *)

            Definition classify_cmp (ty1: type) (ty2: type) :=
              match typeconv ty1, typeconv ty2 with
              | Tpointer _ _ , Tpointer _ _ => cmp_case_pp
              | Tpointer _ _ , Tint _ si _ => cmp_case_pi si
              | Tint _ si _, Tpointer _ _ => cmp_case_ip si
              | Tpointer _ _ , Tlong _ _ => cmp_case_pl
              | Tlong _ _ , Tpointer _ _ => cmp_case_lp
              | _, _ => cmp_default
              end.
            
            Definition cmp_ptr (m: mem) (c: comparison) (v1 v2: val): option val :=
              option_map Val.of_bool
               (if Archi.ptr64
                then Val.cmplu_bool (Mem.valid_pointer m) c v1 v2
                else Val.cmpu_bool (Mem.valid_pointer m) c v1 v2).

            (* Comparison *)
            Definition sem_cmp (c:comparison)
                  (v1: val) (t1: type) (v2: val) (t2: type)
                  (m: mem): option val :=
               match classify_cmp t1 t2 with
               | cmp_case_pp =>
                   cmp_ptr m c v1 v2
               | cmp_case_pi si =>
                   match v2 with
                   | Vint n2 =>
                       let v2' := Vptrofs (ptrofs_of_int si n2) in
                       cmp_ptr m c v1 v2'
                   | Vptr b ofs =>
                       if Archi.ptr64 then None else cmp_ptr m c v1 v2
                   | _ =>
                       None
                   end
               | cmp_case_ip si =>
                   match v1 with
                   | Vint n1 =>
                       let v1' := Vptrofs (ptrofs_of_int si n1) in
                       cmp_ptr m c v1' v2
                   | Vptr b ofs =>
                       if Archi.ptr64 then None else cmp_ptr m c v1 v2
                   | _ =>
                       None
                   end
               | cmp_case_pl =>
                   match v2 with
                   | Vlong n2 =>
                       let v2' := Vptrofs (Ptrofs.of_int64 n2) in
                       cmp_ptr m c v1 v2'
                   | Vptr b ofs =>
                       if Archi.ptr64 then cmp_ptr m c v1 v2 else None
                   | _ =>
                       None
                   end
               | cmp_case_lp =>
                   match v1 with
                   | Vlong n1 =>
                     let v1' := Vptrofs (Ptrofs.of_int64 n1) in
                     cmp_ptr m c v1' v2
                   | Vptr b ofs =>
                       if Archi.ptr64 then cmp_ptr m c v1 v2 else None
                   | _ => None    
               end
               | cmp_default =>
               sem_binarith
                 (fun sg n1 n2 =>
                     Some(Val.of_bool(match sg with Signed => Int.cmp c n1 n2 | Unsigned => Int.cmpu c n1 n2 end)))
                 (fun sg n1 n2 =>
                     Some(Val.of_bool(match sg with Signed => Int64.cmp c n1 n2 | Unsigned => Int64.cmpu c n1 n2 end)))                 
                 v1 t1 v2 t2 m
          end.

          Definition sem_notbool (v: val) (ty: type) (m: mem): option val :=
              option_map (fun b => Val.of_bool (negb b)) (bool_val v ty m).

          (* Bitwise complement *)
          Inductive classify_notint_cases : Type :=
              | notint_case_i(s: signedness)(* int *)
              | notint_case_l(s: signedness)(* long *)
              | notint_default.

          Definition classify_notint (ty: type) : classify_notint_cases :=
              match ty with
              | Tint I32 Unsigned _ => notint_case_i Unsigned
              | Tint _ _ _ => notint_case_i Signed
              | Tlong si _ => notint_case_l si
              | _ => notint_default
              end.

          Definition sem_notint (v: val) (ty: type): option val :=
              match classify_notint ty with
              | notint_case_i sg =>
                  match v with
                  | Vint n => Some (Vint (Int.not n))
                  | _ => None
                  end
              | notint_case_l sg =>
                  match v with
                  | Vlong n => Some (Vlong (Int64.not n))
                  | _ => None
                  end
              | notint_default => None
              end.
          
          Inductive classify_bool_cases : Type :=
                | bool_case_i(* integer *)
                | bool_case_l(* long *)                
                | bool_default.

            Definition classify_bool (ty: type) : classify_bool_cases :=
              match typeconv ty with
              | Tint _ _ _ => bool_case_i
              | Tpointer _ _ => if Archi.ptr64 then bool_case_l else bool_case_i
              | Tlong _ _ => bool_case_l
              | _ => bool_default
              end.
          
          (* Oppositve values *)
          Inductive classify_neg_cases : Type :=
              | neg_case_i(s: signedness)(* int *)
              | neg_case_l(s: signedness)(* long *)
              | neg_default.

            Definition classify_neg (ty: type) : classify_neg_cases :=
              match ty with
              | Tint I32 Unsigned _ => neg_case_i Unsigned
              | Tint _ _ _ => neg_case_i Signed
              | Tlong si _ => neg_case_l si
              | _ => neg_default
              end.

            Definition sem_neg (v: val) (ty: type) : option val :=
              match classify_neg ty with
              | neg_case_i sg =>
                  match v with
                  | Vint n => Some (Vint (Int.neg n))
                  | _ => None
                  end
              | neg_case_l sg =>
                  match v with
                  | Vlong n => Some (Vlong (Int64.neg n))
                  | _ => None
                  end
              | neg_default => None
              end.

          FRecursion sem_unary_operation about unary_operation motive (fun (_ : unary_operation) => val -> type -> mem -> option val).
              Case Onotbool := (fun v ty m =>  sem_notbool v ty m).
              Case Onotint := (fun v ty m => sem_notint v ty).
              Case Oneg := (fun v ty m =>  sem_neg v ty).
          FEnd sem_unary_operation.
            
          FRecursion sem_binary_operation about binary_operation
               motive (fun (_ : binary_operation) => composite_env ->                                                     
                                                     val -> type ->
                                                     val -> type ->
                                                     mem -> option val).
               Case Oadd := (fun cenv v1 t1 v2 t2 m => sem_add ce v1 t1 v2 t2 m).
               Case Osub := (fun cenv v1 t1 v2 t2 m => sem_sub ce v1 t1 v2 t2 m).
               Case Omul := (fun cenv v1 t1 v2 t2 m => sem_mul v1 t1 v2 t2 m).
               Case Odiv := (fun cenv v1 t1 v2 t2 m => sem_div v1 t1 v2 t2 m).
               Case Oeq := (fun cenv v1 t1 v2 t2 m =>  sem_cmp Ceq v1 t1 v2 t2 m).
               Case One := (fun cenv v1 t1 v2 t2 m =>  sem_cmp Cne v1 t1 v2 t2 m).
               Case Olt := (fun cenv v1 t1 v2 t2 m => sem_cmp Clt v1 t1 v2 t2 m).
               Case Ogt := (fun cenv v1 t1 v2 t2 m => sem_cmp Cgt v1 t1 v2 t2 m).
               Case Ole := (fun cenv v1 t1 v2 t2 m => sem_cmp Cle v1 t1 v2 t2 m).
               Case Oge := (fun cenv v1 t1 v2 t2 m => sem_cmp Cge v1 t1 v2 t2 m).
          FEnd sem_binary_operation.


Family Selection { 
      FRecursion sel_constant about Cminor.constant motive (fun (_ : Cminor.constant) => CminorSel.expr).            
            Case Ointconst := (fun n => CminorSel.Eop cheat cheat).
        FEnd sel_constant.

        FRecursion sel_unop about Cminor.unary_operation motive (fun (_ : Cminor.unary_operation) => CminorSel.expr -> CminorSel.expr).
            Case Onegint := (fun arg => cheat).
            Case Onotint := (fun arg => cheat).
        FEnd sel_unop.

        FRecursion sel_binop about Cminor.binary_operation motive (fun (_ : Cminor.binary_operation) => CminorSel.expr -> Cminor.Sel -> CminorSel.expr).
            Case Oadd := (fun arg1 arg2 => cheat). 
            Case Osub := (fun arg1 arg2 => cheat).
            Case Omul := (fun arg1 arg2 => cheat).
            Case Odiv := (fun arg1 arg2 => cheat).
            Case Ocmp := (fun arg1 arg2 => cheat).
            Case Ocmpu := (fun arg1 arg2 => cheat).
        FEnd sel_binop.
}

 FRecursion transl_exitexpr about CminorSel.exitexpr motive (fun (_ : CminorSel.exitexpr) => mapping -> list node -> node).
             Case XEexit := (fun n => fun map nexits => cheat).
             Case XEjumptable := (fun a tbl => fun map nexits => cheat).
             Case XEcondition := (fun a b c => fun map nexits => cheat).
             Case XElet := (fun a b => fun map nexists => cheat).
        FEnd transl_exitexpr.   
*)
