family Cfrontend {                        
    Definition ident := string
    
    Inductive constant : Type :=
        | Ointconst: int -> constant

    Inductive unary_operation : Type := 

    Inductive binary_operation : Type :=
        | Binplus
        | Binminus
        | Binmult.

    Inductive expression : Type :=
        | Evar : ident -> expression
        | Econst : constant -> expression
        | Eunop : unary_operation -> expression -> expression
        | Ebinop : binary_operation -> expr -> expr -> expr.

    Inductive statement : Type :=
       | Sassign : label -> expression -> statement
       | Sseq    : statement -> statement -> statement
       | Sifthenelse : expression -> statement -> statement -> statement       
       | Sskip : statement       
                           
        Record function : Type := mkfunction {   
           (* fn_params: list ident;
           fn_vars: list ident;
           fn_temps: list ident; *)
           fn_body: statement
        }

        Inductive fundef : Type :=
          | Internal: function -> fundef          
        
        Inductive globdef : Type :=
          | Gfun (f: fundef)

        Record program : Type := mkprogram {
           prog_defs: list (ident * globdef);           
           prog_main: ident
        }       
}
       
family Cfrontend.Semantics {
  Inductive cont : Type :=
   | Kstop: cont (* stop program execution *)
   | Kseq: statement -> cont -> cont (* execute stmt, then cont *)   
   | Kcall: option ident -> function -> val -> env -> cont -> cont
                                  
  Inductive state: Type :=
      | State : (* Execution within a function *)
          forall (f: function) (* currently executing function *)
                 (s: stmt) (* statement under consideration *)
                 (k: cont) (* its continuation -- what to do next *)                 
                 (e: env), (* current local environment *)
          state
      | Callstate : (* Invocation of a function *)
          forall (f: fundef) (* function to invoke *)
                 (args: list val) (* arguments provided by caller *)
                 (k: cont), (* what to do next *)
          state
      | Returnstate : (* Return from a function *)
          forall (v: val) (* Return value *)
                 (k: cont), (* what to do next *)
          state
                                                        
  Inductive eval_expr: expression -> Values.value -> Prop :=
   | eval_Evar: forall id v,
       le!id = Some v ->
       eval_expr (Evar id) v           
   | eval_Econst: forall cst v,
       eval_constant cst = Some v ->
       eval_expr (Econst cst) v
   | eval_Eunop: forall op a1 v1 v,
       eval_expr a1 v1 ->
       eval_unop op v1 = Some v ->
       eval_expr (Eunop op a1) v
   | eval_Ebinop: forall op a1 a2 v1 v2 v,
       eval_expr a1 v1 ->
       eval_expr a2 v2 ->
         eval_binop op v1 v2 m = Some v ->
         eval_expr (Ebinop op a1 a2) v        
         
   Inductive step : state -> trace -> state -> Prop :=     
     | step_assign: forall f id a k sp e m v,
           eval_expr sp e m a v ->
           step (State f (Sassign id a) k sp e m)
             E0 (State f Sskip k sp (PTree.set id v e) m)
     | step_seq : forall st c1 c2 k,  
         step (State (Sseq c1 c2) k st)
           E0 (State c1 (Kseq c2 k) st)             
     | step_skip_seq: forall c k st,
         step (State Sskip (Kseq c k) st)
           E0 (State c k st)                                    
     | step_ifthenelse: forall f a s1 s2 k e le m v b,
         eval_expr e le m a v ->
         Value.bool_of_val v b ->
         step (State f (Sifthenelse a s1 s2) k e le m)
           E0 (State f (if b then s1 else s2) k e le m)

     Inductive initial_state (p: program): state -> Prop :=
       | initial_state_intro: forall b f m0,
           let ge := Genv.globalenv p in
           Genv.init_mem p = Some m0 ->
           Genv.find_symbol ge p.(prog_main) = Some b ->
           Genv.find_funct_ptr ge b = Some f ->
           funsig f = signature_main ->
           initial_state p (Callstate f nil Kstop m0)

     Inductive final_state: state -> int -> Prop :=
      | final_state_intro: forall r m,
          final_state (Returnstate (Vint r) Kstop m) r

     Inductive final_state: state -> int -> Prop :=
      | final_state_intro: forall r m,
          final_state (Returnstate (Vint r) Kstop m) r.                      

     Field semantics (p: program) :=
       Semantics step (self.initial_state p) self.final_state (Genv.globalenv p).
}

family ClightVariant extends Cfrontend { }
family CminorVariant extends Cfrontend { }



