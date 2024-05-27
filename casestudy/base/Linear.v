family Base.Linear extends Impbackend { 
    Definition label := positive

    Inductive instruction: Type :=
       | Lgetstack: slot -> Z -> typ -> mreg -> instruction
       | Lsetstack: mreg -> slot -> Z -> typ -> instruction
       | Lop: operation -> list mreg -> mreg -> instruction
       | Llabel: label -> instruction
       | Lgoto: label -> instruction
       | Lcond: condition -> list mreg -> label -> instruction
       | Ljumptable: mreg -> list label -> instruction

    Definition code: Type := list instruction                                            

    family Semantics { 
        Inductive stackframe: Type :=
           | Stackframe:
               forall (f: function) (* calling function *)
                      (sp: val) (* stack pointer in calling function *)
                      (rs: locset) (* location state in calling function *)
                      (c: code), (* program point in calling function *)
               stackframe.

         Inductive state: Type :=
           | State:
               forall (stack: list stackframe) (* call stack *)
                      (f: function) (* function currently executing *)
                      (sp: val) (* stack pointer *)
                      (c: code) (* current program point *)
                      (rs: locset) (* location state *)                       
               state
           | Callstate:
               forall (stack: list stackframe)(* call stack *)
                      (f: fundef)(* function to call *)
                      (rs: locset)(* location state at point of call *)                      
               state
           | Returnstate:
               forall (stack: list stackframe)(* call stack *)
                      (rs: locset)(* location state at point of return *)                      
               state.

          Inductive step: state -> trace -> state -> Prop :=
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
                eval_operation ge sp op (reglist rs args) m = Some v ->
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
            | exec_Ljumptable:
              forall s f sp arg tbl b rs m n lbl b' rs',
              rs (R arg) = Vint n ->
              list_nth_z tbl (Int.unsigned n) = Some lbl ->
              find_label lbl f.(fn_code) = Some b' ->
              rs' = undef_regs (destroyed_by_jumptable) rs ->
              step (State s f sp (Ljumptable arg tbl :: b) rs m)
                E0 (State s f sp b' rs' m)
                
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

           Definition semantics (p: program) :=
             Semantics step (initial_state p) final_state (Genv.globalenv p).
    }
}

(* LTL -> Linear translation *)

family Impzero.Implinearize extends BackendTransform {  
  family Source extends Impltl { }
  family Target extends Implinear { }

  family CorrectnessProof { }
}
