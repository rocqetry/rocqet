(* We need to override the `Lgetstack` / `Lsetstack` 
   instructions to use actual offsets instead of 
   an abstract stack slot. *)
(* I think maybe the stack slot should be a parameter 
   of the `Impbackend` family *)
family Mach {
    Definition label := positive
    
    Inductive instruction: Type :=
      | Mgetstack: ptrofs -> typ -> mreg -> instruction
      | Msetstack: mreg -> ptrofs -> typ -> instruction
      | Mgetparam: ptrofs -> typ -> mreg -> instruction
      | Mop: operation -> list mreg -> mreg -> instruction
      | Mlabel: label -> instruction
      | Mgoto: label -> instruction
      | Mcond: condition -> list mreg -> label -> instruction
      | Mjumptable: mreg -> list label -> instruction        

    Definition code := list instruction                                            
      
    family Semantics { 
      Inductive stackframe: Type :=
        | Stackframe:
            forall (f: block) (* pointer to calling function *)
                   (sp: val) (* stack pointer in calling function *)
                   (retaddr: val) (* Asm return address in calling function *)
                   (c: code), (* program point in calling function *)
            stackframe.

      Inductive state: Type :=
        | State:
            forall (stack: list stackframe)(* call stack *)
                   (f: block) (* pointer to current function *)
                   (sp: val) (* stack pointer *)
                   (c: code) (* current program point *)
                   (rs: regset), (* register state *)        
            state
        | Callstate:
            forall (stack: list stackframe) (* call stack *)
                   (f: block) (* pointer to function to call *)
                   (rs: regset), (* register state *)
            state
        | Returnstate:
            forall (stack: list stackframe), (* call stack *)
                   (rs: regset), (* register state *)                   
            state.

      Inductive step: state -> trace -> state -> Prop :=
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
       | exec_Mjumptable:
           forall s fb f sp arg tbl c rs m n lbl c' rs',
           rs arg = Vint n ->
           list_nth_z tbl (Int.unsigned n) = Some lbl ->
           Genv.find_funct_ptr ge fb = Some (Internal f) ->
           find_label lbl f.(fn_code) = Some c' ->
           rs' = undef_regs destroyed_by_jumptable rs ->
           step (State s fb sp (Mjumptable arg tbl :: c) rs m)
             E0 (State s fb sp c' rs' m)

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

       Definition semantics (rao: function -> code -> ptrofs -> Prop) (p: program) :=
         Semantics (step rao) (initial_state p) final_state (Genv.globalenv p).
    }
}


(* Stacking translation: Linear -> Mach  *)
family Impzero.Impstacking extends ImpbackendTransform {
  family Source extends Implinear { }
  family Target extends Impmach { }

  family CorrectnessProof { }
}
