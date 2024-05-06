(* Common IR for Impbackend languages *)

family Base.Impbackend {
    Inductive instruction :=
        | Lop (op: operation) (args: list mreg) (res: mreg)        
        | Lgetstack (sl: slot) (ofs: Z) (ty: typ) (dst: mreg) (* for local variables *)
        | Lsetstack (src: mreg) (sl: slot) (ofs: Z) (ty: typ)        
        | Lcond (cond: condition) (args: list mreg) (s1 s2: node)                

    family Semantics { }

    family Program { 
      (* Definition bblock := list instruction.
         Definition code: Type := PTree.t bblock. *)
       Field code := ... 
      
       Record function : Type := mkfunction {          
          fn_stacksize: Z;
          fn_code: code
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
}

family Base.Impbackend.Semantics {
     Inductive stackframe: Type :=
        | Stackframe:
            forall (f: function)         (**r calling function *)
                   (sp: val)             (**r stack pointer in calling function *)
                   (rs: locset)          (**r location state in calling function *)
                   (c: code),            (**r program point in calling function *)
            stackframe.

     Inductive state: Type :=
        | State:
            forall (stack: list stackframe) (**r call stack *)
                   (f: function)            (**r function currently executing *)
                   (sp: val)                (**r stack pointer *)
                   (rs: locset)             (**r location state *)
                   (c: code),                (**r current program point *)
            state
      
      Inductive step: state -> state -> Prop := 
         | exec_Lgetstack:
              forall s f sp sl ofs ty dst b rs m rs',
              load_stack m sp ty ofs = Some v ->
              step (State s f sp (Lgetstack sl ofs ty dst :: b) rs m)
                   (State s f sp b rs' m)
         | exec_Lsetstack:
              forall s f sp src sl ofs ty b rs m rs',
              store_stack m sp ty ofs (rs src) = Some m' ->
              step (State s f sp (Lsetstack src sl ofs ty :: b) rs m)
                   (State s f sp b rs' m)
         | exec_Lop:
              forall s f sp op args res b rs m v rs',
              eval_operation ge sp op (reglist rs args) m = Some v ->
               rs' = Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs) ->
               step (State s f sp (Lop op args res :: b) rs m)
                    (State s f sp b rs' m)
         | exec_Lcond_true:
              forall s f sp cond args lbl b rs m rs' b',
              eval_condition cond (reglist rs args) m = Some true ->
              rs' = undef_regs (destroyed_by_cond cond) rs ->
              find_label lbl f.(fn_code) = Some b' ->
              step (State s f sp (Lcond cond args lbl :: b) rs m)
                   (State s f sp b' rs' m)
         | exec_Lcond_false:
             forall s f sp cond args lbl b rs m rs',
             eval_condition cond (reglist rs args) m = Some false ->
             rs' = undef_regs (destroyed_by_cond cond) rs ->
             step (State s f sp (Lcond cond args lbl :: b) rs m)
                  (State s f sp b rs' m)

   Inductive initial_state := ...
   Inductive final_states := ...
   Field semantics := ...
}


family Base.ControlFlowGraphIR extends Impbackend {


}

family Base.LinearIR extends Impbackend { 
  
}
