family LTL extends Cbackend {
    Definition node := positive
    
    Inductive instruction: Type :=
       | Lgetstack (sl: slot) (ofs: Z) (ty: typ) (dst: mreg)
       | Lsetstack (src: mreg) (sl: slot) (ofs: Z) (ty: typ)       
       | Lop (op: operation) (args: list mreg) (res: mreg)       
       | Lbranch (s: node)
       | Lcond (cond: condition) (args: list mreg) (s1 s2: node)
       | Ljumptable (arg: mreg) (tbl: list node)

    Definition bblock := list instruction 

    Definition code := PTree.t bblock
                               
    family Semantics {                            
    
      Inductive stackframe : Type :=
         | Stackframe:
             forall (f: function)(* calling function *)
                    (sp: val)(* stack pointer in calling function *)
                    (ls: locset)(* location state in calling function *)
                    (bb: bblock),(* continuation in calling function *)
                stackframe.
      
      Inductive state : Type :=
        | State:
            forall (stack: list stackframe)(* call stack *)
                   (f: function) (* function currently executing *)
                   (sp: val) (* stack pointer *)
                   (pc: node) (* current program point *)
                   (ls: locset) (* location state *)                 
            state
        | Block:
            forall (stack: list stackframe) (* call stack *)
                   (f: function) (* function currently executing *)
                   (sp: val) (* stack pointer *)
                   (bb: bblock) (* current basic block *)
                   (ls: locset) (* location state *)                 
            state
          
       Inductive step: state -> trace -> state -> Prop :=
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
         | exec_Ljumptable: forall s f sp arg tbl bb rs m n pc rs',
             rs (R arg) = Vint n ->
             list_nth_z tbl (Int.unsigned n) = Some pc ->
             rs' = undef_regs (destroyed_by_jumptable) rs ->
             step (Block s f sp (Ljumptable arg tbl :: bb) rs m)
               E0 (State s f sp pc rs' m)


       Inductive initial_state (p: program): state -> Prop :=
         | initial_state_intro: forall b f m0,
              let ge := Genv.globalenv p in              
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

family RegisterAllocation extends Translation { 
    
}
