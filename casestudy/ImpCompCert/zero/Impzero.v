family Impzero.RTL {
    Definition node := positive.
    
    Inductive instruction: Type :=
       | Inop: node -> instruction       
       | Iop: Asm.Op.operation -> list reg -> reg -> node -> instruction           
       | Icond: Asm.Op.condition -> list reg -> node -> node -> instruction
  
   Definition code: Type := PTree.t instruction.

    family Semantics {
       Inductive stackframe : Type :=
           | Stackframe:
               forall (res: reg)            (**r where to store the result *)                      
                      (pc: node)            (**r program point *)
                      (rs: regset),         (**r register state *)
                 stackframe
                   
       Inductive state : Type :=
          | State:
              forall (stack: list stackframe) (**r call stack *)                     
                     (sp: val)                (**r stack pointer *)
                     (pc: node)               (**r current program point in [c] *)
                     (rs: regset),             (**r register state *)                     
                state

        Inductive step: state -> trace -> state -> Prop :=
           | exec_Inop:
               forall s f sp pc rs m pc',
               (fn_code f)!pc = Some(Inop pc') ->
               step (State s f sp pc rs m)
                 E0 (State s f sp pc' rs m)
           | exec_Iop:
               forall s f sp pc rs m op args res pc' v,
               (fn_code f)!pc = Some(Iop op args res pc') ->
               eval_operation ge sp op rs##args m = Some v ->
               step (State s f sp pc rs m)
                 E0 (State s f sp pc' (rs#res <- v) m)
            | exec_Icond:
               forall s f sp pc rs m cond args ifso ifnot b pc',
               (fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
               eval_condition cond rs##args m = Some b ->
               pc' = (if b then ifso else ifnot) ->
               step (State s f sp pc rs m)
                 E0 (State s f sp pc' rs m)
    }
}

family Impzero.LTL {
   Definition node := positive.

   Inductive instruction: Type :=
     | Lop (op: operation) (args: list mreg) (res: mreg)
     | Lbranch (s: node)
     | Lcond (cond: condition) (args: list mreg) (s1 s2: node)     
   
   Definition bblock := list instruction.
   
   Definition code: Type := PTree.t bblock.

   family Semantics {
     Inductive stackframe : Type :=
        | Stackframe:
            forall (sp: val)          (**r stack pointer *)
                   (ls: locset)       (**r location state *)
                   (bb: bblock),      (**r continuation *)
            stackframe

       Inductive state : Type :=
         | State:
             forall (stack: list stackframe) (**r call stack *)                    
                    (sp: val)                (**r stack pointer *)
                    (pc: node)               (**r current program point *)
                    (ls: locset),             (**r location state *)                    
             state
   }
}   

       
(* Sharing between LTL and RTL *)       
family Impzero.TransferLanguge {
}

family Impzero {
   family LTL { }

   family RTL { }

   family Linearcommon {
       family Semantics { }
   }

   family Linear extends Linearcommon {
          
   }

   family Mach extends Linearcommon {

   }

   family Processor {
      family Op { }      
   } 

   family Aarch64 extends Processor {
      family Op { }
   }
}


