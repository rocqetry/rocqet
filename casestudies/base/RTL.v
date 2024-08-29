

family Imzero.RTL { 
    Inductive instruction : Type := 
        | Inop: node -> instruction
        | Iop: operation -> list reg -> reg -> node -> instruction        
        | Icond: condition -> list reg -> node -> node -> instruction      
        | Ijumptable: reg -> list node -> instruction        
      
    
    family Semantics {       
        Inductive stackframe : Type :=
          | Stackframe:
              forall (res: reg)(* where to store the result *)
                     (f: function)(* calling function *)
                     (sp: val)(* stack pointer in calling function *)
                     (pc: node)(* program point in calling function *)
                     (rs: regset),(* register state in calling function *)
              stackframe.
        
        Inductive state : Type :=
          | State:
              forall (stack: list stackframe)(* call stack *)
                     (f: function)(* current function *)
                     (sp: val)(* stack pointer *)
                     (pc: node)(* current program point in c *)
                     (rs: regset)(* register state *)
                     (m: mem),(* memory state *)
              state
          | Callstate:
              forall (stack: list stackframe)(* call stack *)
                     (f: fundef)(* function to call *)
                     (args: list val)(* arguments to the call *)
                     (m: mem),(* memory state *)
              state
          | Returnstate:
              forall (stack: list stackframe)(* call stack *)
                     (v: val)(* return value for the call *)
                     (m: mem),(* memory state *)
              state.

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
           | exec_Ijumptable:
               forall s f sp pc rs m arg tbl n pc',
               (fn_code f)!pc = Some(Ijumptable arg tbl) ->
               rs#arg = Vint n ->
               list_nth_z tbl (Int.unsigned n) = Some pc' ->
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
    }

}


(* Impminorsel -> RTL *)
(* Nanopasses: *)
(* 
1. Construction of the CFG

*)
family RTLgen extends BackendTranslation {
  
}
