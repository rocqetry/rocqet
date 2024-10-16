Require Import Base.

Family CallExt extends Base. 
   Family C.
      FInductive expr : Type :=
        | Ecall : expr -> list expr -> type -> expr.

      FInductive cont: Type :=
        | Kcall: function ->(* calling function *)
           env ->(* local env of calling function *)
           (expr -> expr) ->(* context of the call *)
           type ->(* type of call expression *)
           cont -> cont.
      
      FInductive estep: state -> trace -> state -> Prop :=
         | step_call: forall f C rf rargs ty k e m targs tres cconv vf vargs fd,
             leftcontext RV RV C ->
             classify_fun (typeof rf) = fun_case_f targs tres cconv ->
             eval_simple_rvalue e m rf vf ->
             eval_simple_list e m rargs targs vargs ->
             Genv.find_funct ge vf = Some fd ->
             type_of_fundef fd = Tfunction targs tres cconv ->
             estep (ExprState f (C (Ecall rf rargs ty)) k e m)
                E0 (Callstate fd vargs (Kcall f e C ty k) m).
   FEnd C.

   Family Cfam.
       FInductive stmt : Type :=
         | Scall : option ident -> signature -> expr -> list expr -> stmt.

       FInductive cont: Type :=
         | Kcall: option ident -> function -> fenv -> env -> cont -> cont.

       FInductive step: state -> trace -> state -> Prop :=
         | step_call: forall f optid sig a bl k sp e m vf vargs fd,
            eval_expr sp e m a vf ->
            eval_exprlist sp e m bl vargs ->
            Genv.find_funct ge vf = Some fd ->
            funsig fd = sig ->
            step (State f (Scall optid sig a bl) k sp e m)
              E0 (Callstate fd vargs (Kcall optid f sp e k) m)
         | step_return: forall v optid f sp e k m,
            step (Returnstate v (Kcall optid f sp e k) m)
              E0 (State f Sskip k sp (set_optvar optid v e) m).
   FEnd Cfam.      
   
   Family Cminor extends Cfam.
        FInductive stmt : Type :=
          | Stailcall: signature -> expr -> list expr -> stmt.

        FInductive step: state -> trace -> state -> Prop :=
          | step_tailcall: forall f sig a bl k sp e m vf vargs fd m',
               eval_expr (Vptr sp Ptrofs.zero) e m a vf ->
               eval_exprlist (Vptr sp Ptrofs.zero) e m bl vargs ->
               Genv.find_funct ge vf = Some fd ->
               funsig fd = sig ->
               Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
               step (State f (Stailcall sig a bl) k (Vptr sp Ptrofs.zero) e m)
                 E0 (Callstate fd vargs (call_cont k) m')
   FEnd Cminor.   

   Family CminorSel extends Cfam.
      FInductive stmt : Type :=  
        | Stailcall: signature -> expr + ident -> exprlist -> stmt.

      FInductive step: state -> trace -> state -> Prop :=
        | step_tailcall: forall f sig a bl k sp e m vf vargs fd m',
            eval_expr_or_symbol (Vptr sp Ptrofs.zero) e m nil a vf ->
            eval_exprlist (Vptr sp Ptrofs.zero) e m nil bl vargs ->
            Genv.find_funct ge vf = Some fd ->
            funsig fd = sig ->
            Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
            step (State f (Stailcall sig a bl) k (Vptr sp Ptrofs.zero) e m)
              E0 (Callstate fd vargs (call_cont k) m')
   FEnd CminorSel.

   Family LTL. 
      FInductive instruction: Type :=
        | Lcall : signature -> mreg + ident -> instruction
        | Ltailcall : signature -> mreg + ident -> instruction.

      FInductive step: state -> trace -> state -> Prop :=
         | exec_Lcall: forall s f sp sig ros bb rs m fd,
             find_function ros rs = Some fd ->
             funsig fd = sig ->
             step (Block s f sp (Lcall sig ros :: bb) rs m)
               E0 (Callstate (Stackframe f sp rs bb :: s) fd rs m)
         | exec_Ltailcall: forall s f sp sig ros bb rs m fd rs' m',
             rs' = return_regs (parent_locset s) rs ->
             find_function ros rs' = Some fd ->
             funsig fd = sig ->
             Mem.free m sp 0 f.(fn_stacksize) = Some m' ->
             step (Block s f (Vptr sp Ptrofs.zero) (Ltailcall sig ros :: bb) rs m)
               E0 (Callstate s fd rs' m').
   FEnd LTL.
   
   Family Lfam.
       FInductive instruction: Type :=
         | Lcall: signature -> mreg + ident -> instruction
         | Ltailcall: signature -> mreg + ident -> instruction

       FInductive step: state -> trace -> state -> Prop :=
          | exec_Lcall:
              forall s f sp sig ros b rs m f',
              find_function ros rs = Some f' ->
              sig = funsig f' ->
              step (State s f sp (Lcall sig ros :: b) rs m)
                E0 (Callstate (Stackframe f sp rs b:: s) f' rs m)
          | exec_Ltailcall:
              forall s f stk sig ros b rs m rs' f' m',
              rs' = return_regs (parent_locset s) rs ->
              find_function ros rs' = Some f' ->
              sig = funsig f' ->
              Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
              step (State s f (Vptr stk Ptrofs.zero) (Ltailcall sig ros :: b) rs m)
                E0 (Callstate s f' rs' m')
   FEnd Lfam.
FEnd CallExt.
