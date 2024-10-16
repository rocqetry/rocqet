Require Import Base.

Family MemExt extends Base.
   Family C.
       FInductive expr : Type :=
         | Evalof : expr -> type -> expr (* l-value used as a r-value *)
         | Ederef : expr -> type -> expr (* pointer dereference (unary * ) *)
         | Eaddrof : expr -> type -> expr (* address-of operators (&) *)
         | Eassign : expr -> expr -> type -> expr. (* assignment l = r *)        
      
      FInductive estep: state -> trace -> state -> Prop :=
         | step_assign: forall f C l r ty k e m b ofs bf v v1 t m' v',
             leftcontext RV RV C ->
             eval_simple_lvalue e m l b ofs bf ->
             eval_simple_rvalue e m r v ->
             sem_cast v (typeof r) (typeof l) m = Some v1 ->
             assign_loc ge (typeof l) m b ofs bf v1 t m' v' ->
             ty = typeof l ->
             estep (ExprState f (C (Eassign l r ty)) k e m)
                 t (ExprState f (C (Eval v' ty)) k e m').
   FEnd C.

   Family Clight.
      FInductive expr : Type :=
         | Ederef: expr -> type -> expr(* pointer dereference ( unary * ) *)
         | Eaddrof: expr -> type -> expr(* address-of operator (&) *)                                
                                            
      FInductive statement : Type :=
          | Sassign : expr -> expr -> statement. (* assignment lvalue = rvalue *)

      FInductive eval_expr: expr -> val -> Prop :=
          | eval_Eaddrof: forall a ty loc ofs,
              eval_lvalue a loc ofs Full ->
              eval_expr (Eaddrof a ty) (Vptr loc ofs)
          | eval_Elvalue: forall a loc ofs bf v,
               eval_lvalue a loc ofs bf ->
               deref_loc (typeof a) m loc ofs bf v ->
               eval_expr a v
      with eval_lvalue: expr -> block -> ptrofs -> bitfield -> Prop :=                         
            | eval_Ederef: forall a ty l ofs,
                 eval_expr a (Vptr l ofs) ->
                 eval_lvalue (Ederef a ty) l ofs Full
              
      FInductive step: state -> trace -> state -> Prop :=
         | step_assign: forall f a1 a2 k e le m loc ofs bf v2 v m',
             eval_lvalue e le m a1 loc ofs bf ->
             eval_expr e le m a2 v2 ->
             sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
             assign_loc ge (typeof a1) m loc ofs bf v m' ->
             step (State f (Sassign a1 a2) k e le m)
               E0 (State f Sskip k e le m').        
   FEnd Clight.
   
   Family Csharpminor.
      FInductive expr : Type :=
        | Eload : memory_chunk -> expr -> expr.
        
      FInductive stmt : Type :=
        | Sstore : memory_chunk -> expr -> expr -> stmt.

      FInductive eval_expr: expr -> val -> Prop :=
         | eval_Eload: forall chunk a v1 v,
            eval_expr a v1 ->
            Mem.loadv chunk m v1 = Some v ->
            eval_expr (Eload chunk a) v.
      
      FInductive step: state -> trace -> state -> Prop :=
        | step_store: forall f chunk addr a k e le m vaddr v m',
           eval_expr e le m addr vaddr ->
           eval_expr e le m a v ->
           Mem.storev chunk m vaddr v = Some m' ->
           step (State f (Sstore chunk addr a) k e le m)
             E0 (State f Sskip k e le m').      
   FEnd Csharpminor.
   
   Family Cminor.
       FInductive expr : Type :=
          | Eload : memory_chunk -> expr -> expr.

       FInductive stmt : Type := 
         | Sstore : memory_chunk -> expr -> expr -> stmt.
       
       FInductive eval_expr: expr -> val -> Prop :=
         | eval_Eload: forall chunk addr vaddr v,
            eval_expr addr vaddr ->
            Mem.loadv chunk m vaddr = Some v ->
            eval_expr (Eload chunk addr) v.

       FInductive step: state -> trace -> state -> Prop :=
         | step_store: forall f chunk addr a k sp e m vaddr v m',
             eval_expr sp e m addr vaddr ->
             eval_expr sp e m a v ->
             Mem.storev chunk m vaddr v = Some m' ->
             step (State f (Sstore chunk addr a) k sp e m)
               E0 (State f Sskip k sp e m').
   FEnd Cminor.   

   Family CminorSel.
       FInductive expr : Type := 
         | Eload : memory_chunk -> addressing -> exprlist -> expr.
         
       FInductive stmt : Type :=
         | Sstore : memory_chunk -> addressing -> exprlist -> expr -> stmt.

       FInductive eval_expr: letenv -> expr -> val -> Prop :=
         | eval_Eload: forall le chunk addr al vl vaddr v,
            eval_exprlist le al vl ->
            eval_addressing ge sp addr vl = Some vaddr ->
            Mem.loadv chunk m vaddr = Some v ->
            eval_expr le (Eload chunk addr al) v.

       FInductive step: state -> trace -> state -> Prop :=
          | step_store: forall f chunk addr al b k sp e m vl v vaddr m',
               eval_exprlist sp e m nil al vl ->
               eval_expr sp e m nil b v ->
               eval_addressing ge sp addr vl = Some vaddr ->
               Mem.storev chunk m vaddr v = Some m' ->
               step (State f (Sstore chunk addr al b) k sp e m)
                 E0 (State f Sskip k sp e m').
   FEnd CminorSel.

   Family LTL. 
      FInductive instruction: Type :=        
        | Lload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
        | Lstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction.

      FInductive step: state -> trace -> state -> Prop :=
          | exec_Lload: forall s f sp chunk addr args dst bb rs m a v rs',
              eval_addressing ge sp addr (reglist rs args) = Some a ->
              Mem.loadv chunk m a = Some v ->
              rs' = Locmap.set (R dst) v (undef_regs (destroyed_by_load chunk addr) rs) ->
              step (Block s f sp (Lload chunk addr args dst :: bb) rs m)
                E0 (Block s f sp bb rs' m)
          | exec_Lstore: forall s f sp chunk addr args src bb rs m a rs' m',
              eval_addressing ge sp addr (reglist rs args) = Some a ->
              Mem.storev chunk m a (rs (R src)) = Some m' ->
              rs' = undef_regs (destroyed_by_store chunk addr) rs ->
              step (Block s f sp (Lstore chunk addr args src :: bb) rs m)
                E0 (Block s f sp bb rs' m').
   FEnd LTL.
   
   Family Lfam.
       FInductive instruction: Type :=
         | Lload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
         | Lstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction.

       FInductive step: state -> trace -> state -> Prop :=
          | exec_Lload:
             forall s f sp chunk addr args dst b rs m a v rs',
             eval_addressing ge sp addr (reglist rs args) = Some a ->
             Mem.loadv chunk m a = Some v ->
             rs' = Locmap.set (R dst) v (undef_regs (destroyed_by_load chunk addr) rs) ->
             step (State s f sp (Lload chunk addr args dst :: b) rs m)
               E0 (State s f sp b rs' m)
          | exec_Lstore:
              forall s f sp chunk addr args src b rs m m' a rs',
              eval_addressing ge sp addr (reglist rs args) = Some a ->
              Mem.storev chunk m a (rs (R src)) = Some m' ->
              rs' = undef_regs (destroyed_by_store chunk addr) rs ->
              step (State s f sp (Lstore chunk addr args src :: b) rs m)
                E0 (State s f sp b rs' m').
   FEnd Lfam.
FEnd MemExt.
