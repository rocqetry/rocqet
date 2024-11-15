From NFPOP Require Import Loader.

From NFPOP Require Import Coqlib.
From NFPOP Require Import Errors.
From NFPOP Require Import Values.
From NFPOP Require Import AST.
From NFPOP Require Import Integers. 
From NFPOP Require Import Floats.
From NFPOP Require Import Memory.
From NFPOP Require Import Globalenvs.
From NFPOP Require Import Smallstep.
From NFPOP Require Import Events.
From NFPOP Require Import Maps.
From NFPOP Require Import Linking.
Require Import NFPOP.CompCert.lib.Ctypes.
From NFPOP Require Import Cop.
From NFPOP Require Import Mon.
Require Import FSets.
Require Import FSetAVL.
Require Import Orders.
Require Import Mergesort.
Require Import Ordered.
Require Import Coq.ZArith.ZArith.
From NFPOP Require Import Prelude.
From NFPOP Require Import Op.

Local Open Scope string_scope.
Local Open Scope list_scope.
Open Scope asm.

Trait Base.

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
| Ecomma : expr -> expr -> type -> expr (* sequence expression r1, r2 *)                
| Eparen : expr -> type -> type -> expr
| Eunop  : Cop.unary_operation -> expr -> type -> expr
| Ebinop : Cop.binary_operation -> expr -> expr -> type -> expr
with exprlist : Type :=
| Enil : exprlist
| Econs : expr -> exprlist -> exprlist.                                                               
        
FRecursion typeof about expr motive (fun (_ : expr) => type) by _rect.
Case Eval v ty := ty.
Case Evar x ty := ty.          
Case Ecast r ty := ty. 
Case Eseqand r1 r2 ty := ty. 
Case Eseqor r1 r2 ty := ty. 
Case Econdition r1 r2 r3 ty := ty.
Case Esizeof ty' ty := ty.
Case Ealignof ty' ty := ty.          
Case Ecomma r1 r2 ty := ty.
Case Eparen e ty' ty := ty.
Case Eunop op e ty := ty.
Case Ebinop op e1 e2 ty := ty.
FEnd typeof.

FDefinition label := ident.     
FInductive stmt : Type :=
| Sseq : stmt -> stmt -> stmt
| Sskip : stmt
| Sdo : expr -> stmt(* evaluate expression for side effects *)        
| Sifthenelse : expr -> stmt -> stmt -> stmt(* conditional *)
| Sreturn : option expr -> stmt (* return statement *)
| Slabel : label -> stmt -> stmt
| Sgoto : label -> stmt
with lbl_stmts : Type :=(* cases of a switch *)
| LSnil: lbl_stmts
| LScons: option Z -> stmt -> lbl_stmts -> lbl_stmts.                       

MetaData function.
Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_body: self__C.stmt
}.
FEnd function.

FDefinition var_names := fun (vars: list(ident * type)) =>
  List.map (@fst ident type) vars.

FDefinition fundef := Ctypes.fundef function.

FDefinition type_of_function : function -> type := fun f => 
  Tfunction (type_of_params (self__C.fn_params f)) (self__C.fn_return f) (self__C.fn_callconv f).

FDefinition type_of_fundef : fundef -> type := fun f => 
  match f with
  | Internal fd => type_of_function fd
  | External id args res cc => Tfunction args res cc
  end.

FDefinition program := Ctypes.program function.

FEnd C. 


Family Clight.
FInductive expr : Type :=          
| Econst_int: int -> type -> expr(* integer literal *)
| Econst_float: float -> type -> expr(* double float literal *)
| Econst_single: float32 -> type -> expr(* single float literal *)
| Econst_long: int64 -> type -> expr(* long integer literal *)                                            
| Etempvar: ident -> type -> expr (* temporary variable *)          
| Esizeof: type -> type -> expr (* size of a type *)
| Ecast: expr -> type -> expr
| Ealignof: type -> type -> expr (* alignment of a type *)
| Eunop: Cop.unary_operation -> expr -> type -> expr (* unary operation *)
  | Ebinop: Cop.binary_operation -> expr -> expr -> type -> expr. (* binary operation *)

       
FRecursion typeof about expr motive (fun (_ : expr) => type) by _rect. 
Case Econst_int i ty := ty. 
Case Econst_float f ty := ty. 
Case Econst_single s ty := ty. 
Case Econst_long l ty := ty. 
Case Etempvar v ty := ty.
Case Esizeof ty' ty := ty.
Case Ealignof ty' ty := ty.
Case Ecast e ty := ty.
Case Eunop op e ty := ty.
Case Ebinop op e0 e1 ty := ty.
FEnd typeof.
       
FDefinition label := ident.
FInductive stmt : Type :=                                        
| Sskip : stmt (* do nothing *)
| Sset : ident -> expr -> stmt (* assignment tempvar = rvalue *)
| Sseq : stmt -> stmt -> stmt (* sequence *)
| Sifthenelse : expr -> stmt -> stmt -> stmt (* conditional *)
| Sreturn : option expr -> stmt (* return statement *)
| Slabel : label -> stmt -> stmt
| Sgoto : label -> stmt
with lbl_stmts : Type :=(* cases of a switch *)
| LSnil: lbl_stmts
| LScons: option Z -> stmt -> lbl_stmts -> lbl_stmts.                       
              
MetaData function.
Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_temps: list (ident * type);
  fn_body: self__Clight.stmt
}.
FEnd function.
              
FDefinition fundef := Ctypes.fundef function.
       
FDefinition type_of_function : function -> type := fun f => 
  Tfunction (type_of_params (self__Clight.fn_params f)) (self__Clight.fn_return f) (self__Clight.fn_callconv f).

FDefinition type_of_fundef : fundef -> type := fun f => 
  match f with
  | Internal fd => type_of_function fd
  | External id args res cc => Tfunction args res cc
  end.

FDefinition program := Ctypes.program function.

FEnd Clight.

(* C -> Clight *)
Family SimplExpr.
Family S extends C. FEnd S.
Family T extends Clight. FEnd T.

Local Open Scope gensym_monad_scope.

MetaData makeseq_rec.
Fixpoint makeseq_rec (s: self__SimplExpr.T.stmt) (l: list self__SimplExpr.T.stmt) : self__SimplExpr.T.stmt :=
   match l with
   | nil => s
   | s' :: l' => makeseq_rec (self__SimplExpr.T.Sseq s s') l'
    end.
FEnd makeseq_rec.
      
FDefinition makeseq : list self__SimplExpr.T.stmt -> self__SimplExpr.T.stmt := fun l => 
  makeseq_rec self__SimplExpr.T.Sskip l.

MetaData set_destination.
Inductive set_destination : Type :=
| SDbase (tycast ty: type) (tmp: ident)
| SDcons (tycast ty: type) (tmp: ident) (sd: set_destination).
FEnd set_destination.

MetaData destination.
Inductive destination : Type :=
| For_val
| For_effects
| For_set (sd: self__SimplExpr.set_destination).
FEnd destination.

MetaData do_set. 
Fixpoint do_set (sd: self__SimplExpr.set_destination) (a: self__SimplExpr.T.expr) : list self__SimplExpr.T.stmt :=
    match sd with
    | self__SimplExpr.SDbase tycast ty tmp => self__SimplExpr.T.Sset tmp (self__SimplExpr.T.Ecast a tycast) :: nil
    | self__SimplExpr.SDcons tycast ty tmp sd' => self__SimplExpr.T.Sset tmp (self__SimplExpr.T.Ecast a tycast) :: do_set sd' (self__SimplExpr.T.Etempvar tmp ty)
    end.
FEnd do_set.

FDefinition finish := fun (dst: destination) (sl: list T.stmt) (a: T.expr) => 
  match dst with
  | self__SimplExpr.For_val => (sl, a)
  | self__SimplExpr.For_effects => (sl, a)
  | self__SimplExpr.For_set sd => (sl ++ do_set sd a, a)
  end.

FDefinition sd_temp := fun (sd: set_destination) =>
  match sd with self__SimplExpr.SDbase _ _ tmp => tmp | self__SimplExpr.SDcons _ _ tmp _ => tmp end.
         
FDefinition sd_head_type := fun (sd: set_destination) => 
  match sd with self__SimplExpr.SDbase _ ty _ => ty | self__SimplExpr.SDcons _ ty _ _ => ty end.
         
FDefinition temp_for_sd : type -> set_destination -> mon ident := fun ty sd => 
  if type_eq ty (sd_head_type sd) then ret (sd_temp sd) else gensym ty.
    
FDefinition dummy_expr := T.Econst_int Int.zero type_int32s.
      
FRecursion eval_simpl_expr about T.expr motive (fun (_ : T.expr) => option val) by _rect.          
Case Econst_float n ty := (Some(Vfloat n)).
Case Econst_int n ty := (Some(Vint n)).
Case Econst_single n ty := (Some(Vsingle n)).
Case Econst_long n ty := (Some(Vlong n)).
Case Ecast b ty := 
  (match eval_simpl_expr b with
    | None => None
    | Some v => Cop.sem_cast v (T.typeof b) ty Mem.empty
    end).
Case Etempvar id ty := None.
Case Esizeof ty' ty := None.
Case Ealignof ty' ty := None.
Case _ := None.
FEnd eval_simpl_expr.

FDefinition makeif : T.expr -> T.stmt -> T.stmt -> T.stmt :=
  fun a s1 s2 =>
    match eval_simpl_expr a with
    | Some v =>
        match Cop.bool_val v (T.typeof a) Mem.empty with
        | Some b => if b then s1 else s2
        | None => T.Sifthenelse a s1 s2
        end
    | None => T.Sifthenelse a s1 s2
    end.
      
FRecursion transl_expr about S.expr motive (fun (_ : S.expr) => composite_env -> destination -> mon (list T.stmt * T.expr))
      with transl_exprlist about S.exprlist motive (fun (_ : S.exprlist) => composite_env -> mon (list T.stmt * list T.expr)) by _rect.
Case Evar id ty := (fun ce dst => ret (finish dst nil (T.Etempvar id ty))).
Case Eval v ty := 
  (fun ce dst => 
    match v with 
    | Vint n => ret (finish dst nil (T.Econst_int n ty)) 
    | Vlong n =>  ret (finish dst nil (T.Econst_long n ty))
    | Vfloat n => ret (finish dst nil (T.Econst_float n ty))
    | Vsingle n => ret (finish dst nil (T.Econst_single n ty))
    | _ => error (msg "SimplExpr.transl_expr: Eval") end).
Case Ecast r1 ty :=
  (fun ce dst => 
      match dst with
      | self__SimplExpr.For_val | self__SimplExpr.For_set _ =>
          do (sl1, a1) <- transl_expr r1 ce self__SimplExpr.For_val;
          ret (finish dst sl1 (T.Ecast a1 ty))
      | self__SimplExpr.For_effects =>
          transl_expr r1 ce self__SimplExpr.For_effects end).
Case Ecomma r1 r2 ty := 
   (fun ce dst => 
      do (sl1, a1) <- transl_expr r1 ce self__SimplExpr.For_effects;
      do (sl2, a2) <- transl_expr r2 ce dst;
      ret (sl1 ++ sl2, a2)).
Case Econdition r1 r2 r3 ty :=
  (fun ce dst => 
      do (sl1, a1) <- transl_expr r1 ce self__SimplExpr.For_val;
      match dst with
      | self__SimplExpr.For_val =>
          do t <- gensym ty;
          let sd := self__SimplExpr.SDbase ty ty t in
          do (sl2, a2) <- transl_expr r2 ce (self__SimplExpr.For_set sd);
          do (sl3, a3) <- transl_expr r3 ce (self__SimplExpr.For_set sd);
          ret (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil,
               T.Etempvar t ty)
      | self__SimplExpr.For_effects =>
          do (sl2, a2) <- transl_expr r2 ce self__SimplExpr.For_effects;
          do (sl3, a3) <- transl_expr r3 ce self__SimplExpr.For_effects;
          ret (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil,
               dummy_expr)
      | self__SimplExpr.For_set sd =>
          do t <- temp_for_sd ty sd;
          let sd' := self__SimplExpr.SDcons ty ty t sd in
          do (sl2, a2) <- transl_expr r2 ce (self__SimplExpr.For_set sd');
          do (sl3, a3) <- transl_expr r3 ce (self__SimplExpr.For_set sd');
          ret (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil,
               dummy_expr)
      end).
Case Eseqor r1 r2 ty := 
  (fun ce dst => 
    do (sl1, a1) <- transl_expr r1 ce self__SimplExpr.For_val;
      match dst with
      | self__SimplExpr.For_val =>
          do t <- gensym ty;
          let sd := self__SimplExpr.SDbase type_bool ty t in
          do (sl2, a2) <- transl_expr r2 ce (self__SimplExpr.For_set sd);
          ret (sl1 ++
               makeif a1 (T.Sset t (T.Econst_int Int.one ty)) (makeseq sl2) :: nil,
               T.Etempvar t ty)
      | self__SimplExpr.For_effects =>
          do (sl2, a2) <- transl_expr r2 ce self__SimplExpr.For_effects;
          ret (sl1 ++ makeif a1 T.Sskip (makeseq sl2) :: nil, dummy_expr)
      | self__SimplExpr.For_set sd =>
          do t <- temp_for_sd ty sd;
          let sd' := self__SimplExpr.SDcons type_bool ty t sd in
          do (sl2, a2) <- transl_expr r2 ce (self__SimplExpr.For_set sd');
          ret (sl1 ++
               makeif a1 (makeseq (do_set sd (T.Econst_int Int.one ty))) (makeseq sl2) :: nil,
               dummy_expr)
      end).
Case Eseqand r1 r2 ty := 
  (fun ce dst => 
    do (sl1, a1) <- transl_expr r1 ce self__SimplExpr.For_val;
      match dst with
      | self__SimplExpr.For_val =>
          do t <- gensym ty;
          let sd := self__SimplExpr.SDbase type_bool ty t in
          do (sl2, a2) <- transl_expr r2 ce (self__SimplExpr.For_set sd);
          ret (sl1 ++
               makeif a1 (makeseq sl2) (T.Sset t (T.Econst_int Int.zero ty)) :: nil,
               T.Etempvar t ty)
      | self__SimplExpr.For_effects =>
          do (sl2, a2) <- transl_expr r2 ce self__SimplExpr.For_effects;
          ret (sl1 ++ makeif a1 (makeseq sl2) T.Sskip :: nil, dummy_expr)
      | self__SimplExpr.For_set sd =>
          do t <- temp_for_sd ty sd;
          let sd' := self__SimplExpr.SDcons type_bool ty t sd in
          do (sl2, a2) <- transl_expr r2 ce (self__SimplExpr.For_set sd');
          ret (sl1 ++
               makeif a1 (makeseq sl2) (makeseq (do_set sd (T.Econst_int Int.zero ty))) :: nil,
               dummy_expr)
      end).                          
Case Esizeof ty' ty := (fun ce dst => ret (finish dst nil (T.Esizeof ty' ty))).
Case Ealignof ty' ty := (fun ce dst => ret (finish dst nil (T.Ealignof ty' ty))).
Case Eparen e tycast ty := (fun ce dst => error (msg "SimplExpr.transl_expr: paren")).
Case Eunop op r1 ty :=
  (fun ce dst =>
    do (sl1, a1) <- transl_expr r1 ce self__SimplExpr.For_val;
    ret (finish dst sl1 (T.Eunop op a1 ty))).
Case Ebinop op r1 r2 ty :=
  (fun ce dst =>
     do (sl1, a1) <- transl_expr r1 ce self__SimplExpr.For_val;
     do (sl2, a2) <- transl_expr r2 ce self__SimplExpr.For_val;
     ret (finish dst (sl1 ++ sl2) (T.Ebinop op a1 a2 ty))).

Case Enil := (fun ce => ret (nil, nil)).
Case Econs r1 rl2 := 
  (fun ce =>
     do (sl1, a1) <- transl_expr r1 ce self__SimplExpr.For_val;
     do (sl2, al2) <- transl_exprlist rl2 ce;
      ret (sl1 ++ sl2, a1 :: al2)).
FEnd transl_expr with transl_exprlist.

FDefinition transl_expression : S.expr -> composite_env -> mon (T.stmt * T.expr) := fun r ce =>
  do (sl, a) <- transl_expr r ce self__SimplExpr.For_val; ret (makeseq sl, a).

FDefinition transl_expr_stmt : S.expr -> composite_env -> mon T.stmt := fun r ce =>
  do (sl, a) <- transl_expr r ce self__SimplExpr.For_effects; ret (makeseq sl).

FDefinition transl_if : S.expr -> T.stmt -> T.stmt -> composite_env -> mon T.stmt  := fun r s1 s2 ce => 
  do (sl, a) <- transl_expr r ce self__SimplExpr.For_val;
  ret (makeseq (sl ++ makeif a s1 s2 :: nil)).

Closing Fact is_Sskip:
  forall s, {s = S.Sskip} + {s <> S.Sskip} by {  destruct s; ((left; reflexivity) || (right; congruence)) }.

FRecursion transl_stmt about S.stmt motive (fun (_ : S.stmt) => composite_env -> mon T.stmt)
       with transl_lblstmt about S.lbl_stmts motive (fun (_ : S.lbl_stmts) => composite_env -> mon T.lbl_stmts) by _rect.
Case Sskip := (fun ce => ret T.Sskip).
Case Sdo e := (fun ce => transl_expr_stmt e ce).
Case Sseq s1 s2 := 
  (fun ce => 
     do ts1 <- transl_stmt s1 ce;
     do ts2 <- transl_stmt s2 ce;
     ret (T.Sseq ts1 ts2)). 
Case Sifthenelse e s1 s2 := 
  (fun ce => 
     do ts1 <- transl_stmt s1 ce;
     do ts2 <- transl_stmt s2 ce;
     do (s', a) <- transl_expression e ce;
     if is_Sskip s1 && is_Sskip s2 then
       ret (T.Sseq s' T.Sskip)
     else
       ret (T.Sseq s' (T.Sifthenelse a ts1 ts2))).
Case Sreturn e := 
  (fun ce => 
    match e with
    | None => ret (T.Sreturn None)
    | Some e =>
        do (s', a) <- transl_expression e ce;
        ret (T.Sseq s' (T.Sreturn (Some a)))
    end).
Case Slabel lbl s1 := 
  (fun ce => 
     do ts1 <- transl_stmt s1 ce;
     ret (T.Slabel lbl ts1)).
Case Sgoto lbl := (fun ce => ret (T.Sgoto lbl)).

Case LSnil := (fun ce => ret T.LSnil).
Case LScons c s ls1 := 
  (fun ce =>
      do ts <- transl_stmt s ce;
      do tls1 <- transl_lblstmt ls1 ce;
      ret (T.LScons c ts tls1)).
FEnd transl_stmt with transl_lblstmt.

FDefinition transl_function : S.function -> composite_env -> res T.function := fun f ce => 
  match transl_stmt (S.fn_body f) ce (initial_generator tt) with
  | Err msg =>
      Error msg
  | Res tbody g i =>
      OK (T.mkfunction
              (S.fn_return f)
              (S.fn_callconv f)
              (S.fn_params f)
              (S.fn_vars f)
              g.(gen_trail)
              tbody)
  end.

Local Open Scope error_monad_scope.

FDefinition transl_fundef : composite_env -> S.fundef -> res T.fundef := fun ce fd =>
    match fd with
    | Internal f =>
        do tf <- transl_function f ce; OK (Internal tf)
    | External ef targs tres cc =>
      OK (External ef targs tres cc)           
    end.
     
FDefinition transl_program : S.program -> res T.program := fun p =>     
  do p1 <- AST.transform_partial_program (transl_fundef p.(prog_comp_env)) p;
  OK {| prog_defs := AST.prog_defs p1;
        prog_public := AST.prog_public p1;
        prog_main := AST.prog_main p1;
        prog_types := prog_types p;
        prog_comp_env := prog_comp_env p;
        prog_comp_env_eq := prog_comp_env_eq p |}.
          
FEnd SimplExpr.

FEnd Base.

Trait Comp_Loops extends Base.

Trait C_Swhile extends C.
FInductive stmt : Type :=  
  | Swhile : expr -> stmt -> stmt(* while loop *)  
  | Sbreak : stmt(* break stmt *)
  | Scontinue : stmt. (* continue statement *)  
FEnd C_Swhile.

Trait C_Sdowhile extends C.
FInductive stmt : Type :=  
| Sdowhile : expr -> stmt -> stmt. (* do loop *)
FEnd C_Sdowhile.

Trait C_Sfor extends C.
FInductive stmt : Type :=  
| Sfor: stmt -> expr -> stmt -> stmt -> stmt. (* for loop *)
FEnd C_Sfor.

Family C extends C_Swhile, C_Sdowhile, C_Sfor.
FEnd C.

Trait Clight_Sloop extends Clight.
FInductive stmt : Type := 
  | Sloop: stmt -> stmt -> stmt (* infinite loop *)
  | Sbreak : stmt (* break statement *)
  | Scontinue : stmt. (* continue statement *) 
FEnd Clight_Sloop.

Family Clight extends Clight_Sloop.
FEnd Clight.

From NFPOP Require Import Mon.
Local Open Scope gensym_monad_scope.

Trait SimplExpr_Swhile extends SimplExpr.
Family S extends C_Swhile. FEnd S.

FRecursion transl_stmt
           with transl_lblstmt.
Case Swhile e s1 :=
(fun ce => 
 do s' <- transl_if e T.Sskip T.Sbreak ce;
 do ts1 <- transl_stmt s1 ce;
 ret (T.Sloop (T.Sseq s' ts1) T.Sskip)).
Case Sbreak := (fun ce => ret T.Sbreak).
Case Scontinue := (fun ce => ret T.Scontinue).
FEnd transl_stmt with transl_lblstmt.

FEnd SimplExpr_Swhile.

Trait SimplExpr_Sdowhile extends SimplExpr.
Family S extends C_Sdowhile. FEnd S.

FRecursion transl_stmt with transl_lblstmt.
Case Sdowhile e s1 :=
(fun ce => 
   do s' <- transl_if e T.Sskip T.Sbreak ce;
   do ts1 <- transl_stmt s1 ce;
   ret (T.Sloop ts1 s')).
FEnd transl_stmt with transl_lblstmt.

FEnd SimplExpr_Sdowhile.

Trait SimplExpr_Sfor extends SimplExpr.
Family S extends C_Sfor. FEnd S.

FRecursion transl_stmt with transl_lblstmt.
Case Sfor s1 e2 s3 s4 :=
(fun ce => 
 do ts1 <- transl_stmt s1 ce;
 do s' <- transl_if e2 T.Sskip T.Sbreak ce;
 do ts3 <- transl_stmt s3 ce;
 do ts4 <- transl_stmt s4 ce;
 if is_Sskip s1 then
   ret (T.Sloop (T.Sseq s' ts4) ts3)
 else
   ret (T.Sseq ts1 (T.Sloop (T.Sseq s' ts4) ts3))).
FEnd transl_stmt with transl_lblstmt.

FEnd SimplExpr_Sfor.

Family SimplExpr extends
  SimplExpr_Swhile,
  SimplExpr_Sdowhile,
  SimplExpr_Sfor.
FEnd SimplExpr.

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family C.
FInductive expr : Type :=
| Ebuiltin : external_function -> list type -> exprlist -> type -> expr.

FRecursion typeof.
Case Ebuiltin ef ts es ty := ty.
FEnd typeof.
FEnd C.

Family Clight.
FInductive stmt : Type :=
| Sbuiltin: option ident -> external_function -> list type -> list expr -> stmt. (* builtin invocation *)
FEnd Clight.

From NFPOP Require Import Mon.
Local Open Scope gensym_monad_scope.

Family SimplExpr.

FRecursion transl_expr with transl_exprlist.
Case Ebuiltin ef tyargs rl ty :=
  (fun ce dst =>
     do (sl, al) <- transl_exprlist rl ce;
      match dst with
      | self__SimplExpr.For_val | self__SimplExpr.For_set _ =>
          do t <- gensym ty;
          ret (finish dst (sl ++ T.Sbuiltin (Some t) ef tyargs al :: nil)
                          (T.Etempvar t ty))
      | self__SimplExpr.For_effects =>
          ret (sl ++ T.Sbuiltin None ef tyargs al :: nil, dummy_expr)
      end).
FEnd transl_expr with transl_exprlist.

FEnd SimplExpr.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

(*| Eassignop (op: binary_operation) (l: expr) (r: expr) (tyres ty: type)
| Epostincr (id: incr_or_decr) (l: expr) (ty: type)  
| Eloc (b: block) (ofs: ptrofs) (bf: bitfield) (ty: type) *)

Trait C_Eassignop extends C.
FInductive expr : Type :=
| Eassignop : Cop.binary_operation -> expr -> expr -> type -> type -> expr.

FRecursion typeof.
Case Eassignop op e0 e1 ty' ty := ty.
FEnd typeof.
FEnd C_Eassignop.

Trait C_Epostincr extends C.
FInductive expr : Type :=
  | Epostincr : incr_or_decr -> expr -> type -> expr.

FRecursion typeof.
Case Epostincr a b ty := ty.
FEnd typeof.
FEnd C_Epostincr.

(* This is used internally by the semantics of memory *)
Trait C_Eloc extends C.
FInductive expr : Type :=
  | Eloc : block -> ptrofs -> bitfield -> type -> expr.

FRecursion typeof.
Case Eloc a b c ty := ty.
FEnd typeof.
FEnd C_Eloc.

Trait C_Eaddrof extends C.
FInductive expr : Type :=
| Eaddrof : expr -> type -> expr. 

FRecursion typeof.
Case Eaddrof e ty := ty.
FEnd typeof.
FEnd C_Eaddrof.

Trait C_Ederef extends C.
FInductive expr : Type :=
| Ederef : expr -> type -> expr. 

FRecursion typeof.
Case Ederef e ty := ty.
FEnd typeof.
FEnd C_Ederef.

Trait C_Evalof extends C.
FInductive expr : Type :=
| Evalof : expr -> type -> expr. (* l-value used as a r-value *)

FRecursion typeof.
Case Evalof e ty := ty.
FEnd typeof.
FEnd C_Evalof.

Trait C_Eassign extends C.
FInductive expr : Type :=
| Eassign : expr -> expr -> type -> expr. (* assignment l = r *)

FRecursion typeof.
Case Eassign e1 e2 ty := ty.
FEnd typeof.
FEnd C_Eassign.

Family C extends 
  C_Eassign,
  C_Evalof,
  C_Ederef,
  C_Eaddrof,
  C_Eassignop,
  C_Epostincr,
  C_Eloc.
FEnd C.

Trait Clight_Evar extends Clight.
FInductive expr : Type :=
| Evar: ident -> type -> expr. (* variable *)

FRecursion typeof.
Case Evar i t := t.
FEnd typeof.
FEnd Clight_Evar.

Trait Clight_Ederef extends Clight.
FInductive expr : Type :=
| Ederef: expr -> type -> expr. (* pointer dereference (unary *)

FRecursion typeof.
Case Ederef i t := t.
FEnd typeof.
FEnd Clight_Ederef.

Trait Clight_Eaddrof extends Clight.
FInductive expr : Type :=
| Eaddrof: expr -> type -> expr. (* address-of operator (&) *)

FRecursion typeof.
Case Eaddrof e t := t.
FEnd typeof.
FEnd Clight_Eaddrof.

Trait Clight_Sassign extends Clight.
FInductive stmt : Type :=
| Sassign : expr -> expr -> stmt. (* assignment lvalue = rvalue *)
FEnd Clight_Sassign.

Family Clight extends 
  Clight_Sassign, 
  Clight_Eaddrof,
  Clight_Ederef,
  Clight_Evar.
FEnd Clight.

Trait SimplExpr_Eassign extends SimplExpr.
Family S extends C_Eassign. FEnd S.

FRecursion eval_simpl_expr.
Case _ := None.
FEnd eval_simpl_expr.

From NFPOP Require Import Mon.
Local Open Scope gensym_monad_scope.

FRecursion is_bitfield_access about T.expr motive (fun (_ : T.expr) => composite_env -> mon bitfield) by _rect.
Case _ := (fun ce => ret Full).
FEnd is_bitfield_access.

FDefinition chunk_for_volatile_type : type -> bitfield -> option memory_chunk := fun ty bf =>
  if type_is_volatile ty then
    match access_mode ty with
    | By_value chunk =>
        match bf with
        | Full => Some chunk
        | Bits _ _ _ _ => None
        end
    | _ => None
    end
  else None.

FDefinition make_assign : bitfield -> T.expr -> T.expr -> T.stmt := fun bf l r =>
  match chunk_for_volatile_type (T.typeof l) bf with
  | None =>
      T.Sassign l r
  | Some chunk =>
      let ty := T.typeof l in
      let typtr := Tpointer ty noattr in      
      T.Sbuiltin None (EF_vstore chunk) (typtr :: (ty :: nil))
                    (T.Eaddrof l typtr :: r :: nil)
  end.

FDefinition make_normalize := fun (sz: intsize) (sg: signedness) (width: Z) (r: T.expr) =>
  let intconst (n: Z) := T.Econst_int (Int.repr n) type_int32s in
  if intsize_eq sz IBool || signedness_eq sg Unsigned then
    let mask := two_p width - 1 in
    T.Ebinop Cop.Oand r (intconst mask) (T.typeof r)
  else
    let amount := Int.zwordsize - width in
    T.Ebinop Cop.Oshr
           (T.Ebinop Cop.Oshl r (intconst amount) type_int32s)
           (intconst amount)
           (T.typeof r).

FDefinition make_assign_value := fun (bf: bitfield) (r: T.expr) =>
  match bf with
  | Full => r
  | Bits sz sg pos width => make_normalize sz sg width r
  end.

FRecursion transl_expr with transl_exprlist.
Case Eassign l1 r2 ty := 
(fun ce dst => 
 do (sl1, a1) <- transl_expr l1 ce self__SimplExpr_Eassign.For_val;
 do (sl2, a2) <- transl_expr r2 ce self__SimplExpr_Eassign.For_val;
 do bf <- is_bitfield_access a1 ce;
 let ty1 := S.typeof l1 in
 let ty2 := S.typeof r2 in
 match dst with
 | self__SimplExpr_Eassign.For_val | self__SimplExpr_Eassign.For_set _ =>
     do t <- gensym ty1;
     ret (finish dst
            (sl1 ++ sl2 ++ T.Sset t (T.Ecast a2 ty1) :: make_assign bf a1 (T.Etempvar t ty1) :: nil)
            (make_assign_value bf (T.Etempvar t ty1)))
 | self__SimplExpr_Eassign.For_effects =>
     ret (sl1 ++ sl2 ++ make_assign bf a1 a2 :: nil,
          dummy_expr)
 end).
FEnd transl_expr with transl_exprlist.
FEnd SimplExpr_Eassign.

Trait SimplExpr_Evalof extends SimplExpr, SimplExpr_Eassign.
Family S extends C_Evalof. FEnd S.

FRecursion eval_simpl_expr.
Case _ := None.
FEnd eval_simpl_expr.

Inherit chunk_for_volatile_type.

FDefinition make_set := fun (bf: bitfield) (id: ident) (l: T.expr) => 
 match chunk_for_volatile_type (T.typeof l) bf with
  | None => T.Sset id l
  | Some chunk =>
      let typtr := Tpointer (T.typeof l) noattr in
      T.Sbuiltin (Some id) (EF_vload chunk) (typtr :: nil) ((T.Eaddrof l typtr):: nil)
  end.

(*FRecursion is_bitfield_access about T.expr motive (fun (_ : T.expr) => mon bitfield) by _rect.
Case _ := (ret Full).
FEnd is_bitfield_access.*)

FDefinition transl_valof : composite_env -> type -> T.expr -> mon (list T.stmt * T.expr) := fun ce ty l =>
  if type_is_volatile ty
  then do t <- gensym ty;
       do bf <- is_bitfield_access l ce;
       ret (make_set bf t l :: nil, T.Etempvar t ty)
  else ret (nil, l).

FRecursion transl_expr with transl_exprlist.
Case Evalof l ty := 
(fun ce dst => 
   do (sl1, a1) <- transl_expr l ce self__SimplExpr_Evalof.For_val;
   do (sl2, a2) <- transl_valof ce (S.typeof l) a1;
   ret (finish dst (sl1 ++ sl2) a2)).
FEnd transl_expr with transl_exprlist.

FEnd SimplExpr_Evalof.

Trait SimplExpr_Ederef extends SimplExpr.
Family S extends C_Ederef. FEnd S.

FRecursion eval_simpl_expr.
Case _ := None.
FEnd eval_simpl_expr.

FRecursion transl_expr with transl_exprlist. 
Case Ederef r ty :=
  (fun ce dst => do (sl, a) <- transl_expr r ce self__SimplExpr_Ederef.For_val;
  ret (finish dst sl (T.Ederef a ty))).
FEnd transl_expr with transl_exprlist.

FEnd SimplExpr_Ederef.

Trait SimplExpr_Eaddrof extends SimplExpr.
Family S extends C_Eaddrof. FEnd S.

FRecursion eval_simpl_expr.
Case _ := None.
FEnd eval_simpl_expr.

FRecursion transl_expr with transl_exprlist. 
Case Eaddrof l ty :=
   (fun ce dst => do (sl, a) <- transl_expr l ce self__SimplExpr_Eaddrof.For_val;
      ret (finish dst sl (T.Eaddrof a ty))).
FEnd transl_expr with transl_exprlist.

FEnd SimplExpr_Eaddrof.

Trait SimplExpr_Eassignop extends SimplExpr_Evalof, SimplExpr_Eassign, SimplExpr.
Family S extends C_Eassignop. FEnd S.

FRecursion eval_simpl_expr.
Case _ := None.
FEnd eval_simpl_expr.

FRecursion transl_expr with transl_exprlist.
Case Eassignop op l1 r2 tyres ty := 
  (fun ce dst =>
     let ty1 := S.typeof l1 in
      do (sl1, a1) <- transl_expr l1 ce self__SimplExpr_Eassignop.For_val;
      do (sl2, a2) <- transl_expr r2 ce self__SimplExpr_Eassignop.For_val;
      do (sl3, a3) <- transl_valof ce ty1 a1;
      do bf <- is_bitfield_access a1 ce;
      match dst with
      | self__SimplExpr_Eassignop.For_val | self__SimplExpr_Eassignop.For_set _ =>
          do t <- gensym ty1;
          ret (finish dst
                 (sl1 ++ sl2 ++ sl3 ++
                  T.Sset t (T.Ecast (T.Ebinop op a3 a2 tyres) ty1) ::
                  make_assign bf a1 (T.Etempvar t ty1) :: nil)
                 (make_assign_value bf (T.Etempvar t ty1)))
      | self__SimplExpr_Eassignop.For_effects =>
          ret (sl1 ++ sl2 ++ sl3 ++ make_assign bf a1 (T.Ebinop op a3 a2 tyres) :: nil,
              dummy_expr)
     end).
FEnd transl_expr with transl_exprlist.

FEnd SimplExpr_Eassignop.

Trait SimplExpr_Epostincr extends SimplExpr_Evalof, SimplExpr_Eassign, SimplExpr.
Family S extends C_Epostincr. FEnd S.

FRecursion eval_simpl_expr.
Case _ := None.
FEnd eval_simpl_expr.


FDefinition transl_incrdecr := fun (id: incr_or_decr) (a: T.expr) (ty: type) =>
  match id with
  | Incr => T.Ebinop Cop.Oadd a (T.Econst_int Int.one Ctypes.type_int32s) (Cop.incrdecr_type ty)
  | Decr => T.Ebinop Cop.Osub a (T.Econst_int Int.one Ctypes.type_int32s) (Cop.incrdecr_type ty)
  end.

FRecursion transl_expr with transl_exprlist.
Case Epostincr id l1 ty :=
  (fun ce dst =>
     let ty1 := S.typeof l1 in
      do (sl1, a1) <- transl_expr l1 ce self__SimplExpr_Epostincr.For_val;
      do bf <- is_bitfield_access a1 ce;
      match dst with
      | self__SimplExpr_Epostincr.For_val | self__SimplExpr_Epostincr.For_set _ =>
          do t <- gensym ty1;
          ret (finish dst
                 (sl1 ++ make_set bf t a1 ::
                  make_assign bf a1 (transl_incrdecr id (T.Etempvar t ty1) ty1) :: nil)
                 (T.Etempvar t ty1))
      | self__SimplExpr_Epostincr.For_effects =>
          do (sl2, a2) <- transl_valof ce ty1 a1;
          ret (sl1 ++ sl2 ++ make_assign bf a1 (transl_incrdecr id a2 ty1) :: nil,
               dummy_expr)
      end).
FEnd transl_expr with transl_exprlist.

FEnd SimplExpr_Epostincr.

Trait SimplExpr_Eloc extends SimplExpr.
Family S extends C_Eloc. FEnd S.

FRecursion eval_simpl_expr.
Case _ := None.
FEnd eval_simpl_expr.


FRecursion transl_expr with transl_exprlist.
Case Eloc b ofs bf ty := 
   (fun ce dst => error (msg "SimplExpr.transl_expr: Eloc")).
FEnd transl_expr with transl_exprlist.

FEnd SimplExpr_Eloc.

Family SimplExpr 
  extends 
  SimplExpr_Eassign, 
  SimplExpr_Evalof,
  SimplExpr_Ederef,
  SimplExpr_Eaddrof,
  SimplExpr_Eassignop,
  SimplExpr_Epostincr,
  SimplExpr_Eloc.
FEnd SimplExpr.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.
Family C.
FInductive expr : Type :=
| Efield : expr -> ident -> type -> expr. 

FRecursion typeof.
Case Efield e i ty := ty.
FEnd typeof.
FEnd C.

Family Clight.
FInductive expr : Type :=
| Efield: expr -> ident -> type -> expr. (* access to a member of a struct or union *)

FRecursion typeof.
Case Efield e i ty := ty.
FEnd typeof.

FEnd Clight.

Family SimplExpr.
Family S extends C. FEnd S.
Family T extends Clight. FEnd T.

FRecursion eval_simpl_expr.
Case Efield e i ty := None.
FEnd eval_simpl_expr.

From NFPOP Require Import Mon.
Local Open Scope gensym_monad_scope.

FDefinition is_bitfield_access_aux := fun 
              (ce : composite_env) (fn: composite_env -> ident -> members -> res (Z * bitfield))
              (id: ident) (fld: ident) => (* : mon bitfield :=*)
  match ce!id with
  | None => error (MSG "unknown composite " :: CTX id :: nil)
  | Some co =>
      match fn ce fld (co_members co) with
      | OK (_, bf) => ret bf
      | Error _ => error (MSG "unknown field " :: CTX fld :: nil)
      end
  end.

FRecursion is_bitfield_access.
Case Efield r f x := 
 (fun cenv => 
  match T.typeof r with
  | Tstruct id _ => is_bitfield_access_aux cenv field_offset id f
  | Tunion id _ => is_bitfield_access_aux cenv union_field_offset id f
  | _ => error (msg "is_bitfield_access")
  end).
FEnd is_bitfield_access.

FRecursion transl_expr with transl_exprlist.
Case Efield r f ty :=
  (fun ce dst =>
    do (sl, a) <- transl_expr r ce self__SimplExpr.For_val;
    ret (finish dst sl (T.Efield a f ty))).
FEnd transl_expr with transl_exprlist.
FEnd SimplExpr.

FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family C.
FInductive expr : Type :=
| Ecall : expr -> exprlist -> type -> expr.

FRecursion typeof.
Case Ecall e args t := t.
FEnd typeof.

FEnd C.

Family Clight.
FInductive stmt : Type :=
| Scall: option ident -> expr -> list expr -> stmt. (* function call *)

FEnd Clight.

From NFPOP Require Import Mon.
Local Open Scope gensym_monad_scope.

Family SimplExpr.
Family S extends C. FEnd S.
Family T extends Clight. FEnd T.

FRecursion transl_expr with transl_exprlist.
Case Ecall r1 rl2 ty :=
  (fun ce dst =>
   do (sl1, a1) <- transl_expr r1 ce self__SimplExpr.For_val;
   do (sl2, al2) <- cheat (*transl_exprlist rl2*);
   match dst with
   | self__SimplExpr.For_val | self__SimplExpr.For_set _ =>
       do t <- gensym ty;
       ret (finish dst (sl1 ++ sl2 ++ T.Scall (Some t) a1 al2 :: nil)
                       (T.Etempvar t ty))
   | self__SimplExpr.For_effects =>
       ret (sl1 ++ sl2 ++ T.Scall None a1 al2 :: nil, dummy_expr)
   end).
FEnd transl_expr with transl_exprlist.

FEnd SimplExpr.

FEnd Comp_Call.

(* small extension *)
Trait Comp_Switch extends Comp_Loops.

Trait C_Switch extends C.
FInductive stmt : Type := 
| Sswitch : expr -> lbl_stmts -> stmt. (* switch statement *)

FEnd C_Switch.

Family C extends C_Switch.
FEnd C.

Trait Clight_Switch extends Clight.
FInductive stmt : Type := 
| Sswitch : expr -> lbl_stmts -> stmt. (* switch statement *)
FEnd Clight_Switch.

Family Clight extends Clight_Switch.
FEnd Clight.

From NFPOP Require Import Mon.
Local Open Scope gensym_monad_scope.

Trait SimplExpr_Switch extends SimplExpr.
Family S extends C_Switch. FEnd S.

FRecursion transl_stmt with transl_lblstmt.
Case Sswitch e ls := 
(fun ce => 
   do (s', a) <- transl_expression e ce;
   do tls <- transl_lblstmt ls ce;
 ret (T.Sseq s' (T.Sswitch a tls))).
FEnd transl_stmt with transl_lblstmt.

FEnd SimplExpr_Switch.

Family SimplExpr extends SimplExpr_Switch.
FEnd SimplExpr.

FEnd Comp_Switch.

Family Comp extends 
  Base,
  Comp_Switch,
  Comp_Loops,
  Comp_Heap, 
  Comp_Field, 
  Comp_Call,
  (* Comp_Float,*)
  Comp_Builtin. 

Family SimplExpr.
Final Family S := C.
Final Family T := Clight.
FEnd SimplExpr.

FEnd Comp.

Require Extraction.
Cd "extraction".

Separate Extraction Comp.SimplExpr.

Separate Extraction X.C.
Extraction Library X.

Require Extraction.
Extraction Language OCaml.
Extraction "compcert.ml" Base.SimplExpr.transl_function.


(*Family CompX extends Comp_Loops.

Family SimplExpr.
Final Family S := C.
Final Family T := Clight.
FEnd SimplExpr.

Family Cshmgen.
Final Family S := Clight.
Final Family T := Csharpminor.
FEnd Cshmgen.

Family Cminorgen.
Final Family S := Csharpminor.
Final Family T := Cminor.
FEnd Cminorgen.

Family Selection. 
Final Family S := Cminor.
Final Family T := CminorSel.
FEnd Selection.

Family RTLgen.
Final Family S := CminorSel.
Final Family T := RTL.
FEnd RTLgen.

Inherit Lfam.
Family Linear extends Lfam. FEnd Linear.
Family Mach extends Lfam. FEnd Mach.

Family Linearize.
Final Family S := LTL.
Final Family T := Linear.

FEnd Linearize.

Family Stacking.
Final Family S := Linear.
Final Family T := Mach.
FEnd Stacking.

Family Asmgen.
Final Family S := Mach.
FEnd Asmgen.

FEnd CompX.*)


(*

 Require Extraction.
Cd "extract_lib".
Extraction Library AST.
Extraction Library Ascii.

Extraction Library Archi.
Extraction Library BinInt.
Extraction Library BinNums.
Extraction Library Bool.
Extraction Library Coqlib.
Extraction Library Datatypes.
Extraction Library Errors.
Extraction Library Floats.
Extraction Library Integers.
Extraction Library List.
Extraction Library Maps.
Extraction Library Specif.
Extraction Library String.

Extraction Library Coqlib.
Extraction Library AST.
Extraction Library Builtins0.
Extraction Library Events.
Extraction Library Intv.
Extraction Library Archi.
Extraction Library Builtins1.
Extraction Library Linking.
Extraction Library Ordered.
Extraction Library Floats.
Extraction Library Maps.
Extraction Library Values.
Extraction Library Axioms.
Extraction Library Globalenvs.
Extraction Library Memdata.
Extraction Library Zbits.
Extraction Library Ctypes.
Extraction Library IEEE754_extra.
Extraction Library Memory.
Extraction Library Smallstep.
Extraction Library Builtins.
Extraction Library Errors.
Extraction Library Integers.
Extraction Library Memtype.
Extraction Library Cop.
Extraction Library Mon.
Extraction Library Prelude.
From NFPOP Require Import Registers.
Extraction Library Registers.
From NFPOP Require Import Decidableplus.
Extraction Library Decidableplus.
From NFPOP Require Import Machregs.
Extraction Library Machregs.
From NFPOP Require Import Locations.
Extraction Library Locations.
From NFPOP Require Import Conventions1.
Extraction Library Conventions1.
From NFPOP Require Import Mregisters.
Extraction Library Mregisters.
From NFPOP Require Import RTLmonad.
Extraction Library RTLmonad.
From NFPOP Require Import Heaps.
Extraction Library Heaps.
From NFPOP Require Import Kildall.
Extraction Library Kildall.
From NFPOP Require Import Lattice.
Extraction Library Lattice.
From NFPOP Require Import Iteration.
Extraction Library Iteration.
From NFPOP Require Import Wfsimpl.
Extraction Library Wfsimpl.
From NFPOP Require Import Bounds.
Extraction Library Bounds.
From NFPOP Require Import Separation.
Extraction Library Separation.
From NFPOP Require Import Stacklayout.
Extraction Library Stacklayout.
From NFPOP Require Import Switch.
Extraction Library Switch.
From NFPOP Require Import Op.
Extraction Library Op.
From NFPOP Require Import BoolEqual.
Extraction Library BoolEqual.

Separate Extraction AST.*)
