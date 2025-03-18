From Rocqet Require Import Loader.
From Rocqet Require Import LibTactics.

From Rocqet Require Import Coqlib.
From Rocqet Require Import Errors.
From Rocqet Require Import Values.
From Rocqet Require Import AST.
From Rocqet Require Import Integers. 
From Rocqet Require Import Floats.
From Rocqet Require Import Memory.
From Rocqet Require Import Globalenvs.
From Rocqet Require Import Smallstep.
From Rocqet Require Import Events.
From Rocqet Require Import Maps.
From Rocqet Require Import Linking.
Require Import Rocqet.CompCert.lib.Ctypes.
From Rocqet Require Import Cop.
From Rocqet Require Import Mon.
Require Import FSets.
Require Import FSetAVL.
Require Import Orders.
Require Import Mergesort.
Require Import Ordered.
Require Import Coq.ZArith.ZArith.
From Rocqet Require Import Prelude.
From Rocqet Require Import Op.

Local Open Scope string_scope.
Local Open Scope list_scope.
Open Scope asm.

Require Import Clight.
Require Import CfamBase.
Require Import Csharpminor.

Trait Base. 

(* ------------------------------------------------ *)
(*             Cshmgen (Clight -> Csharpminor)      *)
(* ------------------------------------------------ *)
Family Cshmgen.
Family S extends Clight. FEnd S.
Family T extends Csharpminor. FEnd T.

FDefinition make_intconst := fun (n: int) => T.Econst (T.Ointconst n).
FDefinition make_longconst := fun (f: int64) => T.Econst (T.Olongconst f).
FDefinition make_floatconst := fun (f: float) => T.Econst (T.Ofloatconst f).
FDefinition make_singleconst := fun (f: float32) => T.Econst (T.Osingleconst f).
FDefinition make_ptrofsconst := fun (n: Z) =>
  if Archi.ptr64 then make_longconst (Int64.repr n) else make_intconst (Int.repr n).            

FDefinition make_singleoffloat := fun (e: T.expr) => T.Eunop Osingleoffloat e.
FDefinition make_floatofsingle := fun (e: T.expr) => T.Eunop Ofloatofsingle e.

FDefinition make_floatofint := fun (e: T.expr) (sg: signedness) =>
  match sg with
  | Signed => T.Eunop Ofloatofint e
  | Unsigned => T.Eunop Ofloatofintu e
  end.

FDefinition make_singleofint := fun (e: T.expr) (sg: signedness) =>
  match sg with
  | Signed => T.Eunop Osingleofint e
  | Unsigned => T.Eunop Osingleofintu e
  end.

FDefinition make_intoffloat := fun (e: T.expr) (sg: signedness) =>
  match sg with
  | Signed => T.Eunop Ointoffloat e
  | Unsigned => T.Eunop Ointuoffloat e
  end.

FDefinition make_intofsingle := fun (e: T.expr) (sg: signedness) =>
  match sg with
  | Signed => T.Eunop Ointofsingle e
  | Unsigned => T.Eunop Ointuofsingle e
  end.

FDefinition make_longofint := fun (e: T.expr) (sg: signedness) =>
  match sg with
  | Signed => T.Eunop Olongofint e
  | Unsigned => T.Eunop Olongofintu e
  end.

FDefinition make_floatoflong := fun (e: T.expr) (sg: signedness) =>
  match sg with
  | Signed => T.Eunop Ofloatoflong e
  | Unsigned => T.Eunop Ofloatoflongu e
  end.

FDefinition make_singleoflong := fun (e: T.expr) (sg: signedness) =>
  match sg with
  | Signed => T.Eunop Osingleoflong e
  | Unsigned => T.Eunop Osingleoflongu e
  end.

FDefinition make_longoffloat := fun (e: T.expr) (sg: signedness) =>
  match sg with
  | Signed => T.Eunop Olongoffloat e
  | Unsigned => T.Eunop Olonguoffloat e
  end.

FDefinition make_longofsingle := fun (e: T.expr) (sg: signedness) =>
  match sg with
  | Signed => T.Eunop Olongofsingle e
  | Unsigned => T.Eunop Olonguofsingle e
  end.

FDefinition sizeof : composite_env -> type -> res Z := fun ce t => 
  if complete_type ce t
  then OK (Ctypes.sizeof ce t)
  else Error (msg "incomplete type").

FDefinition alignof : composite_env -> type -> res Z := fun ce t => 
  if complete_type ce t
  then OK (Ctypes.alignof ce t)
  else Error (msg "incomplete type").

FDefinition make_cmpu_ne_zero_helper := fun (op: binary_operation) (e: T.expr) =>
  match op with                                           
  | Ocmp c => e
  | Ocmpu c => e
  | Ocmpf c => e
  | Ocmpfs c => e
  | Ocmpl c => e
  | Ocmplu c => e
  | _ => T.Ebinop (Ocmpu Cne) e (make_intconst Int.zero)
  end.                  

FRecursion make_cmpu_ne_zero about T.expr motive (fun (_ : T.expr) => T.expr) by _rect.
Case Ebinop op e1 e2 := (make_cmpu_ne_zero_helper op (T.Ebinop op e1 e2)).
Case Evar v := (T.Ebinop (Ocmpu Cne) (T.Evar v) (make_intconst Int.zero)).
Case Eunop op e := (T.Ebinop (Ocmpu Cne) (T.Eunop op e) (make_intconst Int.zero)).
Case Econst c := (T.Ebinop (Ocmpu Cne) (T.Econst c) (make_intconst Int.zero)).
FEnd make_cmpu_ne_zero.

FDefinition make_cast_int := fun (e: T.expr) (sz: intsize) (si: signedness) =>
  match sz, si with
  | I8, Signed => T.Eunop Ocast8signed e
  | I8, Unsigned => T.Eunop Ocast8unsigned e
  | I16, Signed => T.Eunop Ocast16signed e
  | I16, Unsigned => T.Eunop Ocast16unsigned e
  | I32, _ => e
  | IBool, _ => make_cmpu_ne_zero e
  end.

FDefinition make_cast := fun (from to: type) (e: T.expr) =>
  match classify_cast from to with
  | cast_case_pointer => OK e
  | cast_case_i2i sz2 si2 => OK (make_cast_int e sz2 si2)
  | cast_case_f2f => OK e
  | cast_case_s2s => OK e
  | cast_case_f2s => OK (make_singleoffloat e)
  | cast_case_s2f => OK (make_floatofsingle e)
  | cast_case_i2f si1 => OK (make_floatofint e si1)
  | cast_case_i2s si1 => OK (make_singleofint e si1)
  | cast_case_f2i sz2 si2 => OK (make_cast_int (make_intoffloat e si2) sz2 si2)
  | cast_case_s2i sz2 si2 => OK (make_cast_int (make_intofsingle e si2) sz2 si2)
  | cast_case_l2l => OK e
  | cast_case_i2l si1 => OK (make_longofint e si1)
  | cast_case_l2i sz2 si2 => OK (make_cast_int (T.Eunop Ointoflong e) sz2 si2)
  | cast_case_l2f si1 => OK (make_floatoflong e si1)
  | cast_case_l2s si1 => OK (make_singleoflong e si1)
  | cast_case_f2l si2 => OK (make_longoffloat e si2)
  | cast_case_s2l si2 => OK (make_longofsingle e si2)
  | cast_case_i2bool => OK (make_cmpu_ne_zero e)
  | cast_case_f2bool => OK (T.Ebinop (Ocmpf Cne) e (make_floatconst Float.zero))
  | cast_case_s2bool => OK (T.Ebinop (Ocmpfs Cne) e (make_singleconst Float32.zero))
  | cast_case_l2bool => OK (T.Ebinop (Ocmplu Cne) e (make_longconst Int64.zero))
  | cast_case_struct id1 id2 => OK e
  | cast_case_union id1 id2 => OK e
  | cast_case_void => OK e
  | cast_case_default => Error (msg "Cshmgen.make_cast")
  end.

FDefinition make_boolean := fun (e: T.expr) (ty: type) =>
  match classify_bool ty with
  | bool_case_i => make_cmpu_ne_zero e
  | bool_case_f => T.Ebinop (Ocmpf Cne) e (make_floatconst Float.zero)
  | bool_case_s => T.Ebinop (Ocmpfs Cne) e (make_singleconst Float32.zero)
  | bool_case_l => T.Ebinop (Ocmplu Cne) e (make_longconst Int64.zero)
  | bool_default => e (* should not happen *)
  end.

FDefinition make_notbool := fun (e: T.expr) (ty: type) =>
  match classify_bool ty with
  | bool_case_i => OK (T.Ebinop (Ocmpu Ceq) e (make_intconst Int.zero))
  | bool_case_f => OK (T.Ebinop (Ocmpf Ceq) e (make_floatconst Float.zero))
  | bool_case_s => OK (T.Ebinop (Ocmpfs Ceq) e (make_singleconst Float32.zero))
  | bool_case_l => OK (T.Ebinop (Ocmplu Ceq) e (make_longconst Int64.zero))
  | bool_default => Error (msg "Cshmgen.make_notbool")
  end.

FDefinition make_neg := fun (e: T.expr) (ty: type) =>
  match classify_neg ty with
  | neg_case_i _ => OK (T.Eunop Onegint e)
  | neg_case_f => OK (T.Eunop Onegf e)
  | neg_case_s => OK (T.Eunop Onegfs e)
  | neg_case_l _ => OK (T.Eunop Onegl e)
  | neg_default => Error (msg "Cshmgen.make_neg")
  end.

FDefinition make_absfloat := fun (e: T.expr) (ty: type) =>
  match classify_neg ty with
  | neg_case_i sg => OK (T.Eunop Oabsf (make_floatofint e sg))
  | neg_case_f => OK (T.Eunop Oabsf e)
  | neg_case_s => OK (T.Eunop Oabsf (make_floatofsingle e))
  | neg_case_l sg => OK (T.Eunop Oabsf (make_floatoflong e sg))
  | neg_default => Error (msg "Cshmgen.make_absfloat")
  end.

FDefinition make_notint := fun (e: T.expr) (ty: type) =>
  match classify_notint ty with
  | notint_case_i _ => OK (T.Eunop Onotint e)
  | notint_case_l _ => OK (T.Eunop Onotl e)
  | notint_default => Error (msg "Cshmgen.make_notint")
  end.

FDefinition transl_unop := fun (op: Cop.unary_operation) (a: T.expr) (ta: type) =>
  match op with
  | Cop.Onotbool => make_notbool a ta
  | Cop.Onotint => make_notint a ta
  | Cop.Oneg => make_neg a ta
  | Cop.Oabsfloat => make_absfloat a ta
  end.
Local Open Scope error_monad_scope.
FDefinition make_binarith := fun (iop iopu fop sop lop lopu: binary_operation)
                         (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  let c := classify_binarith ty1 ty2 in
  let ty := binarith_type c in
  do e1' <- make_cast ty1 ty e1;
  do e2' <- make_cast ty2 ty e2;
  match c with
  | bin_case_i Signed => OK (T.Ebinop iop e1' e2')
  | bin_case_i Unsigned => OK (T.Ebinop iopu e1' e2')
  | bin_case_f => OK (T.Ebinop fop e1' e2')
  | bin_case_s => OK (T.Ebinop sop e1' e2')
  | bin_case_l Signed => OK (T.Ebinop lop e1' e2')
  | bin_case_l Unsigned => OK (T.Ebinop lopu e1' e2')
  | bin_default => Error (msg "Cshmgen.make_binarith")
  end.

FDefinition make_add_ptr_int := fun (ce: composite_env) (ty: type) (si: signedness) (e1 e2: T.expr) =>
  do sz <- sizeof ce ty;
  if Archi.ptr64 then
    let n := make_longconst (Int64.repr sz) in
    OK (T.Ebinop Oaddl e1 (T.Ebinop Omull n (make_longofint e2 si)))
  else
    let n := make_intconst (Int.repr sz) in
    OK (T.Ebinop Oadd e1 (T.Ebinop Omul n e2)).

FDefinition make_add_ptr_long := fun (ce: composite_env) (ty: type) (e1 e2: T.expr) =>
  do sz <- sizeof ce ty;
  if Archi.ptr64 then
    let n := make_longconst (Int64.repr sz) in
    OK (T.Ebinop Oaddl e1 (T.Ebinop Omull n e2))
  else
    let n := make_intconst (Int.repr sz) in
    OK (T.Ebinop Oadd e1 (T.Ebinop Omul n (T.Eunop Ointoflong e2))).

FDefinition make_add := fun (ce: composite_env) (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  match classify_add ty1 ty2 with
  | add_case_pi ty si => make_add_ptr_int ce ty si e1 e2
  | add_case_pl ty => make_add_ptr_long ce ty e1 e2
  | add_case_ip si ty => make_add_ptr_int ce ty si e2 e1
  | add_case_lp ty => make_add_ptr_long ce ty e2 e1
  | add_default => make_binarith Oadd Oadd Oaddf Oaddfs Oaddl Oaddl e1 ty1 e2 ty2
  end.

FDefinition make_sub := fun (ce: composite_env) (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  match classify_sub ty1 ty2 with
  | sub_case_pi ty si =>
      do sz <- sizeof ce ty;
      if Archi.ptr64 then
        let n := make_longconst (Int64.repr sz) in
        OK (T.Ebinop Osubl e1 (T.Ebinop Omull n (make_longofint e2 si)))
      else
        let n := make_intconst (Int.repr sz) in
        OK (T.Ebinop Osub e1 (T.Ebinop Omul n e2))
  | sub_case_pp ty =>
      do sz <- sizeof ce ty;
      if Archi.ptr64 then
        let n := make_longconst (Int64.repr sz) in
        OK (T.Ebinop Odivl (T.Ebinop Osubl e1 e2) n)
      else
        let n := make_intconst (Int.repr sz) in
        OK (T.Ebinop Odiv (T.Ebinop Osub e1 e2) n)
  | sub_case_pl ty =>
      do sz <- sizeof ce ty;
      if Archi.ptr64 then
        let n := make_longconst (Int64.repr sz) in
        OK (T.Ebinop Osubl e1 (T.Ebinop Omull n e2))
      else
        let n := make_intconst (Int.repr sz) in
        OK (T.Ebinop Osub e1 (T.Ebinop Omul n (T.Eunop Ointoflong e2)))
  | sub_default =>
      make_binarith Osub Osub Osubf Osubfs Osubl Osubl e1 ty1 e2 ty2
  end.

FDefinition make_mul := fun (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  make_binarith Omul Omul Omulf Omulfs Omull Omull e1 ty1 e2 ty2.

FDefinition make_div := fun (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  make_binarith Odiv Odivu Odivf Odivfs Odivl Odivlu e1 ty1 e2 ty2.

FDefinition make_binarith_int :=
  fun (iop iopu lop lopu: binary_operation)
      (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  let c := classify_binarith ty1 ty2 in
  let ty := binarith_type c in
  do e1' <- make_cast ty1 ty e1;
  do e2' <- make_cast ty2 ty e2;
  match c with
  | bin_case_i Signed => OK (T.Ebinop iop e1' e2')
  | bin_case_i Unsigned => OK (T.Ebinop iopu e1' e2')
  | bin_case_l Signed => OK (T.Ebinop lop e1' e2')
  | bin_case_l Unsigned => OK (T.Ebinop lopu e1' e2')
  | bin_case_f | bin_case_s | bin_default => Error (msg "Cshmgen.make_binarith_int")
  end.

FDefinition make_mod := fun (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  make_binarith_int Omod Omodu Omodl Omodlu e1 ty1 e2 ty2.

FDefinition make_and := fun (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  make_binarith_int Oand Oand Oandl Oandl e1 ty1 e2 ty2.

FDefinition make_or := fun (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  make_binarith_int Oor Oor Oorl Oorl e1 ty1 e2 ty2.

FDefinition make_xor := fun (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  make_binarith_int Oxor Oxor Oxorl Oxorl e1 ty1 e2 ty2.

FDefinition make_shl := fun (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  match classify_shift ty1 ty2 with
  | shift_case_ii _ => OK (T.Ebinop Oshl e1 e2)
  | shift_case_li _ => OK (T.Ebinop Oshll e1 e2)
  | shift_case_il _ => OK (T.Ebinop Oshl e1 (T.Eunop Ointoflong e2))
  | shift_case_ll _ => OK (T.Ebinop Oshll e1 (T.Eunop Ointoflong e2))
  | shift_default => Error (msg "Cshmgen.make_shl")
  end.

FDefinition make_shr := fun (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  match classify_shift ty1 ty2 with
  | shift_case_ii Signed => OK (T.Ebinop Oshr e1 e2)
  | shift_case_ii Unsigned => OK (T.Ebinop Oshru e1 e2)
  | shift_case_li Signed => OK (T.Ebinop Oshrl e1 e2)
  | shift_case_li Unsigned => OK (T.Ebinop Oshrlu e1 e2)
  | shift_case_il Signed => OK (T.Ebinop Oshr e1 (T.Eunop Ointoflong e2))
  | shift_case_il Unsigned => OK (T.Ebinop Oshru e1 (T.Eunop Ointoflong e2))
  | shift_case_ll Signed => OK (T.Ebinop Oshrl e1 (T.Eunop Ointoflong e2))
  | shift_case_ll Unsigned => OK (T.Ebinop Oshrlu e1 (T.Eunop Ointoflong e2))
  | shift_default => Error (msg "Cshmgen.make_shr")
  end.

FDefinition make_cmp_ptr := fun (c: comparison) (e1 e2: T.expr) =>
  T.Ebinop (if Archi.ptr64 then Ocmplu c else Ocmpu c) e1 e2.

FDefinition make_cmp := fun (c: comparison) (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  match classify_cmp ty1 ty2 with
  | cmp_case_pp => OK (make_cmp_ptr c e1 e2)
  | cmp_case_pi si =>
      OK (make_cmp_ptr c e1 (if Archi.ptr64 then make_longofint e2 si else e2))
  | cmp_case_ip si =>
      OK (make_cmp_ptr c (if Archi.ptr64 then make_longofint e1 si else e1) e2)
  | cmp_case_pl =>
      OK (make_cmp_ptr c e1 (if Archi.ptr64 then e2 else T.Eunop Ointoflong e2))
  | cmp_case_lp =>
      OK (make_cmp_ptr c (if Archi.ptr64 then e1 else T.Eunop Ointoflong e1) e2)
  | cmp_default =>
      make_binarith
        (Ocmp c) (Ocmpu c) (Ocmpf c) (Ocmpfs c) (Ocmpl c) (Ocmplu c)
        e1 ty1 e2 ty2
  end.

FDefinition transl_binop
  := fun (ce: composite_env)
         (op: Cop.binary_operation)
         (a: T.expr) (ta: type)
         (b: T.expr) (tb: type) =>
  match op with
  | Cop.Oadd => make_add ce a ta b tb
  | Cop.Osub => make_sub ce a ta b tb
  | Cop.Omul => make_mul a ta b tb
  | Cop.Odiv => make_div a ta b tb
  | Cop.Omod => make_mod a ta b tb
  | Cop.Oand => make_and a ta b tb
  | Cop.Oor => make_or a ta b tb
  | Cop.Oxor => make_xor a ta b tb
  | Cop.Oshl => make_shl a ta b tb
  | Cop.Oshr => make_shr a ta b tb
  | Cop.Oeq => make_cmp Ceq a ta b tb
  | Cop.One => make_cmp Cne a ta b tb
  | Cop.Olt => make_cmp Clt a ta b tb
  | Cop.Ogt => make_cmp Cgt a ta b tb
  | Cop.Ole => make_cmp Cle a ta b tb
  | Cop.Oge => make_cmp Cge a ta b tb
  end.

FRecursion translate_expression about S.expr motive
   (fun (_ : S.expr) => composite_env -> res T.expr * res (T.expr * bitfield)) by _rect.
Case Econst_int n ty := (fun ce => (OK(make_intconst n),  Error(msg "Cshmgen.transl_lvalue"))). 
Case Econst_float n ty := (fun ce => (OK(make_floatconst n), Error(msg "Cshmgen.transl_lvalue"))).
Case Econst_single n ty := (fun ce => (OK(make_singleconst n), Error(msg "Cshmgen.transl_lvalue"))).
Case Econst_long n ty := (fun ce => (OK(make_longconst n), Error(msg "Cshmgen.transl_lvalue"))).
Case Etempvar id ty := (fun ce => (OK(T.Evar id), Error(msg "Cshmgen.transl_lvalue"))). 
Case Esizeof ty' ty := (fun ce => (do sz <- sizeof ce ty'; OK(make_ptrofsconst sz), Error(msg "Cshmgen.transl_lvalue"))).
Case Ealignof ty' ty := (fun ce => (do al <- alignof ce ty'; OK(make_ptrofsconst al), Error(msg "Cshmgen.transl_lvalue"))).
Case Ecast b ty := (fun ce => (do tb <- fst (translate_expression b ce); make_cast (S.typeof b) ty tb, Error(msg "Cshmgen.transl_lvalue"))).
Case Eunop op b ty :=
(fun ce =>
   (do tb <- fst (translate_expression b ce);
       transl_unop op tb (S.typeof b),
      Error(msg "Cshmgen.transl_lvalue"))).
Case Ebinop op b c ty :=
(fun ce =>
   (do tb <- fst (translate_expression b ce);
   do tc <- fst (translate_expression c ce);
   transl_binop ce op tb (S.typeof b) tc (S.typeof c),
   Error(msg "Cshmgen.transl_lvalue"))).
FEnd translate_expression.

FDefinition transl_expr := fun e ce => fst (translate_expression e ce).
      
FRecursion transl_stmt about S.stmt motive (fun (_ : S.stmt) => composite_env -> type -> nat -> nat -> res T.stmt) by _rect.     
Case Sskip := (fun ce tyret nbrk ncnt => OK T.Sskip).   
Case Sset x b :=
(fun ce tyret nbrk ncnt => 
  do tb <- transl_expr b ce;
  OK (T.Sassign x tb)).
Case Sseq s1 s2 :=
(fun ce tyret nbrk ncnt => 
  do ts1 <- transl_stmt s1 ce tyret nbrk ncnt;
  do ts2 <- transl_stmt s2 ce tyret nbrk ncnt;
  OK (T.Sseq ts1 ts2)).
Case Sifthenelse e s1 s2 :=
(fun ce tyret nbrk ncnt => 
  do te <- transl_expr e ce;
  do ts1 <- transl_stmt s1 ce tyret nbrk ncnt;
  do ts2 <- transl_stmt s2 ce tyret nbrk ncnt;
  OK (T.Sifthenelse (make_boolean te (S.typeof e)) ts1 ts2)).
Case Sreturn e :=
(fun ce tyret nbrk ncnt =>
   match e with
   | None => OK (T.Sreturn None)
   | Some e => 
       do te <- transl_expr e ce;
       do te' <- make_cast (S.typeof e) tyret te;
       OK (T.Sreturn (Some te'))
   end).
Case Slabel lbl s :=
(fun ce tyret nbrk ncnt => 
  do ts <- transl_stmt s ce tyret nbrk ncnt;
  OK (T.Slabel lbl ts)).
Case Sgoto lbl := (fun ce tyret nbrk ncnt => OK (T.Sgoto lbl)).
FEnd transl_stmt.

(* Translation of functions *)
FDefinition transl_var := fun (ce: composite_env) (v: ident * type) =>
  do sz <- sizeof ce (snd v); OK (fst v, sz).
      
FDefinition signature_of_function := fun (f: S.function) =>
  {| sig_args := map argtype_of_type (map snd (S.fn_params f));
    sig_res  := rettype_of_type (S.fn_return f);
    sig_cc   := S.fn_callconv f |}.
      
FDefinition transl_function : composite_env -> S.function -> res T.function :=
  fun (ce: composite_env) (f: S.function)  =>
  do tbody <- transl_stmt (S.fn_body f) ce (S.fn_return f) 1%nat 0%nat;
  do tvars <- mmap (transl_var ce) (S.fn_vars f);
  OK (T.mkfunction
        (signature_of_function f)
        (map fst (S.fn_params f))
        tvars
        (map fst (S.fn_temps f))
        tbody).      

FDefinition transl_fundef : composite_env -> ident -> S.fundef -> res T.fundef :=
  fun (ce: composite_env) (id: ident) (f: S.fundef) =>
  match f with
  | Internal g =>
      do tg <- transl_function ce g; OK(AST.Internal tg)
  | External ef args res cconv =>
      if signature_eq (ef_sig ef) (signature_of_type args res cconv)
      then OK(AST.External ef)
      else Error(msg "Cshmgen.transl_fundef: wrong external signature")
  end.

FDefinition transl_globvar := fun (id: ident) (ty: type) => OK tt.

FDefinition transl_program : S.program -> res T.program := fun p => 
  transform_partial_program2 (transl_fundef p.(prog_comp_env)) transl_globvar p.

FEnd Cshmgen.

FEnd Base.

Trait Comp_Loops extends Base.

Family Cshmgen.
Family S extends Clight_Sloop. FEnd S.
Family T extends Csharpminor. FEnd T.

FRecursion transl_stmt. (* with transl_lbl_stmt.*)
Case Sloop s1 s2 :=
(fun ce tyret nbrk ncnt =>
  do ts1 <- transl_stmt s1 ce tyret 1%nat 0%nat;
  do ts2 <- transl_stmt s2 ce tyret 0%nat (Datatypes.S ncnt);
  OK (T.Sblock (T.Sloop (T.Sseq (T.Sblock ts1) ts2)))).
Case Sbreak := (fun ce tyret nbrk ncnt => OK (T.Sexit nbrk)).
Case Scontinue := (fun ce tyret nbrk ncnt => OK (T.Sexit ncnt)).
FEnd transl_stmt. (* with transl_lbl_stmt.*)

FEnd Cshmgen.

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family Cshmgen.

Inherit transl_expr.

MetaData transl_arglist.
Fixpoint transl_arglist (ce: composite_env) (al: list self__Cshmgen.S.expr) (tyl: list type)
                         {struct al}: res (list self__Cshmgen.T.expr) :=
  match al, tyl with
  | nil, nil => OK nil
  | a1 :: a2, ty1 :: ty2 =>
      do ta1 <- transl_expr a1 ce;
      do ta1' <- self__Cshmgen.make_cast (self__Cshmgen.S.typeof a1) ty1 ta1;
      do ta2 <- transl_arglist ce a2 ty2;
      OK (ta1' :: ta2)
  | a1 :: a2, nil =>
      do ta1 <- self__Cshmgen.transl_expr a1 ce;
      do ta1' <- self__Cshmgen.make_cast (self__Cshmgen.S.typeof a1) (default_argument_conversion (self__Cshmgen.S.typeof a1)) ta1;
      do ta2 <- transl_arglist ce a2 nil;
      OK (ta1' :: ta2)
  | _, _ =>
      Error(msg "Cshmgen.transl_arglist: arity mismatch")
  end.
FEnd transl_arglist.

FRecursion transl_stmt.
Case Sbuiltin x ef tyargs bl :=
(fun ce tyret nbrk ncnt =>
  do tbl <- transl_arglist ce bl tyargs;
  OK(T.Sbuiltin x ef tbl)).
FEnd transl_stmt.

FEnd Cshmgen.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Family Cshmgen.
Family S extends Clight. FEnd S.
Family T extends Csharpminor. FEnd T.

Inherit alignof.
From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.

FDefinition make_store_bitfield : intsize -> signedness -> Z -> Z -> T.expr -> T.expr -> res T.stmt := 
fun sz signedness pos width addr val => 
  if zle 0 pos && zlt 0 width && zle (pos + width) (bitsize_carrier sz) then
    let amount := first_bit sz pos width in
    let mask := Int.shl (Int.repr (two_p width - 1)) (Int.repr amount) in
    let e1 := T.Eload (chunk_for_carrier sz) addr in
    let e2 := T.Ebinop Oshl val (make_intconst (Int.repr amount)) in
    let e3 := T.Ebinop Oor (T.Ebinop Oand e2 (make_intconst mask))
                         (T.Ebinop Oand e1 (make_intconst (Int.not mask))) in
    OK (T.Sstore (chunk_for_carrier sz) addr e3)
  else
    Error(msg "Cshmgen.make_store_bitfield").

FDefinition make_memcpy : composite_env -> T.expr -> T.expr -> type -> res T.stmt := 
  fun ce dst src ty => 
  do sz <- sizeof ce ty;
  OK (T.Sbuiltin None (EF_memcpy sz (Ctypes.alignof_blockcopy ce ty))
                    (dst :: src :: nil)).

FDefinition make_store := fun (ce: composite_env) (addr: T.expr) (ty: type) (bf: bitfield) (rhs: T.expr) =>
  match bf with
  | Full =>
      match access_mode ty with
      | By_value chunk => OK (T.Sstore chunk addr rhs)
      | By_copy => make_memcpy ce addr rhs ty
      | _ => Error (msg "Cshmgen.make_store")
      end
  | Bits sz sg pos width =>
      make_store_bitfield sz sg pos width addr rhs
  end.

FDefinition make_extract_bitfield 
 : intsize -> signedness -> Z -> Z -> T.expr -> res T.expr := 
fun sz sg pos width addr =>   
  if zle 0 pos && zlt 0 width && zle (pos + width) (bitsize_carrier sz) then
    let amount1 := Int.repr (Int.zwordsize - first_bit sz pos width - width) in
    let amount2 := Int.repr (Int.zwordsize - width) in
    let e1 := T.Eload (chunk_for_carrier sz) addr in
    let e2 := T.Ebinop Oshl e1 (make_intconst amount1) in
    let e3 := T.Ebinop (if intsize_eq sz IBool
                      || signedness_eq sg Unsigned then Oshru else Oshr)
                     e2 (make_intconst amount2) in
    OK e3
  else
    Error(msg "Cshmgen.extract_bitfield").

FDefinition make_load := fun (addr: T.expr) (ty_res: type) (bf: bitfield) =>
  match bf with
  | Full =>
      match access_mode ty_res with
      | By_value chunk => OK (T.Eload chunk addr)
      | By_reference => OK addr
      | By_copy => OK addr
      | By_nothing => Error (msg "Cshmgen.make_load")
      end
  | Bits sz sg pos width =>
      make_extract_bitfield sz sg pos width addr
  end.

FRecursion make_cmpu_ne_zero.
Case Eaddrof v := (T.Ebinop (Ocmpu Cne) (T.Eaddrof v) (make_intconst Int.zero)).
Case Eload ck e := (T.Ebinop (Ocmpu Cne) (T.Eload ck e) (make_intconst Int.zero)).
FEnd make_cmpu_ne_zero.

FRecursion translate_expression.
Case Eaddrof b c :=
(fun ce => 
   (do (tb, bf) <- snd (translate_expression b ce); (* transl_lvalue *)
   match bf with
   | Full => OK tb
   | Bits _ _ _ _ => Error (msg "Cshmgen.transl_expr: addrof bitfield")
   end,
   Error(msg "Cshmgen.transl_lvalue"))).
Case Ederef b ty :=
(fun ce => 
  (do tb <- fst (translate_expression b ce);
   make_load tb ty Full,
   do tb <- fst (translate_expression b ce);
   OK (tb, Full))).
Case Evar id ty :=
   (fun ce => (make_load (T.Eaddrof id) ty Full, OK (T.Eaddrof id, Full))).
FEnd translate_expression.

FDefinition transl_lvalue := fun e ce => snd (translate_expression e ce).

FRecursion transl_stmt.
Case Sassign b c :=
(fun ce tyret nbrk ncnt => 
   do (tb, bf) <- transl_lvalue b ce;
   do tc <- transl_expr c ce;
   do tc' <- make_cast (S.typeof c) (S.typeof b) tc;
   make_store ce tb (S.typeof b) bf tc').
FEnd transl_stmt.

FEnd Cshmgen.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

Family Cshmgen.
Family S extends Clight. FEnd S.
Family T extends Csharpminor. FEnd T.
From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.

Inherit make_load.

FDefinition make_field_access
  := fun (ce: composite_env) (ty: type) (f: ident) (a: T.expr) =>
  do (ofs, bf) <-
    match ty with
    | Tstruct id _ =>
        match ce!id with
        | None => Error (MSG "Undefined struct " :: CTX id :: nil)
        | Some co => field_offset ce f (co_members co)
        end
    | Tunion id _ =>
        match ce!id with
        | None => Error (MSG "Undefined union " :: CTX id :: nil)
        | Some co => union_field_offset ce f (co_members co)
        end
    | _ =>
        Error(msg "Cshmgen.make_field_access")
    end;
  let a' :=
    if Archi.ptr64
    then T.Ebinop Oaddl a (make_longconst (Int64.repr ofs))
    else T.Ebinop Oadd a (make_intconst (Int.repr ofs)) in
  OK (a', bf).

FRecursion translate_expression.
Case Efield b i ty := 
  (fun ce =>
     (do tb <- fst (translate_expression b ce);
     do (addr, bf) <- make_field_access ce (S.typeof b) i tb;
     make_load addr ty bf,
     do tb <- fst (translate_expression b ce);
     make_field_access ce (S.typeof b) i tb)).
FEnd translate_expression.

FEnd Cshmgen.

FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family Cshmgen.
Family S extends Clight. FEnd S.
Family T extends Csharpminor. FEnd T.

FDefinition make_normalization := fun (t: type) (a: T.expr) =>
  match t with
  | Tint IBool _ _ => T.Eunop Ocast8unsigned a
  | Tint I8 Signed _ => T.Eunop Ocast8signed a
  | Tint I8 Unsigned _ => T.Eunop Ocast8unsigned a
  | Tint I16 Signed _ => T.Eunop Ocast16signed a
  | Tint I16 Unsigned _ => T.Eunop Ocast16unsigned a
  | _ => a
  end.

From Rocqet Require Import Conventions1.
(*FDefinition return_value_needs_normalization := fun (_: rettype) => false.*)

FDefinition make_funcall :=
  fun (x: option ident) (tres: type) (sg: signature)
      (fn: T.expr) (args: list T.expr) =>
  match x, return_value_needs_normalization sg.(sig_res) with
  | Some id, true =>
      T.Sseq (T.Scall x sg fn args)
             (T.Sassign id (make_normalization tres (T.Evar id)))
  | _, _ =>
      T.Scall x sg fn args
  end.

MetaData typlist_of_arglist.
Fixpoint typlist_of_arglist (al: list S.expr) (tyl: list type)
                            {struct al}: list xtype :=
  match al, tyl with
  | nil, _ => nil
  | a1 :: a2, ty1 :: ty2 =>
      argtype_of_type ty1 :: typlist_of_arglist a2 ty2
  | a1 :: a2, nil =>
      argtype_of_type (default_argument_conversion (S.typeof a1)) :: typlist_of_arglist a2 nil
  end.
FEnd typlist_of_arglist.

From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.
FRecursion transl_stmt. 
Case Scall x b cl := 
(fun ce tyret nbrk ncnt =>
     match classify_fun (S.typeof b) with
      | fun_case_f args res cconv =>
          do tb <- transl_expr b ce;
          do tcl <- transl_arglist ce cl args; 
          let sg := {| sig_args := typlist_of_arglist cl args;
                       sig_res  := rettype_of_type res;
                       sig_cc   := cconv |} in
          OK (make_funcall x res sg tb tcl)
      | _ => Error(msg "Cshmgen.transl_stmt(call)")
      end).
FEnd transl_stmt.

FEnd Cshmgen.

FEnd Comp_Call.

(* small extension *)
From Rocqet Require Import Switch.
Trait Comp_Switch extends Comp_Loops.

Family Cshmgen.
Family S extends Clight. FEnd S.
Family T extends Csharpminor. FEnd T.

From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.

FRecursion transl_stmt about S.stmt motive (fun (_ : S.stmt) => composite_env -> type -> nat -> nat -> res T.stmt)
     with transl_lbl_stmt about T.lbl_stmts motive (fun (_: S.lbl_stmts) => composite_env -> type -> nat -> nat -> res T.lbl_stmts) by _rect.
Case Sswitch a sl := 
(fun ce tyret nbrk ncnt =>
   do ta <- transl_expr a ce;
   do tsl <- transl_lbl_stmt sl ce tyret 0%nat (Datatypes.S ncnt);
    match classify_switch (S.typeof a) with
    | switch_case_i => OK (T.Sblock (T.Sswitch false ta tsl))
    | switch_case_l => OK (T.Sblock (T.Sswitch true ta tsl ))
    | switch_default => Error(msg "Cshmgen.transl_stmt(switch)")
    end).

Case LSnil := (fun ce tyret nbrk ncnt => OK T.LSnil).
Case LScons n s sl' :=
  (fun ce tyret nbrk ncnt =>
      do ts <- transl_stmt s ce tyret nbrk ncnt;
      do tsl' <- transl_lbl_stmt sl' ce tyret nbrk ncnt;
      OK (T.LScons n ts tsl')).
FEnd transl_stmt with transl_lbl_stmt.

FEnd Cshmgen.

FEnd Comp_Switch.

Family Comp extends 
  Base,
  Comp_Loops,
  Comp_Builtin,
  Comp_Heap, 
  Comp_Field, 
  Comp_Call,
  Comp_Switch.

Inherit Clight.

Inherit Csharpminor.

Family Cshmgen.
Final Family S := Clight.
Final Family T := Csharpminor.
FEnd Cshmgen.

FEnd Comp.

Require Extraction.

(* Go! *)
Cd "extraction".

Separate Extraction Comp.Cshmgen.

Extraction Library AST.
Recursive Library AST. 


Require Extraction.
Cd "extraction".
Separate Extraction X.C.
Extraction Library X.

Require Extraction.
Extraction Language OCaml.
Extraction "compcert.ml" Base.SimplExpr.transl_function.
