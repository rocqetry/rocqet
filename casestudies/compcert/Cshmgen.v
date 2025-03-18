(*only  Clight Cshminor*)
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
Require Import Cfam.
Require Import Csharpminor.

Trait Base. 

(* ------------------------------------------------ *)
(*             Cshmgen (Clight -> Csharpminor)      *)
(* ------------------------------------------------ *)
Family Cshmgen.
Family S extends Clight.

Inherit find_label.

MetaData function_entry2.
Inductive function_entry2 (ge: genv) (f: function) (vargs: list val) (m: mem) (e: env) (le: temp_env) (m': mem) : Prop :=
  | function_entry2_intro:
      list_norepet (var_names f.(fn_vars)) ->
      list_norepet (var_names f.(fn_params)) ->
      list_disjoint (var_names f.(fn_params)) (var_names f.(fn_temps)) ->
      alloc_variables ge empty_env m f.(fn_vars) e m' ->
      bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le ->
      function_entry2 ge f vargs m e le m'.
FEnd function_entry2.
FOverride Definition function_entry := function_entry2.
FEnd S.
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
(* ------------------------------------------------ *)
(* ---------------- Cshmgenproof ------------------ *)
(* ------------------------------------------------ *)


MetaData match_fundef.
Inductive match_fundef (p: self__Cshmgen.S.program) : self__Cshmgen.S.fundef -> self__Cshmgen.T.fundef -> Prop :=
  | match_fundef_internal: forall f tf,
      self__Cshmgen.transl_function p.(prog_comp_env) f = OK tf ->
      match_fundef p (Ctypes.Internal f) (AST.Internal tf)
  | match_fundef_external: forall ef args res cc,
      ef_sig ef = signature_of_type args res cc ->
      match_fundef p (Ctypes.External ef args res cc) (AST.External ef).
FEnd match_fundef.

FDefinition match_varinfo : type -> unit -> Prop := fun v tv => True.

FDefinition match_prog : S.program -> T.program -> Prop := fun p tp =>
  match_program_gen match_fundef match_varinfo p p tp.

FLemma transl_sizeof:
  forall (cunit prog: S.program) t sz,
  linkorder cunit prog ->
  sizeof cunit.(prog_comp_env) t = OK sz ->
  sz = Ctypes.sizeof prog.(prog_comp_env) t.
FProofLemma.
  intros. destruct H.
  unfold sizeof in H0. destruct (complete_type (prog_comp_env cunit) t) eqn:C; inv H0.
  symmetry. apply Ctypes.sizeof_stable; auto.
Qed. CloseFLemma.

(*
Variable prog: Clight.program.
Variable tprog: Csharpminor.program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge := globalenv prog.
Let tge := Genv.globalenv tprog.
 *)
(* ------------------------------------------------ *)
(*                  CONSTRUCTORS                    *)
(* ------------------------------------------------ *)
FLemma make_intconst_correct:
  forall lenv ge n e le m,
  T.eval_expr ge e le m lenv (make_intconst n) (Vint n).
FProofLemma.
intros. unfold make_intconst. fconstructor. fsimpl.
reflexivity.
Qed. CloseFLemma.

FLemma make_floatconst_correct:
  forall lenv ge n e le m,
  T.eval_expr ge e le m lenv (make_floatconst n) (Vfloat n).
FProofLemma.
intros. unfold make_floatconst. fconstructor.
fsimpl. reflexivity.
Qed. CloseFLemma.

FLemma make_singleconst_correct:
  forall lenv ge n e le m,
  T.eval_expr ge e le m lenv (make_singleconst n) (Vsingle n).
FProofLemma.
intros. unfold make_singleconst. fconstructor.
fsimpl. reflexivity.
Qed. CloseFLemma.

FLemma make_longconst_correct:
  forall lenv ge n e le m,
  T.eval_expr ge e le m lenv (make_longconst n) (Vlong n).
FProofLemma.
intros. unfold make_floatconst. fconstructor.
fsimpl. reflexivity.
Qed. CloseFLemma.

FLemma make_ptrofsconst_correct:
  forall lenv ge n e le m,
  T.eval_expr ge e le m lenv (make_ptrofsconst n) (Vptrofs (Ptrofs.repr n)).
FProofLemma.
  intros. unfold Vptrofs, make_ptrofsconst. destruct Archi.ptr64 eqn:SF.
- replace (Ptrofs.to_int64 (Ptrofs.repr n)) with (Int64.repr n).
  apply make_longconst_correct.
  symmetry; auto with ptrofs.
- replace (Ptrofs.to_int (Ptrofs.repr n)) with (Int.repr n).
  apply make_intconst_correct.
  symmetry; auto with ptrofs.
Qed. CloseFLemma.

FLemma make_singleoffloat_correct:
  forall lenv ge a n e le m,
  T.eval_expr ge e le m lenv a (Vfloat n) ->
  T.eval_expr ge e le m lenv (make_singleoffloat a) (Vsingle (Float.to_single n)).
FProofLemma.
  intros. fconstructor.
Qed. CloseFLemma.

FLemma make_floatofsingle_correct:
  forall lenv ge a n e le m,
  T.eval_expr ge e le m lenv a (Vsingle n) ->
  T.eval_expr ge e le m lenv (make_floatofsingle a) (Vfloat (Float.of_single n)).
FProofLemma.
  intros. fconstructor.
Qed. CloseFLemma.

FLemma make_floatofint_correct:
  forall lenv ge a n sg e le m,
  T.eval_expr ge e le m lenv a (Vint n) ->
  T.eval_expr ge e le m lenv (make_floatofint a sg) (Vfloat (cast_int_float sg n)).
FProofLemma.
  intros. unfold make_floatofint, cast_int_float.
  destruct sg; fconstructor; eauto.
Qed. CloseFLemma.

(* Hint Extern 2 (@eq trace _ _) => traceEq: cshm. *)
(* helper lemmas for make_cmpu_ne_zero_correct *)
FLemma default_Vint :
  forall lenv ge e le m a n,
    T.eval_expr ge e le m lenv a (Vint n) ->
    T.eval_expr ge e le m lenv (T.Ebinop (Ocmpu Cne) a (make_intconst Int.zero))
      (Vint (if Int.eq n Int.zero then Int.zero else Int.one)).
FProofLemma.
intros. fconstructor; eauto.
- fconstructor. fsimpl. reflexivity.
- simpl. unfold Val.cmpu, Val.cmpu_bool.
unfold Int.cmpu. destruct (Int.eq n Int.zero); auto.
Qed. CloseFLemma.

FLemma cmp :
  forall n ob,
    Val.of_optbool ob = Vint n ->
    n = (if Int.eq n Int.zero then Int.zero else Int.one).
FProofLemma.
intros. destruct ob; simpl in H; inv H. destruct b; inv H1.
- rewrite Int.eq_false; auto. apply Int.one_not_zero.
- rewrite Int.eq_true. auto.
Qed. CloseFLemma.

(* inversion lemmas for use in make_cmpu_ne_zero_correct *)
Closing Fact eval_Ebinop_inv :
  forall ge lenv e le m op a1 a2 v1 v2 v,
    T.eval_expr ge e le m lenv (T.Ebinop op a1 a2) v ->
    T.eval_expr ge e le m lenv a1 v1 /\
      T.eval_expr ge e le m lenv a2 v2 /\
      eval_binop op v1 v2 m = Some v
    by plain {intros until tmp; intros H; inv H; eauto}.

(* make cmpu is correct, requires nested induction *)
MetaData make_cmpu_ne_zero_correct.
Axiom make_cmpu_ne_zero_correct:
  forall tge e le m a n lenv,
  T.eval_expr tge e le m lenv a (Vint n) ->
  T.eval_expr tge e le m lenv (make_cmpu_ne_zero a) (Vint (if Int.eq n Int.zero then Int.zero else Int.one)).
FEnd make_cmpu_ne_zero_correct.

(* For proving make_cmpu_ne_zero_correct_ptr *)
FLemma default_Vone :
  forall lenv ge e le m a b i,
    T.eval_expr ge e le m lenv a (Vptr b i) ->
    Archi.ptr64 = false ->
    Mem.weak_valid_pointer m b (Ptrofs.unsigned i) = true ->
    T.eval_expr ge e le m lenv (T.Ebinop (Ocmpu Cne) a (make_intconst Int.zero)) Vone.
FProofLemma.
intros. fconstructor. { fconstructor. fsimpl. reflexivity. }
simpl. unfold Val.cmpu, Val.cmpu_bool.
unfold Mem.weak_valid_pointer in H1. rewrite H0, H1.
rewrite Int.eq_true; auto.
Qed. CloseFLemma.

FLemma of_optbool :
  forall ob b i,
    Some (Val.of_optbool ob) <> Some (Vptr b i).
FProofLemma.
intros. destruct ob as [[]|]; discriminate.
Qed. CloseFLemma.
FLemma of_bool :
  forall ob b i,
    option_map Val.of_bool ob <> Some (Vptr b i).
FProofLemma.
intros. destruct ob as [[]|]; discriminate.
Qed. CloseFLemma.

(* same as above *)
MetaData make_cmpu_ne_zero_correct_ptr.
Axiom make_cmpu_ne_zero_correct_ptr:
  forall tge e le m a b i lenv,
  T.eval_expr tge e le m lenv a (Vptr b i) ->
  Archi.ptr64 = false ->
  Mem.weak_valid_pointer m b (Ptrofs.unsigned i) = true ->
  T.eval_expr tge e le m lenv (make_cmpu_ne_zero a) Vone.
FEnd make_cmpu_ne_zero_correct_ptr.

FLemma make_cast_int_correct:
  forall lenv ge e le m a n sz si,
  T.eval_expr ge e le m lenv a (Vint n) ->
  T.eval_expr ge e le m lenv (make_cast_int a sz si) (Vint (cast_int_int sz si n)).
FProofLemma.
intros. unfold make_cast_int, cast_int_int.
destruct sz; destruct si; eauto;try fconstructor;
  eapply make_cmpu_ne_zero_correct in H; apply H ; auto.    
Qed. CloseFLemma.

FLemma make_longofint_correct:
  forall lenv ge e le m a n si,
  T.eval_expr ge e le m lenv a (Vint n) ->
  T.eval_expr ge e le m lenv (make_longofint a si) (Vlong (cast_int_long si n)).
FProofLemma.
intros. unfold make_longofint, cast_int_long. destruct si; eauto;fconstructor.
Qed. CloseFLemma.

Ltac InvEval :=
  match goal with
  | [ H: None = Some _ |- _ ] => discriminate
  | [ H: Some _ = Some _ |- _ ] => inv H; InvEval
  | [ H: match ?x with Some _ => _ | None => _ end = Some _ |- _ ] => destruct x eqn:?; InvEval
  | [ H: match ?x with true => _ | false => _ end = Some _ |- _ ] => destruct x eqn:?; InvEval
  | _ => idtac
  end.

MetaData _chm_db_.
Hint Resolve make_intconst_correct make_floatconst_correct make_longconst_correct
             make_singleconst_correct make_singleoffloat_correct make_floatofsingle_correct
             make_floatofint_correct: cshm.
(* Hint Constructors eval_expr eval_exprlist: cshm.*)
Hint Extern 2 (@eq trace _ _) => traceEq: cshm.
Hint Extern 5 => fconstructor : cshm.
Hint Resolve make_cast_int_correct make_longofint_correct: cshm.
FEnd _chm_db_.

FLemma make_cast_correct:
  forall lenv ge e le m a b v ty1 ty2 v',
  make_cast ty1 ty2 a = OK b ->
  T.eval_expr ge e le m lenv a v ->
  sem_cast v ty1 ty2 m = Some v' ->
  T.eval_expr ge e le m lenv b v'.
FProofLemma.
intros. unfold make_cast, sem_cast in *;
  destruct (classify_cast ty1 ty2); inv H; destruct v; InvEval; eauto with cshm.
- (* single -> int *)
  unfold make_singleofint, cast_int_float. destruct si1; eauto with cshm.
- (* float -> int *)
  apply make_cast_int_correct.
  unfold cast_float_int in Heqo. unfold make_intoffloat.
  destruct si2; fconstructor; eauto; simpl; rewrite Heqo; auto.
- (* single -> int *)
  apply make_cast_int_correct.
  unfold cast_single_int in Heqo. unfold make_intofsingle.
  destruct si2; fconstructor; eauto with cshm; simpl; rewrite Heqo; auto.
- (* long -> float *)
  unfold make_floatoflong, cast_long_float. destruct si1; eauto with cshm.
- (* long -> single *)
  unfold make_singleoflong, cast_long_single. destruct si1; eauto with cshm.
- (* float -> long *)
  unfold cast_float_long in Heqo. unfold make_longoffloat.
  destruct si2; fconstructor; eauto; simpl; rewrite Heqo; auto.
- (* single -> long *)
  unfold cast_single_long in Heqo. unfold make_longofsingle.
  destruct si2; fconstructor; eauto with cshm; simpl; rewrite Heqo; auto.
- (* int -> bool *)
  apply make_cmpu_ne_zero_correct; auto.
- (* pointer (32 bits) -> bool *)
  eapply make_cmpu_ne_zero_correct_ptr; eauto.
- (* long -> bool *)
  fconstructor; eauto with cshm.
  simpl. unfold Val.cmplu, Val.cmplu_bool, Int64.cmpu.
  destruct (Int64.eq i Int64.zero); auto.
- (* pointer (64 bits) -> bool *)
  fconstructor; eauto with cshm.
  simpl. unfold Val.cmplu, Val.cmplu_bool. unfold Mem.weak_valid_pointer in Heqb1.
  rewrite Heqb0, Heqb1. rewrite Int64.eq_true. reflexivity.
- (* float -> bool *)
  fconstructor; eauto with cshm.
  simpl. unfold Val.cmpf, Val.cmpf_bool. rewrite Float.cmp_ne_eq.
  destruct (Float.cmp Ceq f Float.zero); auto.
- (* single -> bool *)
  fconstructor; eauto with cshm.
  simpl. unfold Val.cmpfs, Val.cmpfs_bool. rewrite Float32.cmp_ne_eq.
  destruct (Float32.cmp Ceq f Float32.zero); auto.
- (* struct *)
  destruct (ident_eq id1 id2); inv H1; auto.
- (* union *)
  destruct (ident_eq id1 id2); inv H1; auto.
Qed. CloseFLemma. 

FLemma make_boolean_correct:
 forall lenv ge e le m a v ty b,
  T.eval_expr ge e le m lenv a v ->
  bool_val v ty m = Some b ->
  exists vb,
    T.eval_expr ge e le m lenv (make_boolean a ty) vb
    /\ Val.bool_of_val vb b.
FProofLemma.
intros. unfold make_boolean. unfold bool_val in H0.
  destruct (classify_bool ty); destruct v; InvEval.
- (* int *)
  econstructor; split.
  + eapply make_cmpu_ne_zero_correct ; eauto.
  + destruct (Int.eq i Int.zero); simpl; constructor.
- (* ptr 32 bits *)
  exists Vone; split. eapply make_cmpu_ne_zero_correct_ptr; eauto. constructor.
- (* long *)
  econstructor; split.
  + fconstructor. { fconstructor. fsimpl. reflexivity. }
    simpl. unfold Val.cmplu. simpl. eauto.
  + destruct (Int64.eq i Int64.zero); simpl; constructor.
- (* ptr 64 bits *)
  exists Vone; split.
  fconstructor. { fconstructor. fsimpl. reflexivity. }
  simpl. unfold Val.cmplu, Val.cmplu_bool.
  unfold Mem.weak_valid_pointer in Heqb0. rewrite Heqb0, Heqb1, Int64.eq_true. reflexivity.
  constructor.
- (* float *)
  econstructor; split. fconstructor. { fconstructor. fsimpl. reflexivity. }
  simpl. eauto.
  unfold Val.cmpf, Val.cmpf_bool. simpl. rewrite <- Float.cmp_ne_eq.
  destruct (Float.cmp Cne f Float.zero); constructor.
- (* single *)
  econstructor; split.
  fconstructor. { fconstructor. fsimpl. reflexivity. } simpl. eauto.
  unfold Val.cmpfs, Val.cmpfs_bool. simpl. rewrite <- Float32.cmp_ne_eq.
  destruct (Float32.cmp Cne f Float32.zero); constructor.
Qed. CloseFLemma.

(* ------------------------------------------------ *)
(*                  CORRECTNESS                     *)
(* ------------------------------------------------ *)
(*FLemma function_ptr_translated:
  forall ge tge prog tprog v f,
  Genv.find_funct_ptr ge v = Some f ->
  exists cu tf, Genv.find_funct_ptr tge v = Some tf /\ match_fundef cu f tf /\ linkorder cu prog.
  *)
MetaData match_env.

Record match_env
  (prog: S.program)
  (e: S.env) (te: T.fenv) : Prop :=
 mk_match_env {
   me_local:
     forall id b ty,
       e!id = Some (b, ty) ->
       let ge := S.globalenv prog in 
       te!id = Some (b, Ctypes.sizeof (S.genv_cenv ge) ty);
   me_local_inv:
     forall id b sz,
     te!id = Some (b, sz) -> exists ty, e!id = Some(b, ty)
}.
FEnd match_env.

FLemma match_env_same_blocks:
  forall prog e te,
  match_env prog e te ->
  T.blocks_of_env te = S.blocks_of_env (S.globalenv prog) e.
FProofLemma.
intros.
set (R := fun (x: (block * type)) (y: (block * Z)) =>
            match x, y with
            | (b1, ty), (b2, sz) => b2 = b1 /\ sz = Ctypes.sizeof (S.genv_cenv (S.globalenv prog)) ty
            end).
assert (list_forall2
          (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
          (PTree.elements e) (PTree.elements te)).
    apply PTree.elements_canonical_order. 
    intros id [b ty] GET.
    exists (b, Ctypes.sizeof (S.genv_cenv (S.globalenv prog)) ty); split. eapply me_local; eauto.
    red; auto. 
    intros id [b sz] GET. exploit me_local_inv; eauto. intros [ty EQ].
    exploit me_local; eauto. intros EQ1.
    exists (b, ty); split. auto. red; split; congruence. 
unfold T.blocks_of_env, S.blocks_of_env.
generalize H0. induction 1. auto.
simpl. f_equal; auto.
unfold T.block_of_binding, S.block_of_binding.
destruct a1 as [id1 [blk1 ty1]]. destruct b1 as [id2 [blk2 sz2]].
simpl in *. destruct H1 as [A [B C]]. congruence.
Qed. CloseFLemma.

FLemma match_env_free_blocks:
  forall prog e te m m',
  match_env prog e te ->
  Mem.free_list m (S.blocks_of_env (S.globalenv prog) e) = Some m' ->
  Mem.free_list m (T.blocks_of_env te) = Some m'.
FProofLemma.
intros. rewrite (match_env_same_blocks prog _ _ H). auto.
Qed. CloseFLemma.

FLemma match_env_empty:
  forall prog,
  match_env prog S.empty_env T.empty_fenv.
FProofLemma.
  unfold S.empty_env, T.empty_fenv.
  constructor.
  intros until ty. repeat rewrite PTree.gempty. congruence.
  intros until sz. rewrite PTree.gempty. congruence.
Qed. CloseFLemma.

FLemma match_env_alloc_variables:
  forall prog cunit, linkorder cunit prog -> 
  forall ge e1 m1 vars e2 m2, S.alloc_variables ge e1 m1 vars e2 m2 ->
  forall tvars te1,
  mmap (transl_var cunit.(prog_comp_env)) vars = OK tvars ->
  match_env prog e1 te1 ->
  exists te2,
  T.alloc_variables te1 m1 tvars te2 m2
  /\ match_env prog e2 te2.
FProofLemma.
 induction 2; simpl; intros.
- inv H0. exists te1; split. constructor. auto.
- monadInv H2. monadInv EQ1. simpl in *. monadInv EQ.
  exploit transl_sizeof. eexact H.  eauto. intros SZ; rewrite SZ.
  exploit (IHalloc_variables x0 (PTree.set id (b1, Ctypes.sizeof (S.genv_cenv ge) ty) te1)).
  auto.
  constructor.
    (* me_local *)
    intros until ty0. repeat rewrite PTree.gsspec.
    destruct (peq id0 id); intros. subst ge0. apply cheat. (* congruence. we know ge = ge0 is true *) eapply me_local; eauto.
    (* me_local_inv *)
    intros until sz. repeat rewrite PTree.gsspec.
    destruct (peq id0 id); intros. exists ty; congruence. eapply me_local_inv; eauto.
    intros [te2 [ALLOC MENV]].
    assert (prog_comp_env prog = S.genv_cenv ge) by (apply cheat). (* we kinow this is true *) rewrite H4.
  exists te2; split. econstructor; eauto. exact MENV.  
Qed. CloseFLemma. 

FLemma create_undef_temps_match:
  forall temps,
  T.create_undef_temps (map fst temps) = S.create_undef_temps temps.
FProofLemma.
induction temps; simpl. auto.
destruct a as [id ty]. simpl. decEq. auto.
Qed. CloseFLemma.

FLemma bind_parameter_temps_match:
  forall vars vals le1 le2,
  S.bind_parameter_temps vars vals le1 = Some le2 ->
  T.bind_parameters (map fst vars) vals le1 = Some le2.
FProofLemma.
induction vars; simpl; intros.
destruct vals; inv H. auto.
destruct a as [id ty]. destruct vals; try discriminate. auto.
Qed. CloseFLemma.
FLemma transl_vars_names:
  forall ce vars tvars,
  mmap (transl_var ce) vars = OK tvars ->
  map fst tvars = S.var_names vars.
FProofLemma.
  intros. exploit mmap_inversion; eauto. generalize vars tvars. induction 1; simpl.
- auto.
- monadInv H0. simpl; congruence.
Qed. CloseFLemma.

FLemma function_ptr_translated
  : forall prog tprog ge tge, match_prog prog tprog ->
    ge = Genv.globalenv prog ->
    tge = Genv.globalenv tprog ->
    forall v f, 
      Genv.find_funct_ptr ge v = Some f ->
      exists cu tf, Genv.find_funct_ptr tge v = Some tf /\ match_fundef cu f tf /\ linkorder cu prog.
FProofLemma.
intros until tge. intros TRANSL A B.
rewrite A. rewrite B.
apply (Genv.find_funct_ptr_match TRANSL).
Qed. CloseFLemma.

FLemma symbols_preserved : 
  forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
FProofLemma.
intros until tge; intros TRANSL A B. rewrite A. rewrite B.
apply (Genv.find_symbol_match TRANSL).
Qed. CloseFLemma.

(* ------------------------------------------------ *)
(*               CORRECTNESS - EXPR                 *)
(* ------------------------------------------------ *)
FInduction transl_expr_correct about S.eval_expr 
  motive (fun ge (e: S.env) le m a v (_ : S.eval_expr ge e le m a v) =>
      forall prog tprog tge, match_prog prog tprog ->
      S.globalenv prog = ge -> Genv.globalenv tprog = tge ->
      forall (cunit: S.program) (L : linkorder cunit prog) te ta (MENV: match_env prog e te) lenv,
      transl_expr a cunit.(prog_comp_env) = OK ta ->
      T.eval_expr tge te le m lenv ta v).
FProof.
all: unfold transl_expr in *; unfold fst in *.
(* const int *)
+ intros. fsimpl in H2. inv H2. apply make_intconst_correct.
(* const float *)  
+ intros. fsimpl in H2. inv H2. apply make_floatconst_correct.
(* const single *)  
+ intros. fsimpl in H2. inv H2. apply make_singleconst_correct.
(* const long *)  
+ intros. fsimpl in H2. inv H2. apply make_longconst_correct.
(* cast *)  
+ intros. fsimpl in H3. monadInv H3. eapply make_cast_correct; eauto.
(* temp var *)  
+ intros. fsimpl in H2. monadInv H2. fconstructor.
Qed. FEnd transl_expr_correct.
(* ------------------------------------------------ *)
(*              CORRECTNESS - OTHER1                *)
(* ------------------------------------------------ *)
FInductive match_transl
  : self__Cshmgen.T.stmt -> self__Cshmgen.T.cont ->
    self__Cshmgen.T.stmt -> self__Cshmgen.T.cont -> Prop :=
| match_transl_0: forall ts tk,
    match_transl ts tk ts tk.

FInductive match_cont : composite_env -> type -> nat -> nat -> S.cont -> T.cont -> Prop :=
| match_Kstop: forall ce tyret nbrk ncnt,
    match_cont ce tyret nbrk ncnt S.Kstop T.Kstop      
| match_Kseq: forall ce tyret nbrk ncnt s k ts tk,
    transl_stmt s ce tyret nbrk ncnt = OK ts ->
    match_cont ce tyret nbrk ncnt k tk ->
    match_cont ce tyret nbrk ncnt (S.Kseq s k) (T.Kseq ts tk).
               
MetaData match_states.
Inductive match_states (prog: S.program): S.state -> T.state -> Prop :=
| match_state:
    forall f nbrk ncnt s k e le m tf ts tk te ts' tk' (cu : S.program)
        (LINK: linkorder cu prog)
        (TRF: transl_function cu.(prog_comp_env) f = OK tf)
        (TR: transl_stmt s cu.(prog_comp_env) (S.fn_return f) nbrk ncnt = OK ts)
        (MTR: match_transl ts tk ts' tk')
        (MENV: match_env prog e te)
        (MK: match_cont cu.(prog_comp_env) (S.fn_return f) nbrk ncnt k tk),
    match_states prog (S.State f s k e le m)
      (T.State tf ts' tk' te le m)      
| match_callstate:
    forall fd args k m tfd tk targs tres cconv cu ce
           (LINK: linkorder cu prog)
        (TR: match_fundef cu fd tfd)
        (MK: match_cont ce tres 0%nat 0%nat k tk)
        (ISCC: S.is_call_cont k)
        (TY: S.type_of_fundef fd = Tfunction targs tres cconv)
        (CASTED: Val.has_argtype_list args (List.map argtype_of_type targs)),
    match_states prog (S.Callstate fd args k m)
      (T.Callstate tfd args tk m)      
| match_returnstate:
    forall res tres k m tk ce
        (MK: match_cont ce tres 0%nat 0%nat k tk),
        (* (WT: wt_val res tres),*) (* Need Ctyping.v? *)
    match_states prog (S.Returnstate res k m)
      (T.Returnstate res tk m).
FEnd match_states.

(* This should probably take tprog and match_prog as Hypothesis *)
FLemma match_states_skip:
  forall f e le te nbrk ncnt k tf tk m (cu: S.program) (prog: S.program),
  linkorder cu prog ->
  transl_function cu.(prog_comp_env) f = OK tf ->
  match_env prog e te ->
  match_cont cu.(prog_comp_env) (S.fn_return f) nbrk ncnt k tk ->
  match_states prog (S.State f S.Sskip k e le m) (T.State tf T.Sskip tk te le m).
FProofLemma.
  intros. econstructor; eauto. fsimpl ; reflexivity. fconstructor.
Qed. CloseFLemma.
(* ------------------------------------------------ *)
(*            CORRECTNESS - FIND_LABEL              *)
(* ------------------------------------------------ *)
(* ------------------------------------------------ *)
(*              CORRECTNESS - OTHER2                *)
(* ------------------------------------------------ *)
FInduction match_cont_call_cont about match_cont 
  motive (fun ce tyret nbrk ncnt k tk (_ : match_cont ce tyret nbrk ncnt k tk) =>
  forall ce' nbrk' ncnt',
  match_cont ce' tyret nbrk' ncnt' (S.call_cont k) (T.call_cont tk)).
FProof.
+ intros. do 2 fsimpl. fconstructor.
+ intros until tk; intros A B H. do 2 fsimpl. apply H.
Qed. FEnd match_cont_call_cont. 

FInduction match_cont_is_call_cont about match_cont
  motive (fun ce tyret nbrk ncnt k tk (_ : match_cont ce tyret nbrk ncnt k tk) =>
  forall ce' nbrk' ncnt',
  S.is_call_cont k ->
  match_cont ce' tyret nbrk' ncnt' k tk /\ T.is_call_cont tk).
FProof.
+ intros. fsimpl in *. fsimpl in H. split. fconstructor. auto.
+ intros. fsimpl in *. fsimpl in H0. contradiction.
Qed. FEnd match_cont_is_call_cont.  

(* use closing fact for inversion*)
Closing Fact match_transl_0_inv :
  forall ts tk ts' tk',
    match_transl ts tk ts' tk' ->
    ts' = ts /\ tk' = tk
    by plain {intros until tmp; intros H; inv H; eauto}.

Closing Fact match_Kseq_inv :
  forall ce tyret nbrk ncnt s k the_tk,
    match_cont ce tyret nbrk ncnt (S.Kseq s k) the_tk ->
    exists ts tk,
    the_tk = T.Kseq ts tk /\
      transl_stmt s ce tyret nbrk ncnt = OK ts /\
      match_cont ce tyret nbrk ncnt k tk
    by plain {intros until the_tk; intros H; inv H; eauto}.

Closing Fact match_Kstop_inv :
  forall ce tyret nbrk ncnt tk,
    match_cont ce tyret nbrk ncnt S.Kstop tk ->
    tk = T.Kstop
    by plain {intros until tmp; intros H; inv H; eauto}.

FLemma transl_fundef_sig1:
  forall ce f tf args res cc,
  match_fundef ce f tf ->
  Cop.classify_fun (S.type_of_fundef f) = fun_case_f args res cc ->
  T.funsig tf = signature_of_type args res cc.
FProofLemma.
  intros. inv H.
- monadInv H1. simpl. inversion H0. reflexivity.
- simpl in H0. unfold T.funsig. congruence.
Qed. CloseFLemma.

FLemma transl_fundef_sig2:
  forall ce f tf args res cc,
  match_fundef ce f tf ->
  S.type_of_fundef f = Tfunction args res cc ->
  T.funsig tf = signature_of_type args res cc.
FProofLemma.
  intros. eapply transl_fundef_sig1; eauto.
  rewrite H0; reflexivity.
Qed. CloseFLemma.

FInduction transl_find_label about S.stmt motive (fun (s : S.stmt) =>
  forall ce lbl tyret nbrk ncnt k ts tk
  (TR: transl_stmt s ce tyret nbrk ncnt = OK ts)
  (MC: match_cont ce tyret nbrk ncnt k tk),
  match S.find_label s lbl k with
  | None => T.find_label ts lbl tk = None
  | Some (s', k') =>
      exists ts', exists tk', exists nbrk', exists ncnt',
      T.find_label ts lbl tk = Some (ts', tk')
      /\ transl_stmt s' ce tyret nbrk' ncnt' = OK ts'
      /\ match_cont ce tyret nbrk' ncnt' k' tk'
  end).
FProof.
all: intros; fsimpl in TR; try (monadInv TR); simpl; fsimpl.
(* skip *)
+ fsimpl; reflexivity.
(* assign *)  
+ fsimpl; reflexivity.
(* seq *)  
+ exploit (H ce lbl tyret nbrk ncnt (S.Kseq __i0 k)); eauto. fconstructor; eauto.
  destruct (S.find_label __i lbl (S.Kseq __i0 k)) as [[s' k'] | ].    
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].  fsimpl.
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. fsimpl. rewrite H1. eapply H0; eauto. 
(* ifthenelse *)  
+ exploit H; eauto. instantiate (1 := lbl). fsimpl.
  destruct (S.find_label __i lbl k) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H1. eapply H0; eauto.  
(* return *)  
+ destruct o; monadInv TR; fsimpl; reflexivity.
(* label *)  
+ fsimpl. destruct (ident_eq lbl l). 
  exists x; exists tk; exists nbrk; exists ncnt; auto. 
  eapply H; eauto.
(* goto *)  
+ fsimpl; reflexivity.
Qed. FEnd transl_find_label.

FInduction transl_step about S.step
  motive (fun ge S1 t S2 (_ : S.step ge S1 t S2) => 
            forall prog tprog tge,
            match_prog prog tprog ->
           forall (A : S.globalenv prog = ge) (B : Genv.globalenv tprog = tge), 
  forall T1, match_states prog S1 T1 -> 
  exists T2, plus T.step tge T1 t T2 /\ match_states prog S2 T2).
FProof.
all: intros until tge; intros TRANSL A B; intros T1 MST; inv MST.
(* skip seq *)
+ fsimpl in TR. monadInv TR. apply match_transl_0_inv in MTR; unpack MTR; subst.
  apply match_Kseq_inv in MK; unpack MK. subst.  
  econstructor; split.
  apply plus_one. apply T.step_skip_seq.
  econstructor; eauto. fconstructor.
(* set *)  
+ fsimpl in TR.  monadInv TR. apply match_transl_0_inv in MTR; unpack MTR; subst. econstructor; split.
  apply plus_one. fconstructor. eapply transl_expr_correct; eauto.
  eapply match_states_skip; eauto.
  (* letenv not used *)
  Unshelve. apply nil.
(* seq *)  
+ fsimpl in TR. monadInv TR. apply match_transl_0_inv in MTR; unpack MTR; subst.
  econstructor; split.
  apply plus_one. fconstructor.
  econstructor; eauto. fconstructor.
  fconstructor; eauto.
(* ifthenelse *)  
+ fsimpl in TR. monadInv TR. apply match_transl_0_inv in MTR; unpack MTR; subst.
  exploit make_boolean_correct; eauto.
  exploit transl_expr_correct; eauto.
  intros [v [A B]].
  econstructor; split.
  apply plus_one. apply T.step_ifthenelse with (v := v) (b := b) (lenv := nil); auto.
  apply A. destruct b. econstructor; eauto. fconstructor. econstructor; eauto. fconstructor.
(* return none *)  
+ fsimpl in TR. monadInv TR. apply match_transl_0_inv in MTR; unpack MTR; subst.
  econstructor; split.
  apply plus_one. fconstructor.
  eapply match_env_free_blocks; eauto.
  eapply match_returnstate with (ce := prog_comp_env cu); eauto.
  eapply match_cont_call_cont. eauto.
  (* constructor *)
(* return some *)  
+ fsimpl in TR. monadInv TR. apply match_transl_0_inv in MTR; unpack MTR; subst.
  econstructor; split.
  apply plus_one. fconstructor.
  eapply make_cast_correct; eauto. eapply transl_expr_correct; eauto.
  eapply match_env_free_blocks; eauto.
  eapply match_returnstate with (ce := prog_comp_env cu); eauto.
  eapply match_cont_call_cont. eauto.
  Unshelve. apply nil.
  (* apply wt_val_casted. eapply cast_val_is_casted; eauto. *)
(* skip call *)  
+ fsimpl in TR. monadInv TR. apply match_transl_0_inv in MTR; unpack MTR; subst.
  exploit match_cont_is_call_cont; eauto. intros [A B].
  econstructor; split.
  apply plus_one. apply T.step_skip_call. auto.
  eapply match_env_free_blocks; eauto.
  eapply match_returnstate with (ce := prog_comp_env cu); eauto.
  (* constructor.*)
(* label *)  
+ fsimpl in TR. monadInv TR. apply match_transl_0_inv in MTR; unpack MTR; subst.
  econstructor; split.
  apply plus_one. fconstructor.
  econstructor; eauto. fconstructor.
  
(* goto *)  
+ fsimpl in TR. monadInv TR. apply match_transl_0_inv in MTR; unpack MTR; subst.
  generalize TRF. unfold transl_function. intro TRF'. monadInv TRF'.
  exploit (transl_find_label (S.fn_body f) (prog_comp_env cu) lbl). eexact EQ. eapply match_cont_call_cont. eauto.
  rewrite e0.
  intros [ts' [tk'' [nbrk' [ncnt' [A [B C]]]]]].
  econstructor; split.
  apply plus_one. fconstructor. simpl. (* eexact A.*)
  econstructor; eauto. fconstructor.
  
(* internal function *)  
+ inv f0. inv TR. monadInv H5. 
  exploit match_cont_is_call_cont; eauto. intros [A B].
  exploit match_env_alloc_variables; eauto.
  apply match_env_empty.
  intros [te1 [C D]].
  simpl in TY. unfold S.type_of_function in TY.
  econstructor; split.
  apply plus_one. eapply T.step_internal_function.
  simpl. replace (map snd (S.fn_params f)) with targs. exact CASTED.
  unfold type_of_params in TY; congruence. 
  simpl. erewrite transl_vars_names by eauto. assumption.
  simpl. assumption.
  simpl. assumption.
  simpl; eauto.
  simpl. rewrite create_undef_temps_match. eapply bind_parameter_temps_match; eauto.
  simpl. econstructor; eauto.
  unfold transl_function. rewrite EQ; simpl. rewrite EQ1; simpl. auto.
  fconstructor.
  replace (S.fn_return f) with tres. eassumption. congruence.
Qed. FEnd transl_step.

FLemma transl_initial_states:
  forall S' ge tge prog tprog, match_prog prog tprog -> S.initial_state prog S' ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->                        
  transl_program prog = OK tprog ->
  exists R, T.initial_state tprog R /\ match_states prog S' R.
FProofLemma.
 intros. inv H0.
 exploit function_ptr_translated; eauto. intros (cu & tf & A & B & C).
 remember H as TRANSL.
 assert (D: Genv.find_symbol (Genv.globalenv tprog) (AST.prog_main tprog) = Some b).
 { destruct H as (P & Q & R). rewrite Q.
   rewrite (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSL eq_refl eq_refl). auto. }
  assert (E: T.funsig tf = signature_of_type nil type_int32s cc_default).
  { eapply transl_fundef_sig2; eauto. }
  econstructor; split.
  econstructor; eauto. apply (Genv.init_mem_match TRANSL). eauto.
  econstructor; eauto. instantiate (1 := prog_comp_env cu). fconstructor; auto. fsimpl. exact I. constructor.
Qed. CloseFLemma.          
          
FLemma transl_final_states:
  forall S' R r prog,
  match_states prog S' R -> S.final_state S' r -> T.final_state R r.
FProofLemma.
intros. inv H0. inv H. apply match_Kstop_inv in MK.
subst. constructor.
Qed. CloseFLemma.

FEnd Cshmgen.

FEnd Base.

Trait Comp_Loops extends Base.

Trait Clight_Sloop extends Clight.
FInductive stmt : Type := 
  | Sloop: stmt -> stmt -> stmt (* infinite loop *)
  | Sbreak : stmt (* break statement *)
  | Scontinue : stmt. (* continue statement *)

FInductive cont: Type :=
| Kloop1: stmt -> stmt -> cont -> cont  (* Kloop1 s1 s2 k = after s1 in Sloop s1 s2 *)
| Kloop2: stmt -> stmt -> cont -> cont. (* Kloop2 s1 s2 k = after s2 in Sloop s1 s2 *)

FRecursion call_cont.
Case Kloop1 s1 s2 k := (call_cont k).
Case Kloop2 s1 s2 k := (call_cont k).
FEnd call_cont.

FRecursion is_call_cont.
Case _ := False.
FEnd is_call_cont.

FRecursion find_label.
Case Sloop s1 s2 :=
  (fun lbl k =>
     match find_label s1 lbl (Kloop1 s1 s2 k) with
     | Some sk => Some sk
     | None => find_label s2 lbl (Kloop2 s1 s2 k)
     end).
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_loop: forall ge f s1 s2 k e le m,
      step ge (State f (Sloop s1 s2) k e le m)
        E0 (State f s1 (Kloop1 s1 s2 k) e le m)        
| step_skip_or_continue_loop1: forall ge f s1 s2 k e le m x,
      x = Sskip \/ x = Scontinue ->
      step ge (State f x (Kloop1 s1 s2 k) e le m)
        E0 (State f s2 (Kloop2 s1 s2 k) e le m)
| step_break_loop1: forall ge f s1 s2 k e le m,
      step ge (State f Sbreak (Kloop1 s1 s2 k) e le m)
        E0 (State f Sskip k e le m)
| step_skip_loop2: forall ge f s1 s2 k e le m,
      step ge (State f Sskip (Kloop2 s1 s2 k) e le m)
        E0 (State f (Sloop s1 s2) k e le m)
| step_break_loop2: forall ge f s1 s2 k e le m,
      step ge (State f Sbreak (Kloop2 s1 s2 k) e le m)
        E0 (State f Sskip k e le m).
  
FEnd Clight_Sloop.

Family Clight extends Clight_Sloop.
FEnd Clight.

Trait Csharpminor_Sblock extends Csharpminor.
FInductive stmt : Type :=
| Sblock: stmt -> stmt
| Sexit: nat -> stmt.

FInductive cont: Type :=
| Kblock: cont -> cont.

FRecursion call_cont.
Case Kblock k := (call_cont k).
FEnd call_cont.

FRecursion is_call_cont.
Case _ := False.
FEnd is_call_cont.

FRecursion find_label.
Case Sblock s1 :=
  (fun lbl k => find_label s1 lbl (Kblock k)).
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_block: forall ge f s k e le m,
      step ge (State f (Sblock s) k e le m)
        E0 (State f s (Kblock k) e le m)
| step_skip_block: forall ge f k e le m,
      step ge (State f Sskip (Kblock k) e le m)
        E0 (State f Sskip k e le m)        
| step_exit_seq: forall ge f n s k e le m,
    step ge (State f (Sexit n) (Kseq s k) e le m)
      E0 (State f (Sexit n) k e le m)
| step_exit_block_0: forall ge f k e le m,
    step ge (State f (Sexit O) (Kblock k) e le m)
      E0 (State f Sskip k e le m)
| step_exit_block_S: forall ge f n k e le m,
    step ge (State f (Sexit (S n)) (Kblock k) e le m)
      E0 (State f (Sexit n) k e le m).
  
FEnd Csharpminor_Sblock.

(*Trait Csharpminor_Sexit extends Csharpminor.
FInductive stmt : Type :=
| Sexit: nat -> stmt.
FEnd Csharpminor_Sexit.*)

Trait Csharpminor_Sloop extends Csharpminor.
FInductive stmt : Type :=
| Sloop: stmt -> stmt.

FRecursion find_label.
Case Sloop s1 :=
  (fun lbl k => find_label s1 lbl (Kseq (Sloop s1) k)).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_loop: forall ge f s k e le m,
      step ge (State f (Sloop s) k e le m)
        E0 (State f s (Kseq (Sloop s) k) e le m).

FEnd Csharpminor_Sloop.

Family Csharpminor extends   
  (* Csharpminor_Sexit, *)
  Csharpminor_Sloop,
  Csharpminor_Sblock.
FEnd Csharpminor.

From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.

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

FInductive match_transl
  : T.stmt -> T.cont ->
    T.stmt -> T.cont -> Prop :=
| match_transl_1: forall ts tk,
    match_transl (T.Sblock ts) tk ts (T.Kblock tk).

FDefinition Succ := Datatypes.S.

FInductive match_cont : composite_env -> type -> nat -> nat -> S.cont -> T.cont -> Prop :=               
| match_Kloop1: forall ce tyret s1 s2 k ts1 ts2 nbrk ncnt tk,
    transl_stmt s1 ce tyret 1%nat 0%nat = OK ts1 ->
    transl_stmt s2 ce tyret 0%nat (Succ ncnt) = OK ts2 ->
    match_cont ce tyret nbrk ncnt k tk ->
    match_cont ce tyret 1%nat 0%nat
               (S.Kloop1 s1 s2 k)
               (T.Kblock
                  (T.Kseq ts2
                     (T.Kseq
                        (T.Sloop
                           (T.Sseq
                              (T.Sblock ts1) ts2))
                        (T.Kblock tk))))
| match_Kloop2: forall ce tyret s1 s2 k ts1 ts2 nbrk ncnt tk,
    transl_stmt s1 ce tyret 1%nat 0%nat = OK ts1 ->
    transl_stmt s2 ce tyret 0%nat (Succ ncnt) = OK ts2 ->
    match_cont ce tyret nbrk ncnt k tk ->
    match_cont ce tyret 0%nat (Succ ncnt)
               (S.Kloop2 s1 s2 k)
               (T.Kseq
                  (T.Sloop
                     (T.Sseq
                        (T.Sblock ts1) ts2))
                  (T.Kblock tk)).

Closing Fact match_Kloop1_inv : forall ce tyret nbrk ncnt s1 s2 k tk,
    match_cont ce tyret nbrk ncnt (S.Kloop1 s1 s2 k) tk ->
    exists nbrk' ncnt' ts1 ts2 tk',
       nbrk = 1%nat /\ ncnt = 0%nat /\
       tk =  (T.Kblock (T.Kseq ts2 (T.Kseq (T.Sloop (T.Sseq (T.Sblock ts1) ts2)) (T.Kblock tk')))) /\
       transl_stmt s1 ce tyret 1%nat 0%nat = OK ts1 /\
       transl_stmt s2 ce tyret 0%nat (Succ ncnt') = OK ts2 /\
       match_cont ce tyret nbrk' ncnt' k tk'
by plain { apply cheat }.

Closing Fact match_Kloop2_inv : forall ce tyret nbrk ncnt s1 s2 k tk,
  match_cont ce tyret nbrk ncnt (S.Kloop2 s1 s2 k) tk ->
  exists ncnt' nbrk' tk' ts1 ts2,
    nbrk = 0%nat /\ ncnt = (Succ ncnt') /\
    tk = (T.Kseq (T.Sloop (T.Sseq (T.Sblock ts1) ts2)) (T.Kblock tk')) /\
    transl_stmt s1 ce tyret 1%nat 0%nat = OK ts1 /\
    transl_stmt s2 ce tyret 0%nat (Succ ncnt') = OK ts2 /\
    match_cont ce tyret nbrk' ncnt' k tk'
by plain { apply cheat }.
               
FInduction match_cont_call_cont.
FProof.
all: intros; do 5 fsimpl; auto.
Qed. FEnd match_cont_call_cont.

FInduction match_cont_is_call_cont.
FProof.
all: intros; fsimpl in H0; contradiction. 
Qed. FEnd match_cont_is_call_cont.

FInduction transl_find_label.
FProof.
all: intros; fsimpl in TR; try (monadInv TR); simpl; fsimpl.
(* loop *)
+ exploit (H ce lbl tyret 1%nat 0%nat (S.Kloop1 __i __i0 k)); eauto. fconstructor; eauto.
  destruct (S.find_label __i lbl (S.Kloop1 __i __i0 k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].  
  (*rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H.
  eapply transl_find_label; eauto. econstructor; eauto.*)
  apply cheat.
  apply cheat.
(* break *)  
+ fsimpl; reflexivity.
(* continue *)
+ fsimpl; reflexivity.
Qed. FEnd transl_find_label.

Closing Fact match_transl_1_inv :
  forall ts ts' tk tk', 
    match_transl (T.Sblock ts) tk ts' tk' ->
    ts' = ts /\
    tk' = (T.Kblock tk)
by plain { apply cheat }.                

Closing Fact match_transl_step:
  forall ts tk ts' tk' f te le m tge,
  match_transl (T.Sblock ts) tk ts' tk' ->
  star T.step tge (T.State f ts' tk' te le m) E0 (T.State f ts (T.Kblock tk) te le m)
by plain { apply cheat }.       

(*FLemma match_transl_step:
  forall ts tk ts' tk' f te le m tge,
  match_transl (T.Sblock ts) tk ts' tk' ->
  star T.step tge (T.State f ts' tk' te le m) E0 (T.State f ts (T.Kblock tk) te le m).
FProofLemma.
  intros. apply match_transl_0_inv in H; unpack H. 
  apply star_one. constructor.
  apply star_refl.
Qed.*)


FInduction transl_step.
FProof.
all: intros until tge; intros TRANSL A B; intros T1 MST; inv MST.
(* loop *)
+ fsimpl in TR. monadInv TR.
  econstructor; split.
  eapply star_plus_trans. eapply match_transl_step; eauto.
  eapply plus_left. fconstructor.
  eapply star_left. fconstructor.
  apply star_one. fconstructor.
  reflexivity. reflexivity. traceEq.
  econstructor; eauto. fconstructor. fconstructor; eauto.
  
(* skip-or-continue loop *)  
+  assert ((ts' = T.Sskip \/ ts' = T.Sexit ncnt) /\ tk' = tk).
   { destruct o; subst x; fsimpl in TR; monadInv TR; apply match_transl_0_inv in MTR; unpack MTR; subst; auto. }
  destruct H. apply match_Kloop1_inv in MK; unpack MK; subst.
  econstructor; split.
  eapply plus_left.
  destruct H; subst ts'. 2:fconstructor. fconstructor.
  apply star_one. fconstructor. traceEq.
  econstructor; eauto. fconstructor. fconstructor; eauto.
  
(* break loop1*)  
+  fsimpl in TR. monadInv TR. apply match_transl_0_inv in MTR; unpack MTR; subst. apply match_Kloop1_inv in MK; unpack MK; subst.
  econstructor; split.
  eapply plus_left. fconstructor.
  eapply star_left. fconstructor.
  eapply star_left. fconstructor.
  apply star_one. fconstructor.
  reflexivity. reflexivity. traceEq.
  eapply match_states_skip; eauto.

(* skip loop2 *)  
+ fsimpl in TR. monadInv TR. apply match_transl_0_inv in MTR; unpack MTR; subst. apply match_Kloop2_inv in MK; unpack MK; subst.
  econstructor; split.
  apply plus_one. fconstructor.
  econstructor; eauto.
  fsimpl. rewrite TEMP2; simpl. unfold Succ in TEMP3. rewrite TEMP3; simpl. eauto.
  fconstructor.

(* break loop2 *)    
+ fsimpl in TR. monadInv TR. apply match_transl_0_inv in MTR; unpack MTR; subst. apply match_Kloop2_inv in MK; unpack MK; subst. 
  econstructor; split.
  eapply plus_left. fconstructor.
  apply star_one. fconstructor.
  traceEq.
  eapply match_states_skip; eauto.
Qed. FEnd transl_step.

FEnd Cshmgen.

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family Clight.
FInductive stmt : Type :=
| Sbuiltin: option ident -> external_function -> list type -> list expr -> stmt. (* builtin invocation *)

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

Inherit eval_expr.

MetaData eval_exprlist binds eval_Enil, eval_Econs.
Inductive eval_exprlist: genv -> env -> temp_env -> mem -> list expr -> list type -> list val -> Prop :=
| eval_Enil: forall ge e le m,
    eval_exprlist ge e le m nil nil nil
| eval_Econs: forall ge e le m a bl ty tyl v1 v2 vl,
    eval_expr ge e le m a v1 ->
    Cop.sem_cast v1 (typeof a) ty m = Some v2 ->
    eval_exprlist ge e le m bl tyl vl ->
    eval_exprlist ge e le m (a :: bl) (ty :: tyl) (v2 :: vl).
FEnd eval_exprlist.

FDefinition set_opttemp := fun (optid: option ident) (v: val) (le: temp_env) =>
  match optid with
  | None => le
  | Some id => PTree.set id v le
  end.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_builtin: forall ge f optid ef tyargs al k e le m vargs t vres m',
      eval_exprlist ge e le m al tyargs vargs ->
      external_call ef (Genv.to_senv (self__Clight.genv_genv ge)) vargs m t vres m' ->
      step ge (State f (Sbuiltin optid ef tyargs al) k e le m)
         t (State f Sskip k e (set_opttemp optid vres le) m').
  
FEnd Clight.

Family Cfam.

Inherit env.

FDefinition set_optvar := fun (optid: option ident) (v: val) (e: env) =>
  match optid with
  | None => e
  | Some id => PTree.set id v e
  end.

FEnd Cfam.

Family Csharpminor extends Cfam.
FInductive stmt : Type :=
  | Sbuiltin : option ident -> external_function -> list expr -> stmt.

Inherit eval_expr.

MetaData eval_exprlist binds eval_Enil, eval_Econs.
Inductive eval_exprlist: genv -> fenv -> env -> mem -> letenv -> list expr -> list val -> Prop :=
  | eval_Enil: forall ge lenv e le m,
      eval_exprlist ge le e m lenv nil nil
  | eval_Econs: forall ge le e m lenv a1 al v1 vl,
      eval_expr ge le e m lenv a1 v1 -> eval_exprlist ge le e m lenv al vl ->
      eval_exprlist ge le e m lenv (a1 :: al) (v1 :: vl).
FEnd eval_exprlist.

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_builtin: forall ge f lenv optid ef bl k e le m vargs t vres m',
      eval_exprlist ge e le m lenv bl vargs ->
      external_call ef ge vargs m t vres m' ->
      step ge (State f (Sbuiltin optid ef bl) k e le m)
        t (State f Sskip k e (set_optvar optid vres le) m').
        
FEnd Csharpminor.

From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.

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

FInduction transl_find_label.
FProof.
all: intros; fsimpl in TR; try (monadInv TR); simpl; fsimpl.
+ fsimpl; reflexivity.
Qed. FEnd transl_find_label.

FLemma transl_arglist_correct:
  forall (cunit: S.program) prog tprog (LINK : linkorder cunit prog) al tyl vl ge tge e te le m lenv
         (MENV: match_env prog e te),
  match_prog prog tprog ->    
  S.globalenv prog = ge -> Genv.globalenv tprog = tge ->  
  S.eval_exprlist ge e le m al tyl vl ->
  forall tal, transl_arglist cunit.(prog_comp_env) al tyl = OK tal ->
  T.eval_exprlist tge te le m lenv tal vl.
FProofLemma.
  induction 6; intros.
  monadInv H2. constructor.
  monadInv H5. constructor.
  eapply make_cast_correct; eauto. eapply transl_expr_correct; eauto. auto.
Qed. CloseFLemma.

FLemma senv_preserved: forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
FProofLemma.
intros until tge; intros TRANSL A B. rewrite A. rewrite B.
apply (Genv.senv_match TRANSL).
Qed. CloseFLemma.

FInduction transl_step.
FProof.
all: intros until tge; intros TRANSL A B; intros T1 MST; inv MST.
+ fsimpl in TR. monadInv TR. apply match_transl_0_inv in MTR; unpack MTR; subst.
  econstructor; split.
  apply plus_one. fconstructor.
  eapply transl_arglist_correct; eauto.
  eapply external_call_symbols_preserved with (ge1 := (Genv.to_senv (S.genv_genv (S.globalenv prog)))).
  apply (senv_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSL eq_refl eq_refl).  eauto.
  eapply match_states_skip; eauto.
  Unshelve. apply nil.  
Qed. FEnd transl_step.

FEnd Cshmgen.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Trait Clight_Lvalues extends Clight.
FInductive expr : Type :=
| Evar: ident -> type -> expr (* variable *)
| Ederef: expr -> type -> expr (* pointer dereference (unary *)                             
| Eaddrof: expr -> type -> expr. (* address-of operator (&) *)

FRecursion typeof.
Case Evar i t := t.
Case Eaddrof e t := t.
Case Ederef i t := t.
FEnd typeof.

MetaData deref_loc.
Inductive deref_loc (ty: type) (m: mem) (b: block) (ofs: ptrofs) :
                                             bitfield -> val -> Prop :=
  | deref_loc_value: forall chunk v,
      access_mode ty = By_value chunk ->
      Mem.loadv chunk m (Vptr b ofs) = Some v ->
      deref_loc ty m b ofs Full v
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ty m b ofs Full (Vptr b ofs)
  | deref_loc_copy:
      access_mode ty = By_copy ->
      deref_loc ty m b ofs Full (Vptr b ofs)
  | deref_loc_bitfield: forall sz sg pos width v,
      load_bitfield ty sz sg pos width m (Vptr b ofs) v ->
      deref_loc ty m b ofs (Bits sz sg pos width) v.
FEnd deref_loc.

FInductive eval_expr : genv -> env -> temp_env -> mem -> expr -> val -> Prop :=
| eval_Eaddrof: forall ge e le m a ty loc ofs,
   eval_lvalue ge e le m a loc ofs Ctypes.Full ->
   eval_expr ge e le m (Eaddrof a ty) (Vptr loc ofs)
| eval_Elvalue: forall ge e le m a loc ofs bf v,
      eval_lvalue ge e le m a loc ofs bf ->
      deref_loc (typeof a) m loc ofs bf v ->
      eval_expr ge e le m a v             
with eval_lvalue: genv -> env -> temp_env -> mem -> expr -> block -> ptrofs -> bitfield -> Prop :=
  | eval_Evar_local: forall ge e le m id l ty,
      e!id = Some(l, ty) ->
      eval_lvalue ge e le m (Evar id ty) l Ptrofs.zero Ctypes.Full                  
  | eval_Evar_global: forall ge e le m id l ty,
      e!id = None ->
      Genv.find_symbol (self__Clight_Lvalues.genv_genv ge) id = Some l ->
      eval_lvalue ge e le m (Evar id ty) l Ptrofs.zero Ctypes.Full
  | eval_Ederef: forall ge e le m a ty l ofs,
      eval_expr ge e le m a (Vptr l ofs) ->
      eval_lvalue ge e le m (Ederef a ty) l ofs Ctypes.Full.
             
FEnd Clight_Lvalues.

Trait Clight_Sassign extends Clight, Clight_Lvalues.
FInductive stmt : Type :=
| Sassign : expr -> expr -> stmt. (* assignment lvalue = rvalue *)

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

MetaData assign_loc.
Inductive assign_loc (ce: composite_env) (ty: type) (m: mem) (b: block) (ofs: ptrofs):
                                            bitfield -> val -> mem -> Prop :=
  | assign_loc_value: forall v chunk m',
      access_mode ty = By_value chunk ->
      Mem.storev chunk m (Vptr b ofs) v = Some m' ->
      assign_loc ce ty m b ofs Full v m'
  | assign_loc_copy: forall b' ofs' bytes m',
      access_mode ty = By_copy ->
      (sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs')) ->
      (sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs)) ->
      b' <> b \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs' + sizeof ce ty <= Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs + sizeof ce ty <= Ptrofs.unsigned ofs' ->
      Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ce ty) = Some bytes ->
      Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
      assign_loc ce ty m b ofs Full (Vptr b' ofs') m'
  | assign_loc_bitfield: forall sz sg pos width v m' v',
      store_bitfield ty sz sg pos width m (Vptr b ofs) v m' v' ->
      assign_loc ce ty m b ofs (Bits sz sg pos width) v m'.
FEnd assign_loc.

FInductive step : genv -> state -> trace -> state -> Prop :=  
| step_assign: forall ge f a1 a2 k e le m loc ofs bf v2 v m',
      eval_lvalue ge e le m a1 loc ofs bf ->
      eval_expr ge e le m a2 v2 ->
      Cop.sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
      assign_loc (self__Clight_Sassign.genv_cenv ge) (typeof a1) m loc ofs bf v m' ->
      step ge (State f (Sassign a1 a2) k e le m)
        E0 (State f Sskip k e le m').

FEnd Clight_Sassign.

Family Clight extends 
  Clight_Sassign,   
  Clight_Lvalues.
FEnd Clight.

Trait Csharpminor_Eaddrof extends Csharpminor.
FInductive expr : Type :=
| Eaddrof : ident -> expr. (* taking the address of a variable *)

Inherit letenv.

MetaData eval_var_addr.
Inductive eval_var_addr: genv -> fenv -> ident -> block -> Prop :=
  | eval_var_addr_local:
      forall ge e id b sz,
      PTree.get id e = Some (b, sz) ->
      eval_var_addr ge e id b
  | eval_var_addr_global:
      forall ge e id b,
      PTree.get id e = None ->
      Genv.find_symbol ge id = Some b ->
      eval_var_addr ge e id b.
FEnd eval_var_addr.

FInductive eval_expr :  genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Eaddrof: forall ge le e lenv m id b,
      eval_var_addr ge le id b ->
      eval_expr ge le e m lenv (Eaddrof id) (Vptr b Ptrofs.zero).
                
FEnd Csharpminor_Eaddrof.

Trait Csharpminor_Eload extends Csharpminor.
FInductive expr : Type :=
| Eload : memory_chunk -> expr -> expr. (* memory read *)

FInductive eval_expr :  genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Eload: forall ge le e lenv m chunk a v1 v,
      eval_expr ge le e m lenv a v1 ->
      Mem.loadv chunk m v1 = Some v ->
      eval_expr ge le e m lenv (Eload chunk a) v.
  
FEnd Csharpminor_Eload.

Trait Csharpminor_Sstore extends Csharpminor.
FInductive stmt : Type :=
| Sstore : memory_chunk -> expr -> expr -> stmt.

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_store: forall ge f chunk addr a k e le m vaddr v m' lenv,
      eval_expr ge e le m lenv addr vaddr ->
      eval_expr ge e le m lenv a v ->
      Mem.storev chunk m vaddr v = Some m' ->
      step ge (State f (Sstore chunk addr a) k e le m)
        E0 (State f Sskip k e le m').
  
FEnd Csharpminor_Sstore.

Family Csharpminor extends 
  Csharpminor_Sstore, 
  Csharpminor_Eload, 
  Csharpminor_Eaddrof.
FEnd Csharpminor.

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

FInduction make_cmpu_ne_zero_correct.
FProof.
+ apply cheat.
+ apply cheat.  
Qed. FEnd make_cmpu_ne_zero_correct.

FInduction make_cmpu_ne_zero_correct_ptr.
FProof.
+ apply cheat.
+ apply cheat.
Qed. FEnd make_cmpu_ne_zero_correct_ptr.

Inherit match_env.

FLemma match_env_globals:
  forall prog e te id,
  match_env prog e te ->
  e!id = None ->
  te!id = None.
FProofLemma.
  intros. destruct (te!id) as [[b sz] | ] eqn:?; auto.
  exploit me_local_inv; eauto. intros [ty EQ]. congruence.
Qed. CloseFLemma.

FInduction transl_expr_lvalue about S.eval_lvalue
  motive (fun ge (e: S.env) le m a b ofs bf (_ : S.eval_lvalue ge e le m a b ofs bf) =>
    forall prog tprog tge, match_prog prog tprog ->
    S.globalenv prog = ge -> Genv.globalenv tprog = tge ->
    forall (cunit: S.program) (L : linkorder cunit prog) te ta (MENV: match_env prog e te),
    transl_expr a cunit.(prog_comp_env) = OK ta ->
    exists tb, transl_lvalue a cunit.(prog_comp_env) = OK (tb, bf)
               /\ make_load tb (S.typeof a) bf = OK ta).
FProof.
all: unfold transl_expr in *; unfold transl_lvalue in *; unfold snd in *; unfold fst in *.
(* var local *)
+ intros. fsimpl in H2. exists (T.Eaddrof id); auto. do 2 fsimpl. auto.
(* var global *)  
+ intros. fsimpl in H2. exists (T.Eaddrof id); auto. do 2 fsimpl. auto.
(* deref *)  
+ intros. fsimpl in H2. monadInv H2. unfold fst in *. do 2 fsimpl. unfold fst. rewrite EQ. exists x; auto. 
Qed. FEnd transl_expr_lvalue.  

FLemma first_bit_range: forall sz pos width,
  0 <= pos -> 0 < width -> pos + width <= bitsize_carrier sz ->
     0 <= first_bit sz pos width < Int.zwordsize
  /\ 0 <= Int.zwordsize - first_bit sz pos width - width < Int.zwordsize.
FProofLemma.
  intros.
  assert (bitsize_carrier sz <= Int.zwordsize) by (destruct sz; compute; congruence).
  unfold first_bit; destruct Archi.big_endian; lia.
Qed. CloseFLemma.

FLemma int_ltu_true:
  forall x, 0 <= x < Int.zwordsize -> Int.ltu (Int.repr x) Int.iwordsize = true.
FProofLemma.
  intros. unfold Int.ltu. rewrite Int.unsigned_repr_wordsize, Int.unsigned_repr, zlt_true by (generalize Int.wordsize_max_unsigned; lia).
  auto.
Qed. CloseFLemma.

FLemma make_load_correct:
  forall ge addr ty bf code b ofs v e le m lenv,
  make_load addr ty bf = OK code ->
  T.eval_expr ge e le m lenv addr (Vptr b ofs) ->
  S.deref_loc ty m b ofs bf v ->
  T.eval_expr ge e le m lenv code v.
FProofLemma.
  unfold make_load; intros until lenv; intros MKLOAD EVEXP DEREF.
  inv DEREF.
- (* scalar *)
  rewrite H in MKLOAD. inv MKLOAD. apply T.eval_Eload with (Vptr b ofs); auto.
- (* by reference *)
  rewrite H in MKLOAD. inv MKLOAD. auto.
- (* by copy *)
  rewrite H in MKLOAD. inv MKLOAD. auto.
- (* by bitfield *)
  inv H.
  unfold make_extract_bitfield in MKLOAD. unfold bitfield_extract.
  exploit (first_bit_range sz pos width); eauto. lia. intros [A1 A2].
  set (amount1 := Int.repr (Int.zwordsize - first_bit sz pos width - width)) in MKLOAD.
  set (amount2 := Int.repr (Int.zwordsize - width)) in MKLOAD.
  destruct (zle 0 pos && zlt 0 width && zle (pos + width) (bitsize_carrier sz)); inv MKLOAD.
  set (e1 := T.Eload (chunk_for_carrier sz) addr).
  assert (E1: T.eval_expr ge e le m lenv e1 (Vint c)) by (fconstructor; eauto).
  set (e2 := T.Ebinop Oshl e1 (make_intconst amount1)).
  assert (E2: T.eval_expr ge e le m lenv e2 (Vint (Int.shl c amount1))).
  { fconstructor; eauto using make_intconst_correct. cbn.
    unfold amount1 at 1; rewrite int_ltu_true by lia. auto. }
  fconstructor; eauto using make_intconst_correct.
  destruct (Ctypes.intsize_eq sz IBool || Ctypes.signedness_eq sg Unsigned); cbn.
  + unfold amount2 at 1; rewrite int_ltu_true by lia.
    rewrite Int.unsigned_bitfield_extract_by_shifts by lia. auto.
  + unfold amount2 at 1; rewrite int_ltu_true by lia.
    rewrite Int.signed_bitfield_extract_by_shifts by lia. auto.
Qed. CloseFLemma.

FInduction transl_expr_correct about S.eval_expr 
  motive (fun ge (e: S.env) le m a v (_ : S.eval_expr ge e le m a v) =>
      forall prog tprog tge, match_prog prog tprog ->
      S.globalenv prog = ge -> Genv.globalenv tprog = tge ->
      forall (cunit: S.program) (L : linkorder cunit prog) te ta (MENV: match_env prog e te) lenv,
      transl_expr a cunit.(prog_comp_env) = OK ta ->
      T.eval_expr tge te le m lenv ta v)
with transl_expr_lvalue_correct about S.eval_lvalue
  motive (fun ge (e: S.env) le m a b ofs bf (_ : S.eval_lvalue ge e le m a b ofs bf) =>
      forall prog tprog tge, match_prog prog tprog ->
      S.globalenv prog = ge -> Genv.globalenv tprog = tge ->
      forall (cunit: S.program) (L : linkorder cunit prog) te ta bf' (MENV: match_env prog e te) lenv,
      transl_lvalue a cunit.(prog_comp_env) =  OK (ta, bf') ->
      bf = bf' /\ T.eval_expr tge te le m lenv ta (Vptr b ofs)).
FProof.
all: unfold transl_expr in *; unfold fst in *; unfold transl_lvalue in *; unfold snd in *.
(* addrof *)
+ intros. fsimpl in H3. monadInv H3. destruct x0; inv EQ0. unfold snd in *.
  eapply H with (prog:=prog) (tprog:=tprog) (tge:=(Genv.globalenv tprog)) (te:=te) in EQ;
  destruct EQ; eauto.
(* rvalue out of lvalue *)
+ intros. exploit transl_expr_lvalue; eauto. intros [tb [TRLVAL MKLOAD]].
  eapply H in TRLVAL; destruct TRLVAL; eauto.
  eapply make_load_correct; eauto. 
(* var local *)  
+ intros. fsimpl in H2. monadInv H2. exploit (me_local _ _ _ MENV); eauto. intros EQ.
  split; auto. fconstructor. eapply T.eval_var_addr_local. eauto.
(* var global *)  
+ intros. fsimpl in H2. monadInv H2. split; auto. fconstructor. eapply T.eval_var_addr_global.
  eapply match_env_globals; eauto.  
  rewrite (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) H eq_refl eq_refl). auto.
(* deref *)  
+ intros. fsimpl in H3. monadInv H3. split. reflexivity. eapply H; eauto.
Qed. FEnd transl_expr_correct with transl_expr_lvalue_correct.

FInduction transl_find_label.
FProof.
all: intros; fsimpl in TR; try (monadInv TR); simpl; fsimpl.
(* Sassign *)
+ unfold make_store, make_memcpy in EQ3.
  destruct x0.
  destruct (access_mode (S.typeof e)); monadInv EQ3; auto.
  fsimpl. reflexivity.
  fsimpl. reflexivity.
  (* unfold make_store_bitfield in EQ3.*)
  apply cheat.
  (*destruct (zle 0 pos && zlt 0 width && zle (pos + width) (bitsize_carrier sz));
  monadInv EQ3; auto.*)
Qed. FEnd transl_find_label.

FLemma transl_alignof_blockcopy:
  forall (cunit prog: S.program) t sz,
  linkorder cunit prog ->
  sizeof cunit.(prog_comp_env) t = OK sz ->
  sz = Ctypes.sizeof prog.(prog_comp_env) t /\
  alignof_blockcopy cunit.(prog_comp_env) t = alignof_blockcopy prog.(prog_comp_env) t.
FProofLemma.
  intros. destruct H.
  unfold sizeof in H0. destruct (complete_type (prog_comp_env cunit) t) eqn:C; inv H0.
  split.
- symmetry. apply Ctypes.sizeof_stable; auto.
- revert C. induction t; simpl; auto;
  destruct (prog_comp_env cunit)!i as [co|] eqn:X; try discriminate; erewrite H1 by eauto; auto.
Qed. CloseFLemma.

FLemma make_memcpy_correct:
  forall f dst src ty k e le m b ofs v m' s lenv (prog: S.program) (cunit: S.program) (LINK: linkorder cunit prog) ge,
  T.eval_expr ge e le m lenv dst (Vptr b ofs) ->
  T.eval_expr ge e le m lenv src v ->
  S.assign_loc prog.(prog_comp_env) ty m b ofs Full v m' ->
  access_mode ty = By_copy ->
  make_memcpy cunit.(prog_comp_env) dst src ty = OK s ->
  T.step ge (T.State f s k e le m) E0 (T.State f T.Sskip k e le m').
FProofLemma.
  intros. inv H1; try congruence.
  monadInv H3.
  exploit transl_alignof_blockcopy. eexact LINK. eauto. intros [A B]. rewrite A, B.
  change le with (T.set_optvar None Vundef le) at 2.
  fconstructor.
  econstructor. eauto. econstructor. eauto. constructor.
  econstructor; eauto.
  apply alignof_blockcopy_1248.
  apply sizeof_pos.
  apply sizeof_alignof_blockcopy_compat.
Qed. CloseFLemma.

FLemma make_store_bitfield_correct:
  forall f sz sg pos width dst src ty k e le m b ofs v m' lenv ge (prog: S.program) (cunit: S.program) (LINK: linkorder cunit prog) s,
  T.eval_expr ge e le m lenv dst (Vptr b ofs) ->
  T.eval_expr ge e le m lenv src v ->
  S.assign_loc prog.(prog_comp_env) ty m b ofs (Bits sz sg pos width) v m' ->
  make_store_bitfield sz sg pos width dst src = OK s ->
  T.step ge (T.State f s k e le m) E0 (T.State f T.Sskip k e le m').
FProofLemma.
  intros until s; intros DST SRC ASG MK.
  inv ASG. inv H5. unfold make_store_bitfield in MK.
  destruct (zle 0 pos && zlt 0 width && zle (pos + width) (bitsize_carrier sz)); inv MK.
  fconstructor; eauto.
  exploit (first_bit_range sz pos width); eauto. lia. intros [A1 A2].
  rewrite Int.bitfield_insert_alternative by lia.
  set (amount := first_bit sz pos width).
  set (mask := Int.shl (Int.repr (two_p width - 1)) (Int.repr amount)).
  repeat fconstructor; eauto. cbn; fsimpl. eauto. cbn. rewrite int_ltu_true by lia. auto. fsimpl. eauto. cbn. auto. fsimpl. eauto. cbn. eauto. eauto.
Qed. CloseFLemma.

FLemma make_store_correct:
  forall addr ty bf rhs code e le m b ofs v m' f k lenv (prog: S.program) (cunit: S.program) (LINK: linkorder cunit prog) ge,
  make_store cunit.(prog_comp_env) addr ty bf rhs = OK code ->
  T.eval_expr ge e le m lenv addr (Vptr b ofs) ->
  T.eval_expr ge e le m lenv rhs v ->
  S.assign_loc prog.(prog_comp_env) ty m b ofs bf v m' ->
  T.step ge (T.State f code k e le m) E0 (T.State f T.Sskip k e le m').
FProofLemma.
  unfold make_store. intros until ge; intros MKSTORE EV1 EV2 ASSIGN.
  inversion ASSIGN; subst.
- (* nonvolatile scalar *)
  rewrite H in MKSTORE; inv MKSTORE.
  fconstructor; eauto.
- (* by copy *)
  rewrite H in MKSTORE.
  eapply make_memcpy_correct with (b := b) (v := Vptr b' ofs'); eauto.
- (* bitfield *)
  eapply make_store_bitfield_correct; eauto.
Qed. CloseFLemma.

FInduction transl_step.
FProof.
all: intros until tge; intros TRANSL A B; intros T1 MST; inv MST.
(* assign *)
+ fsimpl in TR. monadInv TR.
  assert (SAME: ts' = ts /\ tk' = tk).
  { apply match_transl_0_inv in MTR; unpack MTR. auto. }
  (*  subst ts. unfold make_store, make_memcpy in EQ3.
    destruct x0.
    destruct (access_mode (typeof a1)); monadInv EQ3; auto.
    unfold make_store_bitfield in EQ3.
    destruct (zle 0 pos && zlt 0 width && zle (pos + width) (bitsize_carrier sz));
    monadInv EQ3; auto.
  }*)
  destruct SAME; subst ts' tk'.
  exploit transl_expr_lvalue_correct; eauto. intros [A B]; subst x0.
  econstructor; split.
  apply plus_one. eapply make_store_correct; eauto.
  eapply make_cast_correct; eauto.
  eapply transl_expr_correct; eauto.
  eapply match_states_skip; eauto. Unshelve. apply nil.
Qed. FEnd transl_step.

FEnd Cshmgen.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

Family Clight.
FInductive expr : Type :=
| Efield: expr -> ident -> type -> expr. (* access to a member of a struct or union *)

FRecursion typeof.
Case Efield e i ty := ty.
FEnd typeof.

FInductive eval_expr : genv -> env -> temp_env -> mem -> expr -> val -> Prop := 
with eval_lvalue: genv -> env -> temp_env -> mem -> expr -> block -> ptrofs -> bitfield -> Prop :=
| eval_Efield_struct: forall ge e le m a i ty l ofs id co att delta bf,
      eval_expr ge e le m a (Vptr l ofs) ->
      typeof a = Tstruct id att ->
      (self__Clight.genv_cenv ge)!id = Some co ->
      field_offset (self__Clight.genv_cenv ge) i (co_members co) = OK (delta, bf) ->
      eval_lvalue ge e le m (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf                  
| eval_Efield_union: forall ge e le m a i ty l ofs id co att delta bf,
      eval_expr ge e le m a (Vptr l ofs) ->
      typeof a = Tunion id att ->
      (self__Clight.genv_cenv ge)!id = Some co ->
      union_field_offset (self__Clight.genv_cenv ge) i (co_members co) = OK (delta, bf) ->
      eval_lvalue ge e le m (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf.

FEnd Clight.

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

FLemma union_field_offset_stable:
  forall (cunit prog: S.program) id co f,
  linkorder cunit prog ->
  cunit.(prog_comp_env)!id = Some co ->
  prog.(prog_comp_env)!id = Some co /\
  union_field_offset prog.(prog_comp_env) f (co_members co) = union_field_offset cunit.(prog_comp_env) f (co_members co).
FProofLemma.
  intros.
  assert (C: composite_consistent cunit.(prog_comp_env) co).
  { apply build_composite_env_consistent with cunit.(prog_types) id; auto.
    apply prog_comp_env_eq. }
  destruct H as [_ A].
  split. auto. apply Ctypes.union_field_offset_stable; eauto using co_consistent_complete.
Qed. CloseFLemma.

FLemma field_offset_stable:
  forall (cunit prog: S.program) id co f,
  linkorder cunit prog ->
  cunit.(prog_comp_env)!id = Some co ->
  prog.(prog_comp_env)!id = Some co /\
  field_offset prog.(prog_comp_env) f (co_members co) = field_offset cunit.(prog_comp_env) f (co_members co).
FProofLemma.
  intros.
  assert (C: composite_consistent cunit.(prog_comp_env) co).
  { apply build_composite_env_consistent with cunit.(prog_types) id; auto.
    apply prog_comp_env_eq. }
  destruct H as [_ A].
  split. auto. apply Ctypes.field_offset_stable; eauto using co_consistent_complete.
Qed. CloseFLemma.

FInduction transl_expr_lvalue.
FProof.
all: unfold transl_expr in *; unfold transl_lvalue in *; unfold snd in *; unfold fst in *.
(* field struct *)
+ intros. fsimpl in H2. monadInv H2.
  assert (x1 = bf).
  { rewrite e0 in EQ1. unfold make_field_access in EQ1.
    destruct ((prog_comp_env cunit)!id) as [co'|] eqn:E; try discriminate.
    monadInv EQ1.
    exploit field_offset_stable. eexact L. eauto. instantiate (1 := i). intros [A B].
    simpl in E, EQ0. apply cheat. (* congruence.*) }
  subst x1.
  exists x0; split; auto. fsimpl; rewrite EQ; auto. fsimpl. eauto.

(* field union *)  
+ intros. fsimpl in H2. monadInv H2.
  assert (x1 = bf).
  { rewrite e0 in EQ1. unfold make_field_access in EQ1.
    destruct ((prog_comp_env cunit)!id) as [co'|] eqn:E; try discriminate.
    monadInv EQ1.
    exploit union_field_offset_stable. eexact L. eauto. instantiate (1 := i). intros [A B].
    simpl in E, EQ0. apply cheat. (* congruence.*) }
  subst x1.
  exists x0; split; auto. fsimpl; rewrite EQ; auto. fsimpl. eauto.
Qed. FEnd transl_expr_lvalue.

FInduction transl_expr_correct with transl_expr_lvalue_correct.
FProof.
all: unfold transl_expr in *; unfold fst in *; unfold transl_lvalue in *; unfold snd in *.
(* field struct *)
+ intros. fsimpl in H3. monadInv H3.
  unfold make_field_access in EQ0. rewrite e0 in EQ0.
  destruct (prog_comp_env cunit)!id as [co'|] eqn:CO; try discriminate; monadInv EQ0.
  exploit field_offset_stable. eexact L. eauto. instantiate (1 := i). intros [A B].
  rewrite <- B in EQ1.
  assert (x0 = delta) by (unfold ge in *; simpl in *; congruence).
  assert (bf' = bf) by (unfold ge in *; simpl in *; congruence).
  subst x0 bf'. split; auto.
  destruct Archi.ptr64 eqn:SF.
- eapply T.eval_Ebinop; eauto using make_longconst_correct.
  simpl. rewrite SF. apply f_equal. apply f_equal. apply f_equal. auto with ptrofs.
- eapply T.eval_Ebinop; eauto using make_intconst_correct.
  simpl. rewrite SF. apply f_equal. apply f_equal. apply f_equal. auto with ptrofs.

(* field union *)
+ intros. fsimpl in H3. monadInv H3.
  unfold make_field_access in EQ0. rewrite e0 in EQ0.
  destruct (prog_comp_env cunit)!id as [co'|] eqn:CO; try discriminate; monadInv EQ0.
  exploit union_field_offset_stable. eexact L. eauto. instantiate (1 := i). intros [A B].
  rewrite <- B in EQ1.
  assert (x0 = delta) by (unfold ge in *; simpl in *; congruence).
  assert (bf' = bf) by (unfold ge in *; simpl in *; congruence).
  subst x0 bf'. split; auto.
  destruct Archi.ptr64 eqn:SF.
- eapply T.eval_Ebinop; eauto using make_longconst_correct.
  simpl. rewrite SF. apply f_equal. apply f_equal. apply f_equal. auto with ptrofs.
- eapply T.eval_Ebinop; eauto using make_intconst_correct.
  simpl. rewrite SF. apply f_equal. apply f_equal. apply f_equal. auto with ptrofs.  
Qed. FEnd transl_expr_correct with transl_expr_lvalue_correct.

FEnd Cshmgen.

FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family Clight.
FInductive stmt : Type :=
| Scall: option ident -> expr -> list expr -> stmt. (* function call *)

FInductive cont: Type :=
| Kcall: option ident ->(* where to store result *)
           function ->(* calling function *)
           env ->(* local env of calling function *)
           temp_env ->(* temporary env of calling function *)
           cont -> cont.  

FRecursion call_cont.
Case Kcall a b c d k := (Kcall a b c d k).
FEnd call_cont.
            
FRecursion is_call_cont.
Case Kcall a b c d k := True.
FEnd is_call_cont.

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_call: forall ge f optid a al k e le m tyargs tyres cconv vf vargs fd,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
      eval_expr ge e le m a vf ->
      eval_exprlist ge e le m al tyargs vargs ->
      Genv.find_funct (self__Clight.genv_genv ge) vf = Some fd ->
      type_of_fundef fd = Tfunction tyargs tyres cconv ->
      step ge (State f (Scall optid a al) k e le m)
        E0 (Callstate fd vargs (Kcall optid f e le k) m)
| step_external_function: forall ge ef targs tres cconv vargs k m vres t m',
      external_call ef (Genv.to_senv (self__Clight.genv_genv ge)) vargs m t vres m' ->
      step ge (Callstate (External ef targs tres cconv) vargs k m)
         t (Returnstate vres k m')
| step_returnstate: forall ge v optid f e le k m,
      step ge (Returnstate v (Kcall optid f e le k) m)
        E0 (State f Sskip k e (set_opttemp optid v le) m).        

FEnd Clight.

Family Csharpminor.
FInductive stmt : Type :=
| Scall : option ident -> signature -> expr -> list expr -> stmt.

FInductive cont: Type :=
| Kcall: option ident -> function -> env -> fenv -> cont -> cont.

FRecursion call_cont.
Case Kcall a b c d k := (Kcall a b c d k).
FEnd call_cont.
            
FRecursion is_call_cont.
Case Kcall a b c d k := True.
FEnd is_call_cont.

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_call: forall ge lenv f optid sig a bl k e le m vf vargs fd,
      eval_expr ge e le m lenv a vf ->
      eval_exprlist ge e le m lenv bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      step ge (State f (Scall optid sig a bl) k e le m)
        E0 (Callstate fd vargs (Kcall optid f le e k) m)
| step_external_function: forall ge ef vargs k m t vres m',
      external_call ef (Genv.to_senv ge) vargs m t vres m' ->
      step ge (Callstate (AST.External ef) vargs k m)
         t (Returnstate vres k m')
| step_return: forall ge v optid f e le k m,
      step ge (Returnstate v (Kcall optid f le e k) m)
        E0 (State f Sskip k e (set_optvar optid v le) m).
        
FEnd Csharpminor.

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

(* Ctyping *)
MetaData wt_val binds has_rettype_wt_val, wt_int.
Definition wt_int (n: int) (sz: intsize) (sg: signedness) : Prop :=
  match sz, sg with
  | IBool, _ => n = Int.zero \/ n = Int.one
  | I8, Unsigned => Int.zero_ext 8 n = n
  | I8, Signed => Int.sign_ext 8 n = n
  | I16, Unsigned => Int.zero_ext 16 n = n
  | I16, Signed => Int.sign_ext 16 n = n
  | I32, _ => True
  end.

Inductive wt_val : val -> type -> Prop :=
  | wt_val_int: forall n sz sg a,
      wt_int n sz sg ->
      wt_val (Vint n) (Tint sz sg a)
  | wt_val_ptr_int: forall b ofs sg a,
      Archi.ptr64 = false ->
      wt_val (Vptr b ofs) (Tint I32 sg a)
  | wt_val_long: forall n sg a,
      wt_val (Vlong n) (Tlong sg a)
  | wt_val_ptr_long: forall b ofs sg a,
      Archi.ptr64 = true ->
      wt_val (Vptr b ofs) (Tlong sg a)
  | wt_val_float: forall f a,
      wt_val (Vfloat f) (Tfloat F64 a)
  | wt_val_single: forall f a,
      wt_val (Vsingle f) (Tfloat F32 a)
  | wt_val_pointer: forall b ofs ty a,
      wt_val (Vptr b ofs) (Tpointer ty a)
  | wt_val_int_pointer: forall n ty a,
      Archi.ptr64 = false ->
      wt_val (Vint n) (Tpointer ty a)
  | wt_val_long_pointer: forall n ty a,
      Archi.ptr64 = true ->
      wt_val (Vlong n) (Tpointer ty a)
  | wt_val_array: forall b ofs ty sz a,
      wt_val (Vptr b ofs) (Tarray ty sz a)
  | wt_val_function: forall b ofs tyargs tyres cc,
      wt_val (Vptr b ofs) (Tfunction tyargs tyres cc)
  | wt_val_struct: forall b ofs id a,
      wt_val (Vptr b ofs) (Tstruct id a)
  | wt_val_union: forall b ofs id a,
      wt_val (Vptr b ofs) (Tunion id a)
  | wt_val_undef: forall ty,
      wt_val Vundef ty
  | wt_val_void: forall v,
      wt_val v Tvoid.

Lemma has_rettype_wt_val:
  forall v ty,
  Val.has_rettype v (rettype_of_type ty) -> wt_val v ty.
Proof.
  unfold rettype_of_type, Val.has_rettype; destruct ty; intros.
- destruct v; contradiction || constructor.
- destruct i; [destruct s | destruct s | | ]; destruct v; try contradiction;
  constructor; unfold wt_int; auto.
- destruct v; try contradiction; constructor; auto.
- destruct f; destruct v; try contradiction; constructor.
- destruct v; try contradiction; constructor; auto.
- destruct v; contradiction || constructor.
- destruct v; contradiction || constructor.
- destruct v; contradiction || constructor.
- destruct v; contradiction || constructor.
Qed.
FEnd wt_val.

FInductive match_cont : composite_env -> type -> nat -> nat -> S.cont -> T.cont -> Prop :=
| match_Kcall: forall prog ce tyret nbrk ncnt nbrk' ncnt' f e k id tf te le tk cu,
      linkorder cu prog ->
      transl_function cu.(prog_comp_env) f = OK tf ->
      match_env prog e te ->
      match_cont cu.(prog_comp_env) (S.fn_return f) nbrk' ncnt' k tk ->
      match_cont ce tyret nbrk ncnt
                 (S.Kcall id f e le k)
                 (T.Kcall id tf le te tk)
| match_Kcall_normalize: forall prog tge ce tyret nbrk ncnt nbrk' ncnt' f e k id a tf te le tk cu,
      linkorder cu prog ->
      transl_function cu.(prog_comp_env) f = OK tf ->
      match_env prog e te ->
      match_cont cu.(prog_comp_env) (S.fn_return f) nbrk' ncnt' k tk ->
      (forall v e le m lenv, wt_val v tyret -> le!id = Some v -> T.eval_expr tge e le m lenv a v) ->
      match_cont ce tyret nbrk ncnt
                 (S.Kcall (Some id) f e le k)
                 (T.Kcall (Some id) tf le te (T.Kseq (T.Sassign id a) tk)).

Closing Fact match_cont_Kcall_inv : forall prog tprog ce tyret nbrk ncnt id f e le k tk,
    match_cont ce tyret nbrk ncnt (S.Kcall id f e le k) tk ->
    
    (exists cu tf te nbrk' ncnt' tk',
    tk = (T.Kcall id tf le te tk') /\        
    linkorder cu prog /\
      transl_function cu.(prog_comp_env) f = OK tf /\
      match_env prog e te /\
      match_cont cu.(prog_comp_env) (S.fn_return f) nbrk' ncnt' k tk')

      \/

    (exists cu a tf te nbrk' ncnt' tk' id',
      id = Some id' /\
      tk = (T.Kcall (Some id') tf le te (T.Kseq (T.Sassign id' a) tk')) /\
      linkorder cu prog /\
      transl_function cu.(prog_comp_env) f = OK tf /\
      match_env prog e te /\
      match_cont cu.(prog_comp_env) (S.fn_return f) nbrk' ncnt' k tk' /\
      (forall v e le m lenv, wt_val v tyret -> le!id' = Some v -> T.eval_expr (Genv.globalenv tprog) e le m lenv a v))
by plain { apply cheat }.

FLemma functions_translated:
  forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  forall v f,
    Genv.find_funct ge v = Some f ->
    exists cu tf, Genv.find_funct tge v = Some tf /\ match_fundef cu f tf /\ linkorder cu prog.
FProofLemma.
intros until tge; intros TRANSL A B. rewrite A. rewrite B.
apply (Genv.find_funct_match TRANSL).
Qed. CloseFLemma.   

FInduction match_cont_call_cont.
FProof.
+ intros. do 2 fsimpl. eapply match_Kcall; eauto.
+ intros. do 2 fsimpl. eapply match_Kcall_normalize; eauto.
Qed. FEnd match_cont_call_cont.

FInduction match_cont_is_call_cont.
FProof.
+ intros. do 2 fsimpl. split; auto; eapply match_Kcall; eauto.
+ intros. do 2 fsimpl. split; auto; eapply match_Kcall_normalize; eauto.
Qed. FEnd match_cont_is_call_cont.

FInduction transl_find_label.
FProof.
all: intros; fsimpl in TR; try (monadInv TR); simpl; fsimpl.
(* call *)
+ simpl in TR. destruct (classify_fun (S.typeof e)); monadInv TR.
  unfold make_funcall.
  destruct o; auto; destruct Conventions1.return_value_needs_normalization; auto.
  do 5 fsimpl. reflexivity. do 3 fsimpl. reflexivity. apply cheat.
  fsimpl. reflexivity. fsimpl. reflexivity.  
Qed. FEnd transl_find_label.

FLemma typlist_of_arglist_eq:
  forall ge e le m al tyl vl,
  S.eval_exprlist ge e le m al tyl vl ->
  typlist_of_arglist al tyl = List.map argtype_of_type tyl.
FProofLemma.
  induction 1; simpl.
  auto.
  f_equal; auto.
Qed. CloseFLemma.

From Rocqet Require Import Cop.
FLemma transl_arglist_typed:
  forall ge e le m al tyl vl,
  S.eval_exprlist ge e le m al tyl vl ->
  Val.has_argtype_list vl (List.map argtype_of_type tyl).
FProofLemma.
induction 1; intros.
- simpl. apply cheat.
- simpl. constructor. apply cheat. apply cheat.
(* TODO: reload Cop *)  
(* simpl; constructor; eauto using val_casted_has_argtype, cast_val_is_casted.*)
Qed. CloseFLemma.

FLemma make_normalization_correct:
  forall ge e le m a v t lenv,
  T.eval_expr ge e le m lenv a v ->
  wt_val v t ->
  T.eval_expr ge e le m lenv (make_normalization t a) v.
FProofLemma.
  intros. destruct t; simpl; auto. inv H0.
- destruct i; simpl in H3.
  + destruct s; fconstructor; eauto; simpl; congruence.
  + destruct s; fconstructor; eauto; simpl; congruence.
  + auto.
  + fconstructor; eauto. destruct H3; subst n; reflexivity.
- auto.
- destruct i.
  + destruct s; fconstructor; eauto.
  + destruct s; fconstructor; eauto.
  + auto.
  + fconstructor; eauto.
Qed. CloseFLemma.

FInduction transl_step.
FProof.
all: intros until tge; intros TRANSL A B; intros T1 MST; inv MST.
(* call *)
+ revert TR. fsimpl. case_eq (classify_fun (S.typeof a)); try congruence.
  intros targs tres cc CF TR. monadInv TR.
  exploit functions_translated; eauto. intros (cu' & tfd & FIND & TFD & LINK').
  rewrite e0 in CF. simpl in CF. inv CF.
  set (sg := {| sig_args := typlist_of_arglist al targs;
                sig_res := rettype_of_type tres;
                sig_cc := cc |}) in *.
  assert (SIG: T.funsig tfd = sg).
  { unfold sg; erewrite typlist_of_arglist_eq by eauto.
    eapply transl_fundef_sig1; eauto. rewrite e4; auto. }
  assert (EITHER: tk' = tk /\ ts' = T.Scall optid sg x x0
               \/ exists id, optid = Some id /\
                  tk' = tk /\ ts' = T.Sseq (T.Scall optid sg x x0)
                                         (T.Sassign id (make_normalization tres (T.Evar id)))).
  { unfold make_funcall in MTR.
    destruct optid. destruct Conventions1.return_value_needs_normalization.
    apply match_transl_0_inv in MTR; unpack MTR; subst. right; exists i; auto.    
    apply match_transl_0_inv in MTR; unpack MTR; subst; auto.
    apply match_transl_0_inv in MTR; unpack MTR; subst; auto. }
  destruct EITHER as [(EK & ES) | (id & EI & EK & ES)]; rewrite EK, ES.
  - (* without normalization of return value *)
    econstructor; split.
    apply plus_one. eapply T.step_call; eauto.
    eapply transl_expr_correct with (cunit := cu); eauto.
    eapply transl_arglist_correct with (cunit := cu); eauto.
    econstructor; eauto.
    eapply match_Kcall with (ce := prog_comp_env cu') (cu := cu); eauto.
    fsimpl. exact I.
    eapply transl_arglist_typed; eauto.
  - (* with normalization of return value *)
    subst optid.
    econstructor; split.
    eapply plus_two. apply T.step_seq. eapply T.step_call; eauto.
    eapply transl_expr_correct with (cunit := cu); eauto.
    eapply transl_arglist_correct with (cunit := cu); eauto.
    traceEq.
    econstructor; eauto.
    eapply match_Kcall_normalize with (ce := prog_comp_env cu') (cu := cu); eauto.
    intros. eapply make_normalization_correct; eauto. fconstructor; eauto.
    fsimpl. exact I.
    eapply transl_arglist_typed; eauto.

(* external function *)
+  inv TR.
  exploit match_cont_is_call_cont; eauto. intros [A B].
  econstructor; split.
  apply plus_one. fconstructor.
  eapply external_call_symbols_preserved; eauto. apply (senv_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSL eq_refl eq_refl). 
  eapply match_returnstate with (ce := ce); eauto. Unshelve. apply nil. apply nil. apply (Genv.globalenv tprog).
  (*apply has_rettype_wt_val.
  replace (rettype_of_type tres0) with (sig_res (ef_sig ef)).
  eapply external_call_well_typed_gen; eauto.
  rewrite H5. simpl. simpl in TY. congruence.*)

(* returnstate *)
+ apply (match_cont_Kcall_inv prog tprog) in MK; destruct MK.
  - (* without normalization *)
    unpack H. subst.
    econstructor; split.
    apply plus_one. fconstructor.
    econstructor; eauto. fsimpl. auto. fconstructor. 
  - (* with normalization *)
    unpack H. subst.
    econstructor; split.
    eapply plus_three. fconstructor. fconstructor. fconstructor.
    simpl. eapply TEMP6. apply cheat. (*add WT to return *)  apply PTree.gss.
    traceEq.
    simpl. rewrite PTree.set2. econstructor; eauto. fsimpl; reflexivity. fconstructor.
    Unshelve. apply nil.
Qed. FEnd transl_step.

FEnd Cshmgen.

FEnd Comp_Call.

(* small extension *)
Trait Comp_Switch extends Comp_Loops.

Family Clight.

FInductive stmt : Type := 
| Sswitch : expr -> lbl_stmts -> stmt. (* switch statement *)

FInductive cont: Type :=
| Kswitch: cont -> cont.

FRecursion call_cont.
Case Kswitch k := (call_cont k).
FEnd call_cont.
            
FRecursion is_call_cont.
Case Kswitch k := False.
FEnd is_call_cont.

FRecursion select_switch_default about lbl_stmts motive (fun (_ : lbl_stmts) => lbl_stmts) by _rect.
Case LSnil := LSnil.
Case LScons opt s sl' :=
  (match opt with
   | None => LScons opt s sl'
   | Some i => select_switch_default sl'
  end).
FEnd select_switch_default.

FRecursion select_switch_case about lbl_stmts motive (fun (_ : lbl_stmts) => Z -> option lbl_stmts) by _rect.
Case LSnil := (fun n => None).
Case LScons opt s sl' :=
  (fun n =>
     match opt with
     | None => select_switch_case sl' n
     | Some c => if zeq c n then Some (LScons opt s sl')  else select_switch_case sl' n
     end).
FEnd select_switch_case.

FDefinition select_switch := fun (n: Z) (sl: lbl_stmts) =>
  match select_switch_case sl n with
  | Some sl' => sl'
  | None => select_switch_default sl
  end.

FRecursion seq_of_labeled_statement about lbl_stmts motive (fun (_: lbl_stmts) => stmt) by _rect.
Case LSnil := Sskip.
Case LScons x s sl' := (Sseq s (seq_of_labeled_statement sl')).
FEnd seq_of_labeled_statement.

FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont))
with find_label_ls about lbl_stmts motive (fun (_ : lbl_stmts) => label -> cont -> option (stmt * cont)) by _rect.
Case Sswitch e sl := (fun lbl k => find_label_ls sl lbl (Kswitch k)).

Case LSnil := (fun lbl k => None).
Case LScons x s sl' :=
  (fun lbl k => 
      match find_label s lbl (Kseq (seq_of_labeled_statement sl') k) with
      | Some sk => Some sk
      | None => find_label_ls sl' lbl k
      end).
FEnd find_label with find_label_ls.      

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_switch: forall ge f a sl k e le m v n,
      eval_expr ge e le m a v ->
      Cop.sem_switch_arg v (typeof a) = Some n ->
      step ge (State f (Sswitch a sl) k e le m)
        E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le m)
| step_skip_break_switch: forall ge f x k e le m,
    x = Sskip \/ x = Sbreak ->
    step ge (State f x (Kswitch k) e le m)
      E0 (State f Sskip k e le m)
| step_continue_switch: forall ge f k e le m,
    step ge (State f Scontinue (Kswitch k) e le m)
      E0 (State f Scontinue k e le m).

FEnd Clight.

Family Csharpminor.

FInductive stmt : Type := 
| Sswitch: bool -> expr -> lbl_stmts -> stmt
with lbl_stmts : Type :=
  | LSnil: lbl_stmts
  | LScons: option Z -> stmt -> lbl_stmts -> lbl_stmts.

From Rocqet Require Import Switch.

FRecursion select_switch_default about lbl_stmts motive (fun (_ : lbl_stmts) => lbl_stmts) by _rect.
Case LSnil := LSnil.
Case LScons opt s sl' :=
  (match opt with
   | None => LScons opt s sl'
   | Some i => select_switch_default sl'
  end).
FEnd select_switch_default.

FRecursion select_switch_case about lbl_stmts motive (fun (_ : lbl_stmts) => Z -> option lbl_stmts) by _rect.
Case LSnil := (fun n => None).
Case LScons opt s sl' :=
  (fun n =>
     match opt with
     | None => select_switch_case sl' n
     | Some c => if zeq c n then Some (LScons opt s sl')  else select_switch_case sl' n
     end).
FEnd select_switch_case.

FDefinition select_switch := fun (n: Z) (sl: lbl_stmts) =>
  match select_switch_case sl n with
  | Some sl' => sl'
  | None => select_switch_default sl
  end.

FRecursion seq_of_lbl_stmt about lbl_stmts motive (fun (_: lbl_stmts) => stmt) by _rect.
Case LSnil := Sskip.
Case LScons c s sl' := (Sseq s (seq_of_lbl_stmt sl')).
FEnd seq_of_lbl_stmt.

FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont)) 
  with find_label_ls about lbl_stmts motive (fun (_ : lbl_stmts) => label -> cont -> option (stmt * cont)) by _rect.
Case Sswitch long a sl := 
  (fun lbl k => find_label_ls sl lbl k).

Case LSnil := (fun lbl k => None).
Case LScons x s sl' :=
  (fun lbl k =>
     match find_label s lbl (Kseq (seq_of_lbl_stmt sl') k) with
     | Some sk => Some sk
     | None => find_label_ls sl' lbl k
     end).
FEnd find_label with find_label_ls.
      
FInductive step : genv -> state -> trace -> state -> Prop :=
| step_switch: forall ge f islong a cases k e le m v n lenv,
      eval_expr ge e le m lenv a v ->
      switch_argument islong v n ->
      step ge (State f (Sswitch islong a cases) k e le m)
        E0 (State f (seq_of_lbl_stmt (select_switch n cases)) k e le m).

FEnd Csharpminor.

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

FInductive match_cont: composite_env -> type -> nat -> nat -> S.cont -> T.cont -> Prop :=
| match_Kswitch: forall ce tyret nbrk ncnt k tk,
   match_cont ce tyret nbrk ncnt k tk ->
   match_cont ce tyret 0%nat (Succ ncnt)
              (S.Kswitch k)
              (T.Kblock tk).

Closing Fact match_cont_Kswitch_inv : forall ce tyret nbrk ncnt k tk,
  match_cont ce tyret nbrk ncnt (S.Kswitch k) tk ->
  exists ncnt' nbrk' tk',
    nbrk = 0%nat /\
    ncnt = (Succ ncnt') /\
    tk = (T.Kblock tk') /\
    match_cont ce tyret nbrk' ncnt' k tk'
by plain { apply cheat }.

FInduction match_cont_call_cont.
FProof.
+ intros. do 2 fsimpl. apply H; eauto.
Qed. FEnd match_cont_call_cont.

FInduction match_cont_is_call_cont.
FProof.
+ intros. fsimpl in H0. contradiction.
Qed. FEnd match_cont_is_call_cont.

(* DFL *)
FInduction transl_lbl_stmt_1_part_one about S.lbl_stmts
  motive (fun (sl : S.lbl_stmts) =>
    forall ce tyret nbrk ncnt tsl,            
    transl_lbl_stmt sl ce tyret nbrk ncnt = OK tsl ->
    transl_lbl_stmt (S.select_switch_default sl) ce tyret nbrk ncnt = OK (T.select_switch_default tsl)).
FProof.
+ intros. do 3 fsimpl. inv H. fsimpl. reflexivity.
+ intros. fsimpl in H0.  monadInv H0. do 3 fsimpl. destruct o; eauto.
  (* rewrite EQ; simpl.*)
  apply cheat.
  apply cheat.
Qed. FEnd transl_lbl_stmt_1_part_one.

(* CASE *)
FInduction transl_lbl_stmt_1_part_two about S.lbl_stmts
  motive (fun (sl : S.lbl_stmts) =>
    forall tsl ce tyret nbrk ncnt n,
    transl_lbl_stmt sl ce tyret nbrk ncnt = OK tsl ->
    match S.select_switch_case sl n with
    | None =>
        T.select_switch_case tsl n = None
    | Some sl' =>
        exists tsl',
           T.select_switch_case tsl n = Some tsl'
        /\ transl_lbl_stmt sl' ce tyret nbrk ncnt = OK tsl'
    end).                                    
FProof.
+ apply cheat.
+ apply cheat.  
Qed. FEnd transl_lbl_stmt_1_part_two.
  
FLemma transl_lbl_stmt_1:
  forall ce tyret nbrk ncnt n sl tsl,
  transl_lbl_stmt sl ce tyret nbrk ncnt = OK tsl ->
  transl_lbl_stmt (S.select_switch n sl) ce tyret nbrk ncnt = OK (T.select_switch n tsl).
FProofLemma.
  intros. specialize (transl_lbl_stmt_1_part_two _ _ _ _ _ _ n H). unfold S.select_switch, T.select_switch.
  destruct (S.select_switch_case sl n) as [sl'|].
  intro CASE. destruct CASE as [tsl' [P Q]]. rewrite P, Q. auto.
  intro CASE. rewrite CASE. simple apply (transl_lbl_stmt_1_part_one sl _ _ _ _ _ H).
Qed. CloseFLemma.

FInduction transl_lbl_stmt_2 about S.lbl_stmts motive
  (fun (sl: S.lbl_stmts) =>
    forall ce tyret nbrk ncnt tsl,
    transl_lbl_stmt sl ce tyret nbrk ncnt = OK tsl ->
    transl_stmt (S.seq_of_labeled_statement sl) ce tyret nbrk ncnt = OK (T.seq_of_lbl_stmt tsl)).
FProof.
+ intros. fsimpl in H. monadInv H. do 3 fsimpl. reflexivity.
+ intros. fsimpl in H0. monadInv H0. do 3 fsimpl. rewrite EQ. rewrite (H ce tyret nbrk ncnt _ EQ1). simpl. auto.
Qed. FEnd transl_lbl_stmt_2. 

FInduction transl_find_label about S.stmt motive (fun (s : S.stmt) =>
  forall ce lbl tyret nbrk ncnt k ts tk
  (TR: transl_stmt s ce tyret nbrk ncnt = OK ts)
  (MC: match_cont ce tyret nbrk ncnt k tk),
  match S.find_label s lbl k with
  | None => T.find_label ts lbl tk = None
  | Some (s', k') =>
      exists ts', exists tk', exists nbrk', exists ncnt',
      T.find_label ts lbl tk = Some (ts', tk')
      /\ transl_stmt s' ce tyret nbrk' ncnt' = OK ts'
      /\ match_cont ce tyret nbrk' ncnt' k' tk'
  end)
with transl_find_label_ls about S.lbl_stmts motive (fun (ls : S.lbl_stmts) =>
    forall ce lbl tyret nbrk ncnt k tls tk
       (TR: transl_lbl_stmt ls ce tyret nbrk ncnt = OK tls)
       (MC: match_cont ce tyret nbrk ncnt k tk),
       match S.find_label_ls ls lbl k with
       | None => T.find_label_ls tls lbl tk = None
       | Some (s', k') =>
           exists ts', exists tk', exists nbrk', exists ncnt',
           T.find_label_ls tls lbl tk = Some (ts', tk')
           /\ transl_stmt s' ce tyret nbrk' ncnt' = OK ts'
           /\ match_cont ce tyret nbrk' ncnt' k' tk'
       end).
FProof.
all: intros; fsimpl in TR; try (monadInv TR); simpl; fsimpl.
(* switch *)
+ assert (exists b, ts = T.Sblock (T.Sswitch b x x0)).
  { destruct (classify_switch (S.typeof e)); inv EQ2; econstructor; eauto. }
  destruct H0 as [b EQ3]; rewrite EQ3; do 2 fsimpl. 
  eapply (H ce lbl tyret _ _ (S.Kswitch k)); eauto. fconstructor; eauto.

(* nil *)  
+ fsimpl; reflexivity.
(* cons *)  
+ exploit (H ce lbl tyret nbrk ncnt (S.Kseq (S.seq_of_labeled_statement __i0) k)); eauto.
  fconstructor; eauto. apply transl_lbl_stmt_2; eauto.
  destruct (S.find_label __i lbl (S.Kseq (S.seq_of_labeled_statement __i0) k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].
  apply cheat. apply cheat.
  (*rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H.
  eapply transl_find_label_ls; eauto.*)
Qed. FEnd transl_find_label with transl_find_label_ls.                                                                              

FInduction transl_step.
FProof.
all: intros until tge; intros TRANSL A B; intros T1 MST; inv MST.
(* switch *)
+  fsimpl in TR. monadInv TR.
  assert (E: exists b, ts = T.Sblock (T.Sswitch b x x0) /\ Switch.switch_argument b v n).
  { unfold sem_switch_arg in e1.
    destruct (classify_switch (S.typeof a)); inv EQ2; econstructor; split; eauto;
    destruct v; inv e1; constructor. }
  destruct E as (b & A & B). subst ts.
  exploit transl_expr_correct; eauto. intro EV.
  econstructor; split.
  eapply star_plus_trans. eapply match_transl_step; eauto.
  apply plus_one. fconstructor; eauto. traceEq.
  econstructor; eauto.
  apply transl_lbl_stmt_2. apply transl_lbl_stmt_1. eauto.
  fconstructor.
  fconstructor. Unshelve. apply nil.
  
(* skip or break switch *)  
+ assert ((ts' = T.Sskip \/ ts' = T.Sexit nbrk) /\ tk' = tk). 
  destruct o; subst x; fsimpl in TR; monadInv TR; apply match_transl_0_inv in MTR; unpack MTR; subst; auto.
  destruct H. apply match_cont_Kswitch_inv in MK; unpack MK; subst. 
  econstructor; split.
  apply plus_one. destruct H; subst ts'. 2:fconstructor. fconstructor.
  eapply match_states_skip; eauto. 

(* continue switch *)  
+ fsimpl in TR. monadInv TR. apply match_transl_0_inv in MTR; unpack MTR. apply match_cont_Kswitch_inv in MK; unpack MK; subst. 
  econstructor; split.
  apply plus_one. fconstructor.
  econstructor; eauto. fsimpl. reflexivity. fconstructor.
Qed. FEnd transl_step.

FEnd Cshmgen.

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

Family Cshmgen.
Final Family S := Clight.
Final Family T := Csharpminor.
FEnd Cshmgen.

FEnd Comp.

Require Extraction.
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
