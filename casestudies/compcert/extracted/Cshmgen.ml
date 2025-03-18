open AST
open Archi
open BinInt
open BinNums
open Clight
open Cminor
open Conventions1
open Cop
open Coqlib
open Csharpminor
open Ctypes
open Datatypes
open Errors
open Floats
open Integers
open List0
open Maps
open Zpower
open Errors

(** val make_intconst : Int.int -> expr **)

let make_intconst n =
  Econst (Ointconst n)

(** val make_longconst : Int64.int -> expr **)

let make_longconst f =
  Econst (Olongconst f)

(** val make_floatconst : float -> expr **)

let make_floatconst f =
  Econst (Ofloatconst f)

(** val make_singleconst : float32 -> expr **)

let make_singleconst f =
  Econst (Osingleconst f)

(** val make_ptrofsconst : coq_Z -> expr **)

let make_ptrofsconst n =
  if ptr64 then make_longconst (Int64.repr n) else make_intconst (Int.repr n)

(** val make_singleoffloat : expr -> expr **)

let make_singleoffloat e =
  Eunop (Osingleoffloat, e)

(** val make_floatofsingle : expr -> expr **)

let make_floatofsingle e =
  Eunop (Ofloatofsingle, e)

(** val make_floatofint : expr -> signedness -> expr **)

let make_floatofint e = function
| Signed -> Eunop (Ofloatofint, e)
| Unsigned -> Eunop (Ofloatofintu, e)

(** val make_singleofint : expr -> signedness -> expr **)

let make_singleofint e = function
| Signed -> Eunop (Osingleofint, e)
| Unsigned -> Eunop (Osingleofintu, e)

(** val make_intoffloat : expr -> signedness -> expr **)

let make_intoffloat e = function
| Signed -> Eunop (Ointoffloat, e)
| Unsigned -> Eunop (Ointuoffloat, e)

(** val make_intofsingle : expr -> signedness -> expr **)

let make_intofsingle e = function
| Signed -> Eunop (Ointofsingle, e)
| Unsigned -> Eunop (Ointuofsingle, e)

(** val make_longofint : expr -> signedness -> expr **)

let make_longofint e = function
| Signed -> Eunop (Olongofint, e)
| Unsigned -> Eunop (Olongofintu, e)

(** val make_floatoflong : expr -> signedness -> expr **)

let make_floatoflong e = function
| Signed -> Eunop (Ofloatoflong, e)
| Unsigned -> Eunop (Ofloatoflongu, e)

(** val make_singleoflong : expr -> signedness -> expr **)

let make_singleoflong e = function
| Signed -> Eunop (Osingleoflong, e)
| Unsigned -> Eunop (Osingleoflongu, e)

(** val make_longoffloat : expr -> signedness -> expr **)

let make_longoffloat e = function
| Signed -> Eunop (Olongoffloat, e)
| Unsigned -> Eunop (Olonguoffloat, e)

(** val make_longofsingle : expr -> signedness -> expr **)

let make_longofsingle e = function
| Signed -> Eunop (Olongofsingle, e)
| Unsigned -> Eunop (Olonguofsingle, e)

(** val make_cmpu_ne_zero : expr -> expr **)

let make_cmpu_ne_zero e = match e with
| Ebinop (b, _, _) ->
  (match b with
   | Ocmp _ -> e
   | Ocmpu _ -> e
   | Ocmpf _ -> e
   | Ocmpfs _ -> e
   | Ocmpl _ -> e
   | Ocmplu _ -> e
   | _ -> Ebinop ((Ocmpu Cne), e, (make_intconst Int.zero)))
| _ -> Ebinop ((Ocmpu Cne), e, (make_intconst Int.zero))

(** val sizeof : composite_env -> coq_type -> coq_Z res **)

let sizeof ce t =
  if complete_type ce t
  then OK (sizeof ce t)
  else Error
         (msg
           ('i'::('n'::('c'::('o'::('m'::('p'::('l'::('e'::('t'::('e'::(' '::('t'::('y'::('p'::('e'::[]))))))))))))))))

(** val alignof : composite_env -> coq_type -> coq_Z res **)

let alignof ce t =
  if complete_type ce t
  then OK (alignof ce t)
  else Error
         (msg
           ('i'::('n'::('c'::('o'::('m'::('p'::('l'::('e'::('t'::('e'::(' '::('t'::('y'::('p'::('e'::[]))))))))))))))))

(** val make_cast_int : expr -> intsize -> signedness -> expr **)

let make_cast_int e sz si =
  match sz with
  | I8 ->
    (match si with
     | Signed -> Eunop (Ocast8signed, e)
     | Unsigned -> Eunop (Ocast8unsigned, e))
  | I16 ->
    (match si with
     | Signed -> Eunop (Ocast16signed, e)
     | Unsigned -> Eunop (Ocast16unsigned, e))
  | I32 -> e
  | IBool -> make_cmpu_ne_zero e

(** val make_cast : coq_type -> coq_type -> expr -> expr res **)

let make_cast from to0 e =
  match classify_cast from to0 with
  | Coq_cast_case_i2i (sz2, si2) -> OK (make_cast_int e sz2 si2)
  | Coq_cast_case_f2s -> OK (make_singleoffloat e)
  | Coq_cast_case_s2f -> OK (make_floatofsingle e)
  | Coq_cast_case_i2f si1 -> OK (make_floatofint e si1)
  | Coq_cast_case_i2s si1 -> OK (make_singleofint e si1)
  | Coq_cast_case_f2i (sz2, si2) ->
    OK (make_cast_int (make_intoffloat e si2) sz2 si2)
  | Coq_cast_case_s2i (sz2, si2) ->
    OK (make_cast_int (make_intofsingle e si2) sz2 si2)
  | Coq_cast_case_i2l si1 -> OK (make_longofint e si1)
  | Coq_cast_case_l2i (sz2, si2) ->
    OK (make_cast_int (Eunop (Ointoflong, e)) sz2 si2)
  | Coq_cast_case_l2f si1 -> OK (make_floatoflong e si1)
  | Coq_cast_case_l2s si1 -> OK (make_singleoflong e si1)
  | Coq_cast_case_f2l si2 -> OK (make_longoffloat e si2)
  | Coq_cast_case_s2l si2 -> OK (make_longofsingle e si2)
  | Coq_cast_case_i2bool -> OK (make_cmpu_ne_zero e)
  | Coq_cast_case_l2bool ->
    OK (Ebinop ((Ocmplu Cne), e, (make_longconst Int64.zero)))
  | Coq_cast_case_f2bool ->
    OK (Ebinop ((Ocmpf Cne), e, (make_floatconst Float.zero)))
  | Coq_cast_case_s2bool ->
    OK (Ebinop ((Ocmpfs Cne), e, (make_singleconst Float32.zero)))
  | Coq_cast_case_default ->
    Error
      (msg
        ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('c'::('a'::('s'::('t'::[]))))))))))))))))))
  | _ -> OK e

(** val make_boolean : expr -> coq_type -> expr **)

let make_boolean e ty =
  match classify_bool ty with
  | Coq_bool_case_i -> make_cmpu_ne_zero e
  | Coq_bool_case_l -> Ebinop ((Ocmplu Cne), e, (make_longconst Int64.zero))
  | Coq_bool_case_f -> Ebinop ((Ocmpf Cne), e, (make_floatconst Float.zero))
  | Coq_bool_case_s ->
    Ebinop ((Ocmpfs Cne), e, (make_singleconst Float32.zero))
  | Coq_bool_default -> e

(** val make_notbool : expr -> coq_type -> expr res **)

let make_notbool e ty =
  match classify_bool ty with
  | Coq_bool_case_i -> OK (Ebinop ((Ocmpu Ceq), e, (make_intconst Int.zero)))
  | Coq_bool_case_l ->
    OK (Ebinop ((Ocmplu Ceq), e, (make_longconst Int64.zero)))
  | Coq_bool_case_f ->
    OK (Ebinop ((Ocmpf Ceq), e, (make_floatconst Float.zero)))
  | Coq_bool_case_s ->
    OK (Ebinop ((Ocmpfs Ceq), e, (make_singleconst Float32.zero)))
  | Coq_bool_default ->
    Error
      (msg
        ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('n'::('o'::('t'::('b'::('o'::('o'::('l'::[])))))))))))))))))))))

(** val make_neg : expr -> coq_type -> expr res **)

let make_neg e ty =
  match classify_neg ty with
  | Coq_neg_case_i _ -> OK (Eunop (Onegint, e))
  | Coq_neg_case_f -> OK (Eunop (Onegf, e))
  | Coq_neg_case_s -> OK (Eunop (Onegfs, e))
  | Coq_neg_case_l _ -> OK (Eunop (Onegl, e))
  | Coq_neg_default ->
    Error
      (msg
        ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('n'::('e'::('g'::[])))))))))))))))))

(** val make_absfloat : expr -> coq_type -> expr res **)

let make_absfloat e ty =
  match classify_neg ty with
  | Coq_neg_case_i sg -> OK (Eunop (Oabsf, (make_floatofint e sg)))
  | Coq_neg_case_f -> OK (Eunop (Oabsf, e))
  | Coq_neg_case_s -> OK (Eunop (Oabsf, (make_floatofsingle e)))
  | Coq_neg_case_l sg -> OK (Eunop (Oabsf, (make_floatoflong e sg)))
  | Coq_neg_default ->
    Error
      (msg
        ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('a'::('b'::('s'::('f'::('l'::('o'::('a'::('t'::[]))))))))))))))))))))))

(** val make_notint : expr -> coq_type -> expr res **)

let make_notint e ty =
  match classify_notint ty with
  | Coq_notint_case_i _ -> OK (Eunop (Cminor.Onotint, e))
  | Coq_notint_case_l _ -> OK (Eunop (Onotl, e))
  | Coq_notint_default ->
    Error
      (msg
        ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('n'::('o'::('t'::('i'::('n'::('t'::[]))))))))))))))))))))

(** val make_binarith :
    binary_operation -> binary_operation -> binary_operation ->
    binary_operation -> binary_operation -> binary_operation -> expr ->
    coq_type -> expr -> coq_type -> expr res **)

let make_binarith iop iopu fop sop lop lopu e1 ty1 e2 ty2 =
  let c = classify_binarith ty1 ty2 in
  let ty = binarith_type c in
  (match make_cast ty1 ty e1 with
   | OK x ->
     (match make_cast ty2 ty e2 with
      | OK x0 ->
        (match c with
         | Coq_bin_case_i s ->
           (match s with
            | Signed -> OK (Ebinop (iop, x, x0))
            | Unsigned -> OK (Ebinop (iopu, x, x0)))
         | Coq_bin_case_l s ->
           (match s with
            | Signed -> OK (Ebinop (lop, x, x0))
            | Unsigned -> OK (Ebinop (lopu, x, x0)))
         | Coq_bin_case_f -> OK (Ebinop (fop, x, x0))
         | Coq_bin_case_s -> OK (Ebinop (sop, x, x0))
         | Coq_bin_default ->
           Error
             (msg
               ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('b'::('i'::('n'::('a'::('r'::('i'::('t'::('h'::[])))))))))))))))))))))))
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)

(** val make_add_ptr_int :
    composite_env -> coq_type -> signedness -> expr -> expr -> expr res **)

let make_add_ptr_int ce ty si e1 e2 =
  match sizeof ce ty with
  | OK x ->
    if ptr64
    then let n = make_longconst (Int64.repr x) in
         OK (Ebinop (Oaddl, e1, (Ebinop (Omull, n, (make_longofint e2 si)))))
    else let n = make_intconst (Int.repr x) in
         OK (Ebinop (Cminor.Oadd, e1, (Ebinop (Cminor.Omul, n, e2))))
  | Error msg0 -> Error msg0

(** val make_add_ptr_long :
    composite_env -> coq_type -> expr -> expr -> expr res **)

let make_add_ptr_long ce ty e1 e2 =
  match sizeof ce ty with
  | OK x ->
    if ptr64
    then let n = make_longconst (Int64.repr x) in
         OK (Ebinop (Oaddl, e1, (Ebinop (Omull, n, e2))))
    else let n = make_intconst (Int.repr x) in
         OK (Ebinop (Cminor.Oadd, e1, (Ebinop (Cminor.Omul, n, (Eunop
         (Ointoflong, e2))))))
  | Error msg0 -> Error msg0

(** val make_add :
    composite_env -> expr -> coq_type -> expr -> coq_type -> expr res **)

let make_add ce e1 ty1 e2 ty2 =
  match classify_add ty1 ty2 with
  | Coq_add_case_pi (ty, si) -> make_add_ptr_int ce ty si e1 e2
  | Coq_add_case_pl ty -> make_add_ptr_long ce ty e1 e2
  | Coq_add_case_ip (si, ty) -> make_add_ptr_int ce ty si e2 e1
  | Coq_add_case_lp ty -> make_add_ptr_long ce ty e2 e1
  | Coq_add_default ->
    make_binarith Cminor.Oadd Cminor.Oadd Oaddf Oaddfs Oaddl Oaddl e1 ty1 e2
      ty2

(** val make_sub :
    composite_env -> expr -> coq_type -> expr -> coq_type -> expr res **)

let make_sub ce e1 ty1 e2 ty2 =
  match classify_sub ty1 ty2 with
  | Coq_sub_case_pi (ty, si) ->
    (match sizeof ce ty with
     | OK x ->
       if ptr64
       then let n = make_longconst (Int64.repr x) in
            OK (Ebinop (Osubl, e1, (Ebinop (Omull, n,
            (make_longofint e2 si)))))
       else let n = make_intconst (Int.repr x) in
            OK (Ebinop (Cminor.Osub, e1, (Ebinop (Cminor.Omul, n, e2))))
     | Error msg0 -> Error msg0)
  | Coq_sub_case_pp ty ->
    (match sizeof ce ty with
     | OK x ->
       if ptr64
       then let n = make_longconst (Int64.repr x) in
            OK (Ebinop (Odivl, (Ebinop (Osubl, e1, e2)), n))
       else let n = make_intconst (Int.repr x) in
            OK (Ebinop (Cminor.Odiv, (Ebinop (Cminor.Osub, e1, e2)), n))
     | Error msg0 -> Error msg0)
  | Coq_sub_case_pl ty ->
    (match sizeof ce ty with
     | OK x ->
       if ptr64
       then let n = make_longconst (Int64.repr x) in
            OK (Ebinop (Osubl, e1, (Ebinop (Omull, n, e2))))
       else let n = make_intconst (Int.repr x) in
            OK (Ebinop (Cminor.Osub, e1, (Ebinop (Cminor.Omul, n, (Eunop
            (Ointoflong, e2))))))
     | Error msg0 -> Error msg0)
  | Coq_sub_default ->
    make_binarith Cminor.Osub Cminor.Osub Osubf Osubfs Osubl Osubl e1 ty1 e2
      ty2

(** val make_mul : expr -> coq_type -> expr -> coq_type -> expr res **)

let make_mul e1 ty1 e2 ty2 =
  make_binarith Cminor.Omul Cminor.Omul Omulf Omulfs Omull Omull e1 ty1 e2 ty2

(** val make_div : expr -> coq_type -> expr -> coq_type -> expr res **)

let make_div e1 ty1 e2 ty2 =
  make_binarith Cminor.Odiv Odivu Odivf Odivfs Odivl Odivlu e1 ty1 e2 ty2

(** val make_binarith_int :
    binary_operation -> binary_operation -> binary_operation ->
    binary_operation -> expr -> coq_type -> expr -> coq_type -> expr res **)

let make_binarith_int iop iopu lop lopu e1 ty1 e2 ty2 =
  let c = classify_binarith ty1 ty2 in
  let ty = binarith_type c in
  (match make_cast ty1 ty e1 with
   | OK x ->
     (match make_cast ty2 ty e2 with
      | OK x0 ->
        (match c with
         | Coq_bin_case_i s ->
           (match s with
            | Signed -> OK (Ebinop (iop, x, x0))
            | Unsigned -> OK (Ebinop (iopu, x, x0)))
         | Coq_bin_case_l s ->
           (match s with
            | Signed -> OK (Ebinop (lop, x, x0))
            | Unsigned -> OK (Ebinop (lopu, x, x0)))
         | _ ->
           Error
             (msg
               ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('b'::('i'::('n'::('a'::('r'::('i'::('t'::('h'::('_'::('i'::('n'::('t'::[])))))))))))))))))))))))))))
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)

(** val make_mod : expr -> coq_type -> expr -> coq_type -> expr res **)

let make_mod e1 ty1 e2 ty2 =
  make_binarith_int Cminor.Omod Omodu Omodl Omodlu e1 ty1 e2 ty2

(** val make_and : expr -> coq_type -> expr -> coq_type -> expr res **)

let make_and e1 ty1 e2 ty2 =
  make_binarith_int Cminor.Oand Cminor.Oand Oandl Oandl e1 ty1 e2 ty2

(** val make_or : expr -> coq_type -> expr -> coq_type -> expr res **)

let make_or e1 ty1 e2 ty2 =
  make_binarith_int Cminor.Oor Cminor.Oor Oorl Oorl e1 ty1 e2 ty2

(** val make_xor : expr -> coq_type -> expr -> coq_type -> expr res **)

let make_xor e1 ty1 e2 ty2 =
  make_binarith_int Cminor.Oxor Cminor.Oxor Oxorl Oxorl e1 ty1 e2 ty2

(** val make_shl : expr -> coq_type -> expr -> coq_type -> expr res **)

let make_shl e1 ty1 e2 ty2 =
  match classify_shift ty1 ty2 with
  | Coq_shift_case_ii _ -> OK (Ebinop (Cminor.Oshl, e1, e2))
  | Coq_shift_case_ll _ -> OK (Ebinop (Oshll, e1, (Eunop (Ointoflong, e2))))
  | Coq_shift_case_il _ ->
    OK (Ebinop (Cminor.Oshl, e1, (Eunop (Ointoflong, e2))))
  | Coq_shift_case_li _ -> OK (Ebinop (Oshll, e1, e2))
  | Coq_shift_default ->
    Error
      (msg
        ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('s'::('h'::('l'::[])))))))))))))))))

(** val make_shr : expr -> coq_type -> expr -> coq_type -> expr res **)

let make_shr e1 ty1 e2 ty2 =
  match classify_shift ty1 ty2 with
  | Coq_shift_case_ii s ->
    (match s with
     | Signed -> OK (Ebinop (Cminor.Oshr, e1, e2))
     | Unsigned -> OK (Ebinop (Oshru, e1, e2)))
  | Coq_shift_case_ll s ->
    (match s with
     | Signed -> OK (Ebinop (Oshrl, e1, (Eunop (Ointoflong, e2))))
     | Unsigned -> OK (Ebinop (Oshrlu, e1, (Eunop (Ointoflong, e2)))))
  | Coq_shift_case_il s ->
    (match s with
     | Signed -> OK (Ebinop (Cminor.Oshr, e1, (Eunop (Ointoflong, e2))))
     | Unsigned -> OK (Ebinop (Oshru, e1, (Eunop (Ointoflong, e2)))))
  | Coq_shift_case_li s ->
    (match s with
     | Signed -> OK (Ebinop (Oshrl, e1, e2))
     | Unsigned -> OK (Ebinop (Oshrlu, e1, e2)))
  | Coq_shift_default ->
    Error
      (msg
        ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('s'::('h'::('r'::[])))))))))))))))))

(** val make_cmp_ptr : comparison -> expr -> expr -> expr **)

let make_cmp_ptr c e1 e2 =
  Ebinop ((if ptr64 then Ocmplu c else Ocmpu c), e1, e2)

(** val make_cmp :
    comparison -> expr -> coq_type -> expr -> coq_type -> expr res **)

let make_cmp c e1 ty1 e2 ty2 =
  match classify_cmp ty1 ty2 with
  | Coq_cmp_case_pp -> OK (make_cmp_ptr c e1 e2)
  | Coq_cmp_case_pi si ->
    OK (make_cmp_ptr c e1 (if ptr64 then make_longofint e2 si else e2))
  | Coq_cmp_case_ip si ->
    OK (make_cmp_ptr c (if ptr64 then make_longofint e1 si else e1) e2)
  | Coq_cmp_case_pl ->
    OK (make_cmp_ptr c e1 (if ptr64 then e2 else Eunop (Ointoflong, e2)))
  | Coq_cmp_case_lp ->
    OK (make_cmp_ptr c (if ptr64 then e1 else Eunop (Ointoflong, e1)) e2)
  | Coq_cmp_default ->
    make_binarith (Ocmp c) (Ocmpu c) (Ocmpf c) (Ocmpfs c) (Ocmpl c) (Ocmplu
      c) e1 ty1 e2 ty2

(** val make_extract_bitfield :
    intsize -> signedness -> coq_Z -> coq_Z -> expr -> expr res **)

let make_extract_bitfield sz sg pos width addr =
  if (&&) ((&&) ((fun x -> x) (zle Z0 pos)) ((fun x -> x) (zlt Z0 width)))
       ((fun x -> x) (zle (Z.add pos width) (bitsize_carrier sz)))
  then let amount1 =
         Int.repr (Z.sub (Z.sub Int.zwordsize (first_bit sz pos width)) width)
       in
       let amount2 = Int.repr (Z.sub Int.zwordsize width) in
       let e1 = Eload ((chunk_for_carrier sz), addr) in
       let e2 = Ebinop (Cminor.Oshl, e1, (make_intconst amount1)) in
       let e3 = Ebinop
         ((if (||) ((fun x -> x) (intsize_eq sz IBool))
                ((fun x -> x) (signedness_eq sg Unsigned))
           then Oshru
           else Cminor.Oshr), e2, (make_intconst amount2))
       in
       OK e3
  else Error
         (msg
           ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('e'::('x'::('t'::('r'::('a'::('c'::('t'::('_'::('b'::('i'::('t'::('f'::('i'::('e'::('l'::('d'::[])))))))))))))))))))))))))

(** val make_load : expr -> coq_type -> bitfield -> expr res **)

let make_load addr ty_res = function
| Full ->
  (match access_mode ty_res with
   | By_value chunk -> OK (Eload (chunk, addr))
   | By_nothing ->
     Error
       (msg
         ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('l'::('o'::('a'::('d'::[]))))))))))))))))))
   | _ -> OK addr)
| Bits (sz, sg, pos, width) -> make_extract_bitfield sz sg pos width addr

(** val make_store_bitfield :
    intsize -> signedness -> coq_Z -> coq_Z -> expr -> expr -> stmt res **)

let make_store_bitfield sz _ pos width addr val0 =
  if (&&) ((&&) ((fun x -> x) (zle Z0 pos)) ((fun x -> x) (zlt Z0 width)))
       ((fun x -> x) (zle (Z.add pos width) (bitsize_carrier sz)))
  then let amount = first_bit sz pos width in
       let mask =
         Int.shl (Int.repr (Z.sub (two_p width) (Zpos Coq_xH)))
           (Int.repr amount)
       in
       let e1 = Eload ((chunk_for_carrier sz), addr) in
       let e2 = Ebinop (Cminor.Oshl, val0, (make_intconst (Int.repr amount)))
       in
       let e3 = Ebinop (Cminor.Oor, (Ebinop (Cminor.Oand, e2,
         (make_intconst mask))), (Ebinop (Cminor.Oand, e1,
         (make_intconst (Int.not mask)))))
       in
       OK (Sstore ((chunk_for_carrier sz), addr, e3))
  else Error
         (msg
           ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('s'::('t'::('o'::('r'::('e'::('_'::('b'::('i'::('t'::('f'::('i'::('e'::('l'::('d'::[]))))))))))))))))))))))))))))

(** val make_memcpy :
    composite_env -> expr -> expr -> coq_type -> stmt res **)

let make_memcpy ce dst src ty =
  match sizeof ce ty with
  | OK x ->
    OK (Sbuiltin (None, (EF_memcpy (x, (alignof_blockcopy ce ty))),
      (dst :: (src :: []))))
  | Error msg0 -> Error msg0

(** val make_store :
    composite_env -> expr -> coq_type -> bitfield -> expr -> stmt res **)

let make_store ce addr ty bf rhs =
  match bf with
  | Full ->
    (match access_mode ty with
     | By_value chunk -> OK (Sstore (chunk, addr, rhs))
     | By_copy -> make_memcpy ce addr rhs ty
     | _ ->
       Error
         (msg
           ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('s'::('t'::('o'::('r'::('e'::[]))))))))))))))))))))
  | Bits (sz, sg, pos, width) -> make_store_bitfield sz sg pos width addr rhs

(** val transl_unop : Cop.unary_operation -> expr -> coq_type -> expr res **)

let transl_unop op a ta =
  match op with
  | Onotbool -> make_notbool a ta
  | Onotint -> make_notint a ta
  | Oneg -> make_neg a ta
  | Oabsfloat -> make_absfloat a ta

(** val transl_binop :
    composite_env -> Cop.binary_operation -> expr -> coq_type -> expr ->
    coq_type -> expr res **)

let transl_binop ce op a ta b tb =
  match op with
  | Oadd -> make_add ce a ta b tb
  | Osub -> make_sub ce a ta b tb
  | Omul -> make_mul a ta b tb
  | Odiv -> make_div a ta b tb
  | Omod -> make_mod a ta b tb
  | Oand -> make_and a ta b tb
  | Oor -> make_or a ta b tb
  | Oxor -> make_xor a ta b tb
  | Oshl -> make_shl a ta b tb
  | Oshr -> make_shr a ta b tb
  | Oeq -> make_cmp Ceq a ta b tb
  | One -> make_cmp Cne a ta b tb
  | Olt -> make_cmp Clt a ta b tb
  | Ogt -> make_cmp Cgt a ta b tb
  | Ole -> make_cmp Cle a ta b tb
  | Oge -> make_cmp Cge a ta b tb

(** val make_field_access :
    composite_env -> coq_type -> ident -> expr -> (expr * bitfield) res **)

let make_field_access ce ty f a =
  match match ty with
        | Tstruct (id, _) ->
          (match PTree.get id ce with
           | Some co -> field_offset ce f co.co_members
           | None ->
             Error ((MSG
               ('U'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::(' '::('s'::('t'::('r'::('u'::('c'::('t'::(' '::[])))))))))))))))))) :: ((CTX
               id) :: [])))
        | Tunion (id, _) ->
          (match PTree.get id ce with
           | Some co -> union_field_offset ce f co.co_members
           | None ->
             Error ((MSG
               ('U'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::(' '::('u'::('n'::('i'::('o'::('n'::(' '::[]))))))))))))))))) :: ((CTX
               id) :: [])))
        | _ ->
          Error
            (msg
              ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('f'::('i'::('e'::('l'::('d'::('_'::('a'::('c'::('c'::('e'::('s'::('s'::[])))))))))))))))))))))))))) with
  | OK p ->
    let (x, y) = p in
    let a' =
      if ptr64
      then Ebinop (Oaddl, a, (make_longconst (Int64.repr x)))
      else Ebinop (Cminor.Oadd, a, (make_intconst (Int.repr x)))
    in
    OK (a', y)
  | Error msg0 -> Error msg0

(** val transl_expr : composite_env -> Clight.expr -> expr res **)

let rec transl_expr ce = function
| Econst_int (n, _) -> OK (make_intconst n)
| Econst_float (n, _) -> OK (make_floatconst n)
| Econst_single (n, _) -> OK (make_singleconst n)
| Econst_long (n, _) -> OK (make_longconst n)
| Clight.Evar (id, ty) -> make_load (Eaddrof id) ty Full
| Etempvar (id, _) -> OK (Evar id)
| Ederef (b, ty) ->
  (match transl_expr ce b with
   | OK x -> make_load x ty Full
   | Error msg0 -> Error msg0)
| Clight.Eaddrof (b, _) ->
  (match transl_lvalue ce b with
   | OK p ->
     let (x, y) = p in
     (match y with
      | Full -> OK x
      | Bits (_, _, _, _) ->
        Error
          (msg
            ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('e'::('x'::('p'::('r'::(':'::(' '::('a'::('d'::('d'::('r'::('o'::('f'::(' '::('b'::('i'::('t'::('f'::('i'::('e'::('l'::('d'::[]))))))))))))))))))))))))))))))))))))))
   | Error msg0 -> Error msg0)
| Clight.Eunop (op, b, _) ->
  (match transl_expr ce b with
   | OK x -> transl_unop op x (typeof b)
   | Error msg0 -> Error msg0)
| Clight.Ebinop (op, b, c, _) ->
  (match transl_expr ce b with
   | OK x ->
     (match transl_expr ce c with
      | OK x0 -> transl_binop ce op x (typeof b) x0 (typeof c)
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)
| Ecast (b, ty) ->
  (match transl_expr ce b with
   | OK x -> make_cast (typeof b) ty x
   | Error msg0 -> Error msg0)
| Efield (b, i, ty) ->
  (match transl_expr ce b with
   | OK x ->
     (match make_field_access ce (typeof b) i x with
      | OK p -> let (x0, y) = p in make_load x0 ty y
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)
| Esizeof (ty', _) ->
  (match sizeof ce ty' with
   | OK x -> OK (make_ptrofsconst x)
   | Error msg0 -> Error msg0)
| Ealignof (ty', _) ->
  (match alignof ce ty' with
   | OK x -> OK (make_ptrofsconst x)
   | Error msg0 -> Error msg0)

(** val transl_lvalue :
    composite_env -> Clight.expr -> (expr * bitfield) res **)

and transl_lvalue ce = function
| Clight.Evar (id, _) -> OK ((Eaddrof id), Full)
| Ederef (b, _) ->
  (match transl_expr ce b with
   | OK x -> OK (x, Full)
   | Error msg0 -> Error msg0)
| Efield (b, i, _) ->
  (match transl_expr ce b with
   | OK x -> make_field_access ce (typeof b) i x
   | Error msg0 -> Error msg0)
| _ ->
  Error
    (msg
      ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('l'::('v'::('a'::('l'::('u'::('e'::[]))))))))))))))))))))))

(** val transl_arglist :
    composite_env -> Clight.expr list -> coq_type list -> expr list res **)

let rec transl_arglist ce al tyl =
  match al with
  | [] ->
    (match tyl with
     | [] -> OK []
     | _ :: _ ->
       Error
         (msg
           ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('a'::('r'::('g'::('l'::('i'::('s'::('t'::(':'::(' '::('a'::('r'::('i'::('t'::('y'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::[]))))))))))))))))))))))))))))))))))))))))
  | a1 :: a2 ->
    (match tyl with
     | [] ->
       (match transl_expr ce a1 with
        | OK x ->
          (match make_cast (typeof a1)
                   (default_argument_conversion (typeof a1)) x with
           | OK x0 ->
             (match transl_arglist ce a2 [] with
              | OK x1 -> OK (x0 :: x1)
              | Error msg0 -> Error msg0)
           | Error msg0 -> Error msg0)
        | Error msg0 -> Error msg0)
     | ty1 :: ty2 ->
       (match transl_expr ce a1 with
        | OK x ->
          (match make_cast (typeof a1) ty1 x with
           | OK x0 ->
             (match transl_arglist ce a2 ty2 with
              | OK x1 -> OK (x0 :: x1)
              | Error msg0 -> Error msg0)
           | Error msg0 -> Error msg0)
        | Error msg0 -> Error msg0))

(** val typlist_of_arglist :
    Clight.expr list -> coq_type list -> xtype list **)

let rec typlist_of_arglist al tyl =
  match al with
  | [] -> []
  | a1 :: a2 ->
    (match tyl with
     | [] ->
       (argtype_of_type (default_argument_conversion (typeof a1))) :: 
         (typlist_of_arglist a2 [])
     | ty1 :: ty2 -> (argtype_of_type ty1) :: (typlist_of_arglist a2 ty2))

(** val make_normalization : coq_type -> expr -> expr **)

let make_normalization t a =
  match t with
  | Tint (i, s, _) ->
    (match i with
     | I8 ->
       (match s with
        | Signed -> Eunop (Ocast8signed, a)
        | Unsigned -> Eunop (Ocast8unsigned, a))
     | I16 ->
       (match s with
        | Signed -> Eunop (Ocast16signed, a)
        | Unsigned -> Eunop (Ocast16unsigned, a))
     | I32 -> a
     | IBool -> Eunop (Ocast8unsigned, a))
  | _ -> a

(** val make_funcall :
    ident option -> coq_type -> signature -> expr -> expr list -> stmt **)

let make_funcall x tres sg fn args =
  match x with
  | Some id ->
    if return_value_needs_normalization sg.sig_res
    then Sseq ((Scall (x, sg, fn, args)), (Sset (id,
           (make_normalization tres (Evar id)))))
    else Scall (x, sg, fn, args)
  | None -> Scall (x, sg, fn, args)

(** val transl_statement :
    composite_env -> coq_type -> nat -> nat -> statement -> stmt res **)


module T = Csharpminor


let transl_lbl_stmt_transl_stmtSskip _ _ _ _ = OK T.Sskip 

let transl_lbl_stmt_transl_stmtSset x b ce _ _ _ =
    bind (transl_expr ce b) (fun tb -> OK (T.Sset (x, tb)))

let transl_lbl_stmt_transl_stmtSseq _ transl_stmt_s1 _ transl_stmt_s2 ce tyret nbrk ncnt =
    bind (transl_stmt_s1 ce tyret nbrk ncnt) (fun ts1 ->
      bind (transl_stmt_s2 ce tyret nbrk ncnt) (fun ts2 -> OK
        (T.Sseq (ts1, ts2))))

let transl_lbl_stmt_transl_stmtSifthenelse e _ transl_stmt_s1 _ transl_stmt_s2 ce tyret nbrk ncnt =
    bind (transl_expr ce e) (fun te ->
      bind (transl_stmt_s1 ce tyret nbrk ncnt) (fun ts1 ->
        bind (transl_stmt_s2 ce tyret nbrk ncnt) (fun ts2 -> OK
          (T.Sifthenelse ((make_boolean te (typeof e)), ts1, ts2)))))

let transl_lbl_stmt_transl_stmtSreturn e ce tyret _ _ =
    match e with
    | Some e0 ->
      bind (transl_expr ce e0) (fun te ->
        bind (make_cast (typeof e0) tyret te) (fun te' -> OK
          (T.Sreturn (Some te'))))
    | None -> OK (T.Sreturn None)

let transl_lbl_stmt_transl_stmtSlabel lbl _ transl_stmt_s ce tyret nbrk ncnt =
    bind (transl_stmt_s ce tyret nbrk ncnt) (fun ts -> OK (T.Slabel (lbl, ts)))

let transl_lbl_stmt_transl_stmtSgoto lbl _ _ _ _ =
    OK (T.Sgoto lbl)  

let transl_lbl_stmt_transl_stmtLSnil _ _ _ _ =
    OK T.LSnil

  let transl_lbl_stmt_transl_stmtLScons n _ transl_stmt_s _ transl_lbl_stmt_sl' ce tyret nbrk ncnt =
    bind (transl_stmt_s ce tyret nbrk ncnt) (fun ts ->
      bind (transl_lbl_stmt_sl' ce tyret nbrk ncnt) (fun tsl' -> OK
        (T.LScons (n, ts,  tsl'))))

  let transl_lbl_stmt_transl_stmtSloop _ transl_stmt_s1 _ transl_stmt_s2 ce tyret _ ncnt =
    bind (transl_stmt_s1 ce tyret (S O) O) (fun ts1 ->
      bind (transl_stmt_s2 ce tyret O (S ncnt)) (fun ts2 -> OK
        (T.Sblock (T.Sloop (T.Sseq ((T.Sblock ts1), ts2))))))

  (** val transl_lbl_stmt_transl_stmtSbreak : __motiveTtransl_stmt **)

  let transl_lbl_stmt_transl_stmtSbreak _ _ nbrk _ =
    OK (T.Sexit nbrk)

  (** val transl_lbl_stmt_transl_stmtScontinue : __motiveTtransl_stmt **)

  let transl_lbl_stmt_transl_stmtScontinue _ _ _ ncnt =
    OK (T.Sexit ncnt)

  (** val transl_lbl_stmt_transl_stmtSswitch :
      S.expr -> S.lbl_stmts -> __motiveTtransl_lbl_stmt -> __motiveTtransl_stmt **)

  let transl_lbl_stmt_transl_stmtSswitch a _ transl_lbl_stmt_sl ce tyret _ ncnt =
    bind (transl_expr ce a) (fun ta ->
      bind (transl_lbl_stmt_sl ce tyret O (S ncnt)) (fun tsl ->
        match classify_switch (typeof a) with
        | Coq_switch_case_i -> OK (T.Sblock (T.Sswitch (false, ta, tsl)))
        | Coq_switch_case_l -> OK (T.Sblock (T.Sswitch (true, ta, tsl)))
        | Coq_switch_default ->
          Error (msg ('c' :: []))))

  let transl_lbl_stmt_transl_stmtSbuiltin x ef tyargs bl ce _ _ _ =
    bind (transl_arglist ce bl tyargs) (fun tbl -> OK (T.Sbuiltin (x, ef, tbl)))

  let transl_lbl_stmt_transl_stmtSassign b c ce _ _ _ =
    bind2 (transl_lvalue ce b) (fun tb bf ->
      bind (transl_expr ce c) (fun tc ->
        bind (make_cast (typeof c) (typeof b) tc) (fun tc' ->
          make_store ce tb (typeof b) bf tc')))

  let transl_lbl_stmt_transl_stmtScall x b cl ce _ _ _ =
    match classify_fun (typeof b) with
    | Coq_fun_case_f (args, res0, cconv) ->
      bind (transl_expr ce b) (fun tb ->
        bind (transl_arglist ce cl args) (fun tcl ->
          let sg = { sig_args = (typlist_of_arglist cl args); sig_res =
            (rettype_of_type res0); sig_cc = cconv }
          in
          OK (make_funcall x res0 sg tb tcl)))
    | Coq_fun_default ->
      Error (msg ('c' :: []))

module S = Clight

let _transl_stmt =
  S.stmt_lbl_stmts_stmt_rect transl_lbl_stmt_transl_stmtSskip
    transl_lbl_stmt_transl_stmtSset transl_lbl_stmt_transl_stmtSseq
    transl_lbl_stmt_transl_stmtSifthenelse transl_lbl_stmt_transl_stmtSreturn
    transl_lbl_stmt_transl_stmtSlabel transl_lbl_stmt_transl_stmtSgoto
    transl_lbl_stmt_transl_stmtSbuiltin transl_lbl_stmt_transl_stmtScall
    transl_lbl_stmt_transl_stmtSassign transl_lbl_stmt_transl_stmtSloop
    transl_lbl_stmt_transl_stmtSbreak transl_lbl_stmt_transl_stmtScontinue
    transl_lbl_stmt_transl_stmtSswitch transl_lbl_stmt_transl_stmtLSnil
    transl_lbl_stmt_transl_stmtLScons

let _transl_lbl_stmt =
  S.lbl_stmts_lbl_stmts_stmt_rect transl_lbl_stmt_transl_stmtSskip
    transl_lbl_stmt_transl_stmtSset transl_lbl_stmt_transl_stmtSseq
    transl_lbl_stmt_transl_stmtSifthenelse transl_lbl_stmt_transl_stmtSreturn
    transl_lbl_stmt_transl_stmtSlabel transl_lbl_stmt_transl_stmtSgoto
    transl_lbl_stmt_transl_stmtSbuiltin transl_lbl_stmt_transl_stmtScall
    transl_lbl_stmt_transl_stmtSassign transl_lbl_stmt_transl_stmtSloop
    transl_lbl_stmt_transl_stmtSbreak transl_lbl_stmt_transl_stmtScontinue
    transl_lbl_stmt_transl_stmtSswitch transl_lbl_stmt_transl_stmtLSnil
    transl_lbl_stmt_transl_stmtLScons

let transl_statement ce ty n1 n2 stmt = _transl_stmt stmt ce ty n1 n2
let transl_lbl_stmt  ce ty n1 n2 stmt = _transl_lbl_stmt stmt ce ty n1 n2

let transl_var ce v =
  match sizeof ce (snd v) with
  | OK x -> OK ((fst v), x)
  | Error msg0 -> Error msg0

(** val signature_of_function : Clight.coq_function -> signature **)

let signature_of_function f =
  { sig_args = (map argtype_of_type (map snd f.Clight.fn_params)); sig_res =
    (rettype_of_type f.fn_return); sig_cc = f.fn_callconv }

let transl_function ce f =
  match _transl_stmt (*transl_statement*) f.Clight.fn_body ce f.fn_return (S O) O  with
  | OK x ->
    (match mmap (transl_var ce) f.Clight.fn_vars with
     | OK x0 ->
       OK { fn_sig = (signature_of_function f); fn_params =
         (map fst f.Clight.fn_params); fn_vars = x0; fn_temps =
         (map fst f.Clight.fn_temps); fn_body = x }
     | Error msg0 -> Error msg0)
  | Error msg0 -> Error msg0

(** val transl_fundef :
    composite_env -> ident -> Clight.fundef -> Csharpminor.fundef res **)

let transl_fundef ce _ = function
| Internal g ->
  (match transl_function ce g with
   | OK x -> OK (AST.Internal x)
   | Error msg0 -> Error msg0)
| External (ef, args, res0, cconv) ->
  if signature_eq (ef_sig ef) (signature_of_type args res0 cconv)
  then OK (AST.External ef)
  else Error
         (msg
           ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('f'::('u'::('n'::('d'::('e'::('f'::(':'::(' '::('w'::('r'::('o'::('n'::('g'::(' '::('e'::('x'::('t'::('e'::('r'::('n'::('a'::('l'::(' '::('s'::('i'::('g'::('n'::('a'::('t'::('u'::('r'::('e'::[]))))))))))))))))))))))))))))))))))))))))))))))))

(** val transl_globvar : ident -> coq_type -> unit res **)

let transl_globvar _ _ =
  OK ()

(** val transl_program : Clight.program -> Csharpminor.program res **)

let transl_program p =
  transform_partial_program2 (transl_fundef p.prog_comp_env) transl_globvar
    (program_of_program p)
