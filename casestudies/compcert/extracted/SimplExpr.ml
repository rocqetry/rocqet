open AST
open BinInt
open BinNums
open BinPos
open Clight
open Cop
open Csyntax
open Ctypes
open Datatypes
open Errors
open Integers
open Maps
open Memory
open Values
open Zpower

type generator = { gen_next : ident; gen_trail : (ident * coq_type) list }

type 'a result =
| Err of errmsg
| Res of 'a * generator

type 'a mon = generator -> 'a result

let ret x g =
  Res (x, g)

(** val error : errmsg -> 'a1 mon **)

let error msg _ =
  Err msg

(** val bind : 'a1 mon -> ('a1 -> 'a2 mon) -> 'a2 mon **)

let bind x f g =
  match x g with
  | Err msg -> Err msg
  | Res (a, g') -> f a g'

(** val bind2 : ('a1, 'a2) prod mon -> ('a1 -> 'a2 -> 'a3 mon) -> 'a3 mon **)

let bind2 x f =
  bind x (fun p -> f (fst p) (snd p))

(** val first_unused_ident : unit -> ident **)

let first_unused_ident = Camlcoq.first_unused_ident

(** val initial_generator : unit -> generator **)

let initial_generator x =
  { gen_next = (first_unused_ident x); gen_trail = [] }

(** val gensym : coq_type -> ident mon **)

let gensym ty g =
  Res (g.gen_next, { gen_next = (Pos.succ g.gen_next); gen_trail =
    ((g.gen_next, ty) :: g.gen_trail) })

(** val makeseq_rec :
    Clight.statement -> Clight.statement list -> Clight.statement **)

let rec makeseq_rec s = function
| [] -> s
| s' :: l' -> makeseq_rec (Clight.Ssequence (s, s')) l'

(** val makeseq : Clight.statement list -> Clight.statement **)

let makeseq l =
  makeseq_rec Clight.Sskip l

module S = Csyntax
module T = Clight

let eval_simpl_exprEconst_float n _ =
      Some (Vfloat n)

    (** val eval_simpl_exprEconst_int : Int.int -> coq_type -> __motiveTeval_simpl_expr **)

    let eval_simpl_exprEconst_int n _ =
      Some (Vint n)

    (** val eval_simpl_exprEconst_single : float32 -> coq_type -> __motiveTeval_simpl_expr **)

    let eval_simpl_exprEconst_single n _ =
      Some (Vsingle n)

    (** val eval_simpl_exprEconst_long : Int64.int -> coq_type -> __motiveTeval_simpl_expr **)

    let eval_simpl_exprEconst_long n _ =
      Some (Vlong n)

    (** val eval_simpl_exprEcast : T.expr -> __motiveTeval_simpl_expr -> coq_type -> __motiveTeval_simpl_expr **)

    let eval_simpl_exprEcast b eval_simpl_expr_b ty =
      match eval_simpl_expr_b with
      | Some v -> sem_cast v (T.typeof b) ty Mem.empty
      | None -> None

    (** val eval_simpl_exprEtempvar : ident -> coq_type -> __motiveTeval_simpl_expr **)

    let eval_simpl_exprEtempvar _ _ =
      None

    (** val eval_simpl_exprEsizeof : coq_type -> coq_type -> __motiveTeval_simpl_expr **)

    let eval_simpl_exprEsizeof _ _ =
      None

    (** val eval_simpl_exprEalignof : coq_type -> coq_type -> __motiveTeval_simpl_expr **)

    let eval_simpl_exprEalignof _ _ =
      None

    (** val eval_simpl_exprEunop : unary_operation -> T.expr -> __motiveTeval_simpl_expr -> coq_type -> __motiveTeval_simpl_expr **)

    let eval_simpl_exprEunop _ _ _ _ =
      None

    (** val eval_simpl_exprEbinop :
        binary_operation -> T.expr -> __motiveTeval_simpl_expr -> T.expr -> __motiveTeval_simpl_expr -> coq_type -> __motiveTeval_simpl_expr **)

    let eval_simpl_exprEbinop _ _ _ _ _ _ =
      None

    (** val eval_simpl_exprEvar : ident -> coq_type -> __motiveTeval_simpl_expr **)

    let eval_simpl_exprEvar _ _ =
      None

    (** val eval_simpl_exprEderef : T.expr -> __motiveTeval_simpl_expr -> coq_type -> __motiveTeval_simpl_expr **)

    let eval_simpl_exprEderef _ _ _ =
      None

    (** val eval_simpl_exprEaddrof : T.expr -> __motiveTeval_simpl_expr -> coq_type -> __motiveTeval_simpl_expr **)

    let eval_simpl_exprEaddrof _ _ _ =
      None

    (** val eval_simpl_exprEfield : T.expr -> __motiveTeval_simpl_expr -> ident -> coq_type -> __motiveTeval_simpl_expr **)

    let eval_simpl_exprEfield _ _ _ _ =
      None

    (** val eval_simpl_expr : T.__internal_expr -> __motiveTeval_simpl_expr **)

    let eval_simpl_expr =
      T.expr_rect eval_simpl_exprEconst_int eval_simpl_exprEconst_float eval_simpl_exprEconst_single eval_simpl_exprEconst_long eval_simpl_exprEtempvar
        eval_simpl_exprEsizeof eval_simpl_exprEcast eval_simpl_exprEalignof eval_simpl_exprEunop eval_simpl_exprEbinop eval_simpl_exprEvar eval_simpl_exprEderef
        eval_simpl_exprEaddrof eval_simpl_exprEfield

(** val makeif :
    Clight.expr -> Clight.statement -> Clight.statement -> Clight.statement **)

let makeif a s1 s2 =
  match eval_simpl_expr a with
  | Some v ->
    (match bool_val v (Clight.typeof a) Mem.empty with
     | Some b -> if b then s1 else s2
     | None -> Clight.Sifthenelse (a, s1, s2))
  | None -> Clight.Sifthenelse (a, s1, s2)

(** val coq_Ederef' : Clight.expr -> coq_type -> Clight.expr **)

let coq_Ederef' a t =
  match a with
  | Clight.Eaddrof (a', _) ->
    if type_eq t (Clight.typeof a') then a' else Clight.Ederef (a, t)
  | _ -> Clight.Ederef (a, t)

(** val coq_Eaddrof' : Clight.expr -> coq_type -> Clight.expr **)

let coq_Eaddrof' a t =
  match a with
  | Clight.Ederef (a', _) ->
    if type_eq t (Clight.typeof a') then a' else Clight.Eaddrof (a, t)
  | _ -> Clight.Eaddrof (a, t)

(** val transl_incrdecr :
    incr_or_decr -> Clight.expr -> coq_type -> Clight.expr **)

let transl_incrdecr id a ty =
  match id with
  | Incr ->
    Clight.Ebinop (Oadd, a, (Econst_int (Int.one, type_int32s)),
      (incrdecr_type ty))
  | Decr ->
    Clight.Ebinop (Osub, a, (Econst_int (Int.one, type_int32s)),
      (incrdecr_type ty))

(** val is_bitfield_access_aux :
    composite_env -> (composite_env -> ident -> members -> (coq_Z * bitfield)
    res) -> ident -> ident -> bitfield mon **)

let is_bitfield_access_aux ce fn id fld g =
  match PTree.get id ce with
  | Some co ->
    (match fn ce fld co.co_members with
     | OK p -> let (_, bf) = p in Res (bf, g)
     | Error _ ->
       Err ((MSG
         ('u'::('n'::('k'::('n'::('o'::('w'::('n'::(' '::('f'::('i'::('e'::('l'::('d'::(' '::[]))))))))))))))) :: ((CTX
         fld) :: [])))
  | None ->
    Err ((MSG
      ('u'::('n'::('k'::('n'::('o'::('w'::('n'::(' '::('c'::('o'::('m'::('p'::('o'::('s'::('i'::('t'::('e'::(' '::[]))))))))))))))))))) :: ((CTX
      id) :: []))

(** val is_bitfield_access : composite_env -> Clight.expr -> bitfield mon **)

(*let is_bitfield_access ce = function
| Clight.Efield (r, f, _) ->
  (match Clight.typeof r with
   | Tstruct (id, _) -> is_bitfield_access_aux ce field_offset id f
   | Tunion (id, _) -> is_bitfield_access_aux ce union_field_offset id f
   | _ ->
     (fun _ -> Err
       (msg
         ('i'::('s'::('_'::('b'::('i'::('t'::('f'::('i'::('e'::('l'::('d'::('_'::('a'::('c'::('c'::('e'::('s'::('s'::[])))))))))))))))))))))
| _ -> (fun g -> Res (Full, g)) *)

let is_bitfield_accessEconst_int _ _ _ =
      ret Full

    (** val is_bitfield_accessEconst_float : float -> coq_type -> __motiveTis_bitfield_access **)

    let is_bitfield_accessEconst_float _ _ _ =
      ret Full

    (** val is_bitfield_accessEconst_single : float32 -> coq_type -> __motiveTis_bitfield_access **)

    let is_bitfield_accessEconst_single _ _ _ =
      ret Full

    (** val is_bitfield_accessEconst_long : Int64.int -> coq_type -> __motiveTis_bitfield_access **)

    let is_bitfield_accessEconst_long _ _ _ =
      ret Full

    (** val is_bitfield_accessEtempvar : ident -> coq_type -> __motiveTis_bitfield_access **)

    let is_bitfield_accessEtempvar _ _ _ =
      ret Full

    (** val is_bitfield_accessEsizeof : coq_type -> coq_type -> __motiveTis_bitfield_access **)

    let is_bitfield_accessEsizeof _ _ _ =
      ret Full

    (** val is_bitfield_accessEcast : T.expr -> __motiveTis_bitfield_access -> coq_type -> __motiveTis_bitfield_access **)

    let is_bitfield_accessEcast _ _ _ _ =
      ret Full

    (** val is_bitfield_accessEalignof : coq_type -> coq_type -> __motiveTis_bitfield_access **)

    let is_bitfield_accessEalignof _ _ _ =
      ret Full

    (** val is_bitfield_accessEunop : unary_operation -> T.expr -> __motiveTis_bitfield_access -> coq_type -> __motiveTis_bitfield_access **)

    let is_bitfield_accessEunop _ _ _ _ _ =
      ret Full

    (** val is_bitfield_accessEbinop :
        binary_operation -> T.expr -> __motiveTis_bitfield_access -> T.expr -> __motiveTis_bitfield_access -> coq_type -> __motiveTis_bitfield_access **)

    let is_bitfield_accessEbinop _ _ _ _ _ _ _ =
      ret Full

    (** val is_bitfield_accessEvar : ident -> coq_type -> __motiveTis_bitfield_access **)

    let is_bitfield_accessEvar _ _ _ =
      ret Full

    (** val is_bitfield_accessEderef : T.expr -> __motiveTis_bitfield_access -> coq_type -> __motiveTis_bitfield_access **)

    let is_bitfield_accessEderef _ _ _ _ =
      ret Full

    (** val is_bitfield_accessEaddrof : T.expr -> __motiveTis_bitfield_access -> coq_type -> __motiveTis_bitfield_access **)

    let is_bitfield_accessEaddrof _ _ _ _ =
      ret Full

    (** val is_bitfield_accessEfield : T.expr -> __motiveTis_bitfield_access -> ident -> coq_type -> __motiveTis_bitfield_access **)

    let is_bitfield_accessEfield r _ f _ cenv =
      match T.typeof r with
      | Tstruct (id, _) -> is_bitfield_access_aux cenv field_offset id f
      | Tunion (id, _) -> is_bitfield_access_aux cenv union_field_offset id f
      | _ ->
        error (msg ('s' :: []))

    (** val is_bitfield_access : T.__internal_expr -> __motiveTis_bitfield_access **)

    let is_bitfield_access =
      T.expr_rect is_bitfield_accessEconst_int is_bitfield_accessEconst_float is_bitfield_accessEconst_single is_bitfield_accessEconst_long is_bitfield_accessEtempvar
        is_bitfield_accessEsizeof is_bitfield_accessEcast is_bitfield_accessEalignof is_bitfield_accessEunop is_bitfield_accessEbinop is_bitfield_accessEvar
        is_bitfield_accessEderef is_bitfield_accessEaddrof is_bitfield_accessEfield

    let is_bitfield_access ce e = is_bitfield_access e ce 
    
(** val chunk_for_volatile_type :
    coq_type -> bitfield -> memory_chunk option **)

let chunk_for_volatile_type ty bf =
  if type_is_volatile ty
  then (match access_mode ty with
        | By_value chunk ->
          (match bf with
           | Full -> Some chunk
           | Bits (_, _, _, _) -> None)
        | _ -> None)
  else None

(** val make_set : bitfield -> ident -> Clight.expr -> Clight.statement **)

let make_set bf id l =
  match chunk_for_volatile_type (Clight.typeof l) bf with
  | Some chunk ->
    let typtr = Tpointer ((Clight.typeof l), noattr) in
    Sbuiltin ((Some id), (EF_vload chunk), (typtr :: []), ((Clight.Eaddrof
    (l, typtr)) :: []))
  | None -> Sset (id, l)

(** val transl_valof :
    composite_env -> coq_type -> Clight.expr -> (Clight.statement
    list * Clight.expr) mon **)

let transl_valof ce ty l g =
  if type_is_volatile ty
  then (match gensym ty g with
        | Err msg0 -> Err msg0
        | Res (a, g') ->
          (match is_bitfield_access ce l g' with
           | Err msg0 -> Err msg0
           | Res (a0, g'0) ->
             Res ((((make_set a0 a l) :: []), (Etempvar (a, ty))), g'0)))
  else Res (([], l), g)

(** val make_assign :
    bitfield -> Clight.expr -> Clight.expr -> Clight.statement **)

let make_assign bf l r =
  match chunk_for_volatile_type (Clight.typeof l) bf with
  | Some chunk ->
    let ty = Clight.typeof l in
    let typtr = Tpointer (ty, noattr) in
    Sbuiltin (None, (EF_vstore chunk), (typtr :: (ty :: [])),
    ((Clight.Eaddrof (l, typtr)) :: (r :: [])))
  | None -> Sassign (l, r)

(** val make_normalize :
    intsize -> signedness -> coq_Z -> Clight.expr -> Clight.expr **)

let make_normalize sz sg width r =
  let intconst = fun n -> Econst_int ((Int.repr n), type_int32s) in
  if (||) ((fun x -> x) (intsize_eq sz IBool))
       ((fun x -> x) (signedness_eq sg Unsigned))
  then let mask = Z.sub (two_p width) (Zpos Coq_xH) in
       Clight.Ebinop (Oand, r, (intconst mask), (Clight.typeof r))
  else let amount = Z.sub Int.zwordsize width in
       Clight.Ebinop (Oshr, (Clight.Ebinop (Oshl, r, (intconst amount),
       type_int32s)), (intconst amount), (Clight.typeof r))

(** val make_assign_value : bitfield -> Clight.expr -> Clight.expr **)

let make_assign_value bf r =
  match bf with
  | Full -> r
  | Bits (sz, sg, _, width) -> make_normalize sz sg width r

type set_destination =
| SDbase of coq_type * coq_type * ident
| SDcons of coq_type * coq_type * ident * set_destination

type destination =
| For_val
| For_effects
| For_set of set_destination

(** val dummy_expr : Clight.expr **)

let dummy_expr =
  Econst_int (Int.zero, type_int32s)

(** val do_set : set_destination -> Clight.expr -> Clight.statement list **)

let rec do_set sd a =
  match sd with
  | SDbase (tycast, _, tmp) -> (Sset (tmp, (Clight.Ecast (a, tycast)))) :: []
  | SDcons (tycast, ty, tmp, sd') ->
    (Sset (tmp, (Clight.Ecast (a,
      tycast)))) :: (do_set sd' (Etempvar (tmp, ty)))

(** val finish :
    destination -> Clight.statement list -> Clight.expr -> Clight.statement
    list * Clight.expr **)

let finish dst sl a =
  match dst with
  | For_set sd -> ((app sl (do_set sd a)), a)
  | _ -> (sl, a)

(** val sd_temp : set_destination -> ident **)

let sd_temp = function
| SDbase (_, _, tmp) -> tmp
| SDcons (_, _, tmp, _) -> tmp

(** val sd_head_type : set_destination -> coq_type **)

let sd_head_type = function
| SDbase (_, ty, _) -> ty
| SDcons (_, ty, _, _) -> ty

(** val temp_for_sd : coq_type -> set_destination -> ident mon **)

let temp_for_sd ty sd =
  if type_eq ty (sd_head_type sd)
  then (fun g -> Res ((sd_temp sd), g))
  else gensym ty

(** val transl_expr :
    composite_env -> destination -> expr -> (Clight.statement
    list * Clight.expr) mon **)


let transl_expr_transl_exprlistEvar id ty _ dst =
      ret (finish dst [] (T.Etempvar (id, ty)))

    (** val transl_expr_transl_exprlistEval : coq_val -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEval v ty _ dst =
      match v with
      | Vint n -> ret (finish dst [] (T.Econst_int (n, ty)))
      | Vlong n -> ret (finish dst [] (T.Econst_long (n, ty)))
      | Vfloat n -> ret (finish dst [] (T.Econst_float (n, ty)))
      | Vsingle n -> ret (finish dst [] (T.Econst_single (n, ty)))
      | _ ->
        error (msg ('c' :: []))
          

    (** val transl_expr_transl_exprlistEcast : S.expr -> __motiveTtransl_expr -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEcast _ transl_expr_r1 ty ce dst = match dst with
    | For_effects -> transl_expr_r1 ce For_effects
    | _ -> bind2 (transl_expr_r1 ce For_val) (fun sl1 a1 -> ret (finish dst sl1 (T.Ecast (a1, ty))))

    (** val transl_expr_transl_exprlistEcomma : S.expr -> __motiveTtransl_expr -> S.expr -> __motiveTtransl_expr -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEcomma _ transl_expr_r1 _ transl_expr_r2 _ ce dst =
      bind2 (transl_expr_r1 ce For_effects) (fun sl1 _ -> bind2 (transl_expr_r2 ce dst) (fun sl2 a2 -> ret (((app sl1 sl2), a2))))

    (** val transl_expr_transl_exprlistEcondition :
        S.expr -> __motiveTtransl_expr -> S.expr -> __motiveTtransl_expr -> S.expr -> __motiveTtransl_expr -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEcondition _ transl_expr_r1 _ transl_expr_r2 _ transl_expr_r3 ty ce dst =
      bind2 (transl_expr_r1 ce For_val) (fun sl1 a1 ->
        match dst with
        | For_val ->
          bind (gensym ty) (fun t ->
            let sd = SDbase (ty, ty, t) in
            bind2 (transl_expr_r2 ce (For_set sd)) (fun sl2 _ ->
              bind2 (transl_expr_r3 ce (For_set sd)) (fun sl3 _ ->
                ret (((app sl1 (((makeif a1 (makeseq sl2) (makeseq sl3)) :: []))), (T.Etempvar (t, ty)))))))
        | For_effects ->
          bind2 (transl_expr_r2 ce For_effects) (fun sl2 _ ->
            bind2 (transl_expr_r3 ce For_effects) (fun sl3 _ -> ret (((app sl1 (((makeif a1 (makeseq sl2) (makeseq sl3)) :: []))), dummy_expr))))
        | For_set sd ->
          bind (temp_for_sd ty sd) (fun t ->
            let sd' = SDcons (ty, ty, t, sd) in
            bind2 (transl_expr_r2 ce (For_set sd')) (fun sl2 _ ->
              bind2 (transl_expr_r3 ce (For_set sd')) (fun sl3 _ -> ret (((app sl1 (((makeif a1 (makeseq sl2) (makeseq sl3)) :: []))), dummy_expr))))))

    (** val transl_expr_transl_exprlistEseqor : S.expr -> __motiveTtransl_expr -> S.expr -> __motiveTtransl_expr -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEseqor _ transl_expr_r1 _ transl_expr_r2 ty ce dst =
      bind2 (transl_expr_r1 ce For_val) (fun sl1 a1 ->
        match dst with
        | For_val ->
          bind (gensym ty) (fun t ->
            let sd = SDbase (type_bool, ty, t) in
            bind2 (transl_expr_r2 ce (For_set sd)) (fun sl2 _ ->
              ret (((app sl1 (((makeif a1 (T.Sset (t, (T.Econst_int (Int.one, ty)))) (makeseq sl2)) :: []))), (T.Etempvar (t, ty))))))
        | For_effects ->
          bind2 (transl_expr_r2 ce For_effects) (fun sl2 _ -> ret (((app sl1 (((makeif a1 T.Sskip (makeseq sl2)) :: []))), dummy_expr)))
        | For_set sd ->
          bind (temp_for_sd ty sd) (fun t ->
            let sd' = SDcons (type_bool, ty, t, sd) in
            bind2 (transl_expr_r2 ce (For_set sd')) (fun sl2 _ ->
              ret (((app sl1 (((makeif a1 (makeseq (do_set sd (T.Econst_int (Int.one, ty)))) (makeseq sl2)) :: []))), dummy_expr)))))

    (** val transl_expr_transl_exprlistEseqand : S.expr -> __motiveTtransl_expr -> S.expr -> __motiveTtransl_expr -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEseqand _ transl_expr_r1 _ transl_expr_r2 ty ce dst =
      bind2 (transl_expr_r1 ce For_val) (fun sl1 a1 ->
        match dst with
        | For_val ->
          bind (gensym ty) (fun t ->
            let sd = SDbase (type_bool, ty, t) in
            bind2 (transl_expr_r2 ce (For_set sd)) (fun sl2 _ ->
              ret (((app sl1 (((makeif a1 (makeseq sl2) (T.Sset (t, (T.Econst_int (Int.zero, ty))))) :: []))), (T.Etempvar (t, ty))))))
        | For_effects ->
          bind2 (transl_expr_r2 ce For_effects) (fun sl2 _ -> ret (((app sl1 (((makeif a1 (makeseq sl2) T.Sskip) :: []))), dummy_expr)))
        | For_set sd ->
          bind (temp_for_sd ty sd) (fun t ->
            let sd' = SDcons (type_bool, ty, t, sd) in
            bind2 (transl_expr_r2 ce (For_set sd')) (fun sl2 _ ->
              ret (((app sl1 (((makeif a1 (makeseq sl2) (makeseq (do_set sd (T.Econst_int (Int.zero, ty))))) :: []))), dummy_expr)))))

    (** val transl_expr_transl_exprlistEsizeof : coq_type -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEsizeof ty' ty _ dst =
      ret (finish dst [] (T.Esizeof (ty', ty)))

    (** val transl_expr_transl_exprlistEalignof : coq_type -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEalignof ty' ty _ dst =
      ret (finish dst [] (T.Ealignof (ty', ty)))

    (** val transl_expr_transl_exprlistEparen : S.expr -> __motiveTtransl_expr -> coq_type -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEparen _ _ _ _ _ _ =
      error (msg ('d' :: []))
        

    (** val transl_expr_transl_exprlistEunop : unary_operation -> S.expr -> __motiveTtransl_expr -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEunop op _ transl_expr_r1 ty ce dst =
      bind2 (transl_expr_r1 ce For_val) (fun sl1 a1 -> ret (finish dst sl1 (T.Eunop (op, a1, ty))))

    (** val transl_expr_transl_exprlistEbinop :
        binary_operation -> S.expr -> __motiveTtransl_expr -> S.expr -> __motiveTtransl_expr -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEbinop op _ transl_expr_r1 _ transl_expr_r2 ty ce dst =
      bind2 (transl_expr_r1 ce For_val) (fun sl1 a1 -> bind2 (transl_expr_r2 ce For_val) (fun sl2 a2 -> ret (finish dst (app sl1 sl2) (T.Ebinop (op, a1, a2, ty)))))

    (** val transl_expr_transl_exprlistEnil : __motiveTtransl_exprlist **)

    let transl_expr_transl_exprlistEnil _ =
      ret (([], []))

    (** val transl_expr_transl_exprlistEcons : S.expr -> __motiveTtransl_expr -> S.exprlist -> __motiveTtransl_exprlist -> __motiveTtransl_exprlist **)

    let transl_expr_transl_exprlistEcons _ transl_expr_r1 _ transl_exprlist_rl2 ce =
      bind2 (transl_expr_r1 ce For_val) (fun sl1 a1 -> bind2 (transl_exprlist_rl2 ce) (fun sl2 al2 -> ret (((app sl1 sl2), (a1 :: al2 )))))

    (** val transl_expr_transl_exprlistEbuiltin : external_function -> coq_type list -> S.exprlist -> __motiveTtransl_exprlist -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEbuiltin ef tyargs _ transl_exprlist_rl ty ce dst =
      bind2 (transl_exprlist_rl ce) (fun sl al ->
        match dst with
        | For_effects -> ret (((app sl (((T.Sbuiltin (None, ef, tyargs, al)) :: []))), dummy_expr))
        | _ -> bind (gensym ty) (fun t -> ret (finish dst (app sl (((T.Sbuiltin ((Some t), ef, tyargs, al)) :: []))) (T.Etempvar (t, ty)))))

    (** val transl_expr_transl_exprlistEassign : S.expr -> __motiveTtransl_expr -> S.expr -> __motiveTtransl_expr -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEassign l1 transl_expr_l1 _ transl_expr_r2 _ ce dst =
      bind2 (transl_expr_l1 ce For_val) (fun sl1 a1 ->
        bind2 (transl_expr_r2 ce For_val) (fun sl2 a2 ->
          bind (is_bitfield_access ce a1) (fun bf ->
            let ty1 = S.typeof l1 in
            (match dst with
             | For_effects -> ret (((app sl1 (app sl2 (((make_assign bf a1 a2) :: [])))), dummy_expr))
             | _ ->
               bind (gensym ty1) (fun t ->
                 ret
                   (finish dst (app sl1 (app sl2 (((T.Sset (t, (T.Ecast (a2, ty1)))) :: (((make_assign bf a1 (T.Etempvar (t, ty1))) :: []))))))
                     (make_assign_value bf (T.Etempvar (t, ty1)))))))))

    (** val transl_expr_transl_exprlistEvalof : S.expr -> __motiveTtransl_expr -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEvalof l transl_expr_l _ ce dst =
      bind2 (transl_expr_l ce For_val) (fun sl1 a1 -> bind2 (transl_valof ce (S.typeof l) a1) (fun sl2 a2 -> ret (finish dst (app sl1 sl2) a2)))

    (** val transl_expr_transl_exprlistEderef : S.expr -> __motiveTtransl_expr -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEderef _ transl_expr_r ty ce dst =
      bind2 (transl_expr_r ce For_val) (fun sl a -> ret (finish dst sl (T.Ederef (a, ty))))

    (** val transl_expr_transl_exprlistEaddrof : S.expr -> __motiveTtransl_expr -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEaddrof _ transl_expr_l ty ce dst =
      bind2 (transl_expr_l ce For_val) (fun sl a -> ret (finish dst sl (T.Eaddrof (a, ty))))

    (** val transl_expr_transl_exprlistEassignop :
        binary_operation -> S.expr -> __motiveTtransl_expr -> S.expr -> __motiveTtransl_expr -> coq_type -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEassignop op l1 transl_expr_l1 _ transl_expr_r2 tyres _ ce dst =
      let ty1 = S.typeof l1 in
      bind2 (transl_expr_l1 ce For_val) (fun sl1 a1 ->
        bind2 (transl_expr_r2 ce For_val) (fun sl2 a2 ->
          bind2 (transl_valof ce ty1 a1) (fun sl3 a3 ->
            bind (is_bitfield_access ce a1) (fun bf ->
              match dst with
              | For_effects -> ret (((app sl1 (app sl2 (app sl3 (((make_assign bf a1 (T.Ebinop (op, a3, a2, tyres))) :: []))))), dummy_expr))
              | _ ->
                bind (gensym ty1) (fun t ->
                  ret
                    (finish dst
                      (app sl1
                        (app sl2
                          (app sl3 (((T.Sset (t, (T.Ecast ((T.Ebinop (op, a3, a2, tyres)), ty1)))) :: (((make_assign bf a1 (T.Etempvar (t, ty1))) ::
                            []))))))) (make_assign_value bf (T.Etempvar (t, ty1)))))))))

    (** val transl_expr_transl_exprlistEpostincr : incr_or_decr -> S.expr -> __motiveTtransl_expr -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEpostincr id l1 transl_expr_l1 _ ce dst =
      let ty1 = S.typeof l1 in
      bind2 (transl_expr_l1 ce For_val) (fun sl1 a1 ->
        bind (is_bitfield_access ce a1) (fun bf ->
          match dst with
          | For_effects ->
            bind2 (transl_valof ce ty1 a1) (fun sl2 a2 ->
              ret (((app sl1 (app sl2 (((make_assign bf a1 (transl_incrdecr id a2 ty1)) :: [])))), dummy_expr)))
          | _ ->
            bind (gensym ty1) (fun t ->
              ret
                (finish dst (app sl1 (((make_set bf t a1) :: (((make_assign bf a1 (transl_incrdecr id (T.Etempvar (t, ty1)) ty1)) :: [])))))
                  (T.Etempvar (t, ty1))))))

    (** val transl_expr_transl_exprlistEloc : block -> Ptrofs.int -> bitfield -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEloc _ _ _ _ _ _ =
      error (msg ('d' :: []))
        

    (** val transl_expr_transl_exprlistEfield : S.expr -> __motiveTtransl_expr -> ident -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEfield _ transl_expr_r f ty ce dst =
      bind2 (transl_expr_r ce For_val) (fun sl a -> ret (finish dst sl (T.Efield (a, f, ty))))

    (** val transl_expr_transl_exprlistEcall : S.expr -> __motiveTtransl_expr -> S.exprlist -> __motiveTtransl_exprlist -> coq_type -> __motiveTtransl_expr **)

    let transl_expr_transl_exprlistEcall _ transl_expr_r1 _ transl_exprlist_r2 ty ce dst =
      bind2 (transl_expr_r1 ce For_val) (fun sl1 a1 ->
        bind2 (transl_exprlist_r2 ce) (fun sl2 al2 ->
          match dst with
          | For_effects -> ret (((app sl1 (app sl2 (((T.Scall (None, a1, al2)) :: [])))), dummy_expr))
          | _ -> bind (gensym ty) (fun t -> ret (finish dst (app sl1 (app sl2 (((T.Scall ((Some t), a1, al2)) :: [])))) (T.Etempvar (t, ty))))))

    (** val transl_expr : S.__internal_expr -> __motiveTtransl_expr **)

    let transl_expr =
      S.expr_expr_exprlist_rect transl_expr_transl_exprlistEval transl_expr_transl_exprlistEvar transl_expr_transl_exprlistEcast transl_expr_transl_exprlistEseqand
        transl_expr_transl_exprlistEseqor transl_expr_transl_exprlistEcondition transl_expr_transl_exprlistEsizeof transl_expr_transl_exprlistEalignof
        transl_expr_transl_exprlistEcomma transl_expr_transl_exprlistEparen transl_expr_transl_exprlistEunop transl_expr_transl_exprlistEbinop
        transl_expr_transl_exprlistEbuiltin transl_expr_transl_exprlistEcall transl_expr_transl_exprlistEloc transl_expr_transl_exprlistEpostincr
        transl_expr_transl_exprlistEassignop transl_expr_transl_exprlistEaddrof transl_expr_transl_exprlistEderef transl_expr_transl_exprlistEvalof
        transl_expr_transl_exprlistEassign transl_expr_transl_exprlistEfield transl_expr_transl_exprlistEnil transl_expr_transl_exprlistEcons
    let transl_expr ce dst e = transl_expr e ce dst





(** val transl_expression :
    composite_env -> expr -> (Clight.statement * Clight.expr) mon **)

let transl_expression ce r g =
  match transl_expr ce For_val r g with
  | Err msg0 -> Err msg0
  | Res (a, g') -> Res (((makeseq (fst a)), (snd a)), g')

(** val transl_expr_stmt : composite_env -> expr -> Clight.statement mon **)

let transl_expr_stmt ce r g =
  match transl_expr ce For_effects r g with
  | Err msg0 -> Err msg0
  | Res (a, g') -> Res ((makeseq (fst a)), g')

(** val transl_if :
    composite_env -> expr -> Clight.statement -> Clight.statement ->
    Clight.statement mon **)

let transl_if ce r s1 s2 g =
  match transl_expr ce For_val r g with
  | Err msg0 -> Err msg0
  | Res (a, g') ->
    Res ((makeseq (app (fst a) ((makeif (snd a) s1 s2) :: []))), g')

(** val is_Sskip : statement -> bool **)

let is_Sskip = function
| Sskip -> true
| _ -> false

let transl_lblstmt_transl_stmtSskip _ =
      ret T.Sskip

    (** val transl_lblstmt_transl_stmtSdo : S.expr -> __motiveTtransl_stmt **)

    let transl_lblstmt_transl_stmtSdo r ce =
      transl_expr_stmt ce r 

    (** val transl_lblstmt_transl_stmtSseq : S.stmt -> __motiveTtransl_stmt -> S.stmt -> __motiveTtransl_stmt -> __motiveTtransl_stmt **)

    let transl_lblstmt_transl_stmtSseq _ transl_stmt_s1 _ transl_stmt_s2 ce =
      bind (transl_stmt_s1 ce) (fun ts1 -> bind (transl_stmt_s2 ce) (fun ts2 -> ret (T.Ssequence (ts1, ts2))))

    (** val transl_lblstmt_transl_stmtSifthenelse : S.expr -> S.stmt -> __motiveTtransl_stmt -> S.stmt -> __motiveTtransl_stmt -> __motiveTtransl_stmt **)

    let transl_lblstmt_transl_stmtSifthenelse e s1 transl_stmt_s1 s2 transl_stmt_s2 ce =
      bind (transl_stmt_s1 ce) (fun ts1 ->
        bind (transl_stmt_s2 ce) (fun ts2 ->
          bind2 (transl_expression ce e) (fun s' a ->
            match match (is_Sskip s1) with
                  | true -> (is_Sskip s2)
                  | false -> false with
            | true -> ret (T.Ssequence (s', T.Sskip))
            | false -> ret (T.Ssequence (s', (T.Sifthenelse (a, ts1, ts2)))))))

    (** val transl_lblstmt_transl_stmtSreturn : S.expr option -> __motiveTtransl_stmt **)

    let transl_lblstmt_transl_stmtSreturn e ce =
      match e with
      | Some e0 -> bind2 (transl_expression ce e0) (fun s' a -> ret (T.Ssequence (s', (T.Sreturn (Some a)))))
      | None -> ret (T.Sreturn None)

    (** val transl_lblstmt_transl_stmtSlabel : S.label -> S.stmt -> __motiveTtransl_stmt -> __motiveTtransl_stmt **)

    let transl_lblstmt_transl_stmtSlabel lbl _ transl_stmt_s1 ce =
      bind (transl_stmt_s1 ce) (fun ts1 -> ret (T.Slabel (lbl, ts1)))

    (** val transl_lblstmt_transl_stmtSgoto : S.label -> __motiveTtransl_stmt **)

    let transl_lblstmt_transl_stmtSgoto lbl _ =
      ret (T.Sgoto lbl)

    (** val transl_lblstmt_transl_stmtLSnil : __motiveTtransl_lblstmt **)

    let transl_lblstmt_transl_stmtLSnil _ =
      ret T.LSnil

    (** val transl_lblstmt_transl_stmtLScons : coq_Z option -> S.stmt -> __motiveTtransl_stmt -> S.lbl_stmts -> __motiveTtransl_lblstmt -> __motiveTtransl_lblstmt **)

    let transl_lblstmt_transl_stmtLScons c _ transl_stmt_s _ transl_lblstmt_ls1 ce =
      bind (transl_stmt_s ce) (fun ts -> bind (transl_lblstmt_ls1 ce) (fun tls1 -> ret (T.LScons (c, ts, tls1))))

    (** val transl_lblstmt_transl_stmtSwhile : S.expr -> S.stmt -> __motiveTtransl_stmt -> __motiveTtransl_stmt **)

    let transl_lblstmt_transl_stmtSwhile e _ transl_stmt_s1 ce =
      bind (transl_if ce e T.Sskip T.Sbreak) (fun s' -> bind (transl_stmt_s1 ce) (fun ts1 -> ret (T.Sloop ((T.Ssequence (s', ts1)), T.Sskip))))

    (** val transl_lblstmt_transl_stmtSbreak : __motiveTtransl_stmt **)

    let transl_lblstmt_transl_stmtSbreak _ =
      ret T.Sbreak

    (** val transl_lblstmt_transl_stmtScontinue : __motiveTtransl_stmt **)

    let transl_lblstmt_transl_stmtScontinue _ =
      ret T.Scontinue

    (** val transl_lblstmt_transl_stmtSdowhile : S.expr -> S.stmt -> __motiveTtransl_stmt -> __motiveTtransl_stmt **)

    let transl_lblstmt_transl_stmtSdowhile e _ transl_stmt_s1 ce =
      bind (transl_if ce e T.Sskip T.Sbreak) (fun s' -> bind (transl_stmt_s1 ce) (fun ts1 -> ret (T.Sloop (ts1, s'))))

    (** val transl_lblstmt_transl_stmtSfor :
        S.stmt -> __motiveTtransl_stmt -> S.expr -> S.stmt -> __motiveTtransl_stmt -> S.stmt -> __motiveTtransl_stmt -> __motiveTtransl_stmt **)

    let transl_lblstmt_transl_stmtSfor s1 transl_stmt_s1 e2 _ transl_stmt_s3 _ transl_stmt_s4 ce =
      bind (transl_stmt_s1 ce) (fun ts1 ->
        bind (transl_if ce e2 T.Sskip T.Sbreak) (fun s' ->
          bind (transl_stmt_s3 ce) (fun ts3 ->
            bind (transl_stmt_s4 ce) (fun ts4 ->
              match is_Sskip s1 with
              | true -> ret (T.Sloop ((T.Ssequence (s', ts4)), ts3))
              | false -> ret (T.Ssequence (ts1, (T.Sloop ((T.Ssequence (s', ts4)), ts3))))))))

    (** val transl_lblstmt_transl_stmtSswitch : S.expr -> S.lbl_stmts -> __motiveTtransl_lblstmt -> __motiveTtransl_stmt **)

    let transl_lblstmt_transl_stmtSswitch e _ transl_lblstmt_ls ce =
      bind2 (transl_expression ce e) (fun s' a -> bind (transl_lblstmt_ls ce) (fun tls -> ret (T.Ssequence (s', (T.Sswitch (a, tls))))))

    (** val transl_stmt : S.__internal_stmt -> __motiveTtransl_stmt **)

    let transl_stmt =
      S.stmt_lbl_stmts_stmt_rect transl_lblstmt_transl_stmtSseq transl_lblstmt_transl_stmtSskip transl_lblstmt_transl_stmtSdo transl_lblstmt_transl_stmtSifthenelse
        transl_lblstmt_transl_stmtSreturn transl_lblstmt_transl_stmtSlabel transl_lblstmt_transl_stmtSgoto transl_lblstmt_transl_stmtSfor
        transl_lblstmt_transl_stmtSdowhile transl_lblstmt_transl_stmtSwhile transl_lblstmt_transl_stmtSbreak transl_lblstmt_transl_stmtScontinue
        transl_lblstmt_transl_stmtSswitch transl_lblstmt_transl_stmtLSnil transl_lblstmt_transl_stmtLScons
    let transl_stmt ce s = transl_stmt s ce



(** val transl_function :
    composite_env -> coq_function -> Clight.coq_function res **)

let transl_function ce f =
  match transl_stmt ce f.fn_body (initial_generator ()) with
  | Err msg0 -> Error msg0
  | Res (tbody, g) ->
    OK { Clight.fn_return = f.fn_return; Clight.fn_callconv = f.fn_callconv;
      Clight.fn_params = f.fn_params; Clight.fn_vars = f.fn_vars; fn_temps =
      g.gen_trail; Clight.fn_body = tbody }

(** val transl_fundef :
    composite_env -> Csyntax.fundef -> Clight.fundef res **)



let transl_fundef ce = function
| Internal f ->
  (match transl_function ce f with
   | OK x -> OK (Internal x)
   | Error msg0 -> Error msg0)
| External (ef, targs, tres, cc) -> OK (External (ef, targs, tres, cc))

(** val transl_program : Csyntax.program -> Clight.program res **)

let transl_program p =
  match transform_partial_program (transl_fundef p.prog_comp_env)
          (program_of_program p) with
  | OK x ->
    OK { prog_defs = x.AST.prog_defs; prog_public = x.AST.prog_public;
      prog_main = x.AST.prog_main; prog_types = p.prog_types; prog_comp_env =
      p.prog_comp_env }
  | Error msg0 -> Error msg0
