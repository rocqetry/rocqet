open AST
open BinNums
open BinPos
open Cminor
open CminorSel
open Coqlib
open Datatypes
open Errors
open Integers
open List0
open Maps
open Op
open RTL
open Registers

type mapping = { map_vars : reg PTree.t; map_letvars : reg list }

type state = { st_nextreg : positive; st_nextnode : positive; st_code : code }

type 'a res =
| Error of errmsg
| OK of 'a * state

type 'a mon = state -> 'a res


let ret x s =
  OK (x, s)

(** val error : errmsg -> ('a1, 'a2) mon **)

let error msg _ =
  Error msg

(** val bind : ('a1, 'a3) mon -> ('a1 -> ('a2, 'a3) mon) -> ('a2, 'a3) mon **)

let bind f g s =
  match f s with
  | Error msg -> Error msg
  | OK (a, s') -> g a s'

(** val bind2 : (('a1, 'a2) prod, 'a4) mon -> ('a1 -> 'a2 -> ('a3, 'a4) mon) -> ('a3, 'a4) mon **)

let bind2 f g =
  bind f (fun xy -> g (fst xy) (snd xy))

(** val handle_error : 'a1 mon -> 'a1 mon -> 'a1 mon **)

let handle_error f g s =
  match f s with
  | Error _ -> g s
  | OK (a, s') -> OK (a, s')

(** val init_state : state **)

let init_state =
  { st_nextreg = Coq_xH; st_nextnode = Coq_xH; st_code = PTree.empty }

(** val add_instr : instruction -> node mon **)

let add_instr i s =
  let n = s.st_nextnode in
  OK (n, { st_nextreg = s.st_nextreg; st_nextnode = (Pos.succ n); st_code =
  (PTree.set n i s.st_code) })

(** val reserve_instr : node mon **)

let reserve_instr s =
  let n = s.st_nextnode in
  OK (n, { st_nextreg = s.st_nextreg; st_nextnode = (Pos.succ n); st_code =
  s.st_code })

(** val check_empty_node : state -> node -> bool **)

let check_empty_node s n =
  match PTree.get n s.st_code with
  | Some _ -> false
  | None -> true

(** val update_instr : node -> instruction -> unit mon **)

let update_instr n i s =
  if plt n s.st_nextnode
  then if check_empty_node s n
       then OK ((), { st_nextreg = s.st_nextreg; st_nextnode = s.st_nextnode;
              st_code = (PTree.set n i s.st_code) })
       else Error
              (msg
                ('R'::('T'::('L'::('g'::('e'::('n'::('.'::('u'::('p'::('d'::('a'::('t'::('e'::('_'::('i'::('n'::('s'::('t'::('r'::[]))))))))))))))))))))
  else Error
         (msg
           ('R'::('T'::('L'::('g'::('e'::('n'::('.'::('u'::('p'::('d'::('a'::('t'::('e'::('_'::('i'::('n'::('s'::('t'::('r'::[]))))))))))))))))))))

(** val new_reg : reg mon **)

let new_reg s =
  OK (s.st_nextreg, { st_nextreg = (Pos.succ s.st_nextreg); st_nextnode =
    s.st_nextnode; st_code = s.st_code })

(** val init_mapping : mapping **)

let init_mapping =
  { map_vars = PTree.empty; map_letvars = [] }

(** val add_var : mapping -> ident -> (reg * mapping) mon **)

let add_var map0 name s =
  match new_reg s with
  | Error msg0 -> Error msg0
  | OK (a, s') ->
    OK ((a, { map_vars = (PTree.set name a map0.map_vars); map_letvars =
      map0.map_letvars }), s')

(** val add_vars : mapping -> ident list -> (reg list * mapping) mon **)

let rec add_vars map0 names s =
  match names with
  | [] -> OK (([], map0), s)
  | n1 :: nl ->
    (match add_vars map0 nl s with
     | Error msg0 -> Error msg0
     | OK (a, s') ->
       (match add_var (snd a) n1 s' with
        | Error msg0 -> Error msg0
        | OK (a0, s'0) -> OK ((((fst a0) :: (fst a)), (snd a0)), s'0)))

(** val find_var : mapping -> ident -> reg mon **)

let find_var map0 name s =
  match PTree.get name map0.map_vars with
  | Some r -> OK (r, s)
  | None ->
    Error ((MSG
      ('R'::('T'::('L'::('g'::('e'::('n'::(':'::(' '::('u'::('n'::('b'::('o'::('u'::('n'::('d'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::[])))))))))))))))))))))))))) :: ((CTX
      name) :: []))

(** val add_letvar : mapping -> reg -> mapping **)

let add_letvar map0 r =
  { map_vars = map0.map_vars; map_letvars = (r :: map0.map_letvars) }

(** val find_letvar : mapping -> nat -> reg mon **)

let find_letvar map0 idx s =
  match nth_error map0.map_letvars idx with
  | Some r -> OK (r, s)
  | None ->
    Error
      (msg
        ('R'::('T'::('L'::('g'::('e'::('n'::(':'::(' '::('u'::('n'::('b'::('o'::('u'::('n'::('d'::(' '::('l'::('e'::('t'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::[])))))))))))))))))))))))))))))

(** val alloc_reg : mapping -> expr -> reg mon **)

(*let alloc_reg map0 = function
| Evar id -> find_var map0 id
| Eletvar n -> find_letvar map0 n
| _ -> new_reg *)
module S = CminorSel
module T = RTL

(** val alloc_regEvar : ident -> __motiveTalloc_reg **)

    let alloc_regEvar id map0 =
      find_var map0 id

    (** val alloc_regEletvar : nat -> __motiveTalloc_reg **)

    let alloc_regEletvar n map0 =
      find_letvar map0 n

    (** val alloc_regEop : operation -> S.exprlist -> __motiveTalloc_reg **)

    let alloc_regEop _ _ _ =
      new_reg

    (** val alloc_regEcondition :
        S.condexpr -> S.expr -> __motiveTalloc_reg -> S.expr -> __motiveTalloc_reg -> __motiveTalloc_reg **)

    let alloc_regEcondition _ _ _ _ _ _ =
      new_reg

    (** val alloc_regElet :
        S.expr -> __motiveTalloc_reg -> S.expr -> __motiveTalloc_reg -> __motiveTalloc_reg **)

    let alloc_regElet _ _ _ _ _ =
      new_reg

    (** val alloc_regEbuiltin : external_function -> S.exprlist -> __motiveTalloc_reg **)

    let alloc_regEbuiltin _ _ _ =
      new_reg

    (** val alloc_regEexternal : ident -> signature -> S.exprlist -> __motiveTalloc_reg **)

    let alloc_regEexternal _ _ _ _ =
      new_reg

    (** val alloc_regEload : memory_chunk -> addressing -> S.exprlist -> __motiveTalloc_reg **)

    let alloc_regEload _ _ _ _ =
      new_reg

    (** val alloc_reg : S.__internal_expr -> __motiveTalloc_reg **)

let alloc_reg =
      S.expr_rect alloc_regEvar alloc_regEcondition alloc_regEop alloc_regElet alloc_regEletvar
        alloc_regEbuiltin alloc_regEexternal alloc_regEload
let alloc_reg arg e = alloc_reg e arg

(** val alloc_regs : mapping -> exprlist -> reg list mon **)

let rec alloc_regs map0 al s =
  match al with
  | Enil -> OK ([], s)
  | Econs (a, bl) ->
    (match alloc_reg map0 a s with
     | Error msg0 -> Error msg0
     | OK (a0, s') ->
       (match alloc_regs map0 bl s' with
        | Error msg0 -> Error msg0
        | OK (a1, s'0) -> OK ((a0 :: a1), s'0)))

let alloc_regsEnil _ =
      ret []

    (** val alloc_regsEcons : S.expr -> S.exprlist -> __motiveTalloc_regs -> __motiveTalloc_regs **)

let alloc_regsEcons a _ alloc_regs_bl map0 =
      bind (alloc_reg map0 a) (fun r -> bind (alloc_regs_bl map0) (fun rl -> ret ((r :: rl))))

let alloc_regs =
  S.exprlist_rect alloc_regsEnil alloc_regsEcons

let alloc_regs (map0: mapping) (es: exprlist) = alloc_regs es map0

(** val alloc_optreg : mapping -> ident option -> reg mon **)

let alloc_optreg map0 = function
| Some id -> find_var map0 id
| None -> new_reg

(** val add_move : reg -> reg -> node -> node mon **)

let add_move rs rd nd =
  if Reg.eq rs rd
  then (fun s -> OK (nd, s))
  else add_instr (Iop (Omove, (rs :: []), rd, nd))

(** val exprlist_of_expr_list : expr list -> exprlist **)

let exprlist_of_expr_list l =
  fold_right (fun x x0 -> Econs (x, x0)) Enil l

(** val convert_builtin_arg :
    expr builtin_arg -> 'a1 list -> 'a1 builtin_arg * 'a1 list **)

let rec convert_builtin_arg a rl =
  match a with
  | BA _ ->
    (match rl with
     | [] -> ((BA_int Int.zero), [])
     | r :: rs -> ((BA r), rs))
  | BA_int n -> ((BA_int n), rl)
  | BA_long n -> ((BA_long n), rl)
  | BA_float n -> ((BA_float n), rl)
  | BA_single n -> ((BA_single n), rl)
  | BA_loadstack (chunk, ofs) -> ((BA_loadstack (chunk, ofs)), rl)
  | BA_addrstack ofs -> ((BA_addrstack ofs), rl)
  | BA_loadglobal (chunk, id, ofs) -> ((BA_loadglobal (chunk, id, ofs)), rl)
  | BA_addrglobal (id, ofs) -> ((BA_addrglobal (id, ofs)), rl)
  | BA_splitlong (hi, lo) ->
    let (hi', rl1) = convert_builtin_arg hi rl in
    let (lo', rl2) = convert_builtin_arg lo rl1 in
    ((BA_splitlong (hi', lo')), rl2)
  | BA_addptr (a1, a2) ->
    let (a1', rl1) = convert_builtin_arg a1 rl in
    let (a2', rl2) = convert_builtin_arg a2 rl1 in
    ((BA_addptr (a1', a2')), rl2)

(** val convert_builtin_args :
    expr builtin_arg list -> 'a1 list -> 'a1 builtin_arg list **)

let rec convert_builtin_args al rl =
  match al with
  | [] -> []
  | a1 :: al0 ->
    let (a1', rl1) = convert_builtin_arg a1 rl in
    a1' :: (convert_builtin_args al0 rl1)

(** val convert_builtin_res :
    mapping -> xtype -> ident builtin_res -> reg builtin_res mon **)

let convert_builtin_res map0 ty r s =
  match r with
  | BR id ->
    (match find_var map0 id s with
     | Error msg0 -> Error msg0
     | OK (a, s') -> OK ((BR a), s'))
  | BR_none ->
    if xtype_eq ty Xvoid
    then OK (BR_none, s)
    else (match new_reg s with
          | Error msg0 -> Error msg0
          | OK (a, s') -> OK ((BR a), s'))
  | BR_splitlong (_, _) ->
    Error
      (msg
        ('R'::('T'::('L'::('g'::('e'::('n'::(':'::(' '::('b'::('a'::('d'::(' '::('b'::('u'::('i'::('l'::('t'::('i'::('n'::('_'::('r'::('e'::('s'::[]))))))))))))))))))))))))


(** val transl_condexpr_transl_expr_transl_exprlistEvar : ident -> __motiveTtransl_expr **)

let transl_condexpr_transl_expr_transl_exprlistEvar v map0 rd nd =
  bind (find_var map0 v) (fun r -> add_move r rd nd)

    (** val transl_condexpr_transl_expr_transl_exprlistElet :
        S.expr -> __motiveTtransl_expr -> S.expr -> __motiveTtransl_expr -> __motiveTtransl_expr **)

let transl_condexpr_transl_expr_transl_exprlistElet _ transl_expr_b _ transl_expr_c map0 rd nd =
  bind new_reg (fun r -> bind (transl_expr_c (add_letvar map0 r) rd nd) (fun nc -> transl_expr_b map0 r nc))

    (** val transl_condexpr_transl_expr_transl_exprlistEop :
        operation -> S.exprlist -> __motiveTtransl_exprlist -> __motiveTtransl_expr **)

let transl_condexpr_transl_expr_transl_exprlistEop op al transl_exprlist_al map0 rd nd =
      bind (alloc_regs map0 al) (fun rl ->
        bind (add_instr (T.Iop (op, rl, rd, nd))) (fun no -> transl_exprlist_al map0 rl no))

    (** val transl_condexpr_transl_expr_transl_exprlistEcondition :
        S.condexpr -> __motiveTtransl_condexpr -> S.expr -> __motiveTtransl_expr -> S.expr ->
        __motiveTtransl_expr -> __motiveTtransl_expr **)

let transl_condexpr_transl_expr_transl_exprlistEcondition _ transl_condexpr_a _ transl_expr_b _ transl_expr_c map0 rd nd =
      bind (transl_expr_c map0 rd nd) (fun nfalse ->
        bind (transl_expr_b map0 rd nd) (fun ntrue -> transl_condexpr_a map0 ntrue nfalse))

    (** val transl_condexpr_transl_expr_transl_exprlistEletvar : nat -> __motiveTtransl_expr **)

let transl_condexpr_transl_expr_transl_exprlistEletvar n map0 rd nd =
      bind (find_letvar map0 n) (fun r -> add_move r rd nd)

    (** val transl_condexpr_transl_expr_transl_exprlistEnil : __motiveTtransl_exprlist **)

let transl_condexpr_transl_expr_transl_exprlistEnil _ rl nd =
      match rl with
      | [] -> ret nd
      | _ :: _ ->
        error (msg ('a' :: []))          

    (** val transl_condexpr_transl_expr_transl_exprlistEcons :
        S.expr -> __motiveTtransl_expr -> S.exprlist -> __motiveTtransl_exprlist -> __motiveTtransl_exprlist **)

let transl_condexpr_transl_expr_transl_exprlistEcons _ transl_expr_b _ transl_exprlist_bs map0 rl nd =
      match rl with
      | [] ->
        error (msg ('b' :: []))          
      | (r :: rs) -> bind (transl_exprlist_bs map0 rs nd) (fun no -> transl_expr_b map0 r no)

    (** val transl_condexpr_transl_expr_transl_exprlistCEcond :
        condition -> S.exprlist -> __motiveTtransl_exprlist -> __motiveTtransl_condexpr **)

let transl_condexpr_transl_expr_transl_exprlistCEcond c al transl_exprlist_al map0 ntrue nfalse =
      bind (alloc_regs map0 al) (fun rl ->
        bind (add_instr (T.Icond (c, rl, ntrue, nfalse))) (fun nt -> transl_exprlist_al map0 rl nt))

    (** val transl_condexpr_transl_expr_transl_exprlistCEcondition :
        S.condexpr -> __motiveTtransl_condexpr -> S.condexpr -> __motiveTtransl_condexpr -> S.condexpr ->
        __motiveTtransl_condexpr -> __motiveTtransl_condexpr **)

let transl_condexpr_transl_expr_transl_exprlistCEcondition _ transl_condexpr_a _ transl_condexpr_b _ transl_condexpr_c map0 ntrue nfalse =
      bind (transl_condexpr_c map0 ntrue nfalse) (fun nc ->
        bind (transl_condexpr_b map0 ntrue nfalse) (fun nb -> transl_condexpr_a map0 nb nc))

    (** val transl_condexpr_transl_expr_transl_exprlistCElet :
        S.expr -> __motiveTtransl_expr -> S.condexpr -> __motiveTtransl_condexpr -> __motiveTtransl_condexpr **)

let transl_condexpr_transl_expr_transl_exprlistCElet _ transl_expr_b _ transl_condexpr_c map0 ntrue nfalse =
      bind new_reg (fun r ->
        bind (transl_condexpr_c (add_letvar map0 r) ntrue nfalse) (fun nc -> transl_expr_b map0 r nc))

    (** val transl_condexpr_transl_expr_transl_exprlistEbuiltin :
        external_function -> S.exprlist -> __motiveTtransl_exprlist -> __motiveTtransl_expr **)

let transl_condexpr_transl_expr_transl_exprlistEbuiltin ef al transl_exprlist_al map0 rd nd =
      bind (alloc_regs map0 al) (fun rl ->
        bind (add_instr (T.Ibuiltin (ef, (map (fun x -> BA x) rl), (BR rd), nd))) (fun no ->
          transl_exprlist_al map0 rl no))

    (** val transl_condexpr_transl_expr_transl_exprlistEexternal :
        ident -> signature -> S.exprlist -> __motiveTtransl_exprlist -> __motiveTtransl_expr **)

    let transl_condexpr_transl_expr_transl_exprlistEexternal id (sg: signature) al transl_exprlist_al map0 rd nd =
      bind (alloc_regs map0 al) (fun rl -> bind (add_instr (T.Icall (sg, (Coq_inr id), rl, rd, nd)))
                                             (fun no -> transl_exprlist_al map0 rl no))

    (** val transl_condexpr_transl_expr_transl_exprlistEload :
        memory_chunk -> addressing -> S.exprlist -> __motiveTtransl_exprlist -> __motiveTtransl_expr **)

let transl_condexpr_transl_expr_transl_exprlistEload chunk addr al transl_exprlist_al map0 rd nd =
      bind (alloc_regs map0 al) (fun rl ->
        bind (add_instr (T.Iload (chunk, addr, rl, rd, nd))) (fun no -> transl_exprlist_al map0 rl no))

    (** val transl_expr : S.__internal_expr -> __motiveTtransl_expr **)

let transl_expr =
   S.expr_condexpr_expr_exprlist_rect transl_condexpr_transl_expr_transl_exprlistEvar
     transl_condexpr_transl_expr_transl_exprlistEcondition transl_condexpr_transl_expr_transl_exprlistEop
     transl_condexpr_transl_expr_transl_exprlistElet transl_condexpr_transl_expr_transl_exprlistEletvar
     transl_condexpr_transl_expr_transl_exprlistEbuiltin transl_condexpr_transl_expr_transl_exprlistEexternal
     transl_condexpr_transl_expr_transl_exprlistEload transl_condexpr_transl_expr_transl_exprlistEnil
     transl_condexpr_transl_expr_transl_exprlistEcons transl_condexpr_transl_expr_transl_exprlistCEcond
     transl_condexpr_transl_expr_transl_exprlistCEcondition transl_condexpr_transl_expr_transl_exprlistCElet
let transl_expr map0 a rd nd =  transl_expr a map0 rd nd
    (** val transl_exprlist : S.__internal_exprlist -> __motiveTtransl_exprlist **)

let transl_exprlist =
  S.exprlist_condexpr_expr_exprlist_rect transl_condexpr_transl_expr_transl_exprlistEvar
    transl_condexpr_transl_expr_transl_exprlistEcondition transl_condexpr_transl_expr_transl_exprlistEop
    transl_condexpr_transl_expr_transl_exprlistElet transl_condexpr_transl_expr_transl_exprlistEletvar
    transl_condexpr_transl_expr_transl_exprlistEbuiltin transl_condexpr_transl_expr_transl_exprlistEexternal
    transl_condexpr_transl_expr_transl_exprlistEload transl_condexpr_transl_expr_transl_exprlistEnil
    transl_condexpr_transl_expr_transl_exprlistEcons transl_condexpr_transl_expr_transl_exprlistCEcond
    transl_condexpr_transl_expr_transl_exprlistCEcondition transl_condexpr_transl_expr_transl_exprlistCElet
let transl_exprlist map0 al rl nd = transl_exprlist al map0 rl nd
    (** val transl_condexpr : S.__internal_condexpr -> __motiveTtransl_condexpr **)

let transl_condexpr =
      S.condexpr_condexpr_expr_exprlist_rect transl_condexpr_transl_expr_transl_exprlistEvar
        transl_condexpr_transl_expr_transl_exprlistEcondition transl_condexpr_transl_expr_transl_exprlistEop
        transl_condexpr_transl_expr_transl_exprlistElet transl_condexpr_transl_expr_transl_exprlistEletvar
        transl_condexpr_transl_expr_transl_exprlistEbuiltin transl_condexpr_transl_expr_transl_exprlistEexternal
        transl_condexpr_transl_expr_transl_exprlistEload transl_condexpr_transl_expr_transl_exprlistEnil
        transl_condexpr_transl_expr_transl_exprlistEcons transl_condexpr_transl_expr_transl_exprlistCEcond
        transl_condexpr_transl_expr_transl_exprlistCEcondition transl_condexpr_transl_expr_transl_exprlistCElet
let transl_condexpr map0 a ntrue nfalse = transl_condexpr a map0 ntrue nfalse


(** val transl_exit : node list -> nat -> node mon **)

let transl_exit nexits n s =
  match nth_error nexits n with
  | Some ne -> OK (ne, s)
  | None ->
    Error
      (msg
        ('R'::('T'::('L'::('g'::('e'::('n'::(':'::(' '::('w'::('r'::('o'::('n'::('g'::(' '::('e'::('x'::('i'::('t'::[])))))))))))))))))))

(** val transl_jumptable : node list -> nat list -> node list mon **)

let rec transl_jumptable nexits tbl s =
  match tbl with
  | [] -> OK ([], s)
  | t1 :: tl ->
    (match transl_exit nexits t1 s with
     | Error msg0 -> Error msg0
     | OK (a, s') ->
       (match transl_jumptable nexits tl s' with
        | Error msg0 -> Error msg0
        | OK (a0, s'0) -> OK ((a :: a0), s'0)))

(** val transl_exitexpr : mapping -> exitexpr -> node list -> node mon **)

let rec transl_exitexpr map0 a nexits =
  match a with
  | XEexit n -> transl_exit nexits n
  | XEjumptable (a0, tbl) ->
    (fun s ->
      match alloc_reg map0 a0 s with
      | Error msg0 -> Error msg0
      | OK (a1, s') ->
        (match transl_jumptable nexits tbl s' with
         | Error msg0 -> Error msg0
         | OK (a2, s'0) ->
           (match add_instr (Ijumptable (a1, a2)) s'0 with
            | Error msg0 -> Error msg0
            | OK (a3, s'1) -> transl_expr map0 a0 a1 a3 s'1)))
  | XEcondition (a0, b, c) ->
    (fun s ->
      match transl_exitexpr map0 c nexits s with
      | Error msg0 -> Error msg0
      | OK (a1, s') ->
        (match transl_exitexpr map0 b nexits s' with
         | Error msg0 -> Error msg0
         | OK (a2, s'0) -> transl_condexpr map0 a0 a2 a1 s'0))
  | XElet (a0, b) ->
    (fun s ->
      match new_reg s with
      | Error msg0 -> Error msg0
      | OK (a1, s') ->
        (match transl_exitexpr (add_letvar map0 a1) b nexits s' with
         | Error msg0 -> Error msg0
         | OK (a2, s'0) -> transl_expr map0 a0 a1 a2 s'0))

(** val more_likely : condexpr -> stmt -> stmt -> bool **)

let more_likely = RTLgenaux.more_likely

type labelmap = node PTree.t

(** val transl_stmt :
    mapping -> stmt -> node -> node list -> labelmap -> node -> reg option ->
    node mon **)

let transl_stmtSskip _ nd _ _ _ _ = ret nd

    (** val transl_stmtSassign : ident -> S.expr -> __motiveTtransl_stmt **)

let transl_stmtSassign v b map0 nd _ _ _ _ =
   bind (find_var map0 v) (fun r -> transl_expr map0 b r nd)

    (** val transl_stmtSseq :
        S.stmt -> __motiveTtransl_stmt -> S.stmt -> __motiveTtransl_stmt -> __motiveTtransl_stmt **)

let transl_stmtSseq _ transl_stmt_s1 _ transl_stmt_s2 map0 nd nexits ngoto nret rret =
      bind (transl_stmt_s2 map0 nd nexits ngoto nret rret) (fun ns ->
        transl_stmt_s1 map0 ns nexits ngoto nret rret)

    (** val transl_stmtSifthenelse :
        S.condexpr -> S.stmt -> __motiveTtransl_stmt -> S.stmt -> __motiveTtransl_stmt -> __motiveTtransl_stmt **)

    let transl_stmtSifthenelse c _ transl_stmt_strue _ transl_stmt_sfalse map0 nd nexits ngoto nret rret =
      bind (transl_stmt_strue map0 nd nexits ngoto nret rret) (fun ntrue ->
        bind (transl_stmt_sfalse map0 nd nexits ngoto nret rret) (fun nfalse ->
          transl_condexpr map0 c ntrue nfalse))

    (** val transl_stmtSreturn : S.expr option -> __motiveTtransl_stmt **)

    let transl_stmtSreturn opt_a map0 _ _ _ nret rret =
      match opt_a with
      | Some a ->
        (match rret with
         | Some r -> transl_expr map0 a r nret
         | None ->
           error (msg ('d' ::[])))
           
      | None -> ret nret

    (** val transl_stmtSlabel : S.label -> S.stmt -> __motiveTtransl_stmt -> __motiveTtransl_stmt **)

    let transl_stmtSlabel lbl _ transl_stmt_s' map0 nd nexits ngoto nret rret =
      bind (transl_stmt_s' map0 nd nexits ngoto nret rret) (fun ns ->
        match PTree.get lbl ngoto with
        | Some n ->
          bind
            (handle_error (update_instr n (T.Inop ns))
              (error (msg ('c' :: []))))
            (fun _ -> ret ns)
        | None ->
         error (msg ('d' ::[])))

    (** val transl_stmtSgoto : S.label -> __motiveTtransl_stmt **)

    let transl_stmtSgoto lbl _ _ _ ngoto _ _ =
      match PTree.get lbl ngoto with
      | Some n -> ret n
      | None ->
        error (msg ('d' ::[]))

    (** val transl_stmtSloop : S.stmt -> __motiveTtransl_stmt -> __motiveTtransl_stmt **)

    let transl_stmtSloop _ transl_stmt_sbody map0 _ nexits ngoto nret rret =
      bind reserve_instr (fun n1 ->
        bind (transl_stmt_sbody map0 n1 nexits ngoto nret rret) (fun n2 ->
          bind (update_instr n1 (T.Inop n2)) (fun _ -> add_instr (T.Inop n2))))

    (** val transl_stmtSblock : S.stmt -> __motiveTtransl_stmt -> __motiveTtransl_stmt **)

    let transl_stmtSblock _ transl_stmt_sbody map0 nd nexits ngoto nret rret =
      transl_stmt_sbody map0 nd ((nd :: nexits)) ngoto nret rret

    (** val transl_stmtSexit : nat -> __motiveTtransl_stmt **)

    let transl_stmtSexit n _ _ nexits _ _ _ =
      transl_exit nexits n

    (** val transl_stmtSswitch : S.exitexpr -> __motiveTtransl_stmt **)

    let transl_stmtSswitch a map0 _ nexits _ _ _ =
      transl_exitexpr map0 a nexits

    (** val transl_stmtSbuiltin :
        ident builtin_res -> external_function -> S.expr builtin_arg list -> __motiveTtransl_stmt **)

    let transl_stmtSbuiltin r ef args map0 nd _ _ _ _ =
      let al = exprlist_of_expr_list (params_of_builtin_args args) in
      bind (alloc_regs map0 al) (fun rargs ->
        let args' = convert_builtin_args args rargs in
        bind (convert_builtin_res map0 (ef_sig ef).sig_res r) (fun res' ->
          bind (add_instr (T.Ibuiltin (ef, args', res', nd))) (fun n1 -> transl_exprlist map0 al rargs n1)))

    (** val transl_stmtSstore : memory_chunk -> addressing -> S.exprlist -> S.expr -> __motiveTtransl_stmt **)

    let transl_stmtSstore chunk addr al b map0 nd _ _ _ _ =
      bind (alloc_regs map0 al) (fun rl ->
        bind (alloc_reg map0 b) (fun r ->
          bind (add_instr (T.Istore (chunk, addr, rl, r, nd))) (fun no ->
            bind (transl_expr map0 b r no) (fun ns -> transl_exprlist map0 al rl ns))))

    (** val transl_stmtScall :
        ident option -> signature -> (S.expr, ident) sum -> S.exprlist -> __motiveTtransl_stmt **)

    let transl_stmtScall optid sig0 expr_ident cl map0 nd _ _ _ _ =
      match expr_ident with
      | Coq_inl b ->
        bind (alloc_reg map0 b) (fun rf ->
          bind (alloc_regs map0 cl) (fun rargs ->
            bind (alloc_optreg map0 optid) (fun r ->
              bind (add_instr (T.Icall (sig0, (Coq_inl rf), rargs, r, nd))) (fun n1 ->
                bind (transl_exprlist map0 cl rargs n1) (fun n2 -> transl_expr map0 b rf n2)))))
      | Coq_inr id ->
        bind (alloc_regs map0 cl) (fun rargs ->
          bind (alloc_optreg map0 optid) (fun r ->
            bind (add_instr (T.Icall (sig0, (Coq_inr id), rargs, r, nd))) (fun n1 ->
              transl_exprlist map0 cl rargs n1)))

    (** val transl_stmtStailcall : signature -> (S.expr, ident) sum -> S.exprlist -> __motiveTtransl_stmt **)

    let transl_stmtStailcall sig0 expr_ident cl map0 _ _ _ _ _ =
      match expr_ident with
      | Coq_inl b ->
        bind (alloc_reg map0 b) (fun rf ->
          bind (alloc_regs map0 cl) (fun rargs ->
            bind (add_instr (T.Itailcall (sig0, (Coq_inl rf), rargs))) (fun n1 ->
              bind (transl_exprlist map0 cl rargs n1) (fun n2 -> transl_expr map0 b rf n2))))
      | Coq_inr id ->
        bind (alloc_regs map0 cl) (fun rargs ->
          bind (add_instr (T.Itailcall (sig0, (Coq_inr id), rargs))) (fun n1 -> transl_exprlist map0 cl rargs n1))

    (** val transl_stmt : S.__internal_stmt -> __motiveTtransl_stmt **)

    let transl_stmt =
      S.stmt_rect transl_stmtSskip transl_stmtSassign transl_stmtSseq transl_stmtSreturn transl_stmtSlabel
        transl_stmtSgoto transl_stmtSifthenelse transl_stmtSbuiltin transl_stmtScall transl_stmtStailcall
        transl_stmtSstore transl_stmtSblock transl_stmtSexit transl_stmtSloop transl_stmtSswitch
let transl_stmt map0 s nd nexits ngoto nret rret = transl_stmt s map0 nd nexits ngoto nret rret


(** val alloc_label : label -> labelmap -> labelmap mon **)

let alloc_label lbl map0 s =
  match reserve_instr s with
  | Error msg0 -> Error msg0
  | OK (a, s') -> OK ((PTree.set lbl a map0), s')

(** val reserve_labels : stmt -> labelmap -> labelmap mon **)

let rec reserve_labels s lm =
  match s with
  | Sseq (s1, s2) ->
    (fun s0 ->
      match reserve_labels s2 lm s0 with
      | Error msg0 -> Error msg0
      | OK (a, s') -> reserve_labels s1 a s')
  | Sifthenelse (_, s1, s2) ->
    (fun s0 ->
      match reserve_labels s2 lm s0 with
      | Error msg0 -> Error msg0
      | OK (a, s') -> reserve_labels s1 a s')
  | Sloop s1 -> reserve_labels s1 lm
  | Sblock s1 -> reserve_labels s1 lm
  | Slabel (lbl, s1) ->
    (fun s0 ->
      match reserve_labels s1 lm s0 with
      | Error msg0 -> Error msg0
      | OK (a, s') -> alloc_label lbl a s')
  | _ -> (fun s0 -> OK (lm, s0))

(** val ret_reg : signature -> reg -> reg option **)

let ret_reg sig0 rd =
  if xtype_eq sig0.sig_res Xvoid then None else Some rd

(** val transl_fun : CminorSel.coq_function -> (node * reg list) mon **)

let transl_fun f s =
  match reserve_labels f.fn_body PTree.empty s with
  | Error msg0 -> Error msg0
  | OK (a, s') ->
    (match add_vars init_mapping f.CminorSel.fn_params s' with
     | Error msg0 -> Error msg0
     | OK (a0, s'0) ->
       (match add_vars (snd a0) f.fn_vars s'0 with
        | Error msg0 -> Error msg0
        | OK (a1, s'1) ->
          (match new_reg s'1 with
           | Error msg0 -> Error msg0
           | OK (a2, s'2) ->
             let orret = ret_reg f.CminorSel.fn_sig a2 in
             (match add_instr (Ireturn orret) s'2 with
              | Error msg0 -> Error msg0
              | OK (a3, s'3) ->
                (match transl_stmt (snd a1) f.fn_body a3 [] a a3 orret s'3 with
                 | Error msg0 -> Error msg0
                 | OK (a4, s'4) -> OK ((a4, (fst a0)), s'4))))))

(** val transl_function :
    CminorSel.coq_function -> coq_function Errors.res **)

let transl_function f =
  match transl_fun f init_state with
  | Error msg0 -> Errors.Error msg0
  | OK (p, s) ->
    let (nentry, rparams) = p in
    Errors.OK { fn_sig = f.CminorSel.fn_sig; fn_params = rparams;
    fn_stacksize = f.fn_stackspace; fn_code = s.st_code; fn_entrypoint =
    nentry }

(** val transl_fundef :
    CminorSel.coq_function AST.fundef -> coq_function AST.fundef Errors.res **)

let transl_fundef =
  transf_partial_fundef transl_function

(** val transl_program : CminorSel.program -> program Errors.res **)

let transl_program p =
  transform_partial_program transl_fundef p
