open AST
open BinNums
open Coqlib
open Datatypes
open Errors
open FSetAVL
open Int0
open Kildall
open LTL
open Lattice
open Linear
open Maps
open Op
open Ordered

module DS = Dataflow_Solver(LBoolean)(NodeSetForward)

(** val reachable_aux : LTL.coq_function -> bool PMap.t option **)

let reachable_aux f =
  DS.fixpoint f.LTL.fn_code successors_block (fun _ r -> r) f.fn_entrypoint
    true

(** val reachable : LTL.coq_function -> bool PMap.t **)

let reachable f =
  match reachable_aux f with
  | Some rs -> rs
  | None -> PMap.init true

(** val enumerate_aux : LTL.coq_function -> bool PMap.t -> node list **)

let enumerate_aux = Linearizeaux.enumerate_aux

module Nodeset = Make(OrderedPositive)

(** val nodeset_of_list : node list -> Nodeset.t -> Nodeset.t res **)

let rec nodeset_of_list l s =
  match l with
  | [] -> OK s
  | hd :: tl ->
    if Nodeset.mem hd s
    then Error
           (msg
             ('L'::('i'::('n'::('e'::('a'::('r'::('i'::('z'::('e'::(':'::(' '::('d'::('u'::('p'::('l'::('i'::('c'::('a'::('t'::('e'::('s'::(' '::('i'::('n'::(' '::('e'::('n'::('u'::('m'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::[])))))))))))))))))))))))))))))))))))))
    else nodeset_of_list tl (Nodeset.add hd s)

(** val check_reachable_aux :
    bool PMap.t -> Nodeset.t -> bool -> node -> bblock -> bool **)

let check_reachable_aux reach s ok pc _ =
  if PMap.get pc reach then (&&) ok (Nodeset.mem pc s) else ok

(** val check_reachable :
    LTL.coq_function -> bool PMap.t -> Nodeset.t -> bool **)

let check_reachable f reach s =
  PTree.fold (check_reachable_aux reach s) f.LTL.fn_code true

(** val enumerate : LTL.coq_function -> node list res **)

let enumerate f =
  let reach = reachable f in
  let enum = enumerate_aux f reach in
  (match nodeset_of_list enum Nodeset.empty with
   | OK x ->
     if check_reachable f reach x
     then OK enum
     else Error
            (msg
              ('L'::('i'::('n'::('e'::('a'::('r'::('i'::('z'::('e'::(':'::(' '::('w'::('r'::('o'::('n'::('g'::(' '::('e'::('n'::('u'::('m'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::[])))))))))))))))))))))))))))))
   | Error msg0 -> Error msg0)

(** val starts_with : label -> code -> bool **)

module S = LTL
module T = Linear

let starts_with_labelLlabel lbl' lbl =
      (peq lbl lbl')

    (** val starts_with_labelLop :
        operation -> mreg list -> mreg -> __motiveTstarts_with_label **)

    let starts_with_labelLop _ _ _ _ =
      false 

    (** val starts_with_labelLgetstack :
        slot -> coq_Z -> typ -> mreg -> __motiveTstarts_with_label **)

    let starts_with_labelLgetstack _ _ _ _ _ =
      false 

    (** val starts_with_labelLsetstack :
        mreg -> slot -> coq_Z -> typ -> __motiveTstarts_with_label **)

    let starts_with_labelLsetstack _ _ _ _ _ =
      false

    (** val starts_with_labelLcond :
        condition -> mreg list -> T.label -> __motiveTstarts_with_label **)

    let starts_with_labelLcond _ _ _ _ =
      false 

    (** val starts_with_labelLreturn : __motiveTstarts_with_label **)

    let starts_with_labelLreturn _ =
      false 

    (** val starts_with_labelLgoto : T.label -> __motiveTstarts_with_label **)

    let starts_with_labelLgoto _ _ =
      false 

    (** val starts_with_labelLstore :
        memory_chunk -> addressing -> mreg list -> mreg ->
        __motiveTstarts_with_label **)

    let starts_with_labelLstore _ _ _ _ _ =
      false

    (** val starts_with_labelLload :
        memory_chunk -> addressing -> mreg list -> mreg ->
        __motiveTstarts_with_label **)

    let starts_with_labelLload _ _ _ _ _ =
      false 

    (** val starts_with_labelLjumptable :
        mreg -> T.label list -> __motiveTstarts_with_label **)

    let starts_with_labelLjumptable _ _ _ =
      false

    (** val starts_with_labelLcall :
        signature -> (mreg, ident) sum -> __motiveTstarts_with_label **)

    let starts_with_labelLcall _ _ _ =
      false

    (** val starts_with_labelLtailcall :
        signature -> (mreg, ident) sum -> __motiveTstarts_with_label **)

    let starts_with_labelLtailcall _ _ _ =
      false

    let starts_with_labelLbuiltin _ _ _ lbl  = false 

    (** val starts_with_label :
        T.__internal_instruction -> __motiveTstarts_with_label **)

    let starts_with_label =
      T.instruction_rect starts_with_labelLop starts_with_labelLcond
        starts_with_labelLlabel starts_with_labelLgoto starts_with_labelLreturn
        starts_with_labelLgetstack starts_with_labelLsetstack starts_with_labelLbuiltin
        starts_with_labelLcall starts_with_labelLtailcall        
        starts_with_labelLjumptable starts_with_labelLload starts_with_labelLstore 

let rec starts_with lbl = function
    | [] -> false
    | i :: k' ->
      (match starts_with_label i lbl with
       | true -> true
       | false -> starts_with lbl k')    

(** val add_branch : label -> code -> code **)

let add_branch s k =
  if starts_with s k then k else (Lgoto s) :: k

(** val linearize_block : bblock -> code -> code **)

(** val translate_instrLop :
        operation -> mreg list -> mreg -> __motiveTtranslate_instr **)

    let translate_instrLop op args res0 f k =
      T.Lop (op, args, res0) :: (f k)

    (** val translate_instrLgetstack :
        slot -> coq_Z -> typ -> mreg -> __motiveTtranslate_instr **)

    let translate_instrLgetstack sl ofs ty r f k =
      T.Lgetstack (sl, ofs, ty, r) :: (f k)

    (** val translate_instrLsetstack :
        mreg -> slot -> coq_Z -> typ -> __motiveTtranslate_instr **)

    let translate_instrLsetstack r sl ofs ty f k =
      T.Lsetstack (r, sl, ofs, ty) :: (f k)

    (** val translate_instrLbranch : S.node -> __motiveTtranslate_instr **)

    let translate_instrLbranch s _ k =
      add_branch s k

    (** val translate_instrLcond :
        condition -> mreg list -> S.node -> S.node -> __motiveTtranslate_instr **)

    let translate_instrLcond cond args s1 s2 _ k =
      match starts_with s1 k with
      | true ->
        (T.Lcond ((negate_condition cond), args, s2)) :: (add_branch s1 k)
      | false -> (T.Lcond (cond, args, s1)) :: (add_branch s2 k)

    (** val translate_instrLreturn : __motiveTtranslate_instr **)

    let translate_instrLreturn f k =
      T.Lreturn :: (f k)

    (** val translate_instrLstore :
        memory_chunk -> addressing -> mreg list -> mreg -> __motiveTtranslate_instr **)

    let translate_instrLstore chunk addr args src f k =
      (T.Lstore (chunk, addr, args, src)) :: (f k)

    (** val translate_instrLload :
        memory_chunk -> addressing -> mreg list -> mreg -> __motiveTtranslate_instr **)

    let translate_instrLload chunk addr args dst f k =
      (T.Lload (chunk, addr, args, dst)) :: (f k)

    (** val translate_instrLjumptable :
        mreg -> S.node list -> __motiveTtranslate_instr **)

    let translate_instrLjumptable args tbl _ k =
      T.Ljumptable (args, tbl) :: k

    (** val translate_instrLcall :
        signature -> (mreg, ident) sum -> __motiveTtranslate_instr **)

    let translate_instrLcall sig0 ros f k =
      T.Lcall (sig0, ros) :: (f k)

    (** val translate_instrLtailcall :
        signature -> (mreg, ident) sum -> __motiveTtranslate_instr **)

    let translate_instrLtailcall sig0 ros _ k =
      T.Ltailcall (sig0, ros) :: k

    (* TODO *)
    let translate_instrLbuiltin ef args res0 f k =
      (Lbuiltin (ef, args, res0)) :: (f k)

    (** val translate_instr :
        S.__internal_instruction -> __motiveTtranslate_instr **)

    let translate_instr =
      S.instruction_rect translate_instrLop translate_instrLgetstack
        translate_instrLsetstack translate_instrLbranch translate_instrLcond
        translate_instrLreturn translate_instrLcall translate_instrLtailcall
        translate_instrLjumptable translate_instrLload translate_instrLstore translate_instrLbuiltin

    (** val linearize_block : S.bblock -> T.code -> T.code **)

    let rec linearize_block b k =
      match b with
      | [] -> k
      | i :: b' -> translate_instr i (linearize_block b') k


(** val linearize_node : LTL.coq_function -> node -> code -> code **)

let linearize_node f pc k =
  match PTree.get pc f.LTL.fn_code with
  | Some b -> (Llabel pc) :: (linearize_block b k)
  | None -> k

(** val linearize_body : LTL.coq_function -> node list -> code **)

let linearize_body f enum =
  list_fold_right (linearize_node f) enum []

(** val transf_function : LTL.coq_function -> coq_function res **)

let transf_function f =
  match enumerate f with
  | OK x ->
    OK { fn_sig = f.LTL.fn_sig; fn_stacksize = f.LTL.fn_stacksize; fn_code =
      (add_branch f.fn_entrypoint (linearize_body f x)) }
  | Error msg0 -> Error msg0

(** val transf_fundef : LTL.fundef -> fundef res **)

let transf_fundef f =
  transf_partial_fundef transf_function f

(** val transf_program : LTL.program -> program res **)

let transf_program p =
  transform_partial_program transf_fundef p
