open BinNums

type errcode =
| MSG of char list
| CTX of positive
| POS of positive

type errmsg = errcode list

(** val msg : char list -> errmsg **)

let msg s =
  (MSG s) :: []

type 'a res =
| OK of 'a
| Error of errmsg

(** val assertion_failed : 'a1 res **)

let assertion_failed =
  Error
    (msg
      ('A'::('s'::('s'::('e'::('r'::('t'::('i'::('o'::('n'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::[])))))))))))))))))

let bind f g =
  match f with
  | OK x -> g x
  | Error msg0 -> Error msg0

(** val bind2 : ('a1, 'a2) prod res -> ('a1 -> 'a2 -> 'a3 res) -> 'a3 res **)

let bind2 f g =
  match f with
  | OK p -> let (x, y) = p in g x y
  | Error msg0 -> Error msg0

(** val mmap : ('a1 -> 'a2 res) -> 'a1 list -> 'a2 list res **)

let rec mmap f = function
| [] -> OK []
| hd :: tl ->
  (match f hd with
   | OK x ->
     (match mmap f tl with
      | OK x0 -> OK (x :: x0)
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)
