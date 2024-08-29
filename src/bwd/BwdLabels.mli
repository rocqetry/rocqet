(**
   Notes on the discrepancies with {!module:ListLabels}:
   {ul
   {- New:
      {ul
      {- {!val:prepend} was added as the {i forward} version of {!val:append}.}
      {- {!val:to_list} and {!val:of_list} were added for conversions between standard lists.}
      {- {!module:Infix} was added for the infix notation.}}}
   {- Changed:
      {ul
      {- [cons] was replaced by {!val:snoc}.}
      {- {!val:append} was replaced by a new version that performs the "textual order yoga".}
      {- All indices count from the right rather than the left:
         {!val:nth}, {!val:nth_opt}, {!val:init}, {!val:iteri}, {!val:mapi}, and {!val:filteri}.}
      {- All iteration functions work from the right rather than the left:
         {!val:iter}, {!val:map}, {!val:fold_left}, {!val:fold_right}, {!val:exists}, {!val:mem},
         {!val:find}, {!val:filter}, and other similar functions.}}}
   {- Forbidden:
     {ul
     {- Functions [rev], [rev_append], [rev_map], and [rev_map2] will {i never} be included.}}}
   {- Missing but may be added in the future:
      {ul
      {- [tl] (as [hd] for lists), [hd] (as [tl] for lists), [concat], [flatten], [concat_map].}
      {- Functions related to association lists.}
      {- Functions related to sorting.}
      {- Conversion from/to sequences.}}}}

   Please {{: https://github.com/RedPRL/ocaml-bwd/issues/new/choose}open a GitHub issue} if you want a function to be included.
   We want to make this library useful to you, too!

   @canonical Bwd.BwdLabels
*)

(** @canonical Bwd.bwd *)
type 'a t = 'a BwdDef.bwd = Emp | Snoc of 'a t * 'a

val length : 'a t -> int
val compare_lengths : 'a t -> 'a t -> int
val compare_length_with : 'a t -> len:int -> int
val is_empty : 'a t -> bool
val snoc : 'a t -> 'a -> 'a t
val nth : 'a t -> int -> 'a
val nth_opt : 'a t -> int -> 'a option
val init : len:int -> f:(int -> 'a) -> 'a t
val append : 'a t -> 'a list -> 'a t
val prepend : 'a t -> 'a list -> 'a list

(** {1 Comparison} *)

val equal : eq:('a -> 'a -> bool) -> 'a t -> 'a t -> bool
val compare : cmp:('a -> 'a -> int) -> 'a t -> 'a t -> int

(** {1 Iterators}

    Note that the iteration direction is from the right to the left,
    in the opposite direction of the corresponding functions in {!module:ListLabels}.
*)

val iter : f:('a -> unit) -> 'a t -> unit
val iteri : f:(int -> 'a -> unit) -> 'a t -> unit
val map : f:('a -> 'b) -> 'a t -> 'b t
val mapi : f:(int -> 'a -> 'b) -> 'a t -> 'b t
val filter_map : f:('a -> 'b option) -> 'a t -> 'b t

val fold_left : f:('a -> 'b -> 'a) -> init:'a -> 'b t -> 'a
(** Not tail-recursive. *)

val fold_right_map : f:('a -> 'b -> 'b * 'c) -> 'a t -> init:'b -> 'b * 'c t
val fold_right : f:('a -> 'b -> 'b) -> 'a t -> init:'b -> 'b

(** {1 Iterators on two lists}

    Note that the iteration direction is from the right to the left,
    in the opposite direction of the corresponding functions in {!module:ListLabels}.
*)

val iter2 : f:('a -> 'b -> unit) -> 'a t -> 'b t -> unit
val map2 : f:('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t

val fold_left2 : f:('a -> 'b -> 'c -> 'a) -> init:'a -> 'b t -> 'c t -> 'a
(** Not tail-recursive. *)

val fold_right2 : f:('a -> 'b -> 'c -> 'c) -> 'a t -> 'b t -> init:'c -> 'c

(** {1 List scanning}

    Note that the iteration direction is from the right to the left,
    in the opposite direction of the corresponding functions in {!module:ListLabels}.
*)

val for_all : f:('a -> bool) -> 'a t -> bool
val exists : f:('a -> bool) -> 'a t -> bool
val for_all2 : f:('a -> 'b -> bool) -> 'a t -> 'b t -> bool
val exists2 : f:('a -> 'b -> bool) -> 'a t -> 'b t -> bool
val mem : 'a -> set:'a t -> bool
val memq : 'a -> set:'a t -> bool

(** {1 List searching}

    Note that the iteration direction is from the right to the left,
    in the opposite direction of the corresponding functions in {!module:ListLabels}.
*)

val find : f:('a -> bool) -> 'a t -> 'a
val find_opt : f:('a -> bool) -> 'a t -> 'a option
val find_index : f:('a -> bool) -> 'a t -> int option
val find_map : f:('a -> 'b option) -> 'a t -> 'b option
val find_mapi : f:(int -> 'a -> 'b option) -> 'a t -> 'b option
val filter : f:('a -> bool) -> 'a t -> 'a t
val find_all : f:('a -> bool) -> 'a t -> 'a t
val filteri : f:(int -> 'a -> bool) -> 'a t -> 'a t
val partition : f:('a -> bool) -> 'a t -> 'a t * 'a t
val partition_map : f:('a -> ('b, 'c) Either.t) -> 'a t -> 'b t * 'c t

(** {1 Lists of pairs} *)

val split : ('a * 'b) t -> 'a t * 'b t
(** Not tail-recursive. *)

val combine : 'a t -> 'b t -> ('a * 'b) t

(** {1 Backward and forward lists} *)

val to_list : 'a t -> 'a list
val of_list : 'a list -> 'a t

(** {1 Infix notation} *)

module Infix : sig
  (** {1 Infix notation} *)

  val ( <: ) : 'a t -> 'a -> 'a t
  (** An alias of {!val:BwdLabels.snoc}.

      @since 2.2.0 *)

  val ( <@ ) : 'a t -> 'a list -> 'a t
  (** An alias of {!val:BwdLabels.append}.

      @since 2.2.0 *)

  val ( @> ) : 'a t -> 'a list -> 'a list
  (** An alias of {!val:BwdLabels.prepend}.

      @since 2.2.0 *)

  (** {1 Deprecated infix notation} *)

  val ( #< ) : 'a t -> 'a -> 'a t
  [@@ocaml.alert deprecated "Use (<:) instead"]
  (** An alias of {!val:BwdLabels.snoc}.

      @deprecated Use [(<:)] *)

  val ( <>< ) : 'a t -> 'a list -> 'a t
  [@@ocaml.alert deprecated "Use (<@) instead"]
  (** An alias of {!val:BwdLabels.append}.

      @deprecated Use [(<@)] *)

  val ( <>> ) : 'a t -> 'a list -> 'a list
  [@@ocaml.alert deprecated "Use (@>) instead"]
  (** An alias of {!val:BwdLabels.prepend}.

      @deprecated Use [(@>)] *)
end

(**/**)

module Notation : module type of Infix
[@@ocaml.alert deprecated "Use BwdLabels.Infix instead"]
