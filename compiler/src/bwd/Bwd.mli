type 'a bwd = 'a BwdDef.bwd = Emp | Snoc of 'a bwd * 'a

module Bwd : module type of BwdNoLabels
(** This module is similar to {!module:List} but for backward lists. *)

module BwdLabels : module type of BwdLabels
(** This module is similar to {!module:ListLabels} but for backward lists. *)

(**/**)

module BwdNotation : module type of BwdNotation
[@@ocaml.alert deprecated "Use Bwd.Infix instead"]
(** An alias of {!module:Bwd.Infix} for infix notation. *)
