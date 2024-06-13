(* "Typechecking" for families

   This ensures that a "family structure" is preserved across nested
   inheritance boundaries.

   In particular, say we have the following program:
   ```
   Family Salad.
   FEnd Salad.

   Family SaladX extends Salad.
   FEnd SaladX.

   Family Dataflow.
       Family Lang extends Salad.
       FEnd Lang.
   FEnd Dataflow.

   Family DataflowX extends Dataflow.
       Family Lang extends SaladX.
       FEnd Lang.
   FEnd DataflowX.
   ```

   Becuase `DataflowX.Lang` further binds `Dataflow.Lang`, we want to ensure that
   `SaladX` extends (or is equal to) `Salad`.

   This check ensures that the structure of `Dataflow.Lang` is preserved across
   the nested inheritance boundary (in particular, further binding). *)

open Env
open Types

let rec check ~further_base ~(base : Linkage.t) =
  (* Physical equality? *)
  if further_base = base then ()
  else
    match base.base with
    | None ->
        Errors.fail
          ~info:
            "Type Error: further binding doesn't preserve inheritance \
             structure."
    | Some base -> check ~further_base ~base

let check_further_binding_structure context =
  let further_base =
    let further = Context.further_bound_linkage context in
    Option.bind further (fun (linkage : Linkage.t) -> linkage.base)
  in
  let base = Context.base_linkage context in
  match (further_base, base) with
  | Some further_base, Some base -> check ~further_base ~base
  (* | Some _, None | None, Some _ -> 
     Errors.fail
          ~info:
            "Type Error: further binding doesn't preserve inheritance \
             structure."*)
  | _, _ -> ()
