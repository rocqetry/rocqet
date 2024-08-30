open Env
open Types

(* Exhaustiveness checking *)
let check_exhaustive ~name ~inductive ~handlers =
  let constructors =
    let _, constructors =
      inductive |> List.hd |> fst |> VernacInductive.extract_type_and_cstrs
    in
    constructors |> List.map fst
  in
  constructors
  |> List.iter (fun constructor ->
         match List.assoc_opt constructor handlers with
         | Some _ -> ()
         | None ->
             let info =
               Printf.sprintf
                 "The pattern matching in %s is not exhaustive. Here is an \
                  example of a case that has no handler: %s"
                 (Names.Id.to_string name)
                 (Names.Id.to_string constructor)
             in
             Errors.fail ~info)

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

let rec check ~(further_base : Linkage.t) ~(base : Linkage.t) =
  (* Physical equality? *)
  (* further_base = base *)
  (* TODO: keep track of the `further_base` in a linkage *)
  if Names.Id.equal further_base.name base.name then ()
  else
    (* This should not only be base.
       There is also a path for further binding *)
    match base.base with
    | None ->
        Errors.fail
          ~info:
            "Type Error: further binding doesn't preserve inheritance \
             structure."
    | Some base -> check ~further_base ~base

let check_further_binding_structure context =
  let further_bases =
    let further = Context.further_bound_linkage context in
    List.map (fun (linkage : Linkage.t) -> linkage.base) further
  in
  let base = Context.base_linkage context in
  further_bases
  |> List.iter (fun further_base ->        
      match (further_base, base) with
      | Some further_base, Some base -> check ~further_base ~base
      | Some _, None ->
          Errors.fail
            ~info:
              "Type Error: further binding doesn't preserve inheritance structure."
      | None, Some _ -> ()
      | None, None -> ())
