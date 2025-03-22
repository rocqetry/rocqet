(* Custom tactics for family polymorphism *)
open Types

(* selfnames -> (function, handler list) *)
let extract_handlers_names names =
  let context = Env.Context.get () in
  names
  |> List.filter_map (fun name ->
         if Naming.is_self_qualid name then
           name |> Naming.remove_self_qualid
           |> Env.Context.lookup_linkage_elem context
           |> Option.map fst
           |> Option.map (function
                | LinkageElem.RecursorDefinition
                    { names; handlers; handlers_table; behaviour_table; _ } ->
                    let prefix = Naming.extract_prefix name in
                    let handlers = handlers |> List.concat_map snd in
                    Some
                      (prefix, names, handlers, handlers_table, behaviour_table)
                | _ -> None)
           |> Option.flatten
         else None)

let handlers_to_computational_axiom handlers =
  let context = Env.Context.get () in
  handlers
  |> List.concat_map (fun (prefix, _recursor_names, handlers, _, table) ->
         handlers
         |> List.map (fun constructor_name ->
                let name = List.assoc constructor_name table in
                let qualid = Naming.qualid_point prefix name in
                Resolver.resolve_qualid ~context ~qualid))

let handlers_to_case_definitions handlers =
  let context = Env.Context.get () in
  handlers
  |> List.concat_map (fun (prefix, _recursors, handlers, table, _) ->
         handlers
         |> List.map (fun case ->
                let name = List.assoc case table in
                let qualid = Naming.qualid_point prefix name in
                Resolver.resolve_qualid ~context ~qualid))

let idtac =
  let open Ltac_plugin in
  let idtac =
    CAst.make
      (Tacexpr.TacArg
         (Tacexpr.TacCall
            (CAst.make
               (Libnames.qualid_of_ident (Names.Id.of_string "idtac"), []))))
  in
  Tacinterp.interp idtac

(* repeat ( rewrite ... in * || ...) *)
let generate_rewrites computational_axioms =
  let open Ltac_plugin in
  let each_rewrite_tactic (each_eq : Libnames.qualid) =
    (* this section can check g_tactic.mlg *)
    let rewrite_atom = Constrexpr_ops.mkRefC each_eq in
    let l =
      [
        (true, Equality.Precisely 1, (None, (rewrite_atom, Tactypes.NoBindings)));
      ]
    in
    let cl = { Locus.onhyps = None; concl_occs = Locus.AllOccurrences } in
    let t = None in
    let rewrite_tacatom =
      CAst.make @@ Tacexpr.TacAtom (TacRewrite (false, l, cl, t))
    in
    Tacinterp.interp rewrite_tacatom
  in
  let all_rewrite_tactics = List.map each_rewrite_tactic computational_axioms in
  (*let tacfail =
      CAst.make (Tacexpr.TacFail (TacLocal,Locus.ArgArg 0,[]))
    in *)
  (* TODO: We actually wanto to do try (rewrite ...) ...  *)
  let union_rewrites =
    List.fold_right
      (fun l r -> Tacticals.tclORELSE l r)
      all_rewrite_tactics idtac
  in
  (* let repeat_union_rewrites = CAst.make (TacRepeat union_rewrites) in  *)
  union_rewrites

(* (unfold ... ) ...  *)
let generate_unfolds unfold case_definitions =
  let open Ltac_plugin in
  let each_rewrite_tactic (each_eq : Libnames.qualid) =
    let each_eq = Tacexpr.TacCall (CAst.make (each_eq, [])) in
    let tactic =
      CAst.make
        (Tacexpr.TacArg
           (Tacexpr.TacCall
              (CAst.make
                 ( Libnames.qualid_of_ident (Names.Id.of_string unfold),
                   [ each_eq ] ))))
    in
    Tacinterp.interp tactic
  in
  let all_unfold_tactics = List.map each_rewrite_tactic case_definitions in
  let union_unfolds =
    List.fold_right (fun l r -> Tacticals.tclTHEN l r) all_unfold_tactics idtac
  in
  union_unfolds

(* fsimpl *)
let fsimpl () =
  Proofview.Goal.enter (fun gl ->
      let goal = Proofview.Goal.concl gl in
      let env = Proofview.Goal.env gl in
      let evar_map = Evd.from_env env in

      let goal_names = Termutils.constants_in_econstr evar_map goal in

      let handlers = extract_handlers_names goal_names in

      let computational_axioms = handlers_to_computational_axiom handlers in

      let case_definitions = handlers_to_case_definitions handlers in

      let rewrites = generate_rewrites computational_axioms in

      let unfolds = generate_unfolds "__funfold" case_definitions in

      let names =
        computational_axioms
        |> List.map Pretty.pretty_qualid
        |> String.concat "\n"
      in
      Feedback.msg_info (Pp.str names);

      let names =
        case_definitions |> List.map Pretty.pretty_qualid |> String.concat "\n"
      in
      Feedback.msg_info (Pp.str names);

      Tacticals.tclTHEN rewrites unfolds)

let fsimpl_star () =
  Proofview.Goal.enter (fun gl ->
      let goal = Proofview.Goal.concl gl in
      let hyps : EConstr.t list =
        gl |> Proofview.Goal.hyps
        |> List.concat_map
             (fun
               (binding :
                 (Evd.econstr, Evd.econstr) Context.Named.Declaration.pt)
             ->
               match binding with
               | Context.Named.Declaration.LocalAssum (_, ty) -> [ ty ]
               | Context.Named.Declaration.LocalDef (_, tm, ty) -> [ tm; ty ])
      in
      let env = Proofview.Goal.env gl in
      let evar_map = Evd.from_env env in

      let goal_names = Termutils.constants_in_econstr evar_map goal in
      let hyps_names =
        hyps |> List.concat_map (Termutils.constants_in_econstr evar_map)
      in
      let all_names = goal_names @ hyps_names in

      let handlers = extract_handlers_names all_names in

      let computational_axioms = handlers_to_computational_axiom handlers in

      let case_definitions = handlers_to_case_definitions handlers in

      let rewrites = generate_rewrites computational_axioms in

      let unfolds = generate_unfolds "__funfold_star" case_definitions in

      let names =
        computational_axioms
        |> List.map Pretty.pretty_qualid
        |> String.concat "\n"
      in
      Feedback.msg_info (Pp.str names);

      let names =
        case_definitions |> List.map Pretty.pretty_qualid |> String.concat "\n"
      in
      Feedback.msg_info (Pp.str names);

      Tacticals.tclTHEN rewrites unfolds)

let fsimpl_in h =
  Proofview.Goal.enter (fun gl ->
      let hyps : EConstr.t list =
        gl |> Proofview.Goal.hyps
        |> List.filter_map
             (fun
               (binding :
                 (Evd.econstr, Evd.econstr) Context.Named.Declaration.pt)
             ->
               match binding with
               | Context.Named.Declaration.LocalAssum ({ binder_name; _ }, ty)
                 when Names.Id.equal binder_name h ->
                   Some [ ty ]
               | Context.Named.Declaration.LocalDef ({ binder_name; _ }, tm, ty)
                 when Names.Id.equal binder_name h ->
                   Some [ tm; ty ]
               | _ -> None)
        |> List.concat
      in
      let env = Proofview.Goal.env gl in
      let evar_map = Evd.from_env env in

      let hyps_names =
        hyps |> List.concat_map (Termutils.constants_in_econstr evar_map)
      in

      let handlers = extract_handlers_names hyps_names in

      let computational_axioms = handlers_to_computational_axiom handlers in

      let case_definitions = handlers_to_case_definitions handlers in

      let rewrites =
        let open Ltac_plugin in
        let each_rewrite_tactic (each_eq : Libnames.qualid) =
          let each_eq = Tacexpr.TacCall (CAst.make (each_eq, [])) in
          let h =
            Tacexpr.TacCall (CAst.make (Libnames.qualid_of_ident h, []))
          in
          let tactic =
            CAst.make
              (Tacexpr.TacArg
                 (Tacexpr.TacCall
                    (CAst.make
                       ( Libnames.qualid_of_ident
                           (Names.Id.of_string "__frewrite_in"),
                         [ each_eq; h ] ))))
          in
          Tacinterp.interp tactic
        in
        let all_rewrite_tactics =
          List.map each_rewrite_tactic computational_axioms
        in
        let union_rewrites =
          List.fold_right
            (fun l r -> Tacticals.tclTHEN l r)
            all_rewrite_tactics idtac
        in
        union_rewrites
      in

      let unfolds =
        let open Ltac_plugin in
        let each_rewrite_tactic (each_eq : Libnames.qualid) =
          let each_eq = Tacexpr.TacCall (CAst.make (each_eq, [])) in
          let h =
            Tacexpr.TacCall (CAst.make (Libnames.qualid_of_ident h, []))
          in
          let tactic =
            CAst.make
              (Tacexpr.TacArg
                 (Tacexpr.TacCall
                    (CAst.make
                       ( Libnames.qualid_of_ident
                           (Names.Id.of_string "__funfold_in"),
                         [ each_eq; h ] ))))
          in
          Tacinterp.interp tactic
        in
        let all_unfold_tactics =
          List.map each_rewrite_tactic case_definitions
        in
        let union_unfolds =
          List.fold_right
            (fun l r -> Tacticals.tclTHEN l r)
            all_unfold_tactics idtac
        in
        union_unfolds
      in

      let names =
        computational_axioms
        |> List.map Pretty.pretty_qualid
        |> String.concat "\n"
      in
      Feedback.msg_info (Pp.str names);

      let names =
        case_definitions |> List.map Pretty.pretty_qualid |> String.concat "\n"
      in
      Feedback.msg_info (Pp.str names);

      Tacticals.tclTHEN rewrites unfolds)

let extract_constructors names =
  let context = Env.Context.get () in
  names
  |> List.filter_map (fun name ->
         if Naming.is_self_qualid name then
           name |> Naming.remove_self_qualid
           |> Env.Context.lookup_linkage_elem context
           |> Option.map fst
           |> Option.map (function
                | LinkageElem.InductiveDefinition { inductive; _ } ->
                    let constructors =
                      inductive |> List.map fst
                      |> List.map VernacInductive.extract_type_and_cstrs
                      |> List.concat_map (fun (_, constructors) ->
                             List.map fst constructors)
                    in
                    let prefix = name |> Naming.extract_prefix in
                    let qualify name =
                      let qualid = Naming.qualid_point prefix name in
                      Resolver.resolve_qualid ~context ~qualid
                    in
                    let constructors = constructors |> List.map qualify in
                    Some constructors
                | _ -> None)
           |> Option.flatten
         else None)

let generate_apply apply_cases =
  let open Ltac_plugin in
  let apply = "__fconstructor" in
  let each_rewrite_tactic (each_eq : Libnames.qualid) =
    let each_eq = Tacexpr.TacCall (CAst.make (each_eq, [])) in
    let tactic =
      CAst.make
        (Tacexpr.TacArg
           (Tacexpr.TacCall
              (CAst.make
                 ( Libnames.qualid_of_ident (Names.Id.of_string apply),
                   [ each_eq ] ))))
    in
    Tacinterp.interp tactic
  in
  let all_apply_tactics = List.map each_rewrite_tactic apply_cases in
  List.fold_right
    (fun l r -> Tacticals.tclOR l r)
    all_apply_tactics
    (Tacticals.tclFAIL @@ Pp.str "No constructor found")

let fconstructor () =
  Proofview.Goal.enter (fun gl ->
      let goal = Proofview.Goal.concl gl in
      let env = Proofview.Goal.env gl in
      let evar_map = Evd.from_env env in

      let names = Termutils.constants_in_econstr evar_map goal in

      let constructors = names |> extract_constructors |> List.concat in
      generate_apply constructors)

let fdiscriminate () =
  Proofview.Goal.enter (fun _gl ->
      let open Ltac_plugin in
      let tactic =
      (* let discriminate = Tacexpr.TacCall (CAst.make (Libnames.qualid_of_ident (Names.Id.of_string "cheat"), [])) in*)
      (* let g = Tacexpr.TacApply (false, true, failwith "", failwith "") in   *)
      CAst.make
        (Tacexpr.TacArg
           (Tacexpr.TacCall
              (CAst.make
                 ( Libnames.qualid_of_ident (Names.Id.of_string "__cheat"),
                   [ ] ))))
      in            
      Tacinterp.interp tactic)

(*
let fhint ~(c1:  Libnames.qualid) ~(c2 : Libnames.qualid) =
  (* if c1 = c2 then fail *)
  let module B = Backend.Vernac in
  let open Env in 
  let module_name = Naming.fresh_name ~prefix:"FHint" in
  let field_name = Naming.extract_path_base c1 in
  let context = Context.get () in
  let compiled_context, parameters = Codegen.compile_linkage_context ~field_name context in
  let name =
     let (^^) l r = Names.Id.of_string (Names.Id.to_string l ^ Names.Id.to_string r) in
     Naming.extract_path_base c1 ^^ Names.Id.of_string "_not_" ^^ Naming.extract_path_base c2
  in 
  let closing_fact_params: Names.Id.t list ref = ref [] in
  let compiled_signature =
    B.run @@
    B.define_module
      ~module_name
      ~parameters
      ~body:(fun _ ->
        let open Constrexpr_ops in
         let constructor_params_c1, fully_applied_constr_c1 =
           Termutils.extract_variables_and_apply (mkRefC c1)
         in
         let constructor_params_c2, fully_applied_constr_c2 =
           Termutils.extract_variables_and_apply (mkRefC c2)
         in                       
         let arguments = constructor_params_c1 @ constructor_params_c2 in

         let extract_name ({ CAst.v = n; _ } : Names.lname) : Names.Id.t =
           match n with
           | Names.Name n -> n
           | _ -> Errors.fail ~info:"Expected non anonymous argument"
         in
         closing_fact_params :=
           arguments
           |> List.concat_map (fun ((ns, _, _), _) -> ns |> List.map extract_name);
       
         let eq_cstr = mkRefC @@ Libnames.qualid_of_ident @@ Names.Id.of_string "eq" in
         let equation = mkAppC (eq_cstr, [ fully_applied_constr_c1; fully_applied_constr_c2 ]) in
         (* TODO fix this: wrong type *)
         let closed_equation =
           List.fold_right
             (fun (a, b, c) body -> mkProdC (a, b, c, body))
             (List.map fst arguments) equation
         in
         B.postulate_axiom ~name ~ty:closed_equation
      )
  in
  let plain = true in
  let default_ctx_params =
    context |> Context.family_linkage |> function
    | { default_ctx_params; _ } -> default_ctx_params
  in
  let type_name = module_name in (* dummy *)
  let (script : Ltac_plugin.Tacexpr.raw_tactic_expr) = failwith "" in
  let f = Ltac_plugin.Tacexpr.
  let elem =
    LinkageElem.ClosingFact
      {
        type_name;
        compiled_context;
        compiled_signature;
        default_ctx_params;
        script;
        plain;
      }
  in
  Context.add_field ~name ~elem

*)  

(*Closing Fact tm_var_not_tm_abs : forall i x body, tm_var i = tm_abs x body -> False
    by { discriminate }. *)

(*
Closing Fact tm_var_not_tm_abs : forall i x body, tm_var i = tm_abs x body -> False
    by { intros until body; intros H; discriminate; eauto }.
*)


