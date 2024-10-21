open Types
open Env

(* The entry point to the language *)

let finductive inductive_definitions =
  PluginScopes.ensure_in_scope ~scope:PluginCmd.Family;
  Inductive.add_inductive_definition inductive_definitions

let fend scope_name =
  match PluginScopes.pop scope_name with
  | None -> Errors.fail ~info:"There is no open scope"
  | Some scope ->
      let PluginCmdScope.{ close; _ } = scope in
      close ()

let family name =
  Family.open_family name;
  PluginScopes.push
    PluginCmdScope.
      { name; command = PluginCmd.Family; close = Family.close_family }

let family_extends ~derived ~base =
  Family.open_family_with_base ~base ~name:derived;
  PluginScopes.push
    PluginCmdScope.
      {
        name = derived;
        command = PluginCmd.Family;
        close = Family.close_family;
      }

let family_extends_list ~derived ~bases =
  let name = derived in
  Family.open_family_with_base_list ~name ~bases;
  PluginScopes.push
    PluginCmdScope.
      { name; command = PluginCmd.Family; close = Family.close_family }

let metadata name =
  Metadata.open_metadata name;
  PluginScopes.push
    PluginCmdScope.
      { name; command = PluginCmd.MetaData; close = Metadata.close_metadata }

let definition ~name ?body_type body_expr =
  Definition.add_definition ~name ?body_type body_expr

let opaque_definition ~name ~body_type ~body_expr =
  Definition.add_opaque_definition ~name ~body_type ~body_expr

let foverride = Definition.override 

let frecursion ~(name : Names.Id.t) ~(inductive : Libnames.qualid)
    ~(motive : Constrexpr.constr_expr) ~(suffix : RecKind.t) =
  Recursion.open_recursion ~name ~inductive_path:inductive ~motive ~suffix
    ~arguments:[];
  PluginScopes.push
    PluginCmdScope.
      { name; command = PluginCmd.Recursion; close = Recursion.close_recursion }

let frecursion_extension ~(name : Names.Id.t) =
  Recursion.open_recursion_extension ~name;
  PluginScopes.push
    PluginCmdScope.
      { name; command = PluginCmd.Recursion; close = Recursion.close_recursion }

let frecursion_handler = Recursion.add_handler

let frecursion_elegant name args =
  Recursion.elegant name args;
  PluginScopes.push
    PluginCmdScope.
      { name; command = PluginCmd.Recursion; close = Recursion.close_recursion }

let finduction ~(name : Names.Id.t) ~(inductive : Libnames.qualid)
    ~(motive : Constrexpr.constr_expr) =
  Theorem.open_theorem ~name ~inductive ~motive;
  PluginScopes.push
    PluginCmdScope.
      { name; command = PluginCmd.Induction; close = Theorem.close_theorem }

let finduction_extension ~(name : Names.Id.t) =
  Theorem.open_theorem_extension ~name;
  PluginScopes.push
    PluginCmdScope.
      { name; command = PluginCmd.Induction; close = Theorem.close_theorem }

(* FProof *)
let fproof () = Theorem.start_proving ()
let fproof_lemma = Lemma.prepare_proving
let flemma name t = Lemma.open_flemma name t
(* PluginScopes.push
   PluginCmdScope.
     { name; command = PluginCmd.Lemma; close = Lemma.close_flemma }*)
let foverride_lemma = Lemma.override

let close_flemma = Lemma.close_flemma
let display_plugin_scope = PluginScopes.display

let closing_fact = Closing_fact.add

let inherit_name = Inheritance.inherit_name

let open_trait_with_base ~name ~base = Trait.open_with_base ~name ~base
