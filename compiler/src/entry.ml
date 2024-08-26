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

let metadata name = 
  Metadata.open_metadata name; 
  PluginScopes.push
    PluginCmdScope.
      {
         name; 
         command = PluginCmd.MetaData; 
         close = Metadata.close_metadata;
      }

let definition ~name ?body_type body_expr =
  Definition.add_definition ~name ?body_type body_expr

let frecursion ~(name : Names.Id.t) ~(inductive : Libnames.qualid)
    ~(motive : Constrexpr.constr_expr) ~(suffix : RecKind.t) =
  Recursion.open_recursion ~name ~inductive ~motive ~suffix ~arguments:[];
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
  Theorem.open_theorem_extension ~name

(* FProof *)
let fproof () = Theorem.start_proving ()

(* FQed *)
let fqed () = Theorem.end_proving ()
