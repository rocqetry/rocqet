(* From https://github.com/tlringer/plugin-tutorial/blob/main/src/termutils.ml *)

(** Get the global environment *)
let _global_env () =
  let env = Global.env () in
  Evd.from_env env, env

(** Push a local binding to an environment *)
let _push_local (n, t) env =
  EConstr.push_rel Context.Rel.Declaration.(LocalAssum (n, t)) env

(** Declare a toplevel binding *)
let _define name body sigma =
  let udecl = UState.default_univ_decl in
  let scope = Locality.Global Locality.ImportDefaultBehavior in
  let kind = Decls.(IsDefinition Definition) in
  let cinfo = Declare.CInfo.make ~name ~typ:None () in
  let info = Declare.Info.make ~scope ~kind  ~udecl ~poly:false () in
  Declare.declare_definition ~info ~cinfo ~opaque:false ~body sigma |> ignore


(** When you first start using a plugin, if you want to manipulate terms
 in an interesting way, you need to move from the external representation
 of terms to the internal representation of terms. This does that for you. *)
let _internalize env trm sigma =
  Constrintern.interp_constr_evars env sigma trm


(* Interface for what a codegen backend should be *)
module type S = sig
  val define_module : Names.Id.t -> unit
  val dump_output : string -> unit
end
