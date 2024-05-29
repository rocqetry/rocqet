open Types

let unique_id =
  let counter = ref 0 in
  fun () ->
    incr counter;
    !counter

let fresh_name ~prefix =
  let time_stamp = string_of_int @@ unique_id () in
  Names.Id.of_string (prefix ^ "回" ^ time_stamp)

(* Referencing the name of a module *)
module ModuleTerm = struct
  type t = Libnames.qualid
end

(* Referencing a module type *)
module ModuleType = struct
  type t = Libnames.qualid
end

(* The interface for a code generation backend *)
module type S = sig
  val assume_parameter : name:Names.Id.t -> ty:Constrexpr.constr_expr -> unit

  val define_moduletype :
    name:Names.Id.t ->
    parameters:(Names.Id.t * Constrexpr.module_ast) list ->
    body:(ModuleTerm.t list -> unit) ->
    Names.ModPath.t
end

(** Code generation backend by mutating internal state with declarations *)
module DeclareBackend = struct
  (** Declare a toplevel binding *)
  let define name body sigma =
    let udecl = UState.default_univ_decl in
    let scope = Locality.Global Locality.ImportDefaultBehavior in
    let kind = Decls.(IsDefinition Definition) in
    let cinfo = Declare.CInfo.make ~name ~typ:None () in
    let info = Declare.Info.make ~scope ~kind ~udecl ~poly:false () in
    Declare.declare_definition ~info ~cinfo ~opaque:false ~body sigma |> ignore

  (** Push a local binding to an environment *)
  let push_local (n, t) env =
    EConstr.push_rel Context.Rel.Declaration.(LocalAssum (n, t)) env
end

(** Code generation backend by writing and interpreting Vernacular commands explicitly *)
module VernacBackend = struct
  type expr =
    | Original of Vernacexpr.vernac_expr
    | TrySilent of Vernacexpr.vernac_expr
    | Thunk of (unit -> expr list)

  type 'a t = expr list * 'a

  let emit_vernac_expr ~silence (orgexpr : Vernacexpr.vernac_expr) : unit =
    let () =
      Feedback.msg_notice
      @@
      let open Pp in
      Ppvernac.pr_vernac_expr orgexpr ++ str "."
    in
    let open Vernacexpr in
    let expr = { control = []; attrs = []; expr = orgexpr } in
    let expr = CAst.make expr in
    let backtrace =
      Printexc.raw_backtrace_to_string @@ Printexc.get_callstack 5
    in
    let dummyst = Vernacstate.freeze_full_state () in
    try
      let _ = Vernacinterp.interp ~st:dummyst expr in
      ()
    with reraise ->
      let info =
        "Exception Info: " ^ Printexc.to_string reraise ^ "\n"
        ^ (Pp.string_of_ppcmds @@ CErrors.print reraise)
        ^ "\n\n"
      in
      let ver_exc =
        "Error happened during translation\n   "
        ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac_expr orgexpr)
        ^ "\n"
      in
      if not silence then
        Ferror.fail ~info:(info ^ ver_exc ^ "Stack Trace \n" ^ backtrace ^ "\n")

  let rec emit = function
    | Original e -> emit_vernac_expr ~silence:false e
    | TrySilent e -> emit_vernac_expr ~silence:true e
    | Thunk f -> f () |> emit_list

  and emit_list exprs = exprs |> List.iter emit

  let vernac_ expr : unit t = ([ Original expr ], ())
  let vernacs_ exprs : unit t = (List.map (fun x -> Original x) exprs, ())
  let try_ expr : unit t = (List.map (fun x -> TrySilent x) expr, ())

  let thunk (e : unit -> unit t) : unit t =
    ([ Thunk (fun () -> fst @@ e ()) ], ())

  let bind (x : 'a t) (f : 'a -> 'b t) : 'b t =
    let x_data, x' = x in
    let y_data, y = f x' in
    (x_data @ y_data, y)

  let ( let* ) x f = bind x f
  let ( >> ) x y = bind x (fun _ -> y)
  let return (x : 'a) : 'a t = ([], x)

  let rec flatmap xs : unit t =
    match xs with [] -> return () | h :: t -> h >> flatmap t

  let run (computation : 'a t) : 'a =
    let expr, result = computation in
    emit_list expr;
    result

  let define_inductive (ind_def : VernacInductive.t) : unit t =
    let open Vernacexpr in
    vernac_ (VernacSynPure (VernacInductive (Inductive_kw, ind_def)))

  let define_term ~(name : Names.Id.t) ~(expr : Constrexpr.constr_expr)
      ~(ty : Constrexpr.constr_expr) : unit t =
    let open Vernacexpr in
    let fname_ = (CAst.make @@ Names.Name.mk_name name, None) in
    vernac_
      (VernacSynPure
         (VernacDefinition
            ( (NoDischarge, Decls.Definition),
              fname_,
              DefineBody ([], None, expr, Some ty) )))

  let define_module ~(module_name : Names.Id.t)
      ~(parameters : (Names.Id.t * Constrexpr.module_ast) list)
      ~(body : ModuleTerm.t list -> unit t) : ModuleTerm.t t =
    let open Vernacexpr in
    let modname_ = CAst.make module_name in
    let parameters_ =
      List.map
        (fun (n, m) -> (None, [ CAst.make n ], (m, Declaremods.DefaultInline)))
        parameters
    in

    let inner_parameter =
      List.map (fun (n, m) -> Libnames.qualid_of_ident n) parameters
    in
    let* _ =
      vernac_
        (VernacSynterp
           (VernacDefineModule
              (None, modname_, parameters_, Declaremods.Check [], [])))
    in
    let* _ = body inner_parameter in
    let* _ = vernac_ (VernacSynterp (VernacEndSegment modname_)) in
    return @@ Libnames.qualid_of_ident module_name

  let define_moduletype ~(module_name : Names.Id.t)
      ~(parameters : (Names.Id.t * Constrexpr.module_ast) list)
      ~(body : ModuleTerm.t list -> unit t) : ModuleType.t t =
    let open Vernacexpr in
    let modname_ = CAst.make module_name in
    let parameters_ =
      List.map
        (fun (n, m) -> (None, [ CAst.make n ], (m, Declaremods.DefaultInline)))
        parameters
    in

    let inner_parameter =
      List.map (fun (n, m) -> Libnames.qualid_of_ident n) parameters
    in
    let* _ =
      vernac_
        (VernacSynterp (VernacDeclareModuleType (modname_, parameters_, [], [])))
    in
    let* _ = body inner_parameter in
    let* _ = vernac_ (VernacSynterp (VernacEndSegment modname_)) in
    return @@ Libnames.qualid_of_ident module_name

  let include_module ~(module_expr : Constrexpr.module_ast) : unit t =
    vernac_
      (VernacSynterp
         (VernacInclude [ (module_expr, Declaremods.DefaultInline) ]))

  let assume_parameter ~(name : Names.Id.t) ~(ty : Constrexpr.constr_expr) :
      unit t =
    let open Vernacexpr in
    let fname_ = (CAst.make @@ name, None) in
    vernac_
      (VernacSynPure
         (VernacAssumption
            ( (NoDischarge, Decls.Definitional),
              Declaremods.NoInline,
              [ (NoCoercion, ([ fname_ ], ty)) ] )))

  let postulate_axiom ~(name : Names.Id.t) ~(ty : Constrexpr.constr_expr) :
      unit t =
    let open Vernacexpr in
    let fname_ = (CAst.make @@ name, None) in
    vernac_
      (VernacSynPure
         (VernacAssumption
            ( (NoDischarge, Decls.Logical),
              Declaremods.NoInline,
              [ (NoCoercion, ([ fname_ ], ty)) ] )))
end
