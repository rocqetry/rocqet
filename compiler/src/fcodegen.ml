(* From https://github.com/tlringer/plugin-tutorial/blob/main/src/termutils.ml *)

(** Get the global environment *)
let _global_env () =
  let env = Global.env () in
  Evd.from_env env, env

(** Push a local binding to an environment *)
let _push_local (n, t) env =
  EConstr.push_rel Context.Rel.Declaration.(LocalAssum (n, t)) env

let _define_module name body (path : Names.ModPath.t)=
  let _stuff = Declaremods.declare_module name in
  let _g = Declaremods.start_module in
  let _i = Declaremods.start_modtype in  
  ()


(** When you first start using a plugin, if you want to manipulate terms
 in an interesting way, you need to move from the external representation
 of terms to the internal representation of terms. This does that for you. *)
let _internalize env trm sigma =
  Constrintern.interp_constr_evars env sigma trm


let unique_id =
  let counter = ref 0 in 
  fun () -> 
  counter := !counter + 1;
  !counter

let fresh_name ~prefix =
   let prefix = Names.Id.to_string prefix in
   let time_stamp = string_of_int @@ unique_id () in     
   Names.Id.of_string (prefix ^ "回" ^ time_stamp)    



(* Interface for what a codegen backend should be *)
(* module type S = sig
  type t 
  val define_module : Names.Id.t -> unit
  val dump_output : string -> unit
end *)

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
  val assume_parameter:
    name:Names.Id.t ->
    ty:Constrexpr.constr_expr ->
    unit
  
  val define_moduletype:
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
    let info = Declare.Info.make ~scope ~kind  ~udecl ~poly:false () in
    Declare.declare_definition ~info ~cinfo ~opaque:false ~body sigma |> ignore
end

(** Code generation backend by writing and interpreting Vernacular commands explicitly *)
module VernacBackend = struct 
  type expr = 
    | Original of Vernacexpr.vernac_expr
    | TrySilent of Vernacexpr.vernac_expr
    | Thunk of (unit -> expr list)

  type 'a t = expr list * 'a

  let emit_vernac_expr ~silence (orgexpr : Vernacexpr.vernac_expr) : unit =
    let () = Feedback.msg_notice @@ 
      let open Pp in 
      (Ppvernac.pr_vernac_expr orgexpr) ++ (str ".") 
    in 
    let open Vernacexpr in 
    let expr = { control = []; attrs = []; expr = orgexpr } in 
    let expr = CAst.make expr in 
    let backtrace = Printexc.raw_backtrace_to_string @@ Printexc.get_callstack 5 in 
    let dummyst = Vernacstate.freeze_interp_state ~marshallable:false in 
    try 
      let _ = Vernacinterp.interp ~st:dummyst expr in () 
    with reraise ->
      let info = "Exception Info: " ^ Printexc.to_string reraise ^ "\n" ^ (Pp.string_of_ppcmds @@ CErrors.print reraise) ^ "\n\n" in 
        let ver_exc = "Error happened during translation\n   " ^ (Pp.string_of_ppcmds @@  Ppvernac.pr_vernac_expr orgexpr) ^ "\n" in         
        if not silence then
           Ferror.fail ~info:(info ^ ver_exc ^ "Stack Trace \n" ^ backtrace ^ "\n") 

  let rec emit = function
    | Original e -> emit_vernac_expr ~silence:false e 
    | TrySilent e -> emit_vernac_expr ~silence:true e 
    | Thunk f -> f () |> emit_list
  and emit_list exprs = exprs |> List.iter emit


  let vernac_ expr : unit t = ([Original expr], ())
  let vernacs_ exprs : unit t = List.map (fun x -> Original x) exprs, ()
  let try_ expr : unit t = List.map (fun x -> TrySilent x) expr, ()
  let thunk (e : unit -> unit t) : unit t = [Thunk (fun () -> fst @@ e ())], ()

   let bind (x : 'a t) (f : 'a -> 'b t) : 'b t =
    let x_data, x' = x in 
    let y_data, y = f x' in 
    (x_data @ y_data, y) 
   
  let (let*) x f = bind x f

  let (>>) x y = bind x (fun _-> y)
  
  let return (x : 'a) : 'a t = ([], x)

  let rec flatmap xs : unit t =
    match xs with 
    | [] -> return ()
    | h::t -> h >> (flatmap t)

  let run (computation: 'a t) : 'a =    
    let expr, result = computation in 
    emit_list expr;
    result

  let define_module 
    ~(module_name : Names.Id.t) 
    ~(parameters : (Names.Id.t * Constrexpr.module_ast) list)
    ~(body : ModuleTerm.t list -> unit t) : ModuleTerm.t t = 
    let open Vernacexpr in
    let modname_ = CAst.make module_name in 
    let parameters_ = 
      List.map 
        (fun (n,m) -> 
          (None, [CAst.make n], (m, Declaremods.DefaultInline))) parameters in 
    
    let inner_parameter =
      List.map 
        (fun (n,m) ->
          Libnames.qualid_of_ident n) parameters in 
    let* _ = vernac_ (VernacDefineModule (None, modname_ , parameters_ , Declaremods.Check [], []) ) in 
    let* _ = body inner_parameter in 
    let* _ = vernac_ (VernacEndSegment modname_) in 
      return @@ Libnames.qualid_of_ident module_name
  
  let define_moduletype 
    ~(module_name : Names.Id.t)
    ~(parameters : (Names.Id.t * Constrexpr.module_ast) list) 
    ~(body : ModuleTerm.t list -> unit t) : ModuleType.t t = 
    let open Vernacexpr in 
    let modname_ = CAst.make module_name in 
    let parameters_ = 
      List.map 
        (fun (n,m) -> 
          (None, [CAst.make n], (m, Declaremods.DefaultInline))) parameters in 
    
    let inner_parameter =
      List.map 
        (fun (n,m) ->
          Libnames.qualid_of_ident n) parameters in 
    let* _ = vernac_ (VernacDeclareModuleType (modname_ , parameters_ , [], []) ) in 
    let* _ = body inner_parameter in 
    let* _ = vernac_ (VernacEndSegment modname_) in 
      return @@ Libnames.qualid_of_ident module_name  

  let assume_parameter
    ~(name : Names.Id.t) 
    ~(ty : Constrexpr.constr_expr) : unit t = 
    let open Vernacexpr in
    let fname_ = (CAst.make @@ name, None)  in 
      vernac_ (VernacAssumption (
                  (NoDischarge, Decls.Definitional), 
                  Declaremods.NoInline , [(false , ([ fname_ ], ty))]))
end



