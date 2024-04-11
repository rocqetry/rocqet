let global_env () =
  let env = Global.env () in
  Evd.from_env env, env

(* Push a local binding to an environment *)
let push_local (n, t) env =
  EConstr.push_rel Context.Rel.Declaration.(LocalAssum (n, t)) env

let define name body sigma =
  let udecl = UState.default_univ_decl in
  let scope = Locality.Global Locality.ImportDefaultBehavior in
  let kind = Decls.(IsDefinition Definition) in
  let cinfo = Declare.CInfo.make ~name ~typ:None () in
  let info = Declare.Info.make ~scope ~kind  ~udecl ~poly:false () in
  Declare.declare_definition ~info ~cinfo ~opaque:false ~body sigma |> ignore


(*
 * When you first start using a plugin, if you want to manipulate terms
 * in an interesting way, you need to move from the external representation
 * of terms to the internal representation of terms. This does that for you.
 *)
let internalize env trm sigma =
  Constrintern.interp_constr_evars env sigma trm

(*
 * This checks if there is any set of internal constraints in the state
 * such that trm1 and trm2 are definitionally equal in the current environment.
 *)
let equal env trm1 trm2 sigma =
  let opt = Reductionops.infer_conv env sigma trm1 trm2 in
  match opt with
  | Some sigma -> sigma, true
  | None -> sigma, false

let _f = Inductive.find_inductive

let _i = Environ.lookup_mind

let _g = Inductive.lookup_mind_specif

let _h (g : Declarations.one_inductive_body) = failwith ""
let _i (g : Declarations.mutual_inductive_body) = failwith ""
(* let _j (g : constructor_body) = failwith "" *)

let _j = Environ.lookup_mind

(* 
val declare_mutual_inductive_with_eliminations
  : ?primitive_expected:bool
  -> ?typing_flags:Declarations.typing_flags
  -> Entries.mutual_inductive_entry
  -> UState.named_universes_entry
  -> one_inductive_impls list
  -> Names.MutInd.t
*)

let _g (f: Entries.mutual_inductive_entry) = failwith ""

let _g = DeclareInd.declare_mutual_inductive_with_eliminations

let _a = Term.decompose_prod_assum
let _b : Vernacexpr.inductive_expr = failwith ""

(* (Vernacexpr.inductive_expr * Vernacexpr.decl_notation list) list *)

let _g something = Vernacexpr.(VernacInductive (Inductive_kw, something))

let compile = Vernacinterp.interp

let transform_name name = Nameops.add_suffix name "'"

let analyze_reference gref = 
  let open Declarations in
  match gref with 
  | Names.GlobRef.IndRef (mind, ind) -> 
     let _, env = global_env () in
     let (mind_decl, ind_decl) = Inductive.lookup_mind_specif env (mind, ind) in
     { mind_decl with 
       mind_packets = 
         mind_decl.mind_packets 
         |> Array.mapi (fun i ind -> 
                { ind with 
                    mind_typename = 
                      transform_name ind.mind_typename})
                    
     }     
  | _ -> failwith "expected and inductive reference"


