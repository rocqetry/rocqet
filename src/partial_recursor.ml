open Env
open Types

(* (forall __i : self__Ix.ty,
 forall P : self__Ix.ty -> Type, forall arg回9 : option (P self__Ix.ty_unit), option (P __i)) *)

let generate_one_computational_axiom 
      ~(inductive: VernacInductive.t)      
      ~(recursor_path: Libnames.qualid)
      ~(constructor_name: Names.Id.t)
      ~(constructor_path: Libnames.qualid)
      ~(handlers: Names.Id.t list)
      ~context =   
  let open Constrexpr_ops in
  let constructor_params, fully_applied_constr =
    Termutils.extract_variables_and_apply (mkRefC constructor_path)
  in
  let extract_name ({ CAst.v = n; _ } : Names.lname) : Names.Id.t =
      match n with
      | Names.Name n -> n
      | _ -> Errors.fail ~info:"Expected non anonymous argument"
  in
  (* The arguments to the consructor *)
  let c_arguments =
      constructor_params
      |> List.map (fun ((lnames, _, _), _) ->
             lnames |> List.hd |> extract_name 
             (*|> Libnames.qualid_of_ident
             |> mkRefC*))
  in
  (* The P predicate *)
  let p_argument = Names.Id.of_string "P" in  
  let generate_h_strings n =
     let rec aux i acc =
       if i > n then
         List.rev acc
       else
         aux (i + 1) (("H" ^ string_of_int i) :: acc)
     in
     aux 1 []
  in
  let find_position x lst =
     let rec aux current_pos = function
       | [] -> Errors.fail ~info:"Handler not found"
       | hd :: tl -> 
           if Names.Id.equal hd x then current_pos
           else aux (current_pos + 1) tl
     in
     aux 1 lst
  in 
  let position = find_position constructor_name handlers in
  (* The "H" function of the current handler *)
  let h_target = 
    Names.Id.of_string (Printf.sprintf "H%d" position)
  in
  (* The H arguments *)
  let h_arguments = 
    handlers
    |> List.length
    |> generate_h_strings
    |> List.map Names.Id.of_string
  in
  let partial_recursor_term arguments = 
    let f = mkRefC recursor_path in 
    mkAppC (f, arguments)
  in
  let equation_side arg = 
    let p_and_hs = 
      (p_argument :: h_arguments) 
      |> List.map (fun n -> n |> Libnames.qualid_of_ident |> mkRefC) 
    in
    let arguments = arg :: p_and_hs in 
    partial_recursor_term arguments
  in
  let left_hand_side = equation_side fully_applied_constr in
  let right_hand_side = 
    let types = 
      Termutils.flatten_inductive_constructor_type 
        ~inductive ~constructor:constructor_name
    in
    let f ty arg =      
      match ty with
      | None -> [ arg |> Libnames.qualid_of_ident |> mkRefC ]
      | Some _ ->          
          let arg = arg |> Libnames.qualid_of_ident |> mkRefC in
          let rec_arg = equation_side arg in
          [ arg; rec_arg ]
    in
    let arguments = List.concat (List.map2 f types c_arguments) in
    let f = h_target |> Libnames.qualid_of_ident |> mkRefC in
    mkAppC (f, arguments)
  in 
  let all_arguments = c_arguments @ [p_argument] @ h_arguments in
  let equation = 
    let eq_cstr = mkRefC @@ Libnames.qualid_of_ident @@ Names.Id.of_string "eq" in
    mkAppC (eq_cstr, [ left_hand_side; right_hand_side ])
  in 
  let full_equation = Termutils.lambda_to_prod @@ Termutils.mk_lambda all_arguments equation in 
  let family_name = context |> Context.family_name in
  let name = Naming.prec_computational_axiom_name ~constructor_name ~family_name in
  (name, full_equation)

let add ~(inductive_path : Libnames.qualid) = 
  let context = Context.get () in  
  let default_ctx_params =
    context |> Context.family_linkage |> function
    | { default_ctx_params; _ } -> default_ctx_params
  in
  let inductive, _, _ =
    Env.Context.lookup_inductive_for_recursion ~name:inductive_path context
  in  
  let handlers = 
    inductive 
    |> List.hd 
    |> fst 
    |> VernacInductive.extract_type_and_cstrs 
    |> snd 
    |> List.map fst 
  in
  let inductive_name = inductive_path |> Naming.path_to_list |> List.rev |> List.hd in   
  let family_name = Context.family_name context in
  let name = Naming.partial_recursor_name ~inductive_name ~family_name in
  
  let type_name = Naming.fresh_name ~prefix:"PrecTy" in
  let ty = Termutils.compute_partial_recursor_signature ~inductive_path ~context in  
  let sigma, env = Termutils.global_env () in
  let s = Ppconstr.pr_constr_expr env sigma ty in 
  Feedback.msg_warning s;
  let _ = Definition.add_definition ~name:type_name ty in
  let context = Context.get () in
  
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let ty =
    let expression = Constrexpr_ops.mkIdentC type_name in  
    Resolver.resolve_constrexpr ~context ~expression
  in 
  let compiled_signature = 
    Codegen.compile_lemma_signature ~name ~ty ~parameters 
  in 
  let elem = 
    LinkageElem.PartialRecursor 
     { 
       inductive_path;
       compiled_signature;
       compiled_context;
       type_name; 
       name;
       default_ctx_params;
       handlers;
     }
  in 
  Context.add_field ~name ~elem
  
