(* Contains only type definitions used around the plugins *)
module VernacInductive = struct 
  type t = (Vernacexpr.inductive_expr * Vernacexpr.decl_notation list) list
end

(* module Family = struct 
  module Ref = struct 
    type t 
  end 
end 

module FamilyId = struct 
  type t = int 
end 

module NameTable = Map.Make(Names.Id)

module FamilyName = struct 
  type t = { name: Names.Id.t; id: FamilyId.t }
end 

(* The type of an "element" in a family *)
module rec FamilyBodyElemTy : sig 
   type t = ..
end = FamilyBodyElemTy

(* The family context, binding names to their respective types *)
and FamilyContext : sig
  type t = FamilyType.t NameTable.t
end = FamilyContext

(* The "type" of a family *)
and FamilyType : sig
  type t =
    { name : FamilyName.t; 
      body : FamilyBodyElemTy.t NameTable.t; }

end = FamilyType

module NestedFamilyContext = struct 
  type t = 
    | Top of FamilyContext.t
    | Level of FamilyContext.t * t
end

(* Field inheritance kind *)
module FieldInheritanceKind = struct 
  type t = New | Extend
end

module FamilyDefinitionContext = struct 
  type t =
    | InitialInhBase of Family.Ref.t option (* A toplevel family *)
end

module PluginCommand = struct 
  type t = 
    | Family
end 

module PluginCommandScope = struct 
  type t = {
      command : PluginCommand.t; 
      name : Names.Id.t; 
      close_plugin_commad: unit -> unit (* This type is a bit worrying *)      
  }
end 

(* Module with all the states *)
module Context = struct 
  module PluginScope = struct 
    let plugin_scopes : PluginCommandScope.t list ref = 
      Summary.ref ~name:"PluginCommandScope" []

    let peek () = 
        match !plugin_scopes with 
        | [] -> None 
        | x :: _xs -> Some x 
  
  end 
  
end


(* Try to integrate Logs library for logging *)
(* Log to file, Log to output *)



(* inherits_all_remained *)
(* close_current_inh_judgement *)
(* ontopinh *)
(* inhnewind *)


(* Step zero: hand compilation for recursors  *)
(* Step one: Add Family with one level of nesting with FInductives *)
(* Step one_A: Add a logging feature to print compilation to an output file 
   and log messages as comments *)
(* Step two: Add mutual inductive types *)
(* Step three: Generalize to arbitrarily nested families *)


*)

