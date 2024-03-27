From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Import MCMonadNotation.

Class TslIdent := { tsl_ident : ident -> ident }.

Print TslIdent.

Local Instance prime_tsl_ident : TslIdent
  := {| tsl_ident := fun id => id ^ "'" |}.

Fixpoint try_remove_n_lambdas (n : nat) (t : term) {struct n} : term :=
  match n, t with
  | 0, _ => t
  | S n, tLambda _ _ t => try_remove_n_lambdas n t
  | S _, _ => t
  end.

Print constructor_body.

Definition tsl_constructor_body (c: constructor_body) : constructor_body :=
  {| cstr_name := tsl_ident c.(cstr_name);
     cstr_args := cstr_args c;
     cstr_indices := cstr_indices c;
     cstr_type := cstr_type c;
    cstr_arity := cstr_arity c |}.

Print firstn.

Definition remove_last_n {A} (l : list A) (n : nat) : list A :=
  firstn (#|l| - n) l.

(* Compute (remove_last_n [1;2;3] 2). *)

Check decompose_prod_assum.
Check decompose_app.

Print constructor_body.

Check ind_npars.

Print mutual_inductive_body.

Definition new_cstr mdecl (idc : ident) (ctor : term) : constructor_body :=
  let '(args, concl) := decompose_prod_assum [] ctor in
  let (hd, indices) := decompose_app concl in
    {| cstr_name := idc;
       cstr_args := remove_last_n args #|mdecl.(ind_params)|;
       cstr_indices := skipn mdecl.(ind_npars) indices;
       cstr_type := ctor;
       cstr_arity := context_assumptions args |}.

Print mutual_inductive_body.
Print inductive_ind.

Print tsl_constructor_body.

Polymorphic Definition add_ctor (mind : mutual_inductive_body) (ind0 : inductive) (idc : ident) (ctor : term)
  : mutual_inductive_body
  := let i0 := inductive_ind ind0 in
     {| ind_finite := mind.(ind_finite);
        ind_npars := mind.(ind_npars) ;
        ind_universes := mind.(ind_universes) ;
        ind_variance := mind.(ind_variance);
        ind_params := mind.(ind_params);
        ind_bodies := mapi (fun (i : nat) (ind : one_inductive_body) =>
          {| ind_name := tsl_ident ind.(ind_name) ;
            ind_indices := ind.(ind_indices);
            ind_sort := ind.(ind_sort);
            ind_type  := ind.(ind_type) ;
            ind_kelim := ind.(ind_kelim) ;
            ind_ctors := let ctors := map tsl_constructor_body ind.(ind_ctors) in
                          if Nat.eqb i i0 then
                            let n := #|ind_bodies mind| in
                            let typ := try_remove_n_lambdas n ctor in
                            ctors ++ [new_cstr mind idc typ]
                          else ctors;
            ind_projs := ind.(ind_projs);
            ind_relevance := ind.(ind_relevance) |})
            mind.(ind_bodies) |}.

Polymorphic Definition add_constructor (tm : Ast.term)
            (idc : ident) (type : Ast.term)
  : TemplateMonad unit
  := match tm with
     | tInd ind0 _ =>
       decl <- tmQuoteInductive (inductive_mind ind0) ;;
       let ind' := add_ctor decl ind0 idc type in
       tmMkInductive' ind'
     | _ => tmPrint tm ;; tmFail " is not an inductive"
     end.

Local Open Scope bs_scope.

MetaCoq Run (
    add_constructor <% bool %> "foo" <% (fun x : Type => nat -> x -> bool -> x) %>).

Check foo.

Print bool'.

Inductive tm :=
| var : nat -> tm
| lam : tm -> tm
| app : tm -> tm -> tm.

MetaCoq Run (add_constructor <%tm%> "letin" <% (fun tm' => tm' -> tm' -> tm') %>).

Check letin.


(* Compute (#|[1; 2; 3]|). *)

(* Print try_remove_n_lambdas. *)








