Ltac unfold_motive G :=
  match G with 
  | ?x => unfold x
  | (?f ?x) => unfold x; unfold_motive f
  end.

Ltac __unfold_ftheorem_motive := 
  match goal with 
  | [ |- ?h ?t] => try unfold h; try unfold t 
  | _ => idtac                                     
  end.

(*Ltac unfold_nested G :=
  match G with 
  | True => idtac
  | (prod (?h ?a) ?G2)  => unfold h; unfold a; unfold_nested G2  
  | ((?h ?a) /\ ?G2) => unfold_motive (h a); unfold_nested G2
  end.*)

Ltac unfold_nested G :=
  match G with 
  | True => idtac
  | (prod (?h ?a) ?G2)  => unfold h; unfold a; unfold_nested G2  
  | ((?h ?a) /\ ?G2) => unfold h; unfold a; unfold_motive h; unfold_motive a; unfold_nested G2
  end.

(* Need a recursive unfolding *)
Ltac __unfold_ftheorem_motive_nested := 
  match goal with 
  | [ |- (prod ?a ?b) ] => unfold_nested (prod a b)
  | [ |- (?a /\ ?b) ] => unfold_nested (a /\ b)
  | _ => idtac
  end.

(* Ltac __auto_split :=
  match goal with
  | [ |- prod _ _ ] => split; __unfold_ftheorem_motive_nested
  | [ |- _ /\ _ ] => split; __unfold_ftheorem_motive_nested
  | _ => idtac
  end.*)

(* For some reason we can't access the "unfold" tactic directly *)
Ltac __funfold f := unfold f.

Ltac __funfold_in f H := unfold f in H.

Ltac __funfold_star f := unfold f in *.

Ltac __frewrite_in f H := try (rewrite f in H).

Ltac __fconstructor H := (eapply H; eauto).

Ltac split_cases_into_goals :=
  match goal with
  | [ |- ?a /\ ?b ] => 
      split; split_cases_into_goals
  | _ => auto
  end.

(* apply @eq_refl; fail. (* intros; simple apply @eq_refl. (*debug eauto 15.*)*) *)
Ltac prove_comp_axiom := eauto. 

Ltac prove_prec :=
  intros x; induction x; eauto; eauto using None.

Declare ML Module "nfpop:nfpop.plugin".
