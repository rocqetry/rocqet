Ltac __unfold_ftheorem_motive := 
  match goal with 
  | [ |- ?h ?t] => try unfold h; try unfold t 
  end.

Ltac unfold_nested G :=
  match G with 
  | True => idtac
  | (prod (?h ?a) ?G2)  => unfold h; unfold a; unfold_nested G2  
  end.

(* Need a recursive unfolding *)
Ltac __unfold_ftheorem_motive_nested := 
  match goal with 
  | [ |- (prod ?a ?b) ] => unfold_nested (prod a b)
  | _ => idtac
  end.

Declare ML Module "nfpop:nfpop.plugin".
