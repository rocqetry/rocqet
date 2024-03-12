Family Impwhile extends Impzero { }

Family Impcontinue extends Impzero { }

Family Impbreak extends Impzero { }

Family Impfor extends Impzero { }

Family Impgoto extends Impzero { }

(* Imp control is Impwhile + Impgoto + Impfor + Impcontinue + Impbreak *)
Family Impcontrol extends Impzero with Impwhile, Impcontinue, Impbreak, Impfor, Impgoto { }
