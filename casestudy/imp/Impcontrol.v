family Impwhile extends Impzero { }

family Impcontinue extends Impzero { }

family Impbreak extends Impzero { }

family Impfor extends Impzero { }

family Impgoto extends Impzero { }

(* Imp control is Impwhile + Impgoto + Impfor + Impcontinue + Impbreak *)
family Impcontrol extends Impzero with Impwhile, Impcontinue, Impbreak, Impfor, Impgoto { }
