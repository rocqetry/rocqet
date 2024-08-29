(** @canonical Bwd.bwd *)
type 'a bwd = Emp | Snoc of 'a bwd * 'a
