Inductive constant : Type :=
  | Ointconst: int -> constant     (**r integer constant *)
  | Oaddrsymbol: ident -> ptrofs -> constant (**r address of the symbol plus the offset *)
  | Oaddrstack: ptrofs -> constant.   (**r stack pointer plus the given offset *)

Inductive unary_operation : Type :=
  | Ocast8unsigned: unary_operation        (**r 8-bit zero extension  *)
  | Ocast8signed: unary_operation          (**r 8-bit sign extension  *)
  | Ocast16unsigned: unary_operation       (**r 16-bit zero extension  *)
  | Ocast16signed: unary_operation         (**r 16-bit sign extension *)
  | Onegint: unary_operation               (**r integer opposite *)
  | Onotint: unary_operation               (**r bitwise complement  *)
  | Onegl: unary_operation                 (**r long integer opposite *)
  | Onotl: unary_operation                 (**r long bitwise complement *)
  | Ointoflong: unary_operation            (**r long to int *)
  | Olongofint: unary_operation            (**r signed int to long *)
  | Olongofintu: unary_operation           (**r unsigned int to long *)

Inductive binary_operation : Type :=
  | Oadd: binary_operation                 (**r integer addition *)
  | Osub: binary_operation                 (**r integer subtraction *)
  | Omul: binary_operation                 (**r integer multiplication *)
  | Odiv: binary_operation                 (**r integer signed division *)
  | Odivu: binary_operation                (**r integer unsigned division *)
  | Omod: binary_operation                 (**r integer signed modulus *)
  | Omodu: binary_operation                (**r integer unsigned modulus *)
  | Oand: binary_operation                 (**r integer bitwise ``and'' *)
  | Oor: binary_operation                  (**r integer bitwise ``or'' *)
  | Oxor: binary_operation                 (**r integer bitwise ``xor'' *)
  | Oshl: binary_operation                 (**r integer left shift *)
  | Oshr: binary_operation                 (**r integer right signed shift *)
  | Oshru: binary_operation                (**r integer right unsigned shift *)
  | Oaddl: binary_operation                (**r long addition *)
  | Osubl: binary_operation                (**r long subtraction *)
  | Omull: binary_operation                (**r long multiplication *)
  | Odivl: binary_operation                (**r long signed division *)
  | Odivlu: binary_operation               (**r long unsigned division *)
  | Omodl: binary_operation                (**r long signed modulus *)
  | Omodlu: binary_operation               (**r long unsigned modulus *)
  | Oandl: binary_operation                (**r long bitwise ``and'' *)
  | Oorl: binary_operation                 (**r long bitwise ``or'' *)
  | Oxorl: binary_operation                (**r long bitwise ``xor'' *)
  | Oshll: binary_operation                (**r long left shift *)
  | Oshrl: binary_operation                (**r long right signed shift *)
  | Oshrlu: binary_operation               (**r long right unsigned shift *)
  | Ocmp: comparison -> binary_operation   (**r integer signed comparison *)
  | Ocmpu: comparison -> binary_operation  (**r integer unsigned comparison *)
  | Ocmpl: comparison -> binary_operation  (**r long signed comparison *)
  | Ocmplu: comparison -> binary_operation. (**r long unsigned comparison *)

Inductive expr : Type :=
  | Evar : ident -> expr
  | Econst : constant -> expr
  | Eunop : unary_operation -> expr -> expr
  | Ebinop : binary_operation -> expr -> expr -> expr
  | Eload : memory_chunk -> expr -> expr.
                           
Inductive stmt : Type :=
  | Sskip: stmt
  | Sassign : ident -> expr -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: expr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: bool -> expr -> list (Z * nat) -> nat -> stmt
  | Sreturn: option expr -> stmt


(*
    Family Impminor extends MinorBase.
       Inductive constant : Type := ...

       Inductive expr : Type := ...

       Inductive constats += Oaddrstack: ptrofs -> constant.

       Inductive stmt += Sswitch: bool -> expr -> list (Z * nat) -> nat -> stmt

    End Impminor.  
 
*)
                              
