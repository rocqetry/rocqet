open BinNums

type errcode =
| MSG of char list
| CTX of positive
| POS of positive

type errmsg = errcode list

val msg : char list -> errmsg

type 'a res =
| OK of 'a
| Error of errmsg

val assertion_failed : 'a1 res

val mmap : ('a1 -> 'a2 res) -> 'a1 list -> 'a2 list res

val bind : 'a1 res -> ('a1 -> 'a2 res) -> 'a2 res
val bind2 : ('a1 * 'a2) res -> ('a1 -> 'a2 -> 'a3 res) -> 'a3 res
