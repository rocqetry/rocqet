exception NestedCommand
exception ClosingWrongScope

val report : error:exn -> 'a
val fail : info:string -> 'a
