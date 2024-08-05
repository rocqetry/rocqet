(* A nested command that is not a family *)
(* e.g
   FRecursions ...
      FRecursion ....
*)
(* Without closing the first scope *)
exception NestedCommand
exception ClosingWrongScope

let report ~error = raise error
let fail ~info = failwith info

let failwith_stacktrace ~info = 
  let backtrace =
      Printexc.raw_backtrace_to_string @@ Printexc.get_callstack 10
  in
  let info = Printf.sprintf "Error: %s \n Stack Trace: %s" info backtrace in 
  fail ~info

(* TODO: Add functions for asserts *)
