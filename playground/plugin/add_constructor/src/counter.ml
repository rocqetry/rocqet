let counter = Summary.ref ~name:"summary" 0

let increment () = incr counter

let value () = !counter
