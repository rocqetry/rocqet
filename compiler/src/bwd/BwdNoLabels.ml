type 'a t = 'a BwdDef.bwd = Emp | Snoc of 'a t * 'a

let length xs =
  let rec go acc = function
    | Emp -> acc
    | Snoc (xs, _) -> (go [@tailcall]) (acc + 1) xs
  in
  go 0 xs

let compare_lengths xs ys =
  let rec go = function
    | Emp, Emp -> 0
    | Snoc _, Emp -> 1
    | Emp, Snoc _ -> -1
    | Snoc (xs, _), Snoc (ys, _) -> (go [@tailcall]) (xs, ys)
  in
  go (xs, ys)

let compare_length_with xs len =
  let rec go len = function
    | Emp -> Int.compare 0 len
    | Snoc (xs, _) -> (go [@tailcall]) (len - 1) xs
  in
  go len xs

let is_empty = function Emp -> true | _ -> false
let snoc l x = Snoc (l, x)

let nth xs i =
  if i < 0 then invalid_arg "Bwd.nth"
  else
    let rec go = function
      | Emp, _ -> failwith "Bwd.nth"
      | Snoc (_, x), 0 -> x
      | Snoc (xs, _), i -> (go [@tailcall]) (xs, i - 1)
    in
    go (xs, i)

let nth_opt xs i =
  if i < 0 then invalid_arg "Bwd.nth_opt"
  else
    let rec go = function
      | Emp, _ -> None
      | Snoc (_, x), 0 -> Some x
      | Snoc (xs, _), i -> (go [@tailcall]) (xs, i - 1)
    in
    go (xs, i)

let init len f =
  if len < 0 then invalid_arg "Bwd.init"
  else
    let[@tail_mod_cons] rec go i last =
      if i > last then Emp
      else if i = last then Snoc (Emp, f i)
      else
        let v1 = f i in
        let v2 = f (i + 1) in
        Snoc (Snoc ((go [@tailcall]) (i + 2) last, v2), v1)
    in
    go 0 (len - 1)

let append xs ys =
  let rec go = function
    | xs, [] -> xs
    | xs, y :: ys -> (go [@tailcall]) (Snoc (xs, y), ys)
  in
  go (xs, ys)

let prepend xs ys =
  let rec go = function
    | Emp, ys -> ys
    | Snoc (xs, x), ys -> (go [@tailcall]) (xs, x :: ys)
  in
  go (xs, ys)

let equal eq xs ys =
  let rec go = function
    | Emp, Emp -> true
    | Snoc (xs, x), Snoc (ys, y) -> eq x y && (go [@tailcall]) (xs, ys)
    | _ -> false
  in
  go (xs, ys)

let compare cmp xs ys =
  let rec go = function
    | Emp, Emp -> 0
    | Emp, _ -> -1
    | _, Emp -> 1
    | Snoc (xs, x), Snoc (ys, y) ->
        let c = cmp x y in
        if c <> 0 then c else (go [@tailcall]) (xs, ys)
  in
  go (xs, ys)

let iter f =
  let rec go = function
    | Emp -> ()
    | Snoc (xs, x) ->
        f x;
        (go [@tailcall]) xs
  in
  go

let iteri f =
  let[@tail_mod_cons] rec go i = function
    | Emp -> ()
    | Snoc (xs, x) ->
        f i x;
        (go [@tailcall]) (i + 1) xs
  in
  go 0

let map f =
  let[@tail_mod_cons] rec go = function
    | Emp -> Emp
    | Snoc (Emp, x) ->
        let y = f x in
        Snoc (Emp, y)
    | Snoc (Snoc (xs, x2), x1) ->
        let y1 = f x1 in
        let y2 = f x2 in
        Snoc (Snoc ((go [@tailcall]) xs, y2), y1)
  in
  go

let mapi f =
  let[@tail_mod_cons] rec go i = function
    | Emp -> Emp
    | Snoc (Emp, x) ->
        let y = f i x in
        Snoc (Emp, y)
    | Snoc (Snoc (xs, x2), x1) ->
        let y1 = f i x1 in
        let y2 = f (i + 1) x2 in
        Snoc (Snoc ((go [@tailcall]) (i + 2) xs, y2), y1)
  in
  go 0

let filter_map f =
  let[@tail_mod_cons] rec go = function
    | Emp -> Emp
    | Snoc (xs, x) -> (
        match f x with
        | None -> go xs
        | Some fx -> Snoc ((go [@tailcall]) xs, fx))
  in
  go

let fold_left f init =
  let rec go = function Emp -> init | Snoc (xs, x) -> f (go xs) x in
  go

let fold_right_map f xs init =
  let rec go xs init ys =
    match xs with
    | Emp -> (init, append Emp ys)
    | Snoc (xs, x) ->
        let init, y = f x init in
        (go [@tailcall]) xs init (y :: ys)
  in
  go xs init []

let fold_right f xs init =
  let rec go init = function
    | Emp -> init
    | Snoc (xs, x) ->
        let init = f x init in
        (go [@tailcall]) init xs
  in
  go init xs

let iter2 f xs ys =
  let rec go = function
    | Emp, Emp -> ()
    | Snoc (xs, x), Snoc (ys, y) ->
        f x y;
        (go [@tailcall]) (xs, ys)
    | _ -> invalid_arg "Bwd.iter2"
  in
  go (xs, ys)

let map2 f xs ys =
  let[@tail_mod_cons] rec go = function
    | Emp, Emp -> Emp
    | Snoc (Emp, x), Snoc (Emp, y) ->
        let z = f x y in
        Snoc (Emp, z)
    | Snoc (Snoc (xs, x2), x1), Snoc (Snoc (ys, y2), y1) ->
        let z1 = f x1 y1 in
        let z2 = f x2 y2 in
        Snoc (Snoc ((go [@tailcall]) (xs, ys), z2), z1)
    | _ -> invalid_arg "Bwd.map2"
  in
  go (xs, ys)

let fold_left2 f init xs ys =
  let rec go = function
    | Emp, Emp -> init
    | Snoc (xs, x), Snoc (ys, y) -> f (go (xs, ys)) x y
    | _ -> invalid_arg "Bwd.fold_left2"
  in
  go (xs, ys)

let fold_right2 f xs ys init =
  let rec go init = function
    | Emp, Emp -> init
    | Snoc (xs, x), Snoc (ys, y) ->
        let init = f x y init in
        (go [@tailcall]) init (xs, ys)
    | _ -> invalid_arg "Bwd.fold_right2"
  in
  go init (xs, ys)

let for_all f =
  let rec go = function
    | Emp -> true
    | Snoc (xs, x) -> f x && (go [@tailcall]) xs
  in
  go

let for_all2 f xs ys =
  let rec go = function
    | Emp, Emp -> true
    | Snoc (xs, x), Snoc (ys, y) -> f x y && (go [@tailcall]) (xs, ys)
    | _ -> invalid_arg "Bwd.for_all2"
  in
  go (xs, ys)

let exists f =
  let rec go = function
    | Emp -> false
    | Snoc (xs, x) -> f x || (go [@tailcall]) xs
  in
  go

let exists2 f xs ys =
  let rec go = function
    | Emp, Emp -> false
    | Snoc (xs, x), Snoc (ys, y) -> f x y || (go [@tailcall]) (xs, ys)
    | _ -> invalid_arg "Bwd.exists2"
  in
  go (xs, ys)

let mem a set =
  let rec go = function
    | Emp -> false
    | Snoc (xs, x) -> a = x || (go [@tailcall]) xs
  in
  go set

let memq a set =
  let rec go = function
    | Emp -> false
    | Snoc (xs, x) -> a == x || (go [@tailcall]) xs
  in
  go set

let find f =
  let rec go = function
    | Emp -> raise Not_found
    | Snoc (xs, x) -> if f x then x else (go [@tailcall]) xs
  in
  go

let find_opt f =
  let rec go = function
    | Emp -> None
    | Snoc (xs, x) -> if f x then Some x else (go [@tailcall]) xs
  in
  go

let find_index f =
  let rec go i = function
    | Emp -> None
    | Snoc (xs, x) -> if f x then Some i else (go [@tallcall]) (i + 1) xs
  in
  go 0

let find_map f =
  let rec go = function
    | Emp -> None
    | Snoc (xs, x) -> (
        match f x with Some _ as r -> r | None -> (go [@tallcall]) xs)
  in
  go

let find_mapi f =
  let rec go i = function
    | Emp -> None
    | Snoc (xs, x) -> (
        match f i x with
        | Some _ as r -> r
        | None -> (go [@tallcall]) (i + 1) xs)
  in
  go 0

let filter f =
  let[@tail_mod_cons] rec go = function
    | Emp -> Emp
    | Snoc (xs, x) ->
        if f x then Snoc ((go [@tailcall]) xs, x) else (go [@tailcall]) xs
  in
  go

let find_all f = filter f

let filteri f =
  let[@tail_mod_cons] rec go i = function
    | Emp -> Emp
    | Snoc (xs, x) ->
        if f i x then Snoc ((go [@tailcall]) (i + 1) xs, x)
        else (go [@tailcall]) (i + 1) xs
  in
  go 0

let partition f xs =
  let rec go xs ys zs =
    match xs with
    | Emp -> (append Emp ys, append Emp zs)
    | Snoc (xs, x) ->
        if f x then (go [@tailcall]) xs (x :: ys) zs
        else (go [@tailcall]) xs ys (x :: zs)
  in
  go xs [] []

let partition_map f xs =
  let rec go xs ys zs =
    match xs with
    | Emp -> (append Emp ys, append Emp zs)
    | Snoc (xs, x) -> (
        match f x with
        | Either.Left y -> (go [@tailcall]) xs (y :: ys) zs
        | Either.Right z -> (go [@tailcall]) xs ys (z :: zs))
  in
  go xs [] []

let rec split = function
  | Emp -> (Emp, Emp)
  | Snoc (xys, (x, y)) ->
      let xs, ys = split xys in
      (Snoc (xs, x), Snoc (ys, y))

let combine xs ys =
  let[@tail_mod_cons] rec go = function
    | Emp, Emp -> Emp
    | Snoc (xs, x), Snoc (ys, y) -> Snoc ((go [@tailcall]) (xs, ys), (x, y))
    | _ -> invalid_arg "Bwd.combine"
  in
  go (xs, ys)

let to_list xs = prepend xs []
let of_list xs = append Emp xs

module Infix = struct
  let ( <: ) = snoc
  let ( <@ ) = append
  let ( @> ) = prepend
  let ( #< ) = snoc
  let ( <>< ) = append
  let ( <>> ) = prepend
end

module Notation = Infix
