type 'a t = 'a BwdDef.bwd = Emp | Snoc of 'a t * 'a

let length = BwdNoLabels.length
let compare_lengths = BwdNoLabels.compare_lengths

let[@inline] compare_length_with xs ~len =
  BwdNoLabels.compare_length_with xs len

let is_empty = BwdNoLabels.is_empty
let snoc = BwdNoLabels.snoc
let nth = BwdNoLabels.nth
let nth_opt = BwdNoLabels.nth_opt
let[@inline] init ~len ~f = BwdNoLabels.init len f
let append = BwdNoLabels.append
let prepend = BwdNoLabels.prepend
let[@inline] equal ~eq xs ys = BwdNoLabels.equal eq xs ys
let[@inline] compare ~cmp xs ys = BwdNoLabels.compare cmp xs ys
let[@inline] iter ~f = BwdNoLabels.iter f
let[@inline] iteri ~f = BwdNoLabels.iteri f
let[@inline] map ~f = BwdNoLabels.map f
let[@inline] mapi ~f = BwdNoLabels.mapi f
let[@inline] filter_map ~f = BwdNoLabels.filter_map f
let[@inline] fold_left ~f ~init = BwdNoLabels.fold_left f init
let[@inline] fold_right_map ~f xs ~init = BwdNoLabels.fold_right_map f xs init
let[@inline] fold_right ~f xs ~init = BwdNoLabels.fold_right f xs init
let[@inline] iter2 ~f xs ys = BwdNoLabels.iter2 f xs ys
let[@inline] map2 ~f xs ys = BwdNoLabels.map2 f xs ys
let[@inline] fold_left2 ~f ~init = BwdNoLabels.fold_left2 f init
let[@inline] fold_right2 ~f xs ys ~init = BwdNoLabels.fold_right2 f xs ys init
let[@inline] for_all ~f = BwdNoLabels.for_all f
let[@inline] for_all2 ~f = BwdNoLabels.for_all2 f
let[@inline] exists ~f = BwdNoLabels.exists f
let[@inline] exists2 ~f = BwdNoLabels.exists2 f
let[@inline] mem a ~set = BwdNoLabels.mem a set
let[@inline] memq a ~set = BwdNoLabels.memq a set
let[@inline] find ~f = BwdNoLabels.find f
let[@inline] find_opt ~f = BwdNoLabels.find_opt f
let[@inline] find_index ~f = BwdNoLabels.find_index f
let[@inline] find_map ~f = BwdNoLabels.find_map f
let[@inline] find_mapi ~f = BwdNoLabels.find_mapi f
let[@inline] filter ~f = BwdNoLabels.filter f
let[@inline] find_all ~f = BwdNoLabels.find_all f
let[@inline] filteri ~f = BwdNoLabels.filteri f
let[@inline] partition ~f = BwdNoLabels.partition f
let[@inline] partition_map ~f = BwdNoLabels.partition_map f
let split = BwdNoLabels.split
let combine = BwdNoLabels.combine
let to_list = BwdNoLabels.to_list
let of_list = BwdNoLabels.of_list

module Infix = BwdNoLabels.Infix
module Notation = BwdNoLabels.Notation [@alert "-deprecated"]
