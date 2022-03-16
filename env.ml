include Map.Make(String)

let (|=>) x y = singleton x y

let (|->) x y = add x y

let create l1 l2 =
  List.fold_left2
    (fun res x y -> add x y res)
    empty
    l1
    l2

let find_default key default env =
  try
    find key env
  with
    Not_found -> default