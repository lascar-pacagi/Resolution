open List
open Formula

let mk_and p q = And (p, q)
let mk_or p q = Or (p, q)
let mk_imp p q = Imp (p, q)
let mk_iff p q = Iff (p, q)
let mk_forall x p = Forall (x, p)
let mk_exists x p = Exists (x, p)

let setify l = sort_uniq Stdlib.compare l

let map_flatten f l = map f l |> flatten

(* l1 and l2 must be setified *)
let rec subset l1 l2 =
  match l1, l2 with
  | l1, [] -> false
  | [], l2 -> true
  | h1 :: r1, h2 :: r2 -> begin
    if h1 = h2 then subset r1 r2
    else if h1 < h2 then false
    else subset l1 r2
  end

(* l1 and l2 must be setified *)
let rec union l1 l2 =
  match l1, l2 with
  | [], l2 -> l2
  | l1, [] -> l1
  | h1 :: r1, h2 :: r2 -> begin
    if h1 = h2 then h1 :: (union r1 r2)
    else
      if h1 < h2 then h1 :: (union r1 l2)
      else h2 :: (union l1 r2)
  end

(* l1 and l2 must be setified *)
let rec subtract l1 l2 =
  match l1, l2 with
  | [], l2 -> []
  | l1, [] -> l1
  | h1 :: r1, h2 :: r2 ->
    if h1 = h2 then subtract r1 r2
    else
      if h1 < h2 then h1 :: subtract r1 l2
      else subtract l1 r2

(* l must be setified *)
let insert x l = union [x] l

(* l must be setified *)
let rec mem_set x l =
  match l with
  | [] -> false
  | y :: r ->
    if x = y then true
    else
      if x < y then false
      else mem_set x r

let image f s = setify (map f s)

let can f x = try f x; true with _ -> false

let rec try_find f l =
  match l with
  | [] -> failwith "try_find"
  | h :: t -> try f h with _ -> try_find f t

let ( ** ) f g x = f (g x)

let rec all_pairs f l1 l2 =
  match l1 with
  | [] -> []
  | h1 :: t1 ->
     fold_left (fun acc x -> f h1 x :: acc) (all_pairs f t1 l2) l2

let cartesian_product l1 l2 = all_pairs (fun x y -> [x;y]) l1 l2

let rec all_sets n l =
  if n = 0 then [[]]
  else
    match l with
    | [] -> []
    | h :: t -> union (image (fun g -> h :: g) (all_sets (n - 1) t)) (all_sets n t)

let rec all_subsets s =
  match s with
  | [] -> [[]]
  | x :: t ->
     let res = all_subsets t in
     union (image (fun s -> x :: s) res) res

let all_nonempty_subsets s = subtract (all_subsets s) [[]]

let get_hyp = function
  | Argument (hyp, _) -> hyp

let get_ccl = function
  | Argument (_, ccl) -> ccl

let rec over_atoms (f : string * term list -> 'a -> 'a) (fm : formula) (acc : 'a) : 'a =
  match fm with
  | R (p, args) -> f (p, args) acc
  | Not p -> over_atoms f p acc
  | And (p, q)
  | Or (p, q)
  | Imp (p, q)
  | Iff (p, q) -> over_atoms f p (over_atoms f q acc)
  | Forall(x, p)
  | Exists(x, p) -> over_atoms f p acc
  | _ -> acc

let fvt tm =
  let rec fvt tm =
    match tm with
    | Var x -> [x]
    | Fn (_, args) -> map_flatten fvt args
  in
  setify (fvt tm)

let fv fm =
  let rec fv fm =
    match fm with
    | False | True -> []
    | R (_, args) -> map_flatten fvt args |> setify
    | Not p -> fv p
    | And (p, q) | Or (p, q) | Imp (p, q) | Iff (p, q) -> union (fv p) (fv q)
    | Forall (x, p) | Exists (x, p) -> subtract (fv p) [x]
  in
  fv fm

let rec simplify1 fm =
  match fm with
  | Not False -> True
  | Not True -> False
  | Not (Not p) -> p
  | And (p, False) | And (False, p) -> False
  | And (p, True)  | And (True, p) -> p
  | Or (p, False) | Or (False, p) -> p
  | Or (p, True) | Or (True, p) -> True
  | Imp (False, p) | Imp (p, True) -> True
  | Imp (True, p) -> p
  | Imp (p, False) -> Not p
  | Iff (p, True) | Iff (True, p) -> p
  | Iff (p, False) | Iff (False, p) -> Not p
  | Forall (x, p)
  | Exists (x, p) -> if mem x (fv p) then fm else p
  | _ -> fm

let rec simplify fm =
  match fm with
  | Not p -> simplify1 (Not (simplify p))
  | And (p, q) -> simplify1 (And (simplify p, simplify q))
  | Or (p, q) -> simplify1 (Or (simplify p, simplify q))
  | Imp (p, q) -> simplify1 (Imp (simplify p, simplify q))
  | Iff (p, q) -> simplify1 (Iff (simplify p, simplify q))
  | Forall(x, p) -> simplify1 (Forall (x, simplify p))
  | Exists(x, p) -> simplify1 (Exists (x, simplify p))
  | _ -> fm

let rec list_conj = function
  | [] -> True
  | [p] -> p
  | p :: r -> And (p, list_conj r)

let rec list_disj = function
  | [] -> False
  | [p] -> p
  | p :: r -> Or (p, list_disj r)

let rec variant x vars =
  if mem x vars then variant (x ^ "'") vars
  else x

let functions fm =
  let rec functions tm =
    match tm with
    | Var _ -> []
    | Fn (f, args) -> f :: (map_flatten functions args)
  in
  over_atoms (fun (_, args) acc -> map_flatten functions args :: acc) fm []
  |> flatten
  |> setify
