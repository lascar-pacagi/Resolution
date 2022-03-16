open Formula
open Env
open Util
open List

let rec nnf fm =
  match fm with
  | And (p, q) -> And (nnf p, nnf q)
  | Or (p, q) -> Or (nnf p, nnf q)
  | Imp (p, q) -> Or (nnf (Not p), nnf q)
  | Iff (p, q) -> Or (And (nnf p, nnf q), And(nnf (Not p), nnf (Not q)))
  | Not (Not p) -> nnf p
  | Not (And (p, q)) -> Or (nnf (Not p), nnf (Not q))
  | Not (Or(p, q)) -> And (nnf (Not p), nnf (Not q))
  | Not (Imp (p, q)) -> And (nnf p, nnf (Not q))
  | Not (Iff (p, q)) -> Or (And (nnf p, nnf (Not q)), And (nnf (Not p), nnf q))
  | Forall (x, p) -> Forall (x, nnf p)
  | Exists (x, p) -> Exists (x, nnf p)
  | Not (Forall (x, p)) -> Exists (x, nnf (Not p))
  | Not (Exists (x, p)) -> Forall (x, nnf (Not p))
  | _ -> fm

let rec pullquants fm =
  match fm with
  | And (Forall (x, p), Forall (y, q)) -> pullq (true, true) fm mk_forall mk_and x y p q
  | Or (Exists (x, p), Exists (y, q)) -> pullq (true, true) fm mk_exists mk_or x y p q
  | And (Forall (x, p), q) -> pullq (true, false) fm mk_forall mk_and x x p q
  | And (p, Forall (y, q)) -> pullq (false, true) fm mk_forall mk_and y y p q
  | Or (Forall(x, p), q) -> pullq (true, false) fm mk_forall mk_or x x p q
  | Or (p, Forall(y, q)) -> pullq (false, true) fm mk_forall mk_or y y p q
  | And (Exists (x, p), q) -> pullq (true, false) fm mk_exists mk_and x x p q
  | And (p, Exists (y, q)) -> pullq (false, true) fm mk_exists mk_and y y p q
  | Or (Exists (x, p), q) -> pullq (true, false) fm mk_exists mk_or x x p q
  | Or (p, Exists (y, q)) -> pullq (false, true) fm mk_exists mk_or y y p q
  | _ -> fm

and pullq (l, r) fm quant op x y p q =
  let z = variant x (fv fm) in
  let p' = if l then Substitution.in_formula (x |=> Var z) p else p
  and q' = if r then Substitution.in_formula (y |=> Var z) q else q in
  quant z (pullquants (op p' q'))

let rec prenex fm =
  match fm with
  | Forall (x, p) -> Forall (x, prenex p)
  | Exists (x, p) -> Exists (x, prenex p)
  | And (p, q) -> pullquants (And (prenex p, prenex q))
  | Or (p, q) -> pullquants (Or (prenex p, prenex q))
  | _ -> fm

let skolem fms =
  let rec skolem1 fm fcts =
    match fm with
    | Exists (y, p) -> begin
      let xs = fv fm in
      let f = variant (if xs = [] then "c_" ^ y else "f_" ^ y) fcts in
      let fx = Fn (f, List.map (fun x -> Var x) xs) in
      skolem1 (Substitution.in_formula (y |=> fx) p) (f :: fcts)
    end
    | Forall (x, p) -> let p', fcts' = skolem1 p fcts in Forall (x, p'), fcts'
    | And (p, q) -> skolem2 mk_and (p, q) fcts
    | Or (p, q) -> skolem2 mk_or (p, q) fcts
    | _ -> fm, fcts
  and skolem2 cons (p, q) fcts =
    let p', fcts'  = skolem1 p fcts in
    let q', fcts'' = skolem1 q fcts' in
    (cons p' q'), fcts''
  in
  fold_left
    (fun (res, fct) fm ->
      let fm', fct' = skolem1 fm fct in
      fm' :: res, fct'
    ) ([], functions (list_conj fms)) fms
  |> fst
  |> rev

let rec specialize fm =
  match fm with
  | Forall (x, p) -> specialize p
  | _ -> fm

let skolemize fms =
  map (prenex ** nnf ** simplify) fms
  |> skolem
  |> map specialize

let distribute l1 l2 =
  cartesian_product l1 l2
  |> map (setify ** flatten)

let pure_cnf fm =
  let rec pure_cnf fm =
    match fm with
    | Or (p, q)  -> distribute (pure_cnf p) (pure_cnf q)
    | And (p, q) -> pure_cnf p @ pure_cnf q
    | _ -> [[fm]]
  in
  setify (pure_cnf fm)

let negative = function (Not p) -> true | _ -> false

let positive lit = not (negative lit)

let negate = function (Not p) -> p | p -> Not p

let trivial literals =
  let pos, neg = partition positive literals in
  exists (fun lit -> mem (negate lit) neg) pos

let simplified_cnf fm =
  if fm = True then []
  else
    if fm = False then [[]]
    else
      let clauses = filter (not ** trivial) (pure_cnf fm) in
      filter
        (
          fun clause ->
            not (exists (fun clause' -> Util.subset clause' clause) clauses)
        )
        clauses

let cnf fms =
  skolemize fms
  |> list_conj
  |> simplified_cnf

let resolvents f clause1 clause2 p acc =
  let cl2 = filter (Unification.unifiable (negate p)) clause2 in
  if cl2 = [] then acc
  else
    let cl1 = filter (fun q -> q <> p && Unification.unifiable p q) clause1 in
    let pairs =
      all_pairs (fun c1 c2 -> c1, c2)
        (map (fun cl -> p :: cl) (all_subsets cl1))
        (all_nonempty_subsets cl2)
    in
    fold_left (fun acc (c1, c2) ->
        try
          (
            let res =
              union (subtract clause1 c1) (subtract clause2 c2)
              |> image (Substitution.in_formula (Unification.mgu empty (c1 @ map negate c2)))
            in
            f res;
            res
          ) :: acc
        with Unification.Not_unifiable -> acc)
      acc pairs

let rename prefix clause =
  let free_variables = fv (list_disj clause) in
  let renamed_variables = map (fun s -> Var (prefix ^ s)) free_variables in
  map (Substitution.in_formula (Env.create free_variables renamed_variables)) clause

let resolve_clauses graph clause1 clause2 =
  let clause1' = rename "x" clause1 in
  let clause2' = rename "y" clause2 in
  fold_right
    (resolvents (fun res -> Graph.add graph res (clause1, clause2)) clause1' clause2')
    clause1'
    []

exception No_proof

let rec term_match env eqs =
  match eqs with
  | [] -> env
  | (Fn (f, fargs), Fn (g, gargs)) :: others when f = g && length fargs = length gargs ->
    term_match env (combine fargs gargs @ others)
  | (Var x, t) :: others -> begin
    if not (Env.mem x env) then term_match ((x |-> t) env) others
    else
      if Env.find x env = t then term_match env others
      else failwith "term_match"
  end
  | _ -> failwith "term_match"

let rec match_literals env (p, q) =
  match p, q with
  | R (p, args1), R (q, args2)
  | Not (R (p, args1)), Not (R (q, args2)) -> term_match env [Fn (p, args1), Fn (q, args2)]
  | _ -> failwith "match_literals"

let subsumes_clause clause1 clause2 =
  let rec subsume env clause =
    match clause with
    | [] -> env
    | lit1 :: others ->
      try_find
        (fun lit2 -> subsume (match_literals env (lit1, lit2)) others)
        clause2
  in
  can (subsume empty) clause1

let rec replace clause clause_list =
  match clause_list with
  | []     -> [clause]
  | c :: r ->
     if subsumes_clause clause c then clause :: r
     else c :: (replace clause r)

let incorporate parent_clause clause unused =
  if trivial clause ||
       exists (fun c -> subsumes_clause c clause) (parent_clause :: unused)
  then
    unused
  else
    replace clause unused

let rec resolution_loop graph (used, unused) =
  match unused with
  | [] -> raise No_proof
  | c :: r -> begin
      let used = insert c used in
      let news =
        map_flatten (resolve_clauses graph c) used
      in
      if mem [] news then
        graph
      else
        resolution_loop graph
          (used, fold_left (fun acc c' -> incorporate c c' acc) r news)
    end

let resolution clauses =
  let graph = Graph.empty () in
  List.iter (fun clause -> Graph.add graph clause ([], [])) clauses;
  resolution_loop graph ([], clauses)
