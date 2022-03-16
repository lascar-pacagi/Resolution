open Formula
open Env
open Util

exception Not_unifiable

let is_trivial env x tm =
  let rec is_trivial x tm =
    match tm with
    | Var y -> y = x || (try is_trivial x (find y env) with Not_found -> false)
    | Fn (_, args) -> List.exists (is_trivial x) args && raise Not_unifiable
  in
  is_trivial x tm

let rec unify env eqs =
  match eqs with
  | [] -> env
  | (Fn (f, fargs), Fn (g, gargs)) :: others -> begin
    if f = g && List.length fargs = List.length gargs then
      unify env (List.combine fargs gargs @ others)
    else
      raise Not_unifiable
  end
  | (Var x, t) :: others -> begin
    try
      unify env ((find x env, t) :: others)
    with Not_found ->
      unify (if is_trivial env x t then env else (x |-> t) env) others
  end
  | (t, Var x) :: others -> unify env ((Var x, t) :: others)

let rec solve env =
  let env' = map (Substitution.in_term env) env in
  if Env.equal (=) env' env then env else solve env'

let full_unify eqs = solve (unify empty eqs)

let unify_and_apply eqs =
  let env = full_unify eqs in
  let apply (t1, t2) =
    Substitution.in_term env t1, Substitution.in_term env t2
  in
  List.map apply eqs

let rec unify_literals env (p, q) =
  match p, q with
  | R (p1, args1), R (p2, args2) -> unify env [Fn (p1, args1), Fn (p2, args2)]
  | Not p, Not q -> unify_literals env (p, q)
  | False, False -> env
  | True, True -> env
  | _ -> raise Not_unifiable

let unifiable p q = can (unify_literals empty) (p, q)

let rec mgu env l =
  match l with
  | a :: b :: rest -> mgu (unify_literals env (a, b)) (b :: rest)
  | _ -> solve env
