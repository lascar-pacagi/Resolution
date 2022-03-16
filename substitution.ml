open Formula
open Env
open Util
open List

let rec in_term env t =
  match t with
  | Var x -> find_default x t env
  | Fn (f, args) -> Fn (f, map (in_term env) args)

let rec in_formula env fm =
  match fm with
  | False -> False
  | True -> True
  | R (p, args) -> R (p, map (in_term env) args)
  | Not p -> Not (in_formula env p)
  | And (p, q) -> And (in_formula env p, in_formula env q)
  | Or (p, q)  -> Or (in_formula env p, in_formula env q)
  | Imp (p, q) -> Imp (in_formula env p, in_formula env q)
  | Iff (p, q) -> Iff (in_formula env p, in_formula env q)
  | Forall (x, p) -> in_formulaq env mk_forall x p
  | Exists (x, p) -> in_formulaq env mk_exists x p

and in_formulaq env quant x p =
  let x' =
    if exists
      (fun y -> mem x (fvt (find_default y (Var y) env)))
      (subtract (fv p) [x])
    then
      variant x (fv (in_formula (Env.remove x env) p))
    else x
  in
  quant x' (in_formula ((x |-> Var x') env) p)

let in_argument env = function
  | Argument (hyp, ccl) -> Argument (map (in_formula env) hyp, in_formula env ccl)
