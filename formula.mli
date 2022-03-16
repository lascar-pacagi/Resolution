type term =
| Var of string
| Fn of string * term list

type formula =
| False
| True
| R of string * term list
| Not of formula
| And of formula * formula
| Or of formula * formula
| Imp of formula * formula
| Iff of formula * formula
| Forall of string * formula
| Exists of string * formula

type argument = Argument of formula list * formula
