open Formula
open Printf

(* ------------------------------------------------------------------------- *)

(* Newlines and indentation. *)

let maxindent =
  120

let whitespace = String.make maxindent ' '

let indentation =
  ref 0

let nl () =
  "\n" ^ String.sub whitespace 0 !indentation

let indent ofs producer () x =
  let old_indentation = !indentation in
  let new_indentation = old_indentation + ofs in
  if new_indentation <= maxindent then
    indentation := new_indentation;
  let result = sprintf "%t%a" nl producer x in
  indentation := old_indentation;
  result

let indent' ofs producer () =
  let old_indentation = !indentation in
  let new_indentation = old_indentation + ofs in
  if new_indentation <= maxindent then
    indentation := new_indentation;
  let result = sprintf "%t%t" nl producer in
  indentation := old_indentation;
  result

(* ------------------------------------------------------------------------- *)

(* Lists. *)

let rec list elem () xs =
  match xs with
  | [] ->
    ""
  | x :: xs ->
      sprintf "%a%a" elem x (list elem) xs

let rec preclist delim elem () xs =
  match xs with
  | [] ->
    ""
  | x :: xs ->
      sprintf "%t%a%a" delim elem x (preclist delim elem) xs

let rec termlist delim elem () xs =
  match xs with
  | [] ->
    ""
  | x :: xs ->
      sprintf "%a%t%a" elem x delim (termlist delim elem) xs

let seplist sep elem () xs =
  match xs with
  | [] ->
    ""
  | x :: xs ->
      sprintf "%a%a" elem x (preclist sep elem) xs

let annlist announcement list () xs =
  match xs with
  | [] ->
    ""
  | _ :: _ ->
      sprintf "%t%a" announcement list xs

(* ------------------------------------------------------------------------- *)

(* Punctuation. *)

let space () =
  sprintf " "

let comma () =
  sprintf ", "

let semicolon () =
  sprintf "; "

let var () =
  sprintf "var "

let seminl () =
  sprintf "%t%t" semicolon nl

let nlspace k () =
  sprintf "%t%s" nl (String.make k ' ')

let nlnl () =
  sprintf "%t%t" nl nl


(* ------------------------------------------------------------------------- *)

(* Formula. *)

let tab = 2

let false_str  = "\xe2\x8a\xa5"
let true_str   = "\xe2\x8a\xa4"
let not_str    = "\xc2\xac"
let and_str    = "\xe2\x88\xa7"
let or_str     = "\xe2\x88\xa8"
let imp_str    = "\xe2\x87\x92"
let iff_str    = "\xe2\x87\x94"
let forall_str = "\xe2\x88\x80"
let exists_str = "\xe2\x88\x83"
let val_str    = "\xe2\x8a\xa8"
let lbrace_str = "\xe2\x9d\xb4"
let rbrace_str = "\xe2\x9d\xb5"
let trianglel_str = "\xe2\x97\x81"
let triangler_str = "\xe2\x96\xb7"
let square = "\xe2\x96\xa1"
let branch = "\xe2\x94\x9c"
let branch_end = "\xe2\x94\x94"
let pipe = "\xe2\x94\x82"

let rec term () = function
| Var x -> x
| Fn (f, args) ->
  sprintf "%s%s%a%s"
    f
    (if args = [] then "" else "(")
    (seplist comma term) args
    (if args = [] then "" else ")")

let rec formula0 () = function
  | False -> false_str
  | True  -> true_str
  | R (p, args) ->
    sprintf "%s%s%a%s"
      p
      (if args = [] then "" else "(")
      (seplist comma term) args
      (if args = [] then "" else ")")
  | p -> sprintf "(%a)" formula p

and formula1 () = function
  | Not p -> sprintf "%s%a" not_str formula1 p
  | p -> formula0 () p

and formula2 () = function
  | And (p, q) ->
    sprintf "%a %s %a"
      formula2 p
      and_str
      formula2 q
  | p -> formula1 () p

and formula3 () = function
  | Or (p, q)  ->
    sprintf "%a %s %a"
      formula3 p
      or_str
      formula3 q
  | p -> formula2 () p

and formula4 () = function
  | Imp (p, q) ->
    sprintf "%a %s %a"
      formula4 p
      imp_str
      formula4 q
  | p -> formula3 () p

and formula5 () = function
  | Iff (p, q) ->
    sprintf "%a %s %a"
      formula5 p
      iff_str
      formula5 q
  | p -> formula4 () p

and formula6 () = function
  | Forall (x, p) ->
    sprintf "%s%s. %a"
      forall_str
      x
      formula6 p
  | Exists (x, p) ->
    sprintf "%s%s. %a"
      exists_str
      x
      formula6 p
  | p -> formula5 () p

and formula () p = formula6 () p

let formulas fms =
  sprintf "%s%a%t%s%t"
    lbrace_str
    (seplist comma (indent tab formula)) fms
    nl
    rbrace_str
    nl
  |> printf "%s%!"

let argument arg =
  (
    match arg with
    | Argument ([], ccl) ->
      sprintf "%s %a%t"
        val_str
        formula ccl
        nl
    | Argument (hyp, ccl) ->
      sprintf "%s%a%t%s %s %a%t"
        lbrace_str
        (seplist comma (indent tab formula)) hyp
        nl
        rbrace_str
        val_str
        formula ccl
        nl
  ) |> printf "%s%!"

let proof graph =
  let rec print prefix () clause =
      let (c1, c2) = Graph.find graph clause in
      if c1 = [] && c2 = [] then
        sprintf " %a"
          formula (Util.list_disj clause)
      else begin
        let s =
          if clause = [] then square
          else sprintf "%a" formula (Util.list_disj clause)
        in
        let prefix' = prefix ^ String.make 2 ' ' in
        sprintf " %s\n%s%s%a\n%s%s%a"
          s
          prefix'
          branch
          (print (prefix' ^ pipe)) c1
          prefix'
          branch_end
          (print (prefix' ^ " ")) c2
      end
  in
  sprintf "%a" (print "") []
  |> printf "%s\n%!"
