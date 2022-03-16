{
  open Lexing
  open Parser

  exception Error of string

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

  let regexp = Str.regexp "=>\\|<=>\\|\\.\\|\\+\\|forall\\|exists\\|true\\|false\\||="
  let bad_atom str = Str.string_match regexp str 0
}

let space = [' ' '\t']
let atom = [^ ' ' '\t' '\n' '(' ')' '{' '}' ',' '~']+

rule get_token = parse
  | "//" [^ '\n']* '\n'
  | '\n'      { newline lexbuf; get_token lexbuf }
  | space+    { get_token lexbuf }
  | "/*"      { comment lexbuf }
  | '+'       { OR }
  | '~'       { NOT }
  | '.'       { AND }
  | "=>"      { IMP }
  | "<=>"     { IFF }
  | "forall"  { FORALL }
  | "exists"  { EXISTS }
  | "|="      { VALIDITY }
  | '('       { LPAREN }
  | ')'       { RPAREN }
  | ","       { COMMA }
  | "true"    { TRUE }
  | "false"   { FALSE }
  | '{'       { LBRACE }
  | '}'       { RBRACE }
  | ['u'-'z'] | ['_''A'-'Z']['_''A'-'Z''a'-'z''0'-'9']* as v { VARIABLE v }
  | atom as a
      {
        if bad_atom a then
          raise (Error ("Illegal atom: " ^ a))
        else ATOM a
      }
  | "//" [^ '\n']* eof
  | eof     { EOF }
  | _ as c  { raise (Error ("Illegal character: " ^ String.make 1 c)) }

and comment = parse
  | "*/"    { get_token lexbuf }
  | '\n'    { newline lexbuf; comment lexbuf }
  | _       { comment lexbuf }
  | eof     { raise (Error ("Unterminated comment")) }
