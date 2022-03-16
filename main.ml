open Formula

let ifile = ref ""

let set_file f s = f := s

let usage = "usage: solver file.arg"

let () =
  Arg.parse [] (set_file ifile) usage;

  if !ifile = "" then begin
    Arg.usage [] usage;
    exit 1
  end;

  if not (Filename.check_suffix !ifile ".arg") then begin
    Printf.printf "filename must have .arg suffix.\n";
    Arg.usage [] usage;
    exit 1
  end;

  let f = open_in !ifile in

  let lexbuf = Lexing.from_channel f in
  lexbuf.Lexing.lex_curr_p <-
    {
      Lexing.pos_fname = !ifile;
      Lexing.pos_lnum  = 1;
      Lexing.pos_bol   = 0;
      Lexing.pos_cnum  = 0
    };
  try
    let argument = Parser.argument Lexer.get_token lexbuf in
    Print.argument argument;
    let set = Util.get_hyp argument @ [Not (Util.get_ccl argument)] in
    let cnf = Proof.cnf set in
    List.map Util.list_disj cnf
    |> Print.formulas;
    Proof.resolution cnf
    |> Print.proof;
    close_in f;
    exit 0
  with
    | Lexer.Error msg ->
        Printf.printf "Lexical error %s:\n%s.\n" (Error.position (Lexing.lexeme_start_p lexbuf)) msg;
        exit 1
    | Parser.Error ->
        Printf.printf "Syntax error %s.\n" (Error.position (Lexing.lexeme_start_p lexbuf));
        exit 1
