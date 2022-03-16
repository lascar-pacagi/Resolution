%{
  open Formula
%}

%token <string> ATOM
%token <string> VARIABLE
%token FALSE TRUE
%token OR AND NOT IMP IFF FORALL EXISTS
%token VALIDITY
%token COMMA
%token LPAREN RPAREN LBRACE RBRACE
%token EOF

%nonassoc QUANT
%right IFF
%right IMP
%left OR
%left AND
%nonassoc NOT

%start argument

%type <Formula.argument> argument

%%

argument:
| hyp = option(LBRACE fs = list(formula) RBRACE { fs }) VALIDITY ccl = formula EOF
   {
     Argument ((match hyp with | None -> [] | Some l -> l), ccl)
   }

term:
| v = VARIABLE { Var v }
| a = ATOM     { Fn (a, []) }
| fct = ATOM LPAREN args = separated_list(COMMA, term) RPAREN { Fn (fct, args) }
| fct = VARIABLE LPAREN args = separated_list(COMMA, term) RPAREN { Fn (fct, args) }

formula:
| p = ATOM LPAREN args = separated_list(COMMA, term) RPAREN { R (p, args) }
| p = VARIABLE LPAREN args = separated_list(COMMA, term) RPAREN { R (p, args) }
| FALSE { False }
| TRUE  { True }
| NOT p = formula { Not p }
| p = formula AND q = formula { And (p, q) }
| p = formula OR  q = formula { Or (p, q) }
| p = formula IMP q = formula { Imp (p, q) }
| p = formula IFF q = formula { Iff (p, q) }
| FORALL x = VARIABLE p = formula %prec QUANT { Forall (x, p) }
| EXISTS x = VARIABLE p = formula %prec QUANT { Exists (x, p) }
| LPAREN p = formula RPAREN { p }
