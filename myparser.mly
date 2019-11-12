%{
open Ast
%}

%token REACH
%token INIT
%token LBRACK
%token RBRACK
%token FREE
%token ALLOC

%token WHILE
%token LBRACE
%token RBRACE
%token IF
%token THEN
%token ELSE
%token ASSIGN
%token PUT
%token ASSUME
%token <string> IDENT
%token EQ
%token NEQ
%token COMMA
%token LPAREN
%token RPAREN
%token SEMICOLON
%token ASSERT
%token SKIP
%token EOF

%start <Ast.prog option> prog
%%

prog:
| p=option(preamble); s=stmt; EOF; { Some (p, s) }

preamble:
| r=reach; INIT; LBRACE; l=separated_list(SEMICOLON, init_location); RBRACE
  { Preamble(r, InitLoc(l)) }

init_location:
| i1=IDENT; ASSIGN; i2=IDENT; { (i1, i2) }

reach:
| REACH; LPAREN;

  LBRACK;
  starts=separated_nonempty_list(COMMA, IDENT);
  RBRACK; COMMA;

  LBRACK;
  pointers=separated_nonempty_list(COMMA, IDENT);
  RBRACK; COMMA;

  LBRACK;
  stop=IDENT;
  RBRACK;

  RPAREN;
  { Reach(starts, pointers, stop) }

stmt:
| s1=stmt; SEMICOLON; s2=stmt; { Seq(s1,s2) }
| a=assume_stmt; { a }
| a=assert_stmt; { a }
| s=skip_stmt; { s }
| f=free_stmt; { f }
| a=assign_stmt; { a }
| a=alloc_stmt; { a }
| w=while_stmt;  { w }
| i=ite; { i }

free_stmt:
| FREE; LPAREN; i=IDENT; RPAREN; { Free(i) }

alloc_stmt:
| i=IDENT; PUT; ALLOC; LPAREN; RPAREN; { Alloc(i) }

assert_stmt:
| ASSERT; LPAREN; c=cond; RPAREN; { Assert(c) }

skip_stmt:
| SKIP; { Skip }

assume_stmt:
| ASSUME; LPAREN; c=cond; RPAREN; { Assume(c) }

term:
| i=IDENT
  { Var(i) }
| i1=IDENT; LPAREN; is=separated_nonempty_list(COMMA, IDENT); RPAREN;
  { App(i1, is) }

assign_stmt:
| t1=term; ASSIGN; t2=term { Assign(t1, t2) }

while_stmt:
| WHILE; LPAREN; c=cond; RPAREN; LBRACE; s=stmt; RBRACE;
  { While(c,s) }

ite:
| IF; LPAREN; c=cond; RPAREN; THEN; LBRACE; s1=stmt; RBRACE; ELSE;
  LBRACE; s2=stmt; RBRACE
  { Ite(c,s1,s2) }

cond:
| i1=IDENT; EQ; i2=IDENT; { Eq(i1,i2) }
| i1=IDENT; NEQ; i2=IDENT; { Neq(i1,i2) }
