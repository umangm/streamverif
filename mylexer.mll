{
open Lexing
open Myparser

exception UnexpectedToken of string

let debug = false
let take s = if debug then print_string s else ()

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum+1
    }
}

let ident = ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let newline = '\r' | '\n' | "\r\n"
let white = [' ' '\t']+

rule read =
  parse
  | white { read lexbuf }
  | newline { next_line lexbuf; read lexbuf }
  | "while" { take "WHILE"; WHILE }
  | "{" { take "LBRACE"; LBRACE }
  | "}" { take "RBRACE"; RBRACE }
  | "if" { take "IF"; IF }
  | "then" { take "THEN"; THEN }
  | "else" { take "ELSE"; ELSE }
  | ":=" { take "ASSIGN"; ASSIGN }
  | "<-" { take "PUT"; PUT }
  | "assume" { take "ASSUME"; ASSUME }
  | "assert" { take "ASSERT"; ASSERT }
  | "skip" { take "SKIP"; SKIP }
  | "Reach" { take "REACH"; REACH }
  | "free" { take "FREE"; FREE }
  | "alloc" { take "ALLOC"; ALLOC }
  | "init" { take "INIT"; INIT }
  | ident { take "IDENT"; IDENT (Lexing.lexeme lexbuf) }
  | "," { take "COMMA"; COMMA }
  | "(" { take "LPAREN"; LPAREN }
  | ")" { take "RPAREN"; RPAREN }
  | "[" { take "LBRACK"; LBRACK }
  | "]" { take "RBRACK"; RBRACK }
  | ";" { take "SEMICOLON"; SEMICOLON }
  | "=" { take "EQ"; EQ }
  | "!=" { take "NEQ"; NEQ }
  | "(*" { take "COMMENT"; read_comment lexbuf }
  | eof { take "EOF"; EOF }
  | _ { raise (UnexpectedToken ("Lexical Error: ")) }

and read_comment =
  parse
  | "*)" { read lexbuf }
  | _ { read_comment lexbuf }
