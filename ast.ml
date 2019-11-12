type prog = preamble option * stmt

and preamble =
  Preamble of reach * init

and init =
    InitLoc of (string * string) list

and reach =
    Reach of string list *
             string list *
             string

and stmt =
  | Seq of stmt * stmt
  | Assert of cond
  | Skip
  | Assume of cond
  | Assign of term * term

  | Free of string
  | Alloc of string

  | While of cond * stmt
  | Ite of cond * stmt * stmt

and cond =
  | Eq of string * string
  | Neq of string * string

and term =
  | Var of string
  | App of string * string list

let hd_of_term t =
  match t with
  | Var s -> s
  | App (s, args) -> s

let args_of_term t =
  match t with
  | Var s -> []
  | App (s, args) -> args
