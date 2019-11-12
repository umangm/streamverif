open Printf
open Lexing
open Ast


let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Myparser.prog Mylexer.read lexbuf with
  | Mylexer.UnexpectedToken msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    None
  | Myparser.Error ->
    fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)

let print oc prog =

  let say s = Core.Out_channel.output_string oc s in
  let sayln s = say s; say "\n" in

  let rec indent = function
    | 0 -> ()
    | x -> say " "; indent (x-1) in

  let rec dolist d sep f = function
    | x::l' -> (match l' with
        | x'::l'' -> (f x (d+1); say sep; dolist d sep f l')
        | [] -> f x (d+1))
    | [] -> () in

  let rec print_stmt stm d =
    match stm with
    | Seq(s1,s2) -> indent d; print_stmt s1 d; sayln ";"; print_stmt s2 d

    | Assert(c) -> indent d; say "assert("; print_cond c d; say ")"

    | Skip -> indent d ; say "skip";

    | Assume(c) -> indent d; say "assume("; print_cond c d; say ")"

    | Assign(t1,t2) -> indent d; print_term t1 d; say " := "; print_term t2 d

    | Free(i) -> indent d; say "free("; print_ident i d; say ")"

    | Alloc(i) -> indent d; print_ident i d; say " := alloc()"

    | While(c,stm') -> indent d; say "while("; print_cond c d; sayln
        ") {"; print_stmt stm' (d+1); sayln ""; say "}"

    | Ite(c,s1,s2) -> indent d; say "if ("; print_cond c d; sayln ") then {";
      print_stmt s1 (d+1); sayln ""; sayln "} else {"; print_stmt s2 (d+1);
      sayln ""; say "}"

  and print_cond c d =
    match c with
    | Eq(v1,v2) -> indent d; say v1; say " = "; say v2
    | Neq(v1,v2) -> indent d; say v1; say " != "; say v2

  and print_ident v d =
    say v

  and print_term t d =
    match t with
    | Var(s) -> say s
    | App(f,args) -> say f; say "("; dolist d "," print_ident args; say ")"

  and print_prog (preamble_opt, stm) d =
    match preamble_opt with
    | Some Preamble(Reach(starts,pointers,stop), InitLoc(inits)) ->
      indent d;
      let print_list_ident l d =
        say "["; dolist d "," print_ident l; say "]"
      in
      say "Reach("; dolist d "," print_list_ident
        [starts;pointers;[stop]]; sayln ")";
      say "init {";
      let print_init (i1,i2) d =
        indent d; print_ident i1 d; say " := "; print_ident i2 d in
      let print_inits l d =
        dolist d ";" print_init l; sayln "" in
      print_inits inits d;
      sayln "}";
      print_stmt stm d
    | None -> print_stmt stm d

  in print_prog prog 0; sayln ""; Core.Out_channel.flush oc

(* -------------------------------------------------------------------------- *)

let parse_from_string content =
  let lexbuf = Lexing.from_string content in
  match parse_with_error lexbuf with

  | Some prog ->

    (* print stdout prog; *)
    let (preamble_opt,stm) = prog in
    let env = Typechecker.typecheck prog in
    let vlst,dtd_list,ltl_list,ltd_list,stop_singleton = Typechecker.names preamble_opt env in
    let stop =
      match stop_singleton with
      | [] -> failwith "Must give a stop location" (* hacky *)
      | x :: xs -> x in
    let startState =
      State.init
        (List.map State.var_of_string vlst)
        (List.map State.func_of_string dtd_list)
        (List.map State.func_of_string ltl_list)
        (List.map State.func_of_string ltd_list)
        (State.var_of_string stop) in
    (prog,env,startState)

  | None -> failwith "Failed to parse"

let parse_from_stdin () =
  let rec get_input content =
    let l = print_string "Next line (or 'q' to stop): "; read_line () in
    if l="q" then content else
    get_input (content ^ l)
  in
  get_input ""

let parse_from_file s =
  let ss = Core.In_channel.read_lines s in
  let content = Core.String.concat ss in
  parse_from_string content

let computeStates env prog startState =
  let rgx = Execution.regexOfProg env prog in
  let states = Fixpoint.computeNextStates rgx (Fixpoint.setOfList [startState]) in
  states

let check_reject states =
  List.for_all (fun st -> State.reject st) states

let test env prog startState =
  computeStates env prog startState

let visualize st =
  State.visualize st

let () =
  if Array.length Sys.argv != 3 then
    printf "Usage: ./main.exe path/to/input/program.unint \
            <true/false>\n\nThe second argument, if present, will \
            check that all complete, memory-safe executions are \
            infeasible\n"
  else
    let path, check = Sys.argv.(1), Sys.argv.(2) in
    let prog,env,startState = parse_from_file path in
    if String.equal check "true" then
      try let statesFinish = test env prog startState in
        printf "safe: %d states\n" (List.length statesFinish);
        if check_reject statesFinish then
          printf "All executions are infeasible\n"
        else
          printf "There is some feasible execution\n"
      with
      | State.MemorySafetyFailure(s) -> printf "unsafe\n"
      | State.MemoizingFailure(s) -> printf "incoherent: memoizing\n"
      | State.EarlyAssumesFailure(s) -> printf "incoherent: assumes\n"
    else if String.equal check "false" then
      try let statesFinish = test env prog startState in
        printf "safe: %d states\n" (List.length statesFinish);
      with
      | State.MemorySafetyFailure(s) -> printf "unsafe\n"
      | State.MemoizingFailure(s) -> printf "incoherent: memoizing\n"
      | State.EarlyAssumesFailure(s) -> printf "incoherent: assumes\n"
    else
      printf "The flag argument must be 'true' or 'false'\n"
