type execRegex =
  | Concat of execRegex * execRegex
  | Union of execRegex * execRegex
  | Star of execRegex
  | Base of instr

and instr =
  | UpdateLocToData of string * string list * string
  | UpdateLocToLoc of string * string list * string
  | AssignFromLocToData of string * string * string list
  | AssignFromLocToLoc of string * string * string list
  | AssignFromDataToData of string * string * string list
  | AssignFromData of string * string
  | AssignFromLoc of string * string
  | AssumeLocEq of string * string
  | AssumeLocNeq of string * string
  | AssumeDataEq of string * string
  | AssumeDataNeq of string * string
  | Free of string
  | Alloc of string
  | Exception
  | Skip

let neg c =
  match c with
  | Ast.Eq(v1,v2) -> Ast.Neq(v1,v2)
  | Ast.Neq(v1,v2) -> Ast.Eq(v1,v2)

let rec regexOfStmt env stm =
  match stm with

  | Ast.Seq(s1,s2) -> Concat(regexOfStmt env s1, regexOfStmt env s2)

  | Ast.Assert(c) ->
    Union
      (Concat (Base(regexOfCond env (neg c)), Base(Exception)),
       Concat (Base(regexOfCond env c), Base(Skip)))

  | Ast.Skip -> Base(Skip)

  | Ast.Assume(c) -> Base(regexOfCond env c)

  | Ast.Assign(t1, t2) ->
    (match t1, t2 with

     | Var i1, Var i2 ->
       (match Typechecker.lookup i1 env, Typechecker.lookup i2 env with
        | Data, Data -> Base(AssignFromData(i1, i2))
        | Location, Location -> Base(AssignFromLoc(i1, i2))
        | _ -> failwith "Typechecker is buggy")

     | App (i1, args), Var i2 ->
       (match Typechecker.lookup i1 env, Typechecker.lookup i2 env with
        | LocToLoc, _ -> Base(UpdateLocToLoc(i1, args, i2))
        | LocToData, _ -> Base(UpdateLocToData(i1, args, i2))
        | _ -> failwith "Typechecker is buggy")

     | Var i1, App (i2, args) ->
       (match Typechecker.lookup i1 env, Typechecker.lookup i2 env with
        | _, LocToLoc -> Base(AssignFromLocToLoc(i1, i2, args))
        | _, LocToData -> Base(AssignFromLocToData(i1, i2, args))
        | _, DataToData(arity) -> Base(AssignFromDataToData(i1, i2, args))
        | _ -> failwith "Typechecker is buggy")

     | _, _ -> failwith "Typechecker is buggy")

  | Ast.Free(i) -> Base(Free(i))

  | Ast.Alloc(i) -> Base(Alloc(i))

  | Ast.While(c,s) ->
    Concat
      (Star(Concat (Base(regexOfCond env c), regexOfStmt env s)),
       Base(regexOfCond env @@ neg c))

  | Ast.Ite(c,s1,s2) ->
    Union
      (Concat (Base(regexOfCond env c), regexOfStmt env s1),
       Concat (Base(regexOfCond env @@ neg c), regexOfStmt env s2))

and regexOfCond env c =
  match c with
  | Ast.Eq(i1, i2) ->
    (match Typechecker.lookup i1 env with
     | Data -> AssumeDataEq(i1, i2)
     | Location -> AssumeLocEq(i1, i2)
     | _ -> failwith "Typechecker is buggy")
  | Ast.Neq(i1, i2) ->
    (match Typechecker.lookup i1 env with
     | Data -> AssumeDataNeq(i1, i2)
     | Location -> AssumeLocNeq(i1, i2)
     | _ -> failwith "Typechecker is buggy")

let regexOfProg env (preamble_opt, stm) =
  match preamble_opt with
  | None -> regexOfStmt env stm
  | Some (Ast.Preamble(_, Ast.InitLoc(init_list))) ->
    List.fold_right
      (fun (i1, i2) acc ->
         Concat(Base(AssignFromLoc(i1, i2)), acc))
      init_list (regexOfStmt env stm)
