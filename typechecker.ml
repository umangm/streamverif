open Ast

exception IllTyped of string

module SymbolMap = Map.Make(
  struct
    type t = string
    let compare = Pervasives.compare
  end)

type t =
  | Data
  | Location
  | LocToLoc
  | LocToData
  | DataToData of int

let string_of_type typ =
  match typ with
  | Data -> "Data"
  | Location -> "Location"
  | LocToLoc -> "LocToLoc"
  | LocToData -> "LocToData"
  | DataToData(_) -> "DataToData"

type env = t SymbolMap.t

let different env i1 i2 =
  assert(SymbolMap.mem i1 env && SymbolMap.mem i2 env);
  match SymbolMap.find i1 env, SymbolMap.find i2 env with
  | Data, Data -> false
  | Location, Location -> false
  | LocToLoc, LocToLoc -> false
  | LocToData, LocToData -> false
  | DataToData(i1), DataToData(i2) -> if i1 = i2 then false else true
  | _, _ -> true

let same_type env args =
  assert (List.for_all (fun arg -> SymbolMap.mem arg env) args);
  let types = List.map (fun arg -> SymbolMap.find arg env) args in
  not ((List.exists
          (fun typ -> match typ with Data -> true | _ -> false) types) &&
       (List.exists
          (fun typ -> match typ with Location -> true | _ -> false) types))

let rec typecheck' env stm =
  match stm with

  | Seq(stm1,stm2) ->
    let env' = typecheck' env stm1 in
    typecheck' env' stm2

  | Assert(c) ->
    typecheck_cond env c

  | Skip -> env

  | Assume(c) ->
    typecheck_cond env c

  | Assign(t1,t2) ->
    typecheck_assign env t1 t2

  | Free(i) ->
    typecheck_loc_ref env i

  | Alloc(i) ->
    typecheck_loc_ref env i

  | While(c,stm') ->
    let env' = typecheck_cond env c in
    typecheck' env' stm'

  | Ite(c,stm1,stm2) ->
    let env' = typecheck_cond env c in
    let env'' = typecheck' env' stm1 in
    typecheck' env'' stm2

and typecheck_var env i =
  match SymbolMap.find_opt i env with
  | None -> SymbolMap.add i Data env
  | Some Data | Some Location -> env
  | _ -> raise(IllTyped("Expected Data or Location, found composite type"))

and typecheck_todata env i args =
  match args with

  | [] ->
    raise (IllTyped("Nullary applications (except alloc) are disallowed)"))

  | x :: xs as args ->
    let env' =
      List.fold_left (fun acc arg -> typecheck_var acc arg) env args
    in
    if same_type env' args then
      (match SymbolMap.find x env' with
       | Data -> SymbolMap.add i (DataToData(List.length args)) env'
       | Location -> SymbolMap.add i LocToData env'
       | _ -> raise (IllTyped("Should not be reachable")))
    else
      raise (IllTyped("Different argument types for application of symbol "^i))

and typecheck_assign env t1 t2 =
  match t1, t2 with

  | Var i1, Var i2 ->
    let env' = typecheck_var (typecheck_var env i1) i2 in
    if (different env' i1 i2) then
      let typ1, typ2 =
        string_of_type @@ SymbolMap.find i1 env',
        string_of_type @@ SymbolMap.find i2 env' in
      raise (IllTyped("Different types in assignment: "^i1^": "^typ1^", and "^i2^" : "^typ2))
    else env'

  | Var i1, App (i2, args) ->
    (match SymbolMap.find_opt i2 env with

     | None ->
       (match SymbolMap.find_opt i1 env with

        | None | Some Data ->
          let env' = SymbolMap.add i1 Data env in
          typecheck_todata env' i2 args

        | Some Location ->
          (* must be LocToLoc *)
          let env' = SymbolMap.add i2 LocToLoc env in
          List.fold_left (fun acc arg -> typecheck_loc_ref acc arg)
            env' args

        | _ -> raise (IllTyped("Attempt to assign to an Application")))

     | Some DataToData(a) ->
       assert(List.length args = a);
       let env' = typecheck_data env i1 in
       List.fold_left (fun acc arg -> typecheck_data acc arg)
         env' args

     | Some LocToData ->
       let env' = typecheck_data env i1 in
       List.fold_left (fun acc arg -> typecheck_loc_ref acc arg)
         env' args

     | Some LocToLoc ->
       let env' = typecheck_loc_ref env i1 in
       List.fold_left (fun acc arg -> typecheck_loc_ref acc arg)
         env' args

     | _ -> raise (IllTyped("Data or Location type is applied to arguments")))

  | App (i1, args), Var i2 ->
    (match SymbolMap.find_opt i1 env with

     | None -> (* must be LocToData *)
       let env' = SymbolMap.add i1 LocToData env in
       let env'' = List.fold_left (fun acc arg -> typecheck_loc_ref acc arg)
           env' args in
       typecheck_data env'' i2

     | Some LocToData ->
       let env' = List.fold_left (fun acc arg -> typecheck_loc_ref acc arg)
           env args in
       typecheck_data env' i2

     | Some DataToData(_) -> raise(IllTyped("Attempt to assign to DataToData"))

     | Some LocToLoc ->
       let env' = List.fold_left (fun acc arg -> typecheck_loc_ref acc arg)
           env args in
       typecheck_loc_ref env' i2

     | _ -> raise (IllTyped("Data or Location type is applied to arguments")))


  | App (i1, args1), App (i2, args2) ->
    failwith "Unsupported: Applications on both sides of assignment operator"

and typecheck_data env i =
  match SymbolMap.find_opt i env with
  | None -> SymbolMap.add i Data env
  | Some Data -> env
  | _ -> raise (IllTyped("Expected Data, found otherwise for symbol "^i))

and typecheck_cond' env i1 i2 =
  let env = typecheck_var (typecheck_var env i1) i2 in
  if (different env i1 i2) then
    let typ1, typ2 =
      string_of_type @@ SymbolMap.find i1 env,
      string_of_type @@ SymbolMap.find i2 env in
    raise
      (IllTyped("Different types in condition: "^i1^": "^typ1^", and "^i2^" : "^typ2))
  else env

and typecheck_cond env c =
  match c with
  | Eq(i1,i2) | Neq(i1,i2) -> typecheck_cond' env i1 i2

(* if i is not already type Location in env, make it so *)
and typecheck_loc_init env i =
  match SymbolMap.find_opt i env with
  | None -> SymbolMap.add i Location env
  | Some Location -> env
  | Some Data -> raise (IllTyped("Expected Location, found Data for symbol "^i))
  | _ -> raise (IllTyped("Expected Location, found Application for symbol "^i))

(* ensure i has type Location in env *)
and typecheck_loc_ref env i =
  match SymbolMap.find_opt i env with
  | None -> raise (IllTyped("Undeclared Location reference of symbol "^i))
  | Some Location -> env
  | Some Data -> raise(IllTyped("Expected Location, found Data for symbol "^i))
  | _ -> raise(IllTyped("Expected Location, found Application for symbol "^i))

(* if i is not already type LocToLoc in env, make it so *)
and typecheck_loctoloc env i =
  match SymbolMap.find_opt i env with
  | None -> SymbolMap.add i LocToLoc env
  | Some LocToLoc -> env
  | _ -> raise (IllTyped("Expected LocToLoc, found something else for symbol "^i))

let typecheck_reach env (starts, pointers, stop) =
  let env = List.fold_left typecheck_loc_init env starts in
  let env = List.fold_left typecheck_loctoloc env pointers in
  let env = typecheck_loc_init env stop in env

let typecheck_init env (i1, i2) =
  let env' = typecheck_loc_ref env i2 in
  typecheck_loc_init env' i1

let typecheck_preamble env preamble_opt =
  match preamble_opt with
  | Some (Preamble(Reach(starts, pointers, stop), InitLoc(inits))) ->
    let env' = typecheck_reach env (starts, pointers, stop) in
    List.fold_left (fun acc init -> typecheck_init acc init) env' inits
  | None -> env

let typecheck (preamble_opt, stm) =
  let env = typecheck_preamble SymbolMap.empty preamble_opt in
  typecheck' env stm

let lookup i env =
  SymbolMap.find i env

let names preamble_opt env =
  let varMap, appMap = SymbolMap.partition
      (fun _ typ ->
         match typ with
         | Data | Location -> true
         | _ -> false) env in
  let var_bindings = SymbolMap.bindings varMap in
  let dataToDataMap, restMap = SymbolMap.partition
      (fun k v -> match v with | DataToData(_) -> true | _ -> false)
      appMap in
  let locToLocMap, locToDataMap = SymbolMap.partition
      (fun k v -> match v with | LocToLoc -> true | _ -> false)
      restMap in
  let dataToData_bindings = SymbolMap.bindings dataToDataMap in
  let locToLoc_bindings = SymbolMap.bindings locToLocMap in
  let locToData_bindings = SymbolMap.bindings locToDataMap in
  let var_list, dataToData_list, locToLoc_list, locToData_list =
    List.map fst var_bindings,
    List.map fst dataToData_bindings,
    List.map fst locToLoc_bindings,
    List.map fst locToData_bindings in
  match preamble_opt with
  | Some Preamble(Reach(_, _, stop), _) ->
    (var_list, dataToData_list, locToLoc_list, locToData_list, [stop])
  | None ->
    (var_list, dataToData_list, locToLoc_list, locToData_list, [])
