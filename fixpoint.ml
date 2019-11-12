exception AssertionFailure of string

let __inspect_loop_invariant__ = false

type stateSet = State.state list

let setOfList stlst =
  stlst

let rec contains st states =
  match states with
  | st'::l' -> if State.equal st st' then true else contains st l'
  | [] -> false

let rec stateUnion states1 states2 =
  match states1, states2 with
  | [],l -> l
  | l,[] -> l
  | s1::l1',l2 ->
    if contains s1 l2
    then stateUnion l1' l2
    else s1::(stateUnion l1' l2)

let nextSingleStateInstr inst st =

  (* Prevent reject states from becoming accepting states. *)
  if State.reject st then st
  else
    (* let () = State.printState st in *)
    match inst with

    | Execution.UpdateLocToData(name, args, from) ->
      let name_func, args_var_list, from_var =
        State.func_of_string name,
        List.map State.var_of_string args,
        State.var_of_string from in
      State.readUpdateLocToData
        st name_func args_var_list from_var

    | Execution.UpdateLocToLoc(name, args, from) ->
      let name_func, args_var_list, from_var =
        State.func_of_string name,
        List.map State.var_of_string args,
        State.var_of_string from in
      State.readUpdateLocToLoc
        st name_func args_var_list from_var

    | Execution.AssignFromLocToData(data, name, args) ->
      let data_var, name_func, args_var_list =
        State.var_of_string data,
        State.func_of_string name,
        List.map State.var_of_string args in
      State.readAssignFromLocToData
        st data_var name_func args_var_list

    | Execution.AssignFromLocToLoc(loc, name, args) ->
      let loc_var, name_func, args_var_list =
        State.var_of_string loc,
        State.func_of_string name,
        List.map State.var_of_string args in
      State.readAssignFromLocToLoc
        st loc_var name_func args_var_list

    | Execution.AssignFromDataToData(data, name, args) ->
      let data_var, name_func, args_var_list =
        State.var_of_string data,
        State.func_of_string name,
        List.map State.var_of_string args in
      State.readAssignFromDataToData
        st data_var name_func args_var_list

    | Execution.AssignFromData(data1, data2) ->
      let data1_var, data2_var =
        State.var_of_string data1,
        State.var_of_string data2 in
      State.readAssignFromData
        st data1_var data2_var

    | Execution.AssignFromLoc(loc1, loc2) ->
      let loc1_var, loc2_var =
        State.var_of_string loc1,
        State.var_of_string loc2 in
      State.readAssignFromLoc
        st loc1_var loc2_var

    | Execution.AssumeLocEq(loc1, loc2) ->
      let loc1_var, loc2_var =
        State.var_of_string loc1,
        State.var_of_string loc2 in
      State.readAssumeLocEq
        st loc1_var loc2_var

    | Execution.AssumeLocNeq(loc1, loc2) ->
      let loc1_var, loc2_var =
        State.var_of_string loc1,
        State.var_of_string loc2 in
      State.readAssumeLocNeq
        st loc1_var loc2_var

    | Execution.AssumeDataEq(data1, data2) ->
      let data1_var, data2_var =
        State.var_of_string data1,
        State.var_of_string data2 in
      State.readAssumeDataEq
        st data1_var data2_var

    | Execution.AssumeDataNeq(data1, data2) ->
      let data1_var, data2_var =
        State.var_of_string data1,
        State.var_of_string data2 in
      State.readAssumeDataNeq
        st data1_var data2_var

    | Execution.Free(loc) ->
      let loc_var = State.var_of_string loc in
      State.readFree st loc_var

    | Execution.Alloc(loc) ->
      let loc_var = State.var_of_string loc in
      State.readAlloc st loc_var

    | Execution.Exception ->
      raise (AssertionFailure("A non-rejecting state reached an exception"))

    | Execution.Skip -> st


let nextStatesInstr inst states =
  List.map (fun st -> nextSingleStateInstr inst st) states

(* `computeNextStates rgx startStates` returns a new set of states
 *  corresponding to all states reachable from states in startStates by
 *  following executions belonging to rgx *)
let rec computeNextStates rgx states =
  match rgx with

  | Execution.Concat(rgx1,rgx2) ->
    let states' = computeNextStates rgx1 states in
    computeNextStates rgx2 states'

  | Execution.Union(rgx1,rgx2) -> stateUnion
                          (computeNextStates rgx1 states)
                          (computeNextStates rgx2 states)

  (* the set of states computed here is a loop invariant *)
  | Execution.Star(rgx') ->
    let states' = computeFixpoint rgx' states in

    let _ =
      if __inspect_loop_invariant__ then
      print_endline "States after reaching fixed point for loop: \n\n";
      List.mapi (fun idx st ->
          print_string @@ "State "^(string_of_int idx)^":\n";
          State.visualize st) states'
    in

    states'

  | Execution.Base(i) -> nextStatesInstr i states

and computeFixpoint rgx states =
  let rec untilFixpoint rgx worklist states =
    (* This `if` could be moved to somewhere later (previous iteration.) *)
    print_endline @@ "Number of states during fixpoint: "^(string_of_int @@ List.length states);
    if List.length worklist = 0 then states else
      let states' = computeNextStates rgx worklist in
      let worklist' =
        List.filter
          (fun st ->
             if contains st states
             then false
             else true) states' in
      let states = stateUnion worklist' states in
      untilFixpoint rgx worklist' states
  in
  untilFixpoint rgx states states
