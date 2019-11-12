exception Unhandled of string
exception MemorySafetyFailure of string
exception MemoizingFailure of string
exception EarlyAssumesFailure of string

type var = Var of string
type func = Func of string

let string_of_var x = match x with Var s -> s
let var_of_string s = Var s

let rec string_of_vars xs =
  match xs with
  | [] -> ""
  | x :: [] -> string_of_var x
  | x :: y :: rest -> string_of_var x ^ ", " ^ string_of_vars (y :: rest)

let string_of_func f = match f with Func s -> s
let func_of_string s = Func s

let compare_var x y =
  Pervasives.compare (string_of_var x) (string_of_var y)

let ( @< ) = fun x y -> compare_var x y < 0
let ( @= ) = fun x y -> compare_var x y = 0
let ( @> ) = fun x y -> compare_var x y > 0

let compare_args xs ys =
  Pervasives.compare (List.map string_of_var xs) (List.map string_of_var ys)

let compare_func x y =
  Pervasives.compare (string_of_func x) (string_of_func y)

let ( #< ) = fun x y -> compare_func x y < 0
let ( #= ) = fun x y -> compare_func x y = 0
let ( #> ) = fun x y -> compare_func x y > 0

(* N.B. same comment as that for maps below *)
module VarSet = Set.Make(
  struct
    type t = var
    let compare = compare_var
  end)

module FuncSet = Set.Make(
  struct
    type t = func
    let compare = compare_func
  end)

module PairSet = Set.Make(
  struct
    type t = var * var
    let compare (v1,v2) (v3,v4) =
      let first = compare_var v1 v3 in
      if first = 0 then compare_var v2 v4
      else first
  end)

(* N.B. cannot hash our maps, since different map insertion
 *      patterns will result in different underlying
 *      tree representations, so to test equality of states, we must use
 *      Map.equal, rather than a proper hash function *)
module VarMap = Map.Make(
  struct
    type t = var
    let compare = compare_var
  end)

module FunctionMap = Map.Make(
  struct
    type t = func
    let compare = compare_func
  end)

module EvaluationMap = Map.Make(
  struct
    type t = var list
    let compare = compare_args
  end)

module ArgumentSet = Set.Make(
  struct
    type t = var list
    let compare = compare_args
  end)

type varset = VarSet.t
type repmap = var VarMap.t
type classmap = VarSet.t VarMap.t
type emap = var EvaluationMap.t
type pmap = emap FunctionMap.t
type deq = PairSet.t
type memo = ArgumentSet.t FunctionMap.t

type maptype = DataToData | LocToLoc | LocToData

(* new memory safety component *)
type safety = {stop : var;
               yes : varset;
               free : varset}

type state = {rm : repmap;
              cm : classmap;
              pm : pmap;
              dq : deq;
              mm : memo;
              safe : safety;
              tp : func -> maptype}


(* Utilities for accessing components of state values *)

let getRmap st = st.rm
let getCmap st = st.cm
let getPmap st = st.pm
let getDeq  st = st.dq
let getMemo st = st.mm
let getSafe st = st.safe
let getTypes st = st.tp

let getStop safe = safe.stop
let getYes safe = safe.yes
let getFree safe = safe.free

(* -------------------------------------------------------------------------- *)

(* Equality of rm *)
let equal_rm rm1 rm2 = VarMap.equal (@=) rm1 rm2
let equal_cm cm1 cm2 = VarMap.equal (VarSet.equal) cm1 cm2
let equal_em em1 em2 = EvaluationMap.equal (@=) em1 em2
let equal_pm pm1 pm2 = FunctionMap.equal (equal_em) pm1 pm2
let equal_dq dq1 dq2 = PairSet.equal dq1 dq2

(* Equality of states *)
let equal st1 st2 =
  let {rm=rm1;cm=cm1;pm=pm1;dq=dq1;_} = st1 in
  let {rm=rm2;cm=cm2;pm=pm2;dq=dq2;_} = st2 in
  (equal_rm rm1 rm2) &&
  (equal_cm cm1 cm2) &&
  (equal_pm pm1 pm2) &&
  (equal_dq dq1 dq2)

(* ----------------------------------------------------------- *)

let find st x = VarMap.find x (getRmap st)

let sameClass st x y =
  find st x @= find st y

let listOfAllReps st =
  let cm = getCmap st in
  List.map fst (VarMap.bindings cm)


(* Returns true iff there is a disequality pair (d1, d2) in st so that
x \in d1, y \in d2 or x \in d2, y \in d1  *)
let disequal st x y =
  let dq = getDeq st in
  let rx,ry = find st x,find st y in
  let less,more = if rx @< ry then rx,ry else ry,rx in
  PairSet.mem (less,more) dq

let isRep st x =
  find st x @= x


(* Functions related to checking memory safety *)

(* Important: this involves checking on x, not its representative *)
let is_stop st x =
  let stop = getStop (getSafe st) in
  x @= stop

let equivalent_to_stop st x =
  let stop = getStop (getSafe st) in
  sameClass st x stop

let disequal_to_stop st x =
  let stop = getStop (getSafe st) in
  disequal st x stop

let safeToReference st args =
  let {yes;free;_} = getSafe st in
  List.for_all (fun arg -> VarSet.mem arg yes) args &&
  List.for_all (fun arg -> not (VarSet.mem arg free)) args

let addToYes st x =
  assert (isRep st x);
  let safe = getSafe st in
  let yes = getYes safe in
  {st with safe={safe with yes=VarSet.add x yes}}

(* Return all vars y such that y and x belong to the same class *)
let getMembers st x =
  let rx = (VarMap.find x (getRmap st)) in
  VarMap.find rx (getCmap st)

let reject st =
  let dq = getDeq st in
  PairSet.exists (fun (l,r) -> l @= r) dq

let size s =
  VarSet.cardinal s

(* TODO: typecheck for non-existence of __ssa__ in the given program *)
(* Remove the __ssa__ completely *)
let ssaVar = Var "__ssa__"

(* -------------------------------------------------------------------------- *)

(* Functions to manage the state of disequalities
 * between classes encoded in a value of type deq *)

let removeFromDeq dq x =
  PairSet.filter (fun (l,r) -> not (l @= x || r @= x)) dq

let addToDeq dq x y =
  let p = if x @< y then (x,y) else (y,x) in
  PairSet.add p dq

(* rename to notIrreflexive *)
let irreflexiveDeq dq =
  PairSet.exists (fun (l,r) -> l @= r) dq

(* -------------------------------------------------------------------------- *)

(* Utility functions for function and evaluation maps *)

let getEvaluationMap pm f =
  FunctionMap.find f pm

let listReplace l old next =
  List.map (fun elt -> if elt @= old then next else elt) l

let refreshEvaluationMap oldRep newRep em =
  let outputsRemapped = EvaluationMap.map
      (fun value ->
         if value @= oldRep
         then newRep
         else value) em in
  let argumentsRemapped =
    EvaluationMap.fold
      (fun args out acc ->
         if List.mem oldRep args
         then let newArgs = listReplace args oldRep newRep in
           EvaluationMap.add newArgs out (EvaluationMap.remove args acc)
         else acc) outputsRemapped outputsRemapped in
  argumentsRemapped

let removeFromEvaluationMap x em =
  EvaluationMap.filter (fun args y -> not (List.mem x args || y @= x)) em

let removeFromPmap pm x =
  FunctionMap.map (removeFromEvaluationMap x) pm

let lookupInEmap em args =
  EvaluationMap.find_opt args em

let lookupInPmap pm f args =
  let em = FunctionMap.find f pm in
  lookupInEmap em args

let refreshMemoSet oldRep newRep ms =
  ArgumentSet.map (fun elt -> listReplace elt oldRep newRep) ms

let updateMemoSet f ms pm rx =
  let em = FunctionMap.find f pm in
  EvaluationMap.fold
    (fun key value acc ->
       if value @= rx
       then ArgumentSet.add key acc
       else acc) em ms

let updateMemo mm pm rx =
  FunctionMap.mapi (fun f ms -> updateMemoSet f ms pm rx) mm

let removeFromMemoSet x ms =
  ArgumentSet.filter (fun elt -> not (List.mem x elt)) ms

let removeFromMemo mm rx =
  FunctionMap.map (removeFromMemoSet rx) mm

let removeFromSafe safe x =
  let {yes;free;_} = safe in
  {safe with free=VarSet.remove x free; yes=VarSet.remove x yes}

(* -------------------------------------------------------------------------- *)

(* Functions to manage the state of equivalence classes when there is
 * a representative change *)

(* returns \lambda z : if z \not\in rm.keys() then None else z \not\in cls then rm[z] else newRep *)
let refreshRmap rm cls newRep =
  VarSet.fold (fun x rm -> VarMap.add x newRep rm) cls rm

let refreshCmap cm oldRep newRep cls =
  let cm' = VarMap.remove oldRep cm
  in VarMap.add newRep cls cm'

let refreshPmap pm oldRep newRep =
  FunctionMap.map (refreshEvaluationMap oldRep newRep) pm

let refreshDeq dq oldRep newRep =
  PairSet.map
    (fun (l,r) ->
       let lSub = if l=oldRep then newRep else l in
       let rSub = if r=oldRep then newRep else r in
       if rSub @< lSub then (rSub,lSub) else (lSub, rSub))
    dq

let refreshMemo mm oldRep newRep =
  FunctionMap.map (refreshMemoSet oldRep newRep) mm

let refreshSafe safe oldRep newRep =
  let {yes;free;_} = safe in
  let yes' =
    if VarSet.mem oldRep yes then
      VarSet.add newRep (VarSet.remove oldRep yes)
    else yes in
  let free' =
    if VarSet.mem oldRep free then
      VarSet.add newRep (VarSet.remove oldRep free)
    else free in
  {safe with yes=yes'; free=free'}


(* Functions to manage removal of a single variable from all state components *)

let add st x y =
  assert (not (is_stop st x));
  let ry = find st y in
  let {rm;cm;pm;dq;mm;safe;tp} = st in
  let cls_y = (VarMap.find ry cm) in
  if x @< ry then
    (* x becomes new rep *)
    let cls = VarSet.add x cls_y in
    let rm' = refreshRmap rm cls x in
    let cm' = refreshCmap cm ry x cls in
    let pm' = refreshPmap pm ry x in
    let dq' = refreshDeq dq ry x in
    let mm' = refreshMemo mm ry x in
    let safe' = refreshSafe safe ry x in
    {rm=rm';cm=cm';pm=pm';dq=dq';mm=mm';safe=safe';tp=tp}
  else
    let rm' = VarMap.add x ry rm in
    let cm' = VarMap.add ry (VarSet.add x cls_y) cm in
    {rm=rm';cm=cm';pm=pm;dq=dq;mm=mm;safe=safe;tp=tp}

let remove st x =
  assert (not (is_stop st x));
  let {rm;cm;pm;dq;mm;safe;tp} = st in
  let rx = find st x in
  let cls = VarMap.find rx cm in
  if (size cls) = 1 then
    (* expunge the class *)
    let rm' = VarMap.remove x rm in
    let cm' = VarMap.remove rx cm in
    let mm' = updateMemo mm pm rx in
    let mm'' = removeFromMemo mm' rx in
    let pm' = removeFromPmap pm rx in
    let dq' = removeFromDeq dq rx in
    let safe' = removeFromSafe safe rx in
    {rm=rm';cm=cm';pm=pm';dq=dq';mm=mm'';safe=safe';tp=tp}
  else if x @= rx then
    (* find a new representative *)
    let cls' = VarSet.remove x cls in
    let newRep = VarSet.min_elt cls' in
    let rm_without_x = VarMap.remove x rm in
    let rm' = refreshRmap rm_without_x cls' newRep in
    let cm' = refreshCmap cm rx newRep cls' in
    let pm' = refreshPmap pm rx newRep in
    let dq' = refreshDeq dq rx newRep in
    let mm' = refreshMemo mm rx newRep in
    let safe' = refreshSafe safe rx newRep in
    {rm=rm';cm=cm';pm=pm';dq=dq';mm=mm';safe=safe';tp=tp}
  else
    let rm' = VarMap.remove x rm in
    let cm' = VarMap.add rx (VarSet.remove x cls) cm in
    {st with rm=rm';cm=cm'}

let moveTo st x y =
  let st = remove st x in
  let st = add st x y in
  st

let makeFresh st x =
  let st' = remove st x in
  let rm'' = VarMap.add x x (getRmap st') in
  let cm'' = VarMap.add x (VarSet.singleton x) (getCmap st') in
  {st' with rm=rm'';cm=cm''}


(* -------------------------------------------------------------------------- *)

(* Functions to transform state for different program instructions *)

let readAssignFromData st x y =
  if sameClass st x y then st
  else moveTo st x y

let readAssignFromLoc st x y =
  if is_stop st x
  then
    raise (Unhandled("Attempt to reassign stop location"))
  else if sameClass st x y
  then st
  else moveTo st x y

let defineTerm st x f args =
  let {pm;mm;_} = st in
  let rargs = List.map (find st) args in
  (* check if breaking memoizing  *)
  let ms = FunctionMap.find f mm in
  if ArgumentSet.mem rargs ms
  then raise (MemoizingFailure("Term " ^ (string_of_func f)
                               ^"("^ (string_of_vars args)^")"^
                               " was computed and dropped"))
  else
    let em = getEvaluationMap pm f in
    let em' = EvaluationMap.add rargs ssaVar em in
    let pm' = FunctionMap.add f em' pm in
    let st' = {st with pm=pm'} in
    (* handle troublesome cases like 'x:=f(x)' *)
    makeFresh (moveTo st' x ssaVar) ssaVar

(* print contents of yes set *)
let debugMemorySafety st =
  let safe = getSafe st in
  let yes = getYes safe in
  VarSet.fold
    (fun v () ->
       print_string ("Yes set: "^(string_of_var v))) yes ()

let readAssignFromLocToData st x f args =
  let rargs = List.map (find st) args in
  if not (safeToReference st rargs)
  then raise (MemorySafetyFailure("Unsafe reference of "^(string_of_func f)))
  else
    let {pm;_} = st in
    let em = getEvaluationMap pm f in
    let target_opt = lookupInEmap em rargs in
    match target_opt with
    | Some t -> assert (isRep st t); readAssignFromData st x t
    | None -> defineTerm st x f args

(* Almost identical to above. Only difference is in first match pattern. *)
let readAssignFromLocToLoc st x f args =
  let rargs = List.map (find st) args in
  if not (safeToReference st rargs)
  then raise (MemorySafetyFailure("Unsafe reference of "^(string_of_func f)))
  else
    let {pm;_} = st in
    let em = getEvaluationMap pm f in
    let target_opt = lookupInEmap em rargs in
    match target_opt with
    | Some t -> assert (isRep st t); readAssignFromLoc st x t
    | None -> defineTerm st x f args

let readAssignFromDataToData st x f args =
  let {pm;_} = st in
  let rargs = List.map (find st) args in
  let em = getEvaluationMap pm f in
  let target_opt = lookupInEmap em rargs in
  match target_opt with
  | Some t -> assert (isRep st t); readAssignFromData st x t
  | None -> defineTerm st x f args

let updatePtr st f args x =
  let {pm;_} = st in
  let rargs = List.map (find st) args in
  let rx = find st x in
  let em = getEvaluationMap pm f in
  let em' = EvaluationMap.add rargs rx em in
  let pm' = FunctionMap.add f em' pm in
  {st with pm=pm'}

let readUpdateLocToData st f args x =
  let rargs = List.map (find st) args in
  if not (safeToReference st rargs)
  then raise (MemorySafetyFailure("Unsafe reference on update of "^(string_of_func f)))
  else updatePtr st f args x

let readUpdateLocToLoc st f args x =
  readUpdateLocToData st f args x

(* x must be in Yes and not in Free *)
let readFree st x =
  let rx = find st x in
  if not (safeToReference st [rx])
  then raise (MemorySafetyFailure("Attempt to free unallocated or \
                                   previously freed location "^(string_of_var x)))
  else
    let safe = getSafe st in
    let free = getFree safe in
    let free' = VarSet.add rx free in
    {st with safe={safe with free=free'}}

(* simplify by assuming single arity pointers *)
let getAllSafeArgs st x =
  assert (isRep st x);
  assert (safeToReference st [x]);
  [[x]]

let initializePtr st f x =
  let safe = getSafe st in
  let stop = getStop safe in
  let rstop = find st stop in
  List.fold_left
    (fun acc args ->
       updatePtr acc f args rstop)
    st (getAllSafeArgs st x)

let initializePtrs st x =
  assert (isRep st x);
  assert (safeToReference st [x]);
  let types = getTypes st in
  let pm = getPmap st in
  let fs = List.map fst (FunctionMap.bindings pm) in
  let locToLocs =
    List.filter (fun f ->
        match types f with
        | LocToLoc -> true
        | _ -> false) fs in
  List.fold_left
    (fun acc f -> initializePtr acc f x) st locToLocs

let readAlloc st x =
  let st = makeFresh st x in
  (* add disequality between x and every other class *)
  assert (isRep st x);
  let cm = getCmap st in
  let allReps = List.map fst (VarMap.bindings cm) in
  let allRepsMinusX = List.filter (fun y -> not (y @= x)) allReps in
  let st'' =
    List.fold_left
      (fun acc rep -> {acc with dq=addToDeq (getDeq acc) x rep})
      st allRepsMinusX
  in
  (* initialize pmaps *)
  let st''' = addToYes st'' x in
  initializePtrs st''' x


(* `union st x y` updates st to reflect the union operation on
 * the classes of x and y, and returns an updated state along with
 * the two representatives (one is formerly a rep) correponding to the union *)
let union st x y =
  let clsX,clsY = getMembers st x,getMembers st y in
  let rx,ry = find st x,find st y in
  let lesserRep,greaterRep = if rx @< ry then rx,ry else ry,rx in
  let newCls = VarSet.union clsX clsY in
  let {rm;cm;pm;dq;mm;_} = st in
  let rm' = refreshRmap rm newCls lesserRep in
  let cm' = refreshCmap cm greaterRep lesserRep newCls in
  let dq' = refreshDeq dq greaterRep lesserRep in
  let mm' = refreshMemo mm greaterRep lesserRep in
  (* evaluation maps handled specially in merge *)
  (lesserRep,greaterRep,{st with rm=rm';cm=cm';pm;dq=dq';mm=mm'})


let rec mergeableArgs args1 args2 x y flag =
  match args1, args2 with
  | [], _::_ | _::_, [] -> raise(Unhandled("Found nullary arguments to function"))
  | [], [] -> flag
  | a1 :: args1', a2 :: args2' ->
    if a1 @= a2 then mergeableArgs args1' args2' x y flag
    else if a1 @= x && a2 @= y
    then mergeableArgs args1' args2' x y true
    else false

(* `allOutputPairs st x y` returns a set of pairs (a,b), one for
 * any occurrence of 'f(x) -> a' and 'f(y) -> b', where (not (find st
 * a @= find st b), in the evaluation map of f, for all functions f *)
let allOutputPairs st x y =
  FunctionMap.fold
    (fun f em pairs ->
       let filteredX = EvaluationMap.filter
           (fun k v ->
              List.mem x k) em in
       let filteredY = EvaluationMap.filter
           (fun k v ->
              List.mem y k) em in
       EvaluationMap.fold
         (fun k1 v1 acc1 ->
            EvaluationMap.fold
              (fun k2 v2 acc2 ->
                 if mergeableArgs k1 k2 x y false then
                   if v1 @< v2 then PairSet.add (v1, v2) acc2
                   else PairSet.add (v2, v1) acc2
                 else acc2
              ) filteredY acc1
         ) filteredX pairs) (getPmap st) PairSet.empty

let rec merge st x y work =
  if sameClass st x y then
    processWorkSet st work
  else
    let lesserRep,greater,st = union st x y in
    (* add to workset *)
    let work = PairSet.union (allOutputPairs st lesserRep greater) work in
    let pm' = refreshPmap (getPmap st) greater lesserRep in
    (* take from workset *)
    processWorkSet {st with pm=pm'} work

and processWorkSet st work =
  let pair_opt = PairSet.min_elt_opt work in
  match pair_opt with
  | Some (w,z) ->
    let work = PairSet.remove (w,z) work in
    merge st w z work
  | None -> st

let localCongruenceClosure st x y = merge st x y PairSet.empty

let readAssumeDataEq st x y =
  (* early assumes violations are not
   * problematic if x and y are already equivalent *)
  let existsDroppedSuperTerm =
    FunctionMap.exists
      (fun f ms ->
         let rx, ry = find st x, find st y in
         ArgumentSet.exists
           (fun elt -> List.mem rx elt || List.mem ry elt) ms) (getMemo st) in
  if (sameClass st x y) || not existsDroppedSuperTerm
  then localCongruenceClosure st x y
  else raise (EarlyAssumesFailure("merging "^(string_of_var x)^" with "^(string_of_var y)))

let readAssumeDataNeq st x y =
  let rx,ry = find st x,find st y in
  {st with dq=addToDeq (getDeq st) rx ry}

let readAssumeLocEq st x y =
  if sameClass st x y then st
  else (* assert (undefinedPtrs st x y && ) *)
    let stop = getStop (getSafe st) in
    (* merge x,y,NIL into a single class, no congruence closure *)
    let lesser,greater,st' = union st x y in
    let pm = refreshPmap (getPmap st') greater lesser in
    let lesser',greater',st'' = union st' x stop in
    let pm' = refreshPmap pm greater' lesser' in
    {st'' with pm=pm'}

let makeDisequalToOthers st x =
  let rx = find st x in
  let cm = getCmap st in
  let allReps = List.map fst (VarMap.bindings cm) in
  let allRepsMinusX = List.filter (fun y -> not (rx @= y)) allReps in
  List.fold_left
    (fun acc rep -> {acc with dq=addToDeq (getDeq acc) rx rep})
    st allRepsMinusX

let readAssumeLocNeq st x y =
  if disequal st x y then st
  else if sameClass st x y then
    {st with dq=addToDeq (getDeq st) (find st x) (find st y)}
  else
    let dq = getDeq st in
    if equivalent_to_stop st x then
      let ry = find st y in
      let st' = addToYes st ry in
      makeDisequalToOthers st' ry
    else if equivalent_to_stop st y then
      let rx = find st x in
      let st' = addToYes st rx in
      makeDisequalToOthers st' rx
    else
      {st with dq=addToDeq dq (find st x) (find st y)}


(* --------------------------- Initialization --------------------------- *)

(* initialize a repmap and classmap over a list of variables vlist *)
let initClasses vlist =
  let rm,cm = VarMap.empty,VarMap.empty in
  let rm = List.fold_left (fun rm x -> VarMap.add x x rm) rm vlist in
  let cm = List.fold_left (fun cm x -> VarMap.add x (VarSet.singleton x) cm) cm vlist in
  (* Handle special variables *)
  let rm = VarMap.add ssaVar ssaVar rm in
  let cm = VarMap.add ssaVar (VarSet.singleton ssaVar) cm in
  (rm,cm)

(* initialize a pmap based on lists of function symbols *)
let initPmap dataToData locToLoc locToData =
  let flist = dataToData @ locToLoc @ locToData in
  List.fold_left (fun pm f -> FunctionMap.add f (EvaluationMap.empty) pm)
    FunctionMap.empty flist

let initDeq () =
  PairSet.empty

let initMemo dataToData locToLoc locToData =
  let flist = dataToData @ locToLoc @ locToData in
  List.fold_left (fun mm f -> FunctionMap.add f (ArgumentSet.empty) mm)
    FunctionMap.empty flist

let initSafety stop =
  let yes = VarSet.empty in
  let free = VarSet.empty in
  {stop=stop;yes=yes;free=free}


(* --------------------------- Visualizing states ------------------------------------ *)

let say s = s
let sayln s = say s ^ say "\n"

let rec indent = function
  | 0 -> ""
  | x -> say " " ^ indent (x-1)

let print_var d x = (string_of_var x)

let rec dolist d sep f = function
  | x::l' -> (match l' with
      | x'::l'' -> (f (d+1) x ^ say sep ^ dolist d sep f l')
      | [] -> f (d+1) x)
  | [] -> ""

let print_list d f l = dolist d ", " f l

let print_var_list d l = dolist d ", " print_var l

let list_of_varset vs =
  VarSet.fold
    (fun x acc ->
       x :: acc) vs []

let visualize_classmap st =
  let classmap_bindings = VarMap.bindings (getCmap st) in
  let classes = List.map snd classmap_bindings in
  let rec print_classes cs =
    match cs with
    | [] -> ""
    | x :: xs ->
      let l = list_of_varset x in
      "{"^(print_var_list 0 l) ^ "}, " ^ (print_classes xs)
  in
  print_classes classes

let print_pair f (x,y) =
  "("^(f x)^", "^(f y)^")"

let visualize_deq st =
  let deq = (getDeq st) in
  "{ "^
  (PairSet.fold
     (fun x acc ->
        (print_pair (print_var 0) x) ^", "^ acc) deq "") ^" }"

let visualize_pmap f em =
  let emap_bindings = EvaluationMap.bindings em in
  List.fold_left
    (fun acc (args_list, output) ->
       string_of_func f ^ "(" ^(print_var_list 0 args_list)^ ") -> " ^
       (print_var 0 output) ^"\n") "" emap_bindings

let visualize_pmaps st =
  let pm = (getPmap st) in
  FunctionMap.fold
    (fun f em acc -> if EvaluationMap.is_empty em then acc
      else (visualize_pmap f em)^acc) pm ""


let visualize st =
  print_string @@ "Classes: "^visualize_classmap st^"\n";
  print_string @@ "Disequalities: "^visualize_deq st^"\n";
  print_string @@ "Maps: \n"^visualize_pmaps st^"\n"


(* -------------------------------- Initialization --------------------------- *)


let init var_list dataToData_list locToLoc_list locToData_list stop =
  (* user may not name a variable __ssa__ *)
  assert (not (List.mem ssaVar var_list));
  let rm,cm = initClasses var_list in
  let pm = initPmap dataToData_list locToLoc_list locToData_list in
  let dq = initDeq () in
  let mm = initMemo dataToData_list locToLoc_list locToData_list in
  let safe = initSafety stop in
  let types =
    List.fold_left
      (fun acc f_dTd ->
         fun x ->
           if x #= f_dTd then
             DataToData
           else acc x) (fun x -> DataToData) dataToData_list
  in
  let types' =
    List.fold_left
      (fun acc f_ltl ->
         fun x ->
           if x #= f_ltl then
             LocToLoc
           else acc x) types locToLoc_list
  in
  let types'' =
    List.fold_left
      (fun acc f_ltd ->
         fun x ->
           if x #= f_ltd then
             LocToData
           else acc x) types' locToData_list
  in
  {rm;cm;pm;dq;mm;safe;tp=types''}


(* -------------------------------------------------------------------------- *)
(* ---------------------------- Tests --------------------------------------- *)

let simpleStartingState =
  let x,y,z,w,f,nil = Var "x",Var"y",Var"z",Var"w",Func"f",Var"NIL" in
  let vlst = [x;y;z;w;nil] in
  let flst = [f] in
  let ltl_list = [] in
  let ltd_list = [] in
  let st = init vlst flst [] [] nil in
  ((x,y,z,w,nil), f, st)

let complexStartingState =
  let a,b,c,d,x,y,z,w,nil =
    Var "a",Var"b",Var"c",Var"d",Var "x",Var"y",Var"z",Var"w",Var"NIL" in
  let vlst = [a;b;c;d;x;y;z;w;nil] in
  let f,g = Func "f",Func "g" in
  let flst = [f;g] in
  let st = init vlst flst [] [] nil in
  ((a,b,c,d,x,y,z,w,nil), f, g, st)

(* Functions for testing that a variable x does not appear in some state component *)

let absenceRmap rm x =
  not (VarMap.exists (fun s t -> if s @= x || t @= x then true else false) rm)

let absenceCmap cm x =
  not (VarMap.exists (fun s t -> if s @= x || VarSet.mem x t then true else false) cm)

let absenceEmap x _ em =
  not (EvaluationMap.exists (fun s t -> if List.mem x s || t @= x then true else false) em)

let absencePmap pm x =
  FunctionMap.for_all (absenceEmap x) pm

let absenceDeq dq x =
  not (PairSet.exists (fun (l,r) -> if x @= l || x @= r then true else false) dq)

let absence st x =
  let {rm;cm;pm;dq;_} = st in
  absenceRmap rm x &&
  absenceCmap cm x &&
  absencePmap pm x &&
  absenceDeq dq x
