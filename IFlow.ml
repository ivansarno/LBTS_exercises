type expr =
 | CstI of int
 | CstB of bool
 | Var of string
 | Prim of string * expr * expr;;


type 'v env = (string * 'v) list;;

let rec lookup env x =
   match env with
   | []        -> failwith (x ^ " not found")
   | (y, v)::r -> if x=y then v else lookup r x;;

type 'v state = 'v env;;

let lookup_s = lookup;;

let assign (state: ' v state) var value = 
  let ns = List.remove_assoc var state in
  (var, value)::ns;;

let remove var state = List.remove_assoc var state;;
 
 type ivalue =
 | Int of int
 | Bool of bool;;
 

 
let rec eval (e : expr) (env : ivalue state)  : ivalue =
  match e with
  | CstI i -> (Int i)
  | CstB b -> Bool(b)
  | Var x  -> (lookup env x)
  | Prim(ope, e1, e2) ->
    let v1 = eval e1 env  in
    let v2 = eval e2 env  in
    begin
    match (ope, v1, v2) with
    | ("*", Int i1, Int i2) -> Int (i1 * i2)
    | ("+", Int i1, Int i2) -> Int (i1 + i2)
    | ("-", Int i1, Int i2) -> Int (i1 - i2)
    | ("=", Int i1, Int i2) -> Bool (if i1 = i2 then true else false)
    | ("<", Int i1, Int i2) -> Bool (if i1 < i2 then true else false)
    |  _ -> failwith "unknown primitive or wrong type" 
    end;;

type command = 
  Assign of string * expr
| If of expr * command * command
| While of expr * command
| For of string * expr * expr * expr * command
| Seq of command * command
| Skip;; 


let rec execute cmd (state : ivalue state) = match cmd with
  Assign(name, exp) -> assign state name (eval exp state)
| If(exp, cmd1, cmd2) -> let guard = eval exp state in 
    begin match guard with
      Bool(true) -> execute cmd1 state
    | Bool(false) -> execute cmd2 state
    | _ -> failwith "not boolean if guard" 
    end
| While(exp, cmd) -> let guard = eval exp state in 
    begin match guard with
      Bool(true) -> let ns = execute cmd state in 
        execute (While(exp, cmd)) ns
    | Bool(false) -> state
    | _ -> failwith "not boolean while guard" 
    end
| For(ind, start, endf, incr, cmd) -> execute_for ind start endf incr cmd state
| Seq(cmd, ocmd) -> let ns = execute cmd state in
  execute ocmd ns
| Skip -> state

and execute_for ind init guard incr cmd state =
  let rec iexec dir start endf inc fstate = match dir with
    true when start <= endf -> iexec dir (start+inc) endf inc (execute cmd (assign fstate ind (Int(start))))
    | false when start >= endf -> iexec dir (start+inc) endf inc (execute cmd (assign fstate ind (Int(start))))
    | _ -> fstate
    in
  match (eval init state), (eval guard state), (eval incr state) with
    Int(init), Int(guard), Int(incr) when init <= guard && incr > 0 -> iexec true init guard incr state |> remove ind
   |Int(init), Int(guard), Int(incr) when init >= guard && incr < 0 -> iexec false init guard incr state |> remove ind
   | _ -> failwith "inlegal for initialization";;

let interp cmd = execute cmd [];;
   
   
type level = Low | High;;

let join a b: level = max a b;;

let rec exp_analisys (e : expr) (env : level state)  : level =
  match e with
  | CstI i -> Low
  | CstB b -> Low
  | Var x  -> (lookup env x)
  | Prim(ope, e1, e2) -> join (exp_analisys e1 env) (exp_analisys e2 env);;


let assign_lev (state: ' v state) var value = 
  match List.assoc_opt var state with
    None -> assign state var value
  | Some(l) -> if l >= value 
    then state 
    else failwith "assignment blocked";;


let rec cmd_analisys cmd (state : level state) ctx = match cmd with
  Assign(name, exp) -> assign_lev state name (join ctx (exp_analisys exp state))
| If(exp, cmd1, cmd2) -> let nctx = join ctx (exp_analisys exp state) in
    let ns = cmd_analisys cmd1 state nctx in 
      cmd_analisys cmd2 ns nctx
| While(exp, cmd) -> if join ctx (exp_analisys exp state) = Low 
  then cmd_analisys cmd state ctx 
  else failwith "possible termination leak"
| For(ind, start, endf, incr, cmd) -> let nctx = join ctx (exp_analisys start state) 
  |> join (exp_analisys endf state) |> join (exp_analisys incr state) in
  let ns = assign state ind nctx in cmd_analisys cmd ns nctx
| Seq(cmd, ocmd) -> let ns = cmd_analisys cmd state ctx in
  cmd_analisys ocmd ns ctx
| Skip -> state;;

let flow_analisys init cmd = cmd_analisys cmd init Low;;

(*Tests*)

let test_flow = flow_analisys [("h", High); ("l", Low)];;

let test_assign1 = test_flow (Assign("h", CstI(5)));;
let test_assign2 = test_flow (Assign("h", Var("l")));;
let test_assign3 = test_flow (Assign("l", Var("h")));;
let test_if1 = test_flow (If(Prim("=", CstI(4), Var("l")), Assign("h", Var("l")), Assign("l", CstB(false))));;
let test_if1 = test_flow (If(Prim("=", CstI(4), Var("h")), Assign("h", Var("l")), Assign("l", CstB(false))));;
let test_seq = test_flow (Seq(Assign("x", CstB(true)), Assign("y", CstI(5))));;
let test_while1 = let guard = Prim("<", Var("l"), CstI(5)) in
  let cmd = Assign("h", Prim("+", Var("h"), CstI(1))) in
  test_flow (Seq(Assign("h", CstI(0)), While(guard, cmd)));;

let test_while2 = let guard = Prim("<", Var("h"), CstI(5)) in
  let cmd = Assign("h", Prim("+", Var("h"), CstI(1))) in
  test_flow (Seq(Assign("h", CstI(0)), While(guard, cmd)));;

let test_for = let cmd = Assign("x", Prim("+", Var("x"), Var("i"))) in
  test_flow (Seq(Assign("x", CstI(0)), For("i", CstI(0), CstI(5), CstI(1), cmd)));;


