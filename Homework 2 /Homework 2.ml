(* Elementi del linguaggio
Eventi relativi alla sicurezza.*)
type event = Read | Write | Exec | Delete | Create;;
(**rappresentazione dello stato dell'automa *)
type a_state = St of int;;
(**rappresentazione della transizione dell'automa *)
type transition = event * a_state;;

type expr =
 | CstI of int
 | CstB of bool
 | Var of string
 | Let of string * expr * expr
 | Prim of string * expr * expr
 | If of expr * expr * expr
 | Fun of string * expr 
 | Rec of string * string * expr
 | Call of expr * expr
 | Read of string
 | Write of expr * string
 | Create of string
 | Delete of string
 | Exec of string
 | Guard of string * expr (*controlla una politica in un blocco*)
 | Define of string * (transition list list) * a_state * expr;; (**Definisce una nuova politica*)

(**Rappresentazione dell'automa; per renderla più comapatta, l'alfabeto è definito dal tipo, gli stati sono 
impliciti nell'array delle transizioni, lo stato iniziale è 0, la transizione di default rimane nello stato corrente.*)
type 's automa = 
{
  transition: (('s * int) list) array;
  accept: int list;
  mutable state: int
};;

let transition a s = match List.assoc_opt s (a.transition.(a.state)) with
  None -> ()
|  Some(st) -> a.state <- st;;

let batch a s = Seq.iter (fun x -> transition a x) s;;

let accept a = List.mem a.state a.accept;;


(*Elementi del runtime *)
type 'v env = (string * 'v) list;;

let rec lookup env x =
   match env with
   | []        -> failwith (x ^ " not found")
   | (y, v)::r -> if x=y then v else lookup r x;;

type value =
 | Int of int
 | Closure of string * expr * (value env) ref;; 
 
(**stato dell'analisi *)
type state = 
{
  history: event Queue.t;
  policies: (string * event automa) list; (**policy attive *)
  availables: (string * event automa) list (**policy disponibili *)
};;

(**se una policy è gia attiva ignora il comando, altrimenti instanzia un nuovo automa e lo aggiorna fino all'ultimo evento della history*)
let add_policy astate name = 
  match (List.assoc_opt name astate.availables, List.mem_assoc name astate.policies) with
    (_, true) -> astate
  | (Some(p), false) -> 
    let a = {p with state=0} in
    batch a (Queue.to_seq astate.history);
    {astate with policies= (name, a)::astate.policies}
  | _ -> failwith "policy not found";;

(**Aggiorna con l'evento corrente tutti gli automi (politiche) attivi. L'automa accetta le politiche violate *)
let analyze (astate: state) e = 
  Queue.add e astate.history;
  let update (_, a) = transition a e; not (accept a) in
  List.for_all update astate.policies;;

let st_to_int s = let St(i) = s in i;;
let trans_from_rep ((e, s):transition) = e, st_to_int s;;
let tab_from_rep rep = List.map (fun x -> List.map trans_from_rep x) rep |> Array.of_list;;

(**è posibile fornire all'interprete delle politiche di default*)
let interp policies exe = 
  let rec ieval (e : expr) (env : value env) astate: value =
    match e with
    | CstI i -> (Int i)
    | CstB b -> (Int (if b then 1 else 0))
    | Var x  -> (lookup env x)
    | Prim(ope, e1, e2) ->
      let v1 = ieval e1 env astate in
      let v2 = ieval e2 env astate in
      begin
      match (ope, v1, v2) with
      | ("*", Int i1, Int i2) -> Int (i1 * i2)
      | ("+", Int i1, Int i2) -> Int (i1 + i2)
      | ("-", Int i1, Int i2) -> Int (i1 - i2)
      | ("=", Int i1, Int i2) -> Int (if i1 = i2 then 1 else 0)
      | ("<", Int i1, Int i2) -> Int (if i1 < i2 then 1 else 0)
      |  _ -> failwith "unknown primitive or wrong type"
      end
    | Let(x, eRhs, letBody) ->
      let xVal = ieval eRhs env astate in
      let letEnv = (x, xVal) :: env in
      ieval letBody letEnv astate
    | If(e1, e2, e3) ->
      begin
      match ieval e1 env astate with
      | Int 0 -> ieval e3 env astate
      | Int _ -> ieval e2 env astate
      | _     -> failwith "eval If"
      end
    | Fun(x,fBody) -> (Closure(x, fBody, ref env))
    | Rec(name, x ,fBody) -> 
      let re = ref env in
      let c = Closure(x, fBody, re) in
      re := (name, c) :: env;
      c
    | Call(eFun, eArg) ->
      let fClosure = ieval eFun env astate in
      begin
      match fClosure with
      | Closure (x, fBody, fDeclEnv) ->
        let xVal = ieval eArg env astate in
        let fBodyEnv = (x, xVal) :: !fDeclEnv in
        ieval fBody (fBodyEnv) astate
      | _ -> failwith "eval Call: not a function"
      end
    | Read(_) -> if analyze astate Read then Int 0 else failwith "read permission denied" 
    | Write(x, _) -> if analyze astate Write then Int 1 else failwith "write permission denied"
    | Delete(_) -> if analyze astate Delete then Int 2 else failwith "delete permission denied" 
    | Create(_) -> if analyze astate Create then Int 3 else failwith "create permission denied" 
    | Exec(_) -> if analyze astate Exec then Int 4 else failwith "execute permission denied"
    | Guard(pol, exp) -> ieval exp env (add_policy astate pol)
    | Define(name, trans, fail, exp) -> 
      let p = name, {state=0; accept=[st_to_int fail]; transition= tab_from_rep trans} in
      ieval exp env {astate with availables= p::astate.availables} in
    ieval exe [] {history=Queue.create(); policies=[]; availables=policies};;
   

(*Tests *)
let norw = "NoRaW", {state=0; accept=[2]; transition=[|[(Write: event), 1]; [(Read: event), 2]|]};;
let nowr = "NoWaR", {state=0; accept=[2]; transition=[|[(Read: event), 1]; [(Write: event), 2]|]};;

let policies = [norw; nowr];;
let eval exp = interp policies exp;;

let plain_fun = Fun("x", Prim("+", Var "x", CstI 5));;
let read_fun = Fun("file", Read("file"));;
let exec_fun = Fun("file", Exec("file"));;
let rec_fun = Rec("r", "x", If(Prim("=", Var("x"), CstI(0)), CstI(0), Call(Var("r"), Prim("-", Var("x"), CstI(1)))));;
let guard_r e = Guard("NoRaW", e);;
let guard_w e = Guard("NoWaR", e);;
let vwr = Let("x", Read "file", Write(Var "x", "file2"));;
let nested = Let("x", guard_w (Read "file"), Write(Var "x", "file2"));;
let prec = Let("x", Read "file", guard_w (Write(Var "x", "file2")));;
let no_exec = Let("ef", exec_fun, Guard("no_ex", Call(Var("ef"), CstI 1)));;

let prog1 = Let("x", CstI 1, Prim("+", Var "x", CstI 5)) in (**atteso Int 6 *)
  eval prog1;;
let prog2 = Let("f", plain_fun, Call(Var "f", CstI 1)) in (**atteso Int 6 *)
  eval prog2;;
let prog3 = Let("f", read_fun, Call(Var "f", CstI 0)) in (**atteso Int 0 *)
  eval prog3;;

let prog4 = Let("f", rec_fun, Call(Var "f", CstI 2)) in (**atteso Int 0 *)
  eval prog4;;

let prog5 = eval (guard_r vwr);; (**atteso Int 1 *)
let prog6 = eval (guard_w vwr);; (**atteso error *)
let prog7 = eval (guard_r nested);; (**atteso Int 1*)
let prog8 = eval prec;; (**atteso error *)
let prog9 = Define("no_ex", [[(Exec: event), St(1)]], St(1), no_exec) in
  eval prog9;; (**atteso error *)