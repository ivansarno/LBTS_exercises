(*Questo progetto implementa un semplice linguaggio funzionale dotato di un sistema di permessi, 
questi sono permessi di scrittura, lettura, cancellazione, creazione ed esecuzione, globali. 
Sono disponibili costrutti del linguaggio per abilitare, disabilitare o controllare i permessi attivi.  
È possibile configurare una policy per l'abilitazione dei permessi a runtime.
I programmi possono utilizzare componenti di diversa origine, con diversi permessi. Ogni funzione etichettata con i permessi del modulo di origine. 
A runtime i permessi disponibili vengono controllati con stack inspection lazy*)

(*costrutti del linguaggio *)
type permission = Readp | Writep | Delp |Execp | Createp;;
type expr =
 | CstI of int
 | CstB of bool
 | Var of string
 | Let of string * expr * expr
 | Prim of string * expr * expr
 | If of expr * expr * expr
 | Fun of string * expr 
 | Call of expr * expr
 | Read of string
 | Write of expr * string
 | Create of string
 | Delete of string
 | Exec of string
 | Disable of permission * expr
 | Enable of permission * expr
 | Check of permission  (**controlla se un permesso è disponibile a runtime *)
 | Use of string * string * expr;; (**permette di usare un espressione esterna, identificata per nome*)


(*Assegnazioni dei permessi: il loader analizza il codice eseguibile e assegna i permessi 
in base all'origine del codice seguendo una policy*)
type prot_dom =
{
  perm : permission list; (*permessi disponibili *)
  priv : permission list; (* privilegi abilitati*)
  origin : string;
};;


type lib = string * expr * prot_dom;;
let loader policy name origin (exp: expr) : lib =  
  let rec analyze (exp: expr) = match exp with
  CstI(i) -> []
  | CstB(b) -> []
  | Var(v) -> []
  | Check(p) -> []
  | Prim(s, e1, e2) -> analyze e1 @  analyze e2
  | Let(s, e1, e2) -> analyze e1 @  analyze e2
  | If (e1, e2, e3) -> analyze e1 @  analyze e2 @ analyze e3
  | Call(e1, e2) -> analyze e1 @  analyze e2
  | Read(s) -> [Readp]  
  | Write(e, s) -> [Writep] 
  | Delete(s) -> [Delp]
  | Create(s) -> [Createp]  
  | Exec(s) -> [Execp]
  | Disable(p, e) -> analyze e 
  | Enable(p, e) -> analyze e 
  | Fun(s, e) -> analyze e   
  | Use(s1, s2, ex) ->  analyze ex in
    let p = (analyze exp) |> List.sort_uniq Stdlib.compare |> List.filter (policy origin)
      in (name, exp, {perm = p; priv = []; origin = origin});;

type exec = lib list;;
let link policy exprs = List.map (fun (n, o, e) -> loader policy n o e) exprs;;

(* Elementi del runtime *)
type 'v env = (string * 'v) list;;

let rec lookup env x =
   match env with
   | []        -> failwith (x ^ " not found")
   | (y, v)::r -> if x=y then v else lookup r x;;

type value =
 | Int of int
 | Closure of string * expr * value env * prot_dom;; 
 
(**stack dei protection domain attivi a runtime *)
type perm_stack = prot_dom list;;

(**stack inspection controlla che tutti i protection domain sullo stack abbiano il permesso 
oppure che il primo abbia un privilegio a runtime*)
let check_perm (perm: permission) (stack: perm_stack) = 
  let pd = List.hd stack in
  if List.exists ((=) perm) pd.priv then true 
  else List.for_all (fun x -> List.exists ((=) perm) x.perm) stack;;

(**quando un protection domain viene aggiunto allo stack eredita i privilegi a runtime da quello precedente*)
let add_perm_frame pdom pstack = 
  let td = List.hd pstack in
    {pdom with priv = td.priv} :: pstack;;

(**decide se abilitare un permesso a runtime in base a una policy e allo stato dell'esecuzione (generico) *)
let request_permission (perm: permission) pstack state policy = match (pstack, policy state perm) with
  (_, false) -> (pstack, false)
  |([], true) -> failwith "empty permission stack"
  |(p::ps, true) -> ({p with priv = perm :: p.priv} :: pstack, true);;

let disable_permission perm pstack = 
  let f l = List.filter ((!=) perm) l in match pstack with
  [] -> []
  |p::ps -> {perm = f p.perm; priv = f p.priv; origin = p.origin}::ps;; 


let set_dom (ps: perm_stack) = let h = List.hd ps in {h with priv = []};; 

(*cerca un modulo con un nome specifico*)
let load libs name = let (_, e, pd) = List.find (fun (x,_, _) -> x = name) libs in (e, pd);;

(**esegue la prima espressione della lista *)
let interp policy (exe: exec) = let (_, e, pd) = List.hd exe in 
  let rec ieval (e : expr) (env : value env) (ps: perm_stack): value =
    match e with
    | CstI i -> (Int i)
    | CstB b -> (Int (if b then 1 else 0))
    | Var x  -> (lookup env x)
    | Prim(ope, e1, e2) ->
      let v1 = ieval e1 env ps  in
      let v2 = ieval e2 env ps  in
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
      let xVal = ieval eRhs env ps in
      let letEnv = (x, xVal) :: env in
      ieval letBody letEnv ps 
    | If(e1, e2, e3) ->
      begin
      match ieval e1 env ps with
      | Int 0 -> ieval e3 env ps 
      | Int _ -> ieval e2 env ps 
      | _     -> failwith "eval If"
      end
    | Fun(x,fBody) -> (Closure(x, fBody, env, set_dom ps)) (**assegna il protection domain *)
    | Call(eFun, eArg) ->
      let fClosure = ieval eFun env ps  in
      begin
      match fClosure with
      | Closure (x, fBody, fDeclEnv, pl) ->
        let xVal = ieval eArg env ps in
        let fBodyEnv =(x, xVal) :: fDeclEnv
        in ieval fBody (fBodyEnv) (add_perm_frame pl ps) (**aggiunge il protection domain della chiusura allo stack *)
      | _ -> failwith "eval Call: not a function"
      end
    | Read(_) -> if check_perm Readp ps then Int 0 else failwith "read permission denied" 
    | Write(x, _) -> if check_perm Writep ps then Int 1 else failwith "writ permission denied"
    | Delete(_) -> if check_perm Delp ps then Int 1 else failwith "delete permission denied" 
    | Create(_) -> if check_perm Createp ps then Int 1 else failwith "create permission denied" 
    | Exec(_) -> if check_perm Execp ps then Int 1 else failwith "execute permission denied"
    | Check(p) -> if check_perm p ps then Int 1 else Int 0
    | Disable(p, ex) -> ieval ex env (disable_permission p ps) 
    | Enable(p, ex) -> 
      begin
      match (request_permission p ps (ps, env) policy) with (**l'ambiente e il perm stack usati come stato *)
      (_, false) -> failwith "enable permission denied"
      |(s, true) -> ieval ex env s
      end 
    | Use(v_name, l_name, ex) -> let (e, pd) = load exe l_name in (**lega ad un nome nell'ambiente il risultato della valutazione di un espressione esterna*)
      let v = ieval e [] [pd] in ieval ex ((v_name, v)::env) ps in  (**la valutazione avviene con un nuovo ambiente e stack dei permessi *)
    ieval e [] [pd];; (**l'esecuzione comincia con il protection domain dell'eseguibile principale *)
   

(*Tests *)  
let load_policy o (p: permission) = match (o, p) with
("trusted", _ ) -> true
|("untrusted", read) -> true
|_ -> false;;

let enable_policy (state, env) p = match (state, p) with 
(hs::ts, p) when hs.origin = "trusted" -> true
|_-> false;;

let eval exp = [(loader load_policy "tests" "trusted" exp)] |>  (interp enable_policy);;

let plain_fun = Fun("x", Prim("+", Var "x", CstI 5));;
let read_fun = Fun("file", Read("file"));;
let exec_fun = Fun("file", Exec("file"));;
let disable_fun = Fun("x", Let("read", read_fun, Disable(Readp, Call(Var("read"), CstI 0))));;
let enable_fun = Fun("file", Enable(Writep, Write( Var "file", "output")));;

let prog1 = Let("x", CstI 1, Prim("+", Var "x", CstI 5)) in (**atteso Int 6 *)
  eval prog1;;
let prog2 = Let("f", plain_fun, Call(Var "f", CstI 1)) in (**atteso Int 6 *)
  eval prog2;;
let prog3 = Let("f", read_fun, Call(Var "f", CstI 0)) in (**atteso Int 0 *)
  eval prog3;;

let prog4 = Let("f", disable_fun, Call(Var "f", CstI 0)) in (**atteso permission denied *)
  eval prog4;;

let prog5 = Let("f", enable_fun, Call(Var "f", CstI 0)) in (**atteso permission denied *)
  [(loader load_policy "tests" "untrusted" prog5)] |>  (interp enable_policy);;

let prog6 = Use("f", "system", Call(Var "f", CstI 0)) in
[("prog6", "untrusted", prog6); ("system", "trusted", exec_fun)] |> (link load_policy) |> interp enable_policy;; (**atteso permission denied *)

let prog7 = Enable(Execp, Use("f", "call", Call(Var "f", CstI 0))) in
[("prog7", "trusted", prog7); ("call", "untrusted", exec_fun)] |> (link load_policy) |> interp enable_policy;; (**atteso Int 1 *)

