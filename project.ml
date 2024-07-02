type ide = string

type sec_level=
  | Secret 
  | Public 
  | Handler 

(* environment -> identifier - value - taitness*) 
type 'v env = (ide * 'v  * bool) list
type 'v priv_TB = (ide * sec_level) list

type exp =
| Eint of int
| Ebool of bool
| Estring of string
| Var of ide
| Prim of ide * exp * exp
| If of exp * exp * exp
| Let of ide * exp * exp
| Fun of ide * exp
| Apply of exp * exp
| Abort of string
| Trustblock of exp 
| LetSecret of ide * exp * exp
| Handle of ide * exp
(*| Include of exp
| Excecute of exp
| EndRecursion *)



type evt =
| Int of int
| Bool of bool
| String of string
| Closure of ide * exp * evt env * evt priv_TB
| Secure_Block of evt priv_TB  



let rec lookup env x =
match env with
| [] -> failwith (x ^ "not found")
| (y, v, _) :: r -> if x = y then v else lookup r x

(* taintness of a variable *) 
let rec t_lookup env x =
match env with
| [] -> failwith (x ^ "not found")
| (y, _, t) :: r -> if x = y then t else t_lookup r x

let rec secret_lookup priv_TB x = 
match priv_TB with
| [] -> failwith (x ^ "not found")
| (y, s) :: r -> if x = y && s = Secret then true else secret_lookup r x

let rec pub_lookup priv_TB x = 
  match priv_TB with
  | [] -> failwith (x ^ "not found")
  | (y, s) :: r -> if x = y && s = Public then true else pub_lookup r x

let bind_env env (x:ide) (v:evt) (t:bool) = (x,v,t)::env
let bind_tb priv_TB (x:ide) (sl:sec_level) = (x,sl)::priv_TB



let rec eval (e : exp) (env:evt env) (t : bool) (priv_TB: evt priv_TB) (inTrustBlock: bool): evt * bool =
match e with
| Eint n -> (Int n, t)
| Ebool b -> (Bool b, t)
| Estring s -> (String s, t)
| Var x -> (lookup env x, t_lookup env x)
| Prim (op, e1, e2) ->
  begin
    let v1, t1 = eval e1 env t priv_TB inTrustBlock in
    let v2, t2 = eval e2 env t priv_TB inTrustBlock in
    match (op, v1, v2) with
    (* taintness of binary ops is given by the OR of the taintness of the args *) 
    | "*", Int i1, Int i2 -> (Int (i1 * i2), t1 || t2)
    | "+", Int i1, Int i2 -> (Int (i1 + i2), t1 || t2)
    | "-", Int i1, Int i2 -> (Int (i1 - i2), t1 || t2)
    | "=", Int i1, Int i2 -> (Bool (if i1 = i2 then true else false), t1 || t2)
    | "<", Int i1, Int i2 -> (Bool (if i1 < i2 then true else false), t1 || t2)
    | ">", Int i1, Int i2 -> (Bool (if i1 > i2 then true else false), t1 || t2)
    | _, _, _ -> failwith "Unexpected primitive."
  end
| If (e1, e2, e3) -> 
  begin
  let v1, t1 = eval e1 env t priv_TB inTrustBlock in 
  match v1 with
    | Bool true -> let v2, t2 = eval e2 env t priv_TB inTrustBlock in (v2, t1 || t2) 
    | Bool false -> let v3, t3 = eval e3 env t priv_TB inTrustBlock in (v3, t1 || t3) 
    | _ -> failwith "Unexpected condition."
  end
| Let (x, exprRight, letBody) ->
      let xVal, taintness = eval exprRight env t priv_TB inTrustBlock in
      let letEnv = bind_env env x xVal taintness in
      eval letBody letEnv t priv_TB inTrustBlock
| Fun (f_param, fBody) ->
  (Closure (f_param, fBody, env, priv_TB), t)
| Apply (eFun, eArg) -> ( 
  let fClosure, tClosure = eval eFun env t priv_TB inTrustBlock in
  match fClosure with
  | Closure (x, fBody, fDeclEnv, priv_TB) ->
      (* xVal is evaluated in the current env *)
      let xVal, taintness = eval eArg env tClosure priv_TB inTrustBlock in
        let fBodyEnv = (x, xVal, taintness) :: fDeclEnv in
          (* fBody is evaluated in the updated env *)
          eval fBody fBodyEnv taintness priv_TB inTrustBlock
  | _ -> failwith "eval Call: not a function")
| Abort msg -> failwith msg
| Trustblock tc ->
    if t then failwith "Tainted sources cannot access trust block"
    else
      let _ , t = eval tc env t priv_TB true in
      (Secure_Block(priv_TB),t)
| LetSecret (id, exprRight, letBody) ->
    if not (inTrustBlock) then failwith "You have to be in a TrustBlock" 
    else
    let xVal, taintness = eval exprRight env t priv_TB inTrustBlock in
    let letEnv = bind_env env id xVal taintness in
    let priv_TB2 = bind_tb priv_TB id Secret in
    eval letBody letEnv t priv_TB2 inTrustBlock 
| Handle (id, next) ->
  if secret_lookup priv_TB id then failwith "can't declare handle a secret"
  else if pub_lookup priv_TB id then
    let priv_TB2 = bind_tb priv_TB id Handler in
    eval next env t priv_TB2 inTrustBlock
  else failwith "can't add to handle list a variable not trusted" 


(*| EndRecursion -> (Secure_Block(priv_TB),t)*)




(*----------------------------------------------------------------------------------------------------*)
(*TEST*)
(*----------------------------------------------------------------------------------------------------*)
(*TEST 1*)
let x = Let("a",Eint 5,  Let("b", Eint 5,Prim ("*", Var "b", Var "a")));;

let env = [] 
let priv_TB = [] 
let prova = eval (x) env false priv_TB false


let print_eval (ris : evt * bool) =
  (*Just to display on the terminal the evaluation result*)
  match ris with
  | Int u, t -> Printf.printf " Result: Int %d, Taintness: %b\n" u t
  | Bool u, t -> Printf.printf " Result: Bool %b, Taintness: %b \n" u t
  | String u, t -> Printf.printf " Result: String %s, Taintness: %b\n" u t
  | _ -> Printf.printf " Closure\n";;
  
  print_eval(prova);;

(*TEST 2*)
let x = Trustblock(Let("a",Eint 5,  Let("b", Eint 5,Prim ("*", Var "b", Var "a"))));;

let env = [] 
let priv_TB = [] 
let prova = eval (x) env false priv_TB false


let print_eval (ris : evt * bool) =
  (*Just to display on the terminal the evaluation result*)
  match ris with
  | Int u, t -> Printf.printf " Result: Int %d, Taintness: %b\n" u t
  | Bool u, t -> Printf.printf " Result: Bool %b, Taintness: %b \n" u t
  | String u, t -> Printf.printf " Result: String %s, Taintness: %b\n" u t
  | Secure_Block u,t ->  Printf.printf " Result: Block created succesfully\n"
  | _ -> Printf.printf " Closure\n";;

  
  print_eval(prova);;
