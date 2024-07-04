(*----------------------------------------------------------------------------------------------------*)
(*TYPE DEFINITION AND ENVIRONMENT*)
(*----------------------------------------------------------------------------------------------------*)
type ide = string

type sec_level=
  | Secret 
  | Public 
  | Handler 

type conf_level = 
  | High 
  | Low

(* 'env' is a list of: identifier ('ide') - value ('v') - taintness ('bool')*) 
type 'v env = (ide * 'v  * bool) list

(*'priv_TB' is a list of: identifier ('ide') - security level ('sec_level')*)
type 'v priv_TB = (ide * sec_level) list

type exp =
| Eint of int
| Ebool of bool
| Estring of string
| Var of ide
| Prim of ide * exp * exp
| If of exp * exp * exp
| Let of ide * exp * exp
| LetIn of ide * exp * exp (* to test the taint analysis *)
| Fun of ide * exp
| Apply of exp * exp
| Trustblock of exp 
| LetSecret of ide * exp * exp
| LetHandle of ide * exp
| LetPublic of ide * exp * exp
| Include of exp
| Execute of exp
| CallHandler of exp * exp
| End

type evt =
| Int of int
| Bool of bool
| String of string
| Closure of ide * exp * evt env * evt priv_TB
| ClosureInclude of exp * evt env
| Secure_Block of evt priv_TB * evt env

(*----------------------------------------------------------------------------------------------------*)
(*UTILITIES*)
(*----------------------------------------------------------------------------------------------------*)

let rec lookup env x =
match env with
| [] -> failwith (x ^ "not found")
| (y, v, _) :: r -> if x = y then v else lookup r x

let rec t_lookup env x =
match env with
| [] -> failwith (x ^ "not found")
| (y, _, t) :: r -> if x = y then t else t_lookup r x

let rec secret_lookup priv_TB x = 
match priv_TB with
| [] -> false
| (y, s) :: r -> if x = y && s = Secret then true else secret_lookup r x

let rec pub_lookup priv_TB x = 
  match priv_TB with
  | [] -> false
  | (y, s) :: r -> if x = y && s = Public then true else pub_lookup r x

let rec handle_lookup priv_TB x = 
  match priv_TB, x with
  | [], _ -> false
  | _, Var y -> (
      match priv_TB with
      | [] -> false
      | (z, s) :: r -> if y = z && s = Handler then true else handle_lookup r x)
  | _, _ -> false

let lattice_checking a b = match a,b with
  | Low, _ -> true
  | _, High -> true
  | _, _ -> false;;  

let join e e' = if e = Low then e' else High ;;

let bind_env env (x:ide) (v:evt) (t:bool) = (x,v,t)::env
let bind_tb priv_TB (x:ide) (sl:sec_level) = (x,sl)::priv_TB

(*----------------------------------------------------------------------------------------------------*)
(*INTERPRETER*)
(*----------------------------------------------------------------------------------------------------*)

let rec eval (e : exp) (env:evt env) (t : bool) (priv_TB: evt priv_TB) (inTrustBlock: bool): evt * bool =
match e with
| Eint n -> (Int n, t)
| Ebool b -> (Bool b, t)
| Estring s -> (String s, t)
| Var x -> 
  if inTrustBlock  && (secret_lookup priv_TB x) || (pub_lookup priv_TB x) then 
    (lookup env x, t_lookup env x)
  else
    if secret_lookup priv_TB x then failwith "Can't access a secret"
    else if handle_lookup priv_TB (Var x) || not (pub_lookup priv_TB x) then (lookup env x, t_lookup env x)
    else failwith "Can't access a variable not trusted"
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
    if inTrustBlock then failwith "You can't declare a variable in a TrustBlock" 
    else
      let xVal, taintness = eval exprRight env t priv_TB inTrustBlock in
      let letEnv = bind_env env x xVal taintness in
      eval letBody letEnv t priv_TB inTrustBlock
| LetIn (x, exprRight, letBody) -> 
    if (inTrustBlock) then failwith "You can't take a var from input in a TrustBlock"
    else
    let xVal, taintness = eval exprRight env true priv_TB inTrustBlock in
    let letEnv = bind_env env x xVal taintness in
    eval letBody letEnv true priv_TB inTrustBlock
| Fun (f_param, fBody) ->
  (Closure (f_param, fBody, env, priv_TB), t)
| Apply (eFun, eArg) -> ( 
  let fClosure, tClosure = eval eFun env t priv_TB inTrustBlock in
  match fClosure with
  | Closure (x, fBody, fDeclEnv, priv_TB) ->
      let xVal, taintness = eval eArg env tClosure priv_TB inTrustBlock in
        let fBodyEnv = (x, xVal, taintness) :: fDeclEnv in
          eval fBody fBodyEnv taintness priv_TB inTrustBlock
  | _ -> failwith "eval Call: not a function")
| Trustblock tc ->
    if t then failwith "The content of the TrustBlock is tainted"
    else
      eval tc env t priv_TB true
| LetSecret (id, exprRight, letBody) ->
    if not (inTrustBlock) then failwith "You have to be in a TrustBlock" 
    else
    let xVal, taintness = eval exprRight env t priv_TB inTrustBlock in
    let letEnv = bind_env env id xVal taintness in
    let priv_TB2 = bind_tb priv_TB id Secret in
    eval letBody letEnv t priv_TB2 inTrustBlock 
| LetHandle (id, next) ->
  if not (inTrustBlock) then failwith "You have to be in a TrustBlock" 
  else
  if secret_lookup priv_TB id then failwith "can't declare handle a secret"
  else if pub_lookup priv_TB id then
    let priv_TB2 = bind_tb priv_TB id Handler in
    eval next env t priv_TB2 inTrustBlock
  else failwith "can't add to handle list a variable not trusted" 
| LetPublic (id, exprRight, letBody) ->
    if not (inTrustBlock) then failwith "You have to be in a TrustBlock" 
    else
    let xVal, taintness = eval exprRight env t priv_TB inTrustBlock in
    let letEnv = bind_env env id xVal taintness in
    let priv_TB2 = bind_tb priv_TB id Public in
    eval letBody letEnv t priv_TB2 inTrustBlock   
| Include iBody -> (
  if inTrustBlock then failwith "You can't include a file in a TrustBlock" 
  else
  match iBody with
  | Include _ -> failwith "Cannot nest include blocks"
  | Trustblock _ ->
      failwith "Cannot create TrustBlocks inside an Include"
  | _ -> (ClosureInclude (iBody, env), t))
| Execute e -> 
  if inTrustBlock then failwith "You can't execute a file in a TrustBlock" 
  else
  begin
    let v1, t1 = eval e env t priv_TB inTrustBlock in
    match v1 with
    | ClosureInclude (iBody, iEnv) -> eval iBody iEnv true priv_TB inTrustBlock
    | _ -> failwith "Unexpected condition."
  end
| CallHandler (e1, e2) -> (
    let v1, t1 = eval e1 env t priv_TB inTrustBlock in
    if not (handle_lookup priv_TB e2) then failwith "You can access only an handle var"
    else
      match (v1, t1) with
      | Secure_Block(priv_TB, secondEnv), t1 -> eval e2 secondEnv t1 priv_TB inTrustBlock
      | _ -> failwith "the access must be applied to an trustblock")
| End -> (Secure_Block(priv_TB,env),t)

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

(*TEST 2
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
  | Secure_Block (u,b),t ->  Printf.printf " Result: Block created succesfully\n"
  | _ -> Printf.printf " Closure\n";;

  
  print_eval(prova);;
*)
(*TEST 3*)
let x = Let("mytrustB",Trustblock(LetPublic("x",Eint 11,LetHandle("x",End))),
        Let("a",Eint 5,  Let("b", Eint 5,Prim ("*", Var "b", Var "a"))));;

let env = [] 
let priv_TB = [] 
let prova = eval (x) env false priv_TB false


let print_eval (ris : evt * bool) =
  (*Just to display on the terminal the evaluation result*)
  match ris with
  | Int u, t -> Printf.printf " Result: Int %d, Taintness: %b\n" u t
  | Bool u, t -> Printf.printf " Result: Bool %b, Taintness: %b \n" u t
  | String u, t -> Printf.printf " Result: String %s, Taintness: %b\n" u t
  | Secure_Block (u,b),t ->  Printf.printf " Result: Block created succesfully\n"
  | _ -> Printf.printf " Closure\n";;

  
  print_eval(prova);;
  
  (*TEST 4 -> prova di access trust*)
  let x = Let("mytrustB",Trustblock(LetPublic("x",Eint 11,LetPublic("f",Var "x",LetHandle("f", End)))),
  CallHandler(Var "mytrustB", Var "f")
);;
  
  let env = [] 
  let priv_TB = [] 
  let prova = eval (x) env false priv_TB false
  
  
  let print_eval (ris : evt * bool) =
    (*Just to display on the terminal the evaluation result*)
    match ris with
    | Int u, t -> Printf.printf " Result: Int %d, Taintness: %b\n" u t
    | Bool u, t -> Printf.printf " Result: Bool %b, Taintness: %b \n" u t
    | String u, t -> Printf.printf " Result: String %s, Taintness: %b\n" u t
    | Secure_Block (u,b),t ->  Printf.printf " Result: Block created succesfully\n"
    | _ -> Printf.printf " Closure\n";;
  
    
    print_eval(prova);;

 
  (*TEST 5 -> prova di include*)
  let x = Let("extCode",Include(Let("a",Eint 5,Let("b",Eint 2,Prim ("*", Var "b", Var "a")))),
      Execute(Var "extCode"));;
  
  let env = [] 
  let priv_TB = [] 
  let prova = eval (x) env false priv_TB false
  
  
  let print_eval (ris : evt * bool) =
    (*Just to display on the terminal the evaluation result*)
    match ris with
    | Int u, t -> Printf.printf " Result: Int %d, Taintness: %b\n" u t
    | Bool u, t -> Printf.printf " Result: Bool %b, Taintness: %b \n" u t
    | String u, t -> Printf.printf " Result: String %s, Taintness: %b\n" u t
    | Secure_Block (u,b),t ->  Printf.printf " Result: Block created succesfully\n"
    | _ -> Printf.printf " Closure\n";;
  
    
    print_eval(prova);;   

  (*TEST 6 -> let da input*)
  let x = Let("mytrustB",Trustblock(LetIn("a",Eint 5,  End)), Prim ("*", Eint 5, Eint 6));;
  
  let env = [] 
  let priv_TB = [] 
  let prova = eval (x) env false priv_TB false
  
  
  let print_eval (ris : evt * bool) =
    (*Just to display on the terminal the evaluation result*)
    match ris with
    | Int u, t -> Printf.printf " Result: Int %d, Taintness: %b\n" u t
    | Bool u, t -> Printf.printf " Result: Bool %b, Taintness: %b \n" u t
    | String u, t -> Printf.printf " Result: String %s, Taintness: %b\n" u t
    | Secure_Block (u,b),t ->  Printf.printf " Result: Block created succesfully\n"
    | _ -> Printf.printf " Closure\n";;
  
    
    print_eval(prova);; 