open Ast 
open Utilities 

let rec eval (e : exp) (env:evt env) (t : bool) (priv_TB: evt priv_TB) (inTrustBlock: bool): evt * bool =
  match e with
  | Eint n -> (Int n, t)
  | Ebool b -> (Bool b, t)
  | Estring s -> (String s, t)
  | Var x -> 
    if inTrustBlock  && (secret_lookup priv_TB x) || (pub_lookup priv_TB x) then 
      (lookup env x, t_lookup env x)
    else
      if secret_lookup priv_TB x then failwith "Can't access a secret entity"
      else if handle_lookup priv_TB (Var x) || not (pub_lookup priv_TB x) then (lookup env x, t_lookup env x)
      else failwith "Can't access a variable not trusted"
  | Prim (op, e1, e2) ->
    begin
      let v1, t1 = eval e1 env t priv_TB inTrustBlock in
      let v2, t2 = eval e2 env t priv_TB inTrustBlock in
      match (op, v1, v2) with
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
  | Let (x, value, body) ->
      if inTrustBlock then failwith "You can't use Let in a TrustBlock" 
      else
        let v, taintness = eval value env t priv_TB inTrustBlock in
        let newEnv = bind_env env x v taintness in
        eval body newEnv t priv_TB inTrustBlock
  | LetIn (x, value, body) -> 
      if (inTrustBlock) then failwith "You can't take a var from input in a TrustBlock"
      else
      let v, taintness = eval value env true priv_TB inTrustBlock in
      let newEnv = bind_env env x v taintness in
      eval body newEnv true priv_TB inTrustBlock
  | Fun (param, body) ->
    (Closure (param, body, env, priv_TB), t)
  | Apply (eFun, eArg) -> ( 
    let fClosure, tClosure = eval eFun env t priv_TB inTrustBlock in
    match fClosure with
    | Closure (x, fBody, fDeclEnv, priv_TB) ->
        let v, taintness = eval eArg env tClosure priv_TB inTrustBlock in
          let fBodyEnv = (x, v, taintness) :: fDeclEnv in
            eval fBody fBodyEnv taintness priv_TB inTrustBlock
    | _ -> failwith "eval Call: not a function")
  | Trustblock content ->
      if inTrustBlock then failwith "You can't create a TrustBlock inside a TrustBlock"
      else
      if t then failwith "The content of the TrustBlock is tainted"
      else
        eval content env t priv_TB true
  | LetSecret (x, value, body) ->
      if not (inTrustBlock) then failwith "You have to be in a TrustBlock" 
      else
      let v, taintness = eval value env t priv_TB inTrustBlock in
      let newEnv = bind_env env x v taintness in
      let priv_TB2 = bind_tb priv_TB x Secret in
      eval body newEnv t priv_TB2 inTrustBlock 
  | LetHandle (x, body) ->
    if not (inTrustBlock) then failwith "You have to be in a TrustBlock" 
    else
    if secret_lookup priv_TB x then failwith "can't declare handle a secret"
    else if pub_lookup priv_TB x then
      let priv_TB2 = bind_tb priv_TB x Handler in
      eval body env t priv_TB2 inTrustBlock
    else failwith "can't add to handle list a variable not trusted" 
  | LetPublic (x, value, body) ->
      if not (inTrustBlock) then failwith "You have to be in a TrustBlock" 
      else
      let v, taintness = eval value env t priv_TB inTrustBlock in
      let newEnv = bind_env env x v taintness in
      let priv_TB2 = bind_tb priv_TB x Public in
      eval body newEnv t priv_TB2 inTrustBlock   
  | Include content -> (
    if inTrustBlock then failwith "You can't include a file in a TrustBlock" 
    else
    match content with
    | Include _ -> failwith "Cannot include within an Include"
    | Trustblock _ ->
        failwith "Cannot create TrustBlocks inside an Include"
    | _ -> (ClosureInclude (content, env), t))
  | Execute e -> 
    if inTrustBlock then failwith "You can't execute a file in a TrustBlock" 
    else
    begin
      let v1, t1 = eval e env t priv_TB inTrustBlock in
      match v1 with
      | ClosureInclude (iBody, iEnv) -> eval iBody iEnv true priv_TB inTrustBlock
      | _ -> failwith "Unexpected condition."
    end
  | CallHandler (trustblock, handler) -> (
      let v1, t1 = eval trustblock env t priv_TB inTrustBlock in
        match (v1, t1) with
        | Secure_Block(priv_TB1, secondEnv), t1 -> 
          if not (handle_lookup priv_TB1 handler) 
            then failwith "You can access only an handle var" 
          else
            eval handler secondEnv t1 priv_TB1 inTrustBlock
        | _ -> failwith "the access must be applied to an trustblock")
  | Assert param -> (
        let v1, t1 = eval param env t priv_TB inTrustBlock in
        if t1 = true then failwith "Assertion failed"
        else (Int 1,true)
        )
  | End ->  Secure_Block(priv_TB,env),t