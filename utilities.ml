(*----------------------------------------------------------------------------------------------------*)
(*UTILITIES*)
(*----------------------------------------------------------------------------------------------------*)

open Ast
let rec lookup env x =
  match env with
  | [] -> failwith (x ^ " not found in lookup")
  | (y, v, _) :: r -> if x = y then v else lookup r x
  
  let rec t_lookup env x =
  match env with
  | [] -> failwith (x ^ " not found in t_lookup")
  | (y, _, t) :: r -> if x = y then t else t_lookup r x
  
  let rec c_lookup env x =
    match env with
    | [] -> failwith (x ^ " not found in c_lookup")
    | (y, c) :: r -> if x = y then c else c_lookup r x
  
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
  let bind_cf c_env (x:ide) (cf:conf_level) = (x,cf)::c_env
  
  let string_of_conf_level = function
    | High -> "High"
    | Low -> "Low"