type ide = string

(* environment -> identifier - value - taitness - secret - handle *) 
type 'v env = (string * 'v * bool * bool * bool) list

type exp =
| Eint of int
| Ebool of bool
| Estring of string
| Var of ide
| Prim of ide * exp * exp
| Let of ide * exp * exp
| If of exp * exp * exp
| Fun of ide * exp
| Call of exp * exp
| Abort of string
| Trustblock of tcb 
| Include of exp
| Excecute of exp

and tcb = 
| LetSecret of ide * exp * tcb
| Handle of ide * tcb
| EndRecursion 


type evt =
  | Int of int
  | Bool of bool
  | String of string
  | Closure of ide * exp * evt env 



let rec lookup env x =
match env with
| [] -> failwith (x ^ "not found")
| (y, v, _, _, _) :: r -> if x = y then v else lookup r x

(* taintness of a variable *) 
let rec t_lookup env x =
match env with
| [] -> failwith (x ^ "not found")
| (y, _, t, _, _) :: r -> if x = y then t else t_lookup r x

let bind env (x:ide) (v:int) (t:bool) (s:bool) (h:bool)= (x,v,t,s,h)::env

let rec eval (e : exp) (env:evt env) (t : bool) (s : bool) (h : bool) : evt * bool =
match e with
| Eint n -> (Int n, t)
| Ebool b -> (Bool b, t)
| Estring s -> (String s, t)
| Var x -> (lookup env x, t_lookup env x)
| Prim (op, e1, e2) ->
  begin
    let v1, t1 = eval e1 env t s h in 
    let v2, t2 = eval e2 env t s h in
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
  let v1, t1 = eval e1 env t s h in 
  match v1 with
    | Bool true -> let v2, t2 = eval e2 env t s h in (v2, t1 || t2) 
    | Bool false -> let v3, t3 = eval e3 env t s h in (v3, t1 || t3) 
    | _ -> failwith "Unexpected condition."
  end
| Let(i, e, ebody) ->
  let tipo , risultato = (eval e env t s h) in 
    eval ebody (bind env i risultato s h) t s h









