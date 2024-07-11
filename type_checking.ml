(*----------------------------------------------------------------------------------------------------*)
(*TYPE CHECKING*)
(*----------------------------------------------------------------------------------------------------*)
open Ast 
open Utilities 
let rec type_check_exp (e:exp) (c_env: conf_level c_env)  =
  match e with
  | Eint i -> Low
  | Ebool b -> Low
  | Var x -> c_lookup c_env x
  | Prim (op, e1, e2) ->  let t = type_check_exp e1 c_env in
                          let t1 = type_check_exp e2 c_env in
                          (join t t1) 
  | _ -> Low;; 

let rec type_check_com (c:exp) (c_env: conf_level c_env) (cxt: conf_level) : bool =
  match c with
  | If(e, c1, c2) ->  let t = type_check_exp e c_env in
                      let cxt1 = (join cxt t) in
                      (type_check_com c1 c_env cxt1) &&
                      (type_check_com c2 c_env cxt1)
  | Let(x, value, body) -> 
                    let t = 
                    match value with 
                    | Trustblock _ -> let a = type_check_com value c_env cxt in
                                      if a = true 
                                        then Low
                                        else failwith "Information flow error in trustblock" 
                    | _ -> type_check_exp value c_env 
                    in
                      let cxt1 = (join cxt t) in
                      if (lattice_checking cxt1 (Low)) then
                        let c_env1 = bind_cf c_env x Low in
                          type_check_com body c_env1 cxt1
                      else false
  | Fun(x, c) -> type_check_com c c_env cxt
  | Trustblock content -> type_check_com content c_env cxt
  | LetSecret(x, value, body) -> let t = type_check_exp value c_env in 
                          let cxt1 = (join cxt t) in
                          if (lattice_checking cxt1 (High)) then
                            let c_env1 = bind_cf c_env x High in
                              type_check_com body c_env1 cxt1
                          else false
  | LetPublic(x, value, body) -> let t = type_check_exp value c_env in 
                          let cxt1 = (join cxt t) in
                          if (lattice_checking cxt1 (Low)) then
                            let c_env1 = bind_cf c_env x Low in
                                type_check_com body c_env1 cxt1
                          else false                        
  | LetHandle(x, body) -> if (c_lookup c_env x) = High 
                        then 
                            failwith "Handle must be Low"
                        else 
                            type_check_com body c_env cxt
  | _-> true;;