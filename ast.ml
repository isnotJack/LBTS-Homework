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
(* 'c_env' is a list of: identifier ('ide') - confidential level ('conf_level')*) 
type 'v c_env = (ide * conf_level) list
(*'priv_TB' is a list of: identifier ('ide') - security level ('sec_level')x*)
type 'v priv_TB = (ide * sec_level) list

type exp =
| Eint of int
| Ebool of bool
| Estring of string
| Var of ide
| Prim of ide * exp * exp
| If of exp * exp * exp
| Let of ide * exp * exp
| LetIn of ide * exp * exp  (* to test the taint analysis *)
| Fun of ide * exp
| Apply of exp * exp
| Trustblock of exp 
| LetSecret of ide * exp * exp
| LetHandle of ide * exp
| LetPublic of ide * exp * exp
| Include of exp
| Execute of exp
| CallHandler of exp * exp
| Assert of exp
| End                         (* end of a trust block*)

type evt =
| Int of int
| Bool of bool
| String of string
| Closure of ide * exp * evt env * evt priv_TB
| ClosureInclude of exp * evt env
| Secure_Block of evt priv_TB * evt env
