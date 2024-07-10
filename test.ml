(*----------------------------------------------------------------------------------------------------*)
(*TEST*)
(*----------------------------------------------------------------------------------------------------*)

open Ast 
open Utilities 
open Eval 
open Type_checking  


(*let rec print_list priv_TB =
(*Just to display on the terminal the evaluation result*)
match priv_TB with
| [] -> Printf.printf " Lista vuota \n"
| (x,s,_) :: rest -> let _ = Printf.printf " Ide %s, " x (*(string_of_conf_level s)*) in 
print_list rest *)

let print_eval (ris : evt * bool) =
(*Just to display on the terminal the evaluation result*)
match ris with
| Int u, t -> Printf.printf " Result: Int %d, Taintness: %b\n" u t
| Bool u, t -> Printf.printf " Result: Bool %b, Taintness: %b \n" u t
| String u, t -> Printf.printf " Result: String %s, Taintness: %b\n" u t
| _ -> Printf.printf " Closure\n";;


let print_type (ris : bool) =
(*Just to display on the terminal the information flow result*)
match ris with
| true-> Printf.printf " Result: Well typed \n" 
| false -> Printf.printf " Result: Illegal flow \n" ;;

let run_test name test_fn =   
try     
  Printf.printf "Running %s...\n" name;     
  test_fn ();     
  Printf.printf "%s passed.\n" name;   
with   
  | Failure msg -> Printf.printf "%s failed: %s\n" name msg   
  | exn -> Printf.printf "%s failed with unexpected exception: %s\n" name (Printexc.to_string exn)

(*TEST 1: try to innest a let inside onother let *)
let test_1 () = 
let x = Let("a",Eint 5,  Let("b", Eint 5,Prim ("*", Var "b", Var "a"))) in
let env = [] in
let priv_TB = [] in
let c_env = [] in
let test_IF = type_check_com x c_env Low in
let _ = print_type(test_IF) in
let test_eval = eval (x) env false priv_TB false in
print_eval(test_eval);;

(*TEST 2: try to verify if the LetHandle works correctly*)
let test_2 () = 
let x = Let("mytrustB",Trustblock(LetPublic("x_1",Eint 11,LetHandle("x_1",End))),Let("a",Eint 6,Let("b", Eint 6,Prim ("*", Var "b", Var "a")))) in
let env = [] in
let priv_TB = [] in
let c_env = [] in
let test_IF = type_check_com x c_env Low in
let _ = print_type(test_IF) in
let test_eval = eval (x) env false priv_TB false in
print_eval(test_eval);;

(*TEST 3 -> try to verify if the CallHandler works correctly*)
let test_3 () =
  let x = Let("mytrustB",Trustblock(LetPublic("x",Eint 11,LetPublic("f",Var "x",LetHandle("f", End)))),CallHandler(Var "mytrustB", Var "f"))in  
  let env = [] in
  let priv_TB = [] in
  let c_env = [] in
  let test_IF = type_check_com x c_env Low in
  let _ = print_type(test_IF) in
  let test_eval = eval (x) env false priv_TB false in
  print_eval(test_eval);;

(*TEST 4 -> try to verify if the CallHandler works correctly with a function *)
let test_4 () =
  let x = Let("mytrustB",Trustblock(LetPublic("x",Eint 11,LetPublic("f",Fun ("c",Prim ("+", Var "c", Eint 5)),LetHandle("f", End)))),Apply(CallHandler(Var "mytrustB", Var "f"), Eint 5))in  
  let env = [] in
  let priv_TB = [] in
  let c_env = [] in
  let test_IF = type_check_com x c_env Low in
  let _ = print_type(test_IF) in
  let test_eval = eval (x) env false priv_TB false in
  print_eval(test_eval);;

(*TEST 5 -> try to verify if Include and Execute works correctly *)
let test_5 () =
  let x = Let("plugin",Include(Let("a",Eint 5,Let("b",Eint 2,Prim ("*", Var "b", Var "a")))),Execute(Var "plugin")) in
  let env = [] in
  let priv_TB = [] in
  let c_env = [] in
  let test_IF = type_check_com x c_env Low in
  let _ = print_type(test_IF) in
  let test_eval = eval (x) env false priv_TB false in
  print_eval(test_eval);;
(*TEST 6 ->  try to verify if LetIn works correctly*)
let test_6 () =
  let x = Let("mytrustB",Trustblock(LetIn("a",Eint 5,  End)), Prim ("*", Eint 5, Eint 6)) in
  let env = [] in
  let priv_TB = [] in
  let c_env = [] in
  let test_IF = type_check_com x c_env Low in
  let _ = print_type(test_IF) in
  let test_eval = eval (x) env false priv_TB false in
  print_eval(test_eval);;
(*TEST 7 -> try to verify if Trustblock C can access a secret variable (called a) from Trusstblock B*)
let test_7 () =
  let x = Let("mytrustB",Trustblock(LetSecret("a",Eint 5,  End)), Let("mytrustC",Trustblock(LetPublic("y",Var "a",LetHandle("y", End))),Prim ("*", Eint 5, Var "y"))) in
  let env = [] in
  let priv_TB = [] in
  let c_env = [] in
  let test_IF = type_check_com x c_env Low in
  let _ = print_type(test_IF) in
  let test_eval = eval (x) env false priv_TB false in
  print_eval(test_eval);;
(*TEST 8 -> try to verify if there is an information flow between the secret variable y and the pubblic x*)
let test_8 () = 
  let x = Let("mytrustB",Trustblock(LetSecret("y", Eint 22, LetPublic("x",Var "y",LetHandle("x",End)))),Let("a",Eint 5,  Let("b", Eint 5,Prim ("*", Var "b", Var "a")))) in
  let env = [] in
  let priv_TB = [] in
  let c_env = [] in
  let test_IF = type_check_com x c_env Low in
  let _ = print_type(test_IF) in
  let test_eval = eval (x) env false priv_TB false in
  print_eval(test_eval);;
(*TEST 09 -> try to verify that the plugin cannot access a secret variable*)
let test_9 () = 
  let x = Let("mytrustA", Trustblock(LetSecret("x", Eint 11, End)), Let("c",Include(Let("y", Var "x",Var "y")), Execute(Var "c")))in
  let env = [] in
  let priv_TB = [] in
  let c_env = [] in
  let test_IF = type_check_com x c_env Low in
  let _ = print_type(test_IF) in
  let test_eval = eval (x) env false priv_TB false in
  print_eval(test_eval);;
(*TEST 10 -> Plugin attempt to access a handle variable*)
let test_10 () = 
  let x = Let("mytrustB",Trustblock(LetSecret("x",Eint 5,LetPublic ("y",Eint 2,LetHandle ("y", End)))),Let("code",CallHandler(Var "mytrustB", Var "y"),Let("plugin",Include(Let("a",Eint 4,Let("b",CallHandler (Var "mytrustB", Var "y"),Prim ("*", Var "b", Var "a")))),Execute (Var "plugin"))))in
  let env = [] in
  let priv_TB = [] in
  let c_env = [] in
  let test_IF = type_check_com x c_env Low in
  let _ = print_type(test_IF) in
  let test_eval = eval (x) env false priv_TB false in
  print_eval(test_eval);;
(*TEST 11 -> A Include inside a Trusblock*)
let test_11 () = 
  let x = Let("mytrustB",Trustblock(Include(Let("a",Eint 5,Let("b",Eint 2,Prim ("*", Var "b", Var "a"))))),Eint 6)in
  let env = [] in
  let priv_TB = [] in
  let c_env = [] in
  let test_IF = type_check_com x c_env Low in
  let _ = print_type(test_IF) in
  let test_eval = eval (x) env false priv_TB false in
  print_eval(test_eval);;

(*TEST 12 -> LetPublic outside a TrustBlock*)
let test_12 () = 
  let x = LetPublic("mytrustB",Trustblock((Let("a",Eint 5,Let("b",Eint 2,Prim ("*", Var "b", Var "a"))))),Eint 6)in
  let env = [] in
  let priv_TB = [] in
  let test_eval = eval (x) env false priv_TB false in
  print_eval(test_eval);;

  (*TEST 13 -> Trustblock inside a Trustblock*)
  let test_13 () = 
    let x = Let("mytrustB",Trustblock(Trustblock(Let("a",Eint 5,Let("b",Eint 2,Prim ("*", Var "b", Var "a"))))),Eint 6)in
    let env = [] in
    let priv_TB = [] in
    let test_eval = eval (x) env false priv_TB false in
    print_eval(test_eval);;

  (*TEST 14 -> Include inside an Include*)
  let test_14 () = 
    let x = Let("Include",Include(Include(Let("a",Eint 5,Let("b",Eint 2,Prim ("*", Var "b", Var "a"))))),Eint 6)in
    let env = [] in
    let priv_TB = [] in
    let test_eval = eval (x) env false priv_TB false in
    print_eval(test_eval);;
  (*TEST 15 -> Trustblock inside an Include*)
  let test_15 () = 
  let x = Let("mytrustB",Include(Trustblock(Let("a",Eint 5,Let("b",Eint 2,Prim ("*", Var "b", Var "a"))))),Eint 6)in
  let env = [] in
  let priv_TB = [] in
  let test_eval = eval (x) env false priv_TB false in
  print_eval(test_eval);;

(*TEST 16 -> Operation between a tainted and an untainted value*)
let test_16 () = 
  let x = Let("plugin", Include(Let("a", Eint 2, Let("b", Eint 4, Prim("+", Var "a", Var "b")))),Let("Executed", Execute(Var "plugin"), Let("g", Eint 5, Prim("*", Var "g", Var "Executed"))))in
  let env = [] in
  let priv_TB = [] in
  let c_env = [] in
  let test_IF = type_check_com x c_env Low in
  let _ = print_type(test_IF) in
  let test_eval = eval (x) env false priv_TB false in
  print_eval(test_eval);;

(*TEST 17 -> CallHandler on a variable that isn't handler*)
let test_17 () = 
  let x = Let("mytrustB",Trustblock(LetPublic("x",Eint 11,LetPublic("f",Var "x",LetHandle("f", End)))),CallHandler(Var "mytrustB", Var "x")) in
  let env = [] in
  let priv_TB = [] in
  let c_env = [] in
  let test_IF = type_check_com x c_env Low in
  let _ = print_type(test_IF) in
  let test_eval = eval (x) env false priv_TB false in
  print_eval(test_eval);;

(*TEST 18 -> try to verify if the assert works*)
let test_18 () = 
  let x = LetIn("a",Eint 5, Assert(Var "a"))  in
  let env = [] in
  let priv_TB = [] in
  let c_env = [] in
  let test_IF = type_check_com x c_env Low in
  let _ = print_type(test_IF) in
  let test_eval = eval (x) env false priv_TB false in
  print_eval(test_eval);;


let () = 
  run_test "test 1" test_1;
  run_test "test 2" test_2;
  run_test "test 3" test_3;
  run_test "test 4" test_4;
  run_test "test 5" test_5;
  run_test "test 6" test_6;
  run_test "test 7" test_7;
  run_test "test 8" test_8;
  run_test "test 9" test_9;
  run_test "test 10" test_10;
  run_test "test 11" test_11;
  run_test "test 12" test_12;
  run_test "test 13" test_13;
  run_test "test 14" test_14;
  run_test "test 15" test_15;
  run_test "test 16" test_16;
  run_test "test 17" test_17;
  run_test "test 18" test_18;;