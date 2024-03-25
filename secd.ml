type exp = Num of int | Bl of bool
  | V of string
  | Plus of exp * exp | Times of exp * exp
  | And of exp * exp | Or of exp * exp | Not of exp
  | Eq of exp * exp | Gt of exp * exp  
  | IfTE of exp * exp *exp
  | Pair of exp * exp
  | Fst of exp | Snd of exp
  (* | Abs of string * exp | App of exp * exp *)

  ;;


type opcode = LDN of int | LDB of bool | LOOKUP of string
  | PLUS | TIMES | AND | OR | NOT | EQ | GT
  | COND of opcode list * opcode list
  | PAIR
  | FST | SND
  ;;

type values = N of int | B of bool | P of values * values;; 

let rec compile e = match e with
  Num n -> [ LDN n ]
  | Bl b -> [ LDB b ] 
  | V x -> [LOOKUP x] 
  | Plus (e1, e2) -> (compile e1) @ (compile e2) @ [PLUS]
  | Times (e1, e2) -> (compile e1) @ (compile e2) @ [TIMES]
  | And (e1, e2) -> (compile e1) @ (compile e2) @ [AND]
  | Or (e1, e2) -> (compile e1) @ (compile e2) @ [OR]
  | Not e1 -> (compile e1) @ [NOT]
  | Eq (e1, e2) -> (compile e1) @ (compile e2) @ [EQ]
  | Gt(e1, e2) -> (compile e1) @ (compile e2) @ [GT]
  | IfTE(e0, e1, e2) -> (compile e0) @ [COND(compile e1, compile e2)]
  | Pair (e1, e2) -> (compile e1) @ (compile e2) @ [PAIR]
  | Fst e -> (compile e) @ [FST]
  | Snd e -> (compile e) @ [SND]
  ;;


exception Stuck of (string -> values) * values list * opcode list;;

let rec stkmc g s c = match s, c with
v::_, [ ] -> v 
| s, (LDN n)::c' -> stkmc g ((N n)::s) c'
| s, (LDB b)::c' -> stkmc g ((B b)::s) c'
| s, (LOOKUP x)::c' -> stkmc g ((g x)::s) c'
| (N n2)::(N n1)::s', PLUS::c' -> stkmc g (N(n1+n2)::s') c'
| (N n2)::(N n1)::s', TIMES::c' -> stkmc g (N(n1*n2)::s') c'
| (B b2)::(B b1)::s', AND::c' -> stkmc g(B(b1 && b2)::s') c'
| (B b2)::(B b1)::s', OR::c' -> stkmc g (B(b1 || b2)::s') c'
| (B b1)::s', NOT::c' -> stkmc g (B(not b1)::s') c'
| (N n2)::(N n1)::s', EQ::c' -> stkmc g (B(n1 = n2)::s') c'
| (N n2)::(N n1)::s', GT::c' -> stkmc g (B(n1 > n2)::s') c'
| (B true)::s', COND(c1,c2)::c' -> stkmc g s' (c1 @ c')
| (B false)::s', COND(c1,c2)::c' -> stkmc g s' (c2 @ c')
| (v2 :: v1 :: s', PAIR :: c') -> stkmc g (P (v1, v2) :: s') c'
| (P (v1, _) :: s', FST :: c') -> stkmc g (v1 :: s') c'
| (P (_, v2) :: s', SND :: c') -> stkmc g (v2 :: s') c'
| _, _ -> raise (Stuck (g, s, c))
;;

let rec string_of_opcode opcode = match opcode with
  | LDN n -> "LDN " ^ string_of_int n
  | LDB b -> "LDB " ^ string_of_bool b
  | LOOKUP x -> "LOOKUP " ^ x
  | PLUS -> "PLUS"
  | TIMES -> "TIMES"
  | AND -> "AND"
  | OR -> "OR"
  | NOT -> "NOT"
  | EQ -> "EQ"
  | GT -> "GT"
  | COND (c1, c2) -> "COND [" ^ (String.concat "; " (List.map string_of_opcode c1)) ^ "], [" ^ (String.concat "; " (List.map string_of_opcode c2)) ^ "]"
  | PAIR -> "PAIR"
  | FST -> "FST"
  | SND -> "SND";;


(* checking opcodes *)
let print_opcodes opcodes =
  let rec print_opcodes_helper = function
    | [] -> ()
    | opcode :: rest ->
        print_endline (string_of_opcode opcode);
        print_opcodes_helper rest
  in
  print_opcodes_helper opcodes;;


(* checking compile *)
let test_cases = [
(* Test addition *)
(Num 5, [LDN 5]);

(* Test boolean *)
(Bl true, [LDB true]);

(* Test variable *)
(V "x", [LOOKUP "x"]);

(* Test addition of two numbers *)
(Plus (Num 3, Num 4), [LDN 3; LDN 4; PLUS]);

(* Test if-then-else *)
(IfTE (Bl true, Num 1, Num 2), [LDB true; COND ([LDN 1], [LDN 2])]);

(* Test pair *)
(Pair (Num 5, Bl true), [LDN 5; LDB true; PAIR]);

(* Test projection *)
(Fst (Pair (Num 5, Bl true)), [LDN 5; LDB true; PAIR; FST]);

(* Test multiple operations *)
(Plus (Num 3, Times (Num 4, Num 2)), [LDN 3; LDN 4; LDN 2; TIMES; PLUS]);
]

let test_compile () =
  let rec run_tests = function
    | [] -> print_endline "All test cases passed!"
    | (expr, expected_opcodes) :: rest ->
        let generated_opcodes = compile expr in
        if generated_opcodes = expected_opcodes then
          (print_endline "Test passed!";
           run_tests rest)
        else
          (print_endline "Test failed!";
           print_endline ("Expected: " ^ (String.concat "; " (List.map string_of_opcode expected_opcodes)));
           print_endline ("Generated: " ^ (String.concat "; " (List.map string_of_opcode generated_opcodes))))
  in
  run_tests test_cases;;

(* Run test cases *)
test_compile ();;
