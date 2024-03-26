open Stdlib

type exp = Num of int | Bl of bool
  | V of string
  | Plus of exp * exp | Times of exp * exp
  | And of exp * exp | Or of exp * exp | Not of exp
  | Eq of exp * exp | Gt of exp * exp  
  | IfTE of exp * exp *exp
  | Pair of exp * exp
  | Fst of exp | Snd of exp
  | Abs of string * exp | App of exp * exp
  ;;



type opcode = LDN of int | LDB of bool | LOOKUP of string
  | PLUS | TIMES | AND | OR | NOT | EQ | GT
  | COND of opcode list * opcode list
  | PAIR
  | FST | SND
  | APP | MKCLOS of string * opcode list | RET
  ;;

  
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
  | Abs (x,e) -> [ MKCLOS(x, compile(e)@[RET]) ]
  | App (e1,e2) -> compile(e1)@compile(e2)@[APP]
;;

type values = N of int | B of bool | P of values * values |  Closure of string * opcode list * ((string*values) list);; 
type env = (string*values) list

exception Stuck of env * values list * opcode list;;

let rec lookup_var x env = match env with
  | [] -> raise Not_found
  | (x',v) :: _ when x = x' -> v
  | _ :: rest -> lookup_var x rest

let rec update_var x v env = match env with
  | [] -> [(x, v)]
  | (x', _) :: rest when x = x' -> (x, v) :: rest
  | binding :: rest -> binding :: update_var x v rest

let rec stkmc g s c d = match s, c, d  with
  v::_, [ ] , _-> v 
  | s, (LDN n)::c' , _-> stkmc g ((N n)::s) c' d
  | s, (LDB b)::c' , _ -> stkmc g ((B b)::s) c' d
  | s, (LOOKUP x)::c' , _ -> 
    let a = lookup_var x g in
    stkmc g (a::s) c' d
  | (N n2)::(N n1)::s', PLUS::c' , _ -> stkmc g (N(n1+n2)::s') c' d
  | (N n2)::(N n1)::s', TIMES::c' , _ -> stkmc g (N(n1*n2)::s') c' d
  | (B b2)::(B b1)::s', AND::c' , _ -> stkmc g (B(b1 && b2)::s') c' d
  | (B b2)::(B b1)::s', OR::c' , _ -> stkmc g (B(b1 || b2)::s') c' d
  | (B b1)::s', NOT::c' , _ -> stkmc g (B(not b1)::s') c' d
  | (N n2)::(N n1)::s', EQ::c' , _ -> stkmc g (B(n1 = n2)::s') c' d
  | (N n2)::(N n1)::s', GT::c' , _ -> stkmc g (B(n1 > n2)::s') c' d
  | (B true)::s', COND(c1,c2)::c' , _ -> stkmc g s' (c1 @ c') d
  | (B false)::s', COND(c1,c2)::c' , _ -> stkmc g s' (c2 @ c') d
  | v2 :: v1 :: s', PAIR :: c' , _ -> stkmc g (P (v1, v2) :: s') c' d
  | P (v1, _) :: s', FST :: c' , _  -> stkmc g (v1 :: s') c' d
  | P (_, v2) :: s', SND :: c'  , _ -> stkmc g (v2 :: s') c' d
  | s, MKCLOS(x',c')::c'',d -> 
    let closure = Closure (x', c', g) in
    stkmc g (closure :: s) c'' d
  | a::Closure (x,c',g')::s' ,APP::c'', d -> 
    let g'' =  update_var x a g' in
    stkmc g'' [] c' ((s',g,c'')::d)
  | a::s', RET :: c' , (s'',g',c'')::d -> stkmc g' (a::s'') c'' d
  | _, _,_ -> raise (Stuck (g, s, c))
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
  | SND -> "SND"
  | RET -> "RET"
  | APP -> "APP"
  | MKCLOS(a,b) -> "MKCLOS [" ^ a ^ "], [" ^ (String.concat "; " (List.map string_of_opcode b)) ^ "]"
;;


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
let test_cases_compile = [
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
  run_tests test_cases_compile;;

(* Run test cases *)
(* test_compile ();; *)


let test_cases = [
  (* Basic arithmetic and comparison *)
  ([N 1],[],[],[],N 1);
  ([],[],compile(Plus(Num 3,Num 4)),[], N 7);
  ([],[],compile(Times(Num 8,Num 9)),[], N 72);
  ([], [], compile(Plus(Num 3, Num 4)), [], N 7);
  ([], [], compile(Times(Num 8, Num 9)), [], N 72);
  ([], [], compile(Eq(Num 5, Num 5)), [], B true);
  ([], [], compile(Eq(Num 5, Num 6)), [], B false);
  ([], [], compile(Gt(Num 7, Num 4)), [], B true);
  ([], [], compile(Gt(Num 3, Num 5)), [], B false);

  (* Boolean expressions *)
  ([], [], compile(And(Bl true, Bl true)), [], B true);
  ([], [], compile(And(Bl true, Bl false)), [], B false);
  ([], [], compile(Or(Bl false, Bl false)), [], B false);
  ([], [], compile(Or(Bl false, Bl true)), [], B true);
  ([], [], compile(Not(Bl true)), [], B false);
  ([], [], compile(Not(Bl false)), [], B true);

  (* Conditional expressions *)
  ([], [], compile(IfTE(Bl true, Num 10, Num 20)), [], N 10);
  ([], [], compile(IfTE(Bl false, Num 10, Num 20)), [], N 20);

  (* Variables *)
  ([],[("x", N 6);("y",N 7)], compile(Plus(V "x",V "y")),[], N 13);
  ([],[("x", B true);("y", N 1);("z",N 0)],compile(IfTE(V "x", V "y", V "z")),[], N 1);

  (* Pairs and projections *)
  ([],[("x", N 42);("y",B true)],compile(Pair(V "x", V "y")),[], P(N 42, B true));
  ([],["pair", P(N 42, B true)],compile(Fst(V "pair")),[],N 42);
  ([],["pair", P(N 42, B true)],compile(Snd(V "pair")),[],B true);

  (* Function abstraction and application *)
  

  (* Error cases  *)

]


let rec run_tests cases = match cases with
  | [] -> print_endline "All test cases passed!"
  | (stack,env,control,dump, expected_result)::rest ->
      let result = stkmc env stack control dump in
        if result = expected_result then(
          print_endline "Test passed!";
          run_tests rest
        )else(
          print_endline "Test failed!";
        );;



run_tests test_cases;;