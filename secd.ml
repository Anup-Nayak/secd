type exp = N of int | B of bool
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
  N n -> [ LDN n ]
  | B b -> [ LDB b ] 
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
  | Fst e1 -> (compile e1) @ [FST]
  | Snd e1 -> (compile e1) @ [SND]
  | Abs (x,e1) -> [ MKCLOS(x, compile(e1)@[RET]) ]
  | App (e1,e2) -> compile(e1)@compile(e2)@[APP]
;;

type values = N of int | B of bool | P of values * values |  Closure of string * opcode list * ((string*values) list);; 
type env = (string*values) list;;

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
  | a::Closure (x,c',g')::s', APP::c'', d -> 
    let g'' =  update_var x a g' in
    stkmc g'' [] c' ((s',g,c'')::d)
  | a::s', RET :: c' , (s'',g',c'')::d -> stkmc g' (a::s'') c'' d
  | _, _,_ -> raise (Stuck (g, s, c))
  ;;


let test_cases = [
  (* Basic arithmetic and comparison *)
  ([N 1],[],[],[],N 1);
  ([],[],compile(Plus(N 3,N 4)),[], N 7);
  ([],[],compile(Times(N 8,N 9)),[], N 72);
  ([], [], compile(Plus(N 3, N 4)), [], N 7);
  ([], [], compile(Times(N 8, N 9)), [], N 72);
  ([], [], compile(Eq(N 5, N 5)), [], B true);
  ([], [], compile(Eq(N 5, N 6)), [], B false);
  ([], [], compile(Gt(N 7, N 4)), [], B true);
  ([], [], compile(Gt(N 3, N 5)), [], B false);

  (* Boolean expressions *)
  ([], [], compile(And(B true, B true)), [], B true);
  ([], [], compile(And(B true, B false)), [], B false);
  ([], [], compile(Or(B false, B false)), [], B false);
  ([], [], compile(Or(B false, B true)), [], B true);
  ([], [], compile(Not(B true)), [], B false);
  ([], [], compile(Not(B false)), [], B true);

  (* Conditional expressions *)
  ([], [], compile(IfTE(B true, N 10, N 20)), [], N 10);
  ([], [], compile(IfTE(B false, N 10, N 20)), [], N 20);

  (* Variables *)
  ([],[("x", N 6);("y",N 7)], compile(Plus(V "x",V "y")),[], N 13);
  ([],[("x", B true);("y", N 1);("z",N 0)],compile(IfTE(V "x", V "y", V "z")),[], N 1);

  (* Pairs and projections *)
  ([],[("x", N 42);("y",B true)],compile(Pair(V "x", V "y")),[], P(N 42, B true));
  ([],["pair", P(N 42, B true)],compile(Fst(V "pair")),[],N 42);
  ([],["pair", P(N 42, B true)],compile(Snd(V "pair")),[],B true);

  (* Function abstraction and application *)
  ([],[],[MKCLOS("x",[])],[],Closure("x",[],[]));
  ([],[],[MKCLOS("x",[PLUS;EQ])],[],Closure("x",[PLUS;EQ],[]));
  ([],[("y", N 42)],[MKCLOS("x",[PLUS;EQ])],[],Closure("x",[PLUS;EQ],[("y", N 42)]));
  ([],[],compile(App(Abs("x",Plus(V "x", N 20)),N 5)),[],N 25);

  (* Nested applications *)
  ([], [], compile(App(Abs("y", App(Abs("x", Plus(V "x", V "y")), N 3)), N 2)), [], N 5);

  (* Variable capture in abstraction and scoping *)
  ([], [("x", N 22)], compile(App(Abs("x", Plus(V "x", N 20)), V "x")), [], N 42);
  ([], [("x", N 22);("y", N 2)], compile(App(Abs("x", Times(Plus(V "x", N 20),V "y")), V "x")), [], N 84);

  (* Error cases  *)
  (* change any of the above input/output *)

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