(* $Id: Semantics.ml $ *)

(*
 * Semantics of program commands.
 *)

open Z3

(* Create a variable in the z3 context with the correct syntax x$i *)
let z3_var ctx var i =
  Arithmetic.Integer.mk_const_s ctx (var ^ "$" ^ (string_of_int i))

(* Define new operations that take a list of expressions
 and return a list of expressions,
 TODO:  ensure the denominator is non zero *)
let div ctx expr_list =
  let a = List.nth expr_list 0
  and b = List.nth expr_list 1
  in
  Arithmetic.mk_div ctx a b

  
(* Evaluation of an expression. *)
let rec eval ctx e i =
    match e with
    | Command.Expression.Cst c -> Arithmetic.Integer.mk_numeral_i ctx c
    | Command.Expression.Var v -> z3_var ctx v i
    | Command.Expression.Op (e, o, e') ->
       let fun_op =
         match o with
         | Command.Expression.Add -> Arithmetic.mk_add
         | Command.Expression.Sub -> Arithmetic.mk_sub
         | Command.Expression.Mul -> Arithmetic.mk_mul
         | Command.Expression.Div -> div                        
       in
    fun_op ctx [(eval ctx e i); (eval ctx e' i)]

(* Check if two z3 variables are equal *)           
let z3_variable_equality ctx x y =
  (* to verify equality, we check if x and y can be different,
     if the formula is unsat, then it is the same variable *)
  let x_equals_y = Boolean.mk_eq ctx x y in
  let x_diff_y = Boolean.mk_not ctx x_equals_y in
  let solver = (Solver.mk_simple_solver ctx) in
  Solver.add solver [x_diff_y] ;
  let status = Solver.check solver [] in
  match status with
  | Solver.UNSATISFIABLE -> true
  | Solver.SATISFIABLE
  | Solver.UNKNOWN -> false




let apply_assign ctx a var i =
  let (v, exp) = a in
  let xi =  z3_var ctx var i
  and xi1 =  z3_var ctx var (i+1)
  and affected_xi = z3_var ctx v i
  in
  (* Check if the current variable is the affected variable *)
  let equality = z3_variable_equality ctx xi affected_xi in
  if equality then
    (
      match exp with
      (* constant is assigned to var *)
      | Command.Expression.Cst cst ->
         (* Create the integer numeral for the constant. *)
         let z3_cst  = Arithmetic.Integer.mk_numeral_i ctx cst in
         let formula = Boolean.mk_eq ctx xi1 z3_cst in
         formula
      (* another variable is assigned to var *)
      | Command.Expression.Var assigned_variable ->  
         (* create the variable in Z3 context y$i *)      
         let z3_assigned_variable =  z3_var ctx assigned_variable i in
         Boolean.mk_eq ctx xi1 z3_assigned_variable
      (* an expression is assigned to var *)
      | Command.Expression.Op (e, op, e') ->
          let z3_assigned_expression = eval ctx exp i in
          Boolean.mk_eq ctx xi1 z3_assigned_expression
    )
  (* If not we just want x$i = x$(i+1) *)
  else
    Boolean.mk_eq ctx xi  xi1

                  
let transform_var ctx i cmd var =
  (* Define two variables, x$i and x$(i+1) before and after the operation *)
  let xi =  z3_var ctx var i
  and xi1 = z3_var ctx var (i+1)
  in
  (* What sort is the cmd operation *)
  match cmd with
  | Command.Skip -> Boolean.mk_eq ctx xi  xi1   
  | Command.Guard p -> Boolean.mk_eq ctx xi  xi1 (* TODO *)
  | Command.Assign (v, e) -> apply_assign ctx (v, e) var i
                            
let formula ctx vars i cmd =
  (* Iterate through vars and get the corresponding boolean expression *)
  List.map
    (transform_var ctx  i cmd) vars
