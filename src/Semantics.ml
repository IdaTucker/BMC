(* $Id: Semantics.ml $ *)

(*
 * Semantics of program commands.
 *)

open Z3

let ht = Hashtbl.create 100;;

let z3_var ctx var i =
  Arithmetic.Integer.mk_const_s ctx (var ^ "$" ^ (string_of_int i))

let add_unchanged ctx xi f =
  let key = (Expr.to_string xi) in
  Hashtbl.add ht key f

let add_guard ctx f =
  let key = "guard" in
  Hashtbl.add ht key f 

let add_assigned ctx xi f =
  let key = (Expr.to_string xi) in
  Hashtbl.replace ht key f

let add_non_zero ctx xi f =
  let key = (Expr.to_string xi) ^ "non-zero" in
  Hashtbl.add ht key f

let apply_skip ctx i var =
(* Define two variables, x$i and x$(i+1) before and after the operation *)
  let xi =  z3_var ctx var i
  and xi1 = z3_var ctx var (i+1)
  in
  let f = Boolean.mk_eq ctx xi  xi1 in
  add_unchanged ctx xi f; ()

let div ctx expr_list =
  let a = List.nth expr_list 0
  and b = List.nth expr_list 1
  in
  let division = Arithmetic.mk_div ctx a b
  and zero = Arithmetic.Integer.mk_numeral_i ctx 0                  
  in
  let eq_zero = Boolean.mk_eq ctx b zero in
  let non_zero = Boolean.mk_not ctx eq_zero in
  
  (*arithmetic_constraints := List.append !arithmetic_constraints [non_zero];
  Format.printf "Arithmetic constraints is \n";
  List.iter print !arithmetic_constraints;*)
  add_non_zero ctx b non_zero;
  division

(* Evaluation of an expression.*)
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

let apply_guard ctx p i vars =
   let (expr, op, expr') = p in
   let z3_expr =  eval ctx expr i
   and z3_expr' = eval ctx expr' i
   in
   let z3_guard_formula =
     match op with
     | Command.Predicate.Eq  -> Boolean.mk_eq ctx  z3_expr z3_expr'
     | Command.Predicate.Lst -> Arithmetic.mk_lt ctx z3_expr z3_expr'
     | Command.Predicate.Gst -> Arithmetic.mk_gt ctx z3_expr z3_expr'
     | Command.Predicate.Leq -> Arithmetic.mk_le ctx z3_expr z3_expr'
     | Command.Predicate.Geq -> Arithmetic.mk_ge ctx z3_expr z3_expr'
   in
   add_guard ctx z3_guard_formula;
   (* Iterate through vars and add unchanged formula for each variable *)    
   List.map (apply_skip ctx  i ) vars;
   ()
     
let apply_assign ctx a i vars =
  let (v, exp) = a in
  let affected_xi = z3_var ctx v i
  and affected_xi1 = z3_var ctx v (i+1)
  in
  (* Iterate through vars and add unchanged formula for each variable *)    
  List.map (apply_skip ctx  i ) vars;
  (* Replace the binding of the affected variable *)
  let z3_assign_formula =
    match exp with
    (* constant is assigned to var *)
    | Command.Expression.Cst cst ->
       (* Create the integer numeral for the constant. *)
       let z3_cst  = Arithmetic.Integer.mk_numeral_i ctx cst in
       Boolean.mk_eq ctx affected_xi1 z3_cst
    (* another variable is assigned to var *)
    | Command.Expression.Var assigned_variable ->  
       (* create the variable in Z3 context y$i *)      
       let z3_assigned_variable =  z3_var ctx assigned_variable i in
       Boolean.mk_eq ctx affected_xi1 z3_assigned_variable
    (* an expression is assigned to var *)
    | Command.Expression.Op (e, op, e') ->
       let z3_assigned_expression = eval ctx exp i in
       Boolean.mk_eq ctx affected_xi1 z3_assigned_expression
  in
  add_assigned ctx affected_xi z3_assign_formula;
  ()
  
let formula ctx vars i cmd =
  (* reset arithmetic constraints to empty list *)
  Hashtbl.reset ht;

  (* What sort is the cmd operation *)
  match cmd with
  | Command.Skip ->
     (* Iterate through vars and add unchanged formula for each variable*)
     List.map (apply_skip ctx  i ) vars;
     Hashtbl.fold (fun _ v acc -> v :: acc) ht []
  | Command.Guard p ->
     apply_guard ctx p i vars;
     Hashtbl.fold (fun _ v acc -> v :: acc) ht []
  | Command.Assign (v, e) ->
     apply_assign ctx (v,e) i vars;
     Hashtbl.fold (fun _ v acc -> v :: acc) ht []

