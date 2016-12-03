(* $Id: BoundedModelChecking.ml $ *)


(**
 * Bounded Model-Checking.
 *
 * This module solves the bounded model-checking problem for program automata
 * (see {! Automaton}).  The implementation looks for a feasible path from the
 * initial location to the final location.  It proceeds through a depth-first
 * exploration of the program automaton (viewed as a graph).
 *)
open Z3
let visited_ht = Hashtbl.create 100;;
let path = ref [];;
let bad_path = ref [];;
let bound_reached = ref false;;
let depth = ref 0;;
  
type result =
  | Path of (Command.t * Automaton.Node.t) list
  | Empty of bool

let is_satisfiable solver =
  begin
    (* Check satisfiability of the solver's assertions. *)
    let status = Solver.check solver [] in
    match status with
    | Solver.UNSATISFIABLE ->
       false
    | Solver.SATISFIABLE ->
       true
    | Solver.UNKNOWN ->
       true
  end

let rec depth_first_search ctx solver automaton bound (cmd, current) =
  if (!bad_path <> []) then
    (
      ()
    )
  else if (!depth = bound) then
    (
      bound_reached := true;
      ()
    )
  else
    (
      let vars =  Automaton.variables automaton
      and children = Automaton.succ automaton current
      in
      depth := !depth + 1;
      (*Format.printf "Depth is %s\n" (string_of_int !depth);*)
      Solver.push solver;
      let f = Boolean.mk_and ctx (Semantics.formula ctx vars !depth cmd) in
      (*Format.printf "@[Formula f:@ %s@]@." (Expr.to_string f);*)
      Solver.add solver [f] ;
      (*
       TODO: if at a given location, the solver is equivalen to when the node was 
       previously visited, do not propagate the depth first search
       TEST: loop_never_sat.aut should retuen no feasible path
       let assertions = Solver.get_assertions solver in
       let visited = Hashtbl.find visited_ht current in
      
       Hashtbl.add visited_ht current assertions;
      
      
      Format.printf "@[Solver: %s@]@." (Solver.to_string solver);
      Format.printf "@[Current is: %a@]@." Automaton.Node.print current;
       *)
      path := List.append [(cmd, current)] !path;
      if (is_satisfiable solver = false) then
        (
          Solver.pop solver 1;
          depth := !depth - 1;
          path := List.tl !path;
          () 
        )
      else if (current = (Automaton.final automaton)) then
        (
          bad_path := !path;
          ()
        )
      else
        (
          List.iter
            ( depth_first_search ctx solver automaton bound ) children;
          Solver.pop solver 1;
          depth := !depth - 1;
          path := List.tl !path;
          ()
        )
    )

           

let search automaton bound =
  depth := -1;
  Hashtbl.reset visited_ht;
  bound_reached := false;
  let ctx = mk_context []
  in
  let init = Automaton.initial automaton
  and solver = (Solver.mk_simple_solver ctx) 
  in
  depth_first_search ctx solver automaton bound (Command.Skip, init);
  (* If bad_path is not empty we have found a valid path that leads to the bad state *) 
  if !bad_path <> [] then
    (
      (* Reverse order of the list and remove (init,skip) *)
      let ordered_bad_path = List.tl (List.rev !bad_path) in
      Path ordered_bad_path
    )
  (* Otherwise, if the bound has been reached,
     there is no feasable path of length <= bound *)
  else if !bound_reached then
    Empty false
          
  (* Otherwise the program is safe *)      
  else
    Empty true

                       
    
