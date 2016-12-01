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
    ()
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
      if (current <> (Automaton.initial automaton)) then
        (
          depth := !depth + 1;
          Solver.push solver;
          let f = Boolean.mk_and ctx (Semantics.formula ctx vars bound cmd) in
          Solver.add solver [f] ;
          path := List.append [(cmd, current)] !path;
          if (is_satisfiable solver = false) then
            (
              Solver.pop solver 1;
              path := List.tl !path; (* Bug here *)
              ()
            )
          else if (current = (Automaton.final automaton)) then
            (
              bad_path := !path;
              ()
            )
          else
            let next_bound = bound + 1 in
            List.iter
              (depth_first_search ctx solver automaton next_bound ) children;
            Solver.pop solver 1;
            ()
        )
      else
        (
          let next_bound = bound + 1 in
          List.iter
            (depth_first_search ctx solver automaton next_bound ) children;
          Solver.pop solver 1;
          ()
        )
    )
    


let search automaton bound =
  Format.printf "Beginning of search";
  depth := 0;
  let ctx = mk_context []
  in
  let init = Automaton.initial automaton
  and solver = (Solver.mk_simple_solver ctx) 
  in
  depth_first_search ctx solver automaton bound (Command.Skip, init);
  if !bad_path <> [] then
    Path !bad_path
  else if !bound_reached then
    Empty true
  else
    Empty false

                       
    
