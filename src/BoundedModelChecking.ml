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
(* let path_ht = Hashtbl.create 10;;*)
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
  if (Hashtbl.mem visited_ht current) then
    (
      ()
    )
  else
    (
      Hashtbl.add visited_ht current 1;
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
          if (current <> (Automaton.initial automaton)) then
            (
              depth := !depth + 1;
              Solver.push solver;
              let f = Boolean.mk_and ctx (Semantics.formula ctx vars !depth cmd) in
              Solver.add solver [f] ;
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
                  (*let next_bound = bound + 1 in*)
                  List.iter
                    ( depth_first_search ctx solver automaton bound ) children;
                  Solver.pop solver 1;
                  depth := !depth - 1;
                  ()
                )
            )
          else
            (
              (*let next_bound = bound + 1 in*)
              depth := !depth + 1;
              List.iter
                (depth_first_search ctx solver automaton bound ) children;
              depth := !depth - 1;
              ()
            )
        )
    )


let search automaton bound =
  depth := 0;
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
      let ordered_bad_path = List.rev !bad_path in
      Path ordered_bad_path
    )
  (* Otherwise, if the bound has been reached,
     there is no feasable path of length <= bound *)
  else if !bound_reached then
    Empty false
          
  (* Otherwise the program is safe *)      
  else
    Empty true

                       
    
