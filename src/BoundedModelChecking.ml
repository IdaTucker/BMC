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
(*
 * Create a Z3 context.  We only need to create it once and then pass it to the
 * Z3 functions.
 *)

let search automaton bound =
  let ctx = mk_context []
  and vars = Automaton.variables automaton
  in
  let formulas = Semantics.formula ctx vars bound cmd
   [Automaton.initial automaton ; automaton.initial]

end



