import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProgramCompilation
import Mettapedia.Languages.OCaml.Machine

/-! The indexed compiler's source-machine state boundary. Pattern and clause
references must resolve in the prepared pool. Values, environments and code
references reuse the compiler's existing representation.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def build (kind : OCaml.Build) : Pattern := match kind with
  | .tuple => node "MlBuildTuple"
  | .variant typeId constructor => node "MlBuildVariant" [tag typeId constructor]
  | .primitive operator => node "MlBuildPrimitive" [primitive operator]

def fault (error : OCaml.Fault) : Pattern := match error with
  | .divisionByZero => node "MlDivisionByZero"
  | .matchFailure => node "MlMatchFailure"
  | .functionalComparison => node "MlFunctionalComparison"

def frame? (pool : List OCaml.MatchPattern) (frame : OCaml.Frame) (rest : Pattern) : Option Pattern := do
  match frame with
  | .argument function captured => pure (node "MlKArgument" [code function, environment captured, rest])
  | .function argument => pure (node "MlKFunction" [value argument, rest])
  | .letValue pattern body captured =>
      pure (node "MlKLet" [← patternReference? pool pattern, code body, environment captured, rest])
  | .branch yes no captured => pure (node "MlKBranch" [code yes, code no, environment captured, rest])
  | .andThen right captured => pure (node "MlKAnd" [code right, environment captured, rest])
  | .orElse right captured => pure (node "MlKOr" [code right, environment captured, rest])
  | .booleanResult => pure (node "MlKBoolean" [rest])
  | .consTail head captured => pure (node "MlKConsTail" [code head, environment captured, rest])
  | .consHead tail => pure (node "MlKConsHead" [value tail, rest])
  | .gather kind reversed captured suffix =>
      pure (node "MlKBuild" [build kind, codes (reversed.map code), environment captured, valueList suffix, rest])
  | .matchValue clauses captured =>
      pure (node "MlKMatch" [← clauseList? pool clauses, environment captured, rest])

def continuation? (pool : List OCaml.MatchPattern) : OCaml.Continuation → Option Pattern
  | [] => some (node "MlKDone")
  | frame :: rest => do frame? pool frame (← continuation? pool rest)

def state? (pool : List OCaml.MatchPattern) : OCaml.MachineState → Option Pattern
  | .evaluate reference captured continuation => do
      pure (node "MlEvaluate" [code reference, environment captured, ← continuation? pool continuation])
  | .returned result continuation => do
      pure (node "MlReturn" [value result, ← continuation? pool continuation])
  | .halted (.ok result) => pure (node "MlDone" [value result])
  | .halted (.error error) => pure (node "MlFault" [fault error])

theorem initial_state (program : OCaml.Program) (pool : List OCaml.MatchPattern) :
    state? pool (OCaml.begin program) = some (initial program) := by
  simp only [state?, OCaml.begin, continuation?, environment, initial]
  rfl

theorem environment_append (first second : List OCaml.Value) :
    environment (first ++ second) = first.foldr (fun head tail => node "MlEnvironmentCons" [value head, tail])
      (environment second) := by
  induction first with
  | nil => rfl
  | cons first rest ih => simp only [List.cons_append, environment, List.foldr_cons, ih]

theorem environment_extend (captured bindings : List OCaml.Value) :
    environment (OCaml.extend captured bindings) = extend (bindings.map value) (environment captured) := by
  rw [OCaml.extend, environment_append]
  simp only [extend, List.foldl_map, List.foldr_reverse]

theorem recursive_environment (group : Nat) (definitions : List OCaml.Code) (captured : OCaml.Environment) :
    environment (OCaml.recursiveEnvironment group definitions captured) =
      recursiveEnvironment group definitions (environment captured) := by
  rw [OCaml.recursiveEnvironment, environment_extend]
  simp only [OCaml.recursiveBindings, List.map_map, Function.comp_def, value, recursiveEnvironment]

example : continuation? [] [.letValue .bind 0 []] = none := by decide_cbv
example : continuation? [.bind] [.letValue .bind 0 []] ≠ none := by
  decide_cbv

#print axioms initial_state
#print axioms environment_extend
#print axioms recursive_environment

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
