import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlWrapExecution

/-! Signed wrapping has an exact completed operational observation in the
loaded OCaml runtime, including its store and I/O frame.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlWrapObservation

open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource

theorem exact_observation (state : State) (number : Int)
    (after : State) (answers input output : List Atom) :
    Runs runtime {state := state, control := .evaluate [] (apply "gslt:ml:wrap" [integer number])}
      (.complete after answers input output) ↔
      after = state ∧ answers = [integer (OCaml.wrapInteger number)] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff runtime [] state state _ _
    (OCamlWrapExecution.wrap_returns state number) after answers input output

theorem wrong_answer_refused (state : State) (number other : Int) (different : other ≠ OCaml.wrapInteger number) :
    ¬ Runs runtime {state := state, control := .evaluate [] (apply "gslt:ml:wrap" [integer number])}
      (.complete state [integer other] [] []) := by
  intro completed
  have same := ((exact_observation state number state [integer other] [] []).mp completed).2.1
  have integerSame : other = OCaml.wrapInteger number := by simpa [integer] using same
  exact different integerSame

example (state : State) :
    ¬ Runs runtime {state := state, control := .evaluate [] (apply "gslt:ml:wrap" [integer (2 ^ 62)])}
      (.complete state [integer (2 ^ 62)] [] []) := by
  apply wrong_answer_refused
  decide +kernel

#print axioms exact_observation
#print axioms wrong_answer_refused

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlWrapObservation
