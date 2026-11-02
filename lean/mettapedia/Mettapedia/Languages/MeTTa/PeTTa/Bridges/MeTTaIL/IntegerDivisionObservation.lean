import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerDivisionWrapper

/-! Public division has an exact completed operational observation. The
independent target judgment cannot return another quotient/remainder or
alter store and I/O state for this computation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerDivisionObservation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource

theorem exact_observation (state : State) (number divisor : Nat) (positive : 0 < divisor)
    (after : State) (answers input output : List Atom) :
    Runs integerLibrary.runtime {state := state, control := (.evaluate []
      (apply "gslt:integer:divmod" [WireKit.number number, WireKit.number divisor]))}
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (IntegerDivisionExecution.resultTerm (number / divisor) (number % divisor))] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff integerLibrary.runtime [] state state _ _
    (IntegerDivisionWrapper.divmod_returns state number divisor positive) after answers input output

#print axioms exact_observation

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerDivisionObservation
