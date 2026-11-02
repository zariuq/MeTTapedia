import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAllPrimitiveExecution

/-! The exhaustive dispatcher theorem admits a genuine result and refuses
invented values, wrapped-overflow mistakes and the wrong remainder policy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAllPrimitiveControls

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource

theorem zero_divisor_is_fault (state : State) :
    PureReturns runtime [] state
      (OCamlPrimitiveReflection.call .divide [.literal (.integer 7), .literal (.integer 0)]) state
      (encoded (OCamlArithmeticAdequacy.resultTerm (.error .divisionByZero))) :=
  OCamlAllPrimitiveExecution.returns state .divide _ _ rfl

theorem zero_divisor_cannot_be_value (state : State) (answer : OCaml.Value) :
    ¬ Runs runtime {state := state, control := (.evaluate []
      (OCamlPrimitiveReflection.call .divide [.literal (.integer 7), .literal (.integer 0)]))}
      (.complete state [encoded (OCamlArithmeticAdequacy.resultTerm (.ok answer))] [] []) := by
  intro observed
  have source := (OCamlAllPrimitiveExecution.result_iff state .divide _ (.error .divisionByZero) (.ok answer) rfl).mp observed
  cases source

theorem negative_remainder_is_not_euclidean (state : State) :
    ¬ Runs runtime {state := state, control := (.evaluate []
      (OCamlPrimitiveReflection.call .modulo [.literal (.integer (-7)), .literal (.integer 3)]))}
      (.complete state [encoded (OCamlArithmeticAdequacy.resultTerm (.ok (.literal (.integer 2))))] [] []) := by
  intro observed
  have source := (OCamlAllPrimitiveExecution.result_iff state .modulo _ (.ok (.literal (.integer (-1)))) _ rfl).mp observed
  cases source

#print axioms zero_divisor_is_fault
#print axioms zero_divisor_cannot_be_value
#print axioms negative_remainder_is_not_euclidean

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAllPrimitiveControls
