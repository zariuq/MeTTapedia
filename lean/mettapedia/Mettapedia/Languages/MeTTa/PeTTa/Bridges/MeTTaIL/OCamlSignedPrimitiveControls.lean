import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionAdequacy
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlUnaryAdequacy

/-! Completed observations separate ordinary division faults from values,
truncating remainder from Euclidean remainder, and wrapped minimum-integer
negation from a positive unwrapped result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSignedPrimitiveControls

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource

theorem zero_divisor_fault (state : State) (modulo : Bool) (left : Int) :
    Runs runtime {state := state, control := (.evaluate []
      (OCamlPrimitiveReflection.call (OCamlDivisionSource.source modulo) [.literal (.integer left), .literal (.integer 0)]))}
      (.complete state [encoded (OCamlArithmeticAdequacy.resultTerm (.error .divisionByZero))] [] []) := by
  apply (OCamlDivisionAdequacy.division_iff state modulo left 0 _).mpr
  rw [OCamlDivisionSource.source_evaluates]
  rfl

theorem zero_divisor_value_refused (state : State) (modulo : Bool) (left answer : Int) :
    ¬ Runs runtime {state := state, control := (.evaluate []
      (OCamlPrimitiveReflection.call (OCamlDivisionSource.source modulo) [.literal (.integer left), .literal (.integer 0)]))}
      (.complete state [encoded (OCamlArithmeticAdequacy.resultTerm (.ok (.literal (.integer answer))))] [] []) := by
  intro completed
  have same := (OCamlDivisionAdequacy.division_iff state modulo left 0 _).mp completed
  rw [OCamlDivisionSource.source_evaluates] at same
  cases same

theorem euclidean_remainder_refused (state : State) :
    ¬ Runs runtime {state := state, control := (.evaluate []
      (OCamlPrimitiveReflection.call .modulo [.literal (.integer (-7)), .literal (.integer 3)]))}
      (.complete state [encoded (OCamlArithmeticAdequacy.resultTerm (.ok (.literal (.integer 2))))] [] []) := by
  intro completed
  have same := (OCamlDivisionAdequacy.division_iff state true (-7) 3 _).mp completed
  change Except.ok (Except.ok (OCaml.Value.literal (.integer (-1)))) =
    Except.ok (Except.ok (.literal (.integer 2))) at same
  cases same

theorem minimum_negation_positive_refused (state : State) :
    ¬ Runs runtime {state := state, control := (.evaluate []
      (OCamlPrimitiveReflection.call .negate [.literal (.integer (-4611686018427387904))]))}
      (.complete state [encoded (OCamlArithmeticAdequacy.resultTerm (.ok (.literal (.integer 4611686018427387904))))] [] []) := by
  intro completed
  have same := (OCamlUnaryAdequacy.negate_iff state (-4611686018427387904) _).mp completed
  change Except.ok (Except.ok (OCaml.Value.literal (.integer (-4611686018427387904)))) =
    Except.ok (Except.ok (.literal (.integer 4611686018427387904))) at same
  cases same

#print axioms zero_divisor_fault
#print axioms zero_divisor_value_refused
#print axioms euclidean_remainder_refused
#print axioms minimum_negation_positive_refused

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSignedPrimitiveControls
