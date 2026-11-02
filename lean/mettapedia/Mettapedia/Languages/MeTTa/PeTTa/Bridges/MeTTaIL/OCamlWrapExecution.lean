import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlWrapRecovery
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionBody
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerAgreement

/-! The loaded signed wrapping source uses exact magnitude division and
agrees with the independent OCaml integer profile at every integer.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlWrapExecution

open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

theorem wrap_body_returns (state : State) (number : Int) :
    PureReturns runtime (Library.bind ["number"] [integer number]) state
      (library.body "gslt:ml:wrap") state (integer (OCaml.wrapInteger number)) := by
  metta_literal
  apply pure_let_star_returns _ _ _ _ _ _ _ rfl
  apply pure_let_returns _ _ _ "negative" _ (Effects.boolean (decide (number < 0))) _ _ (by rfl)
  · exact integer_lt_returns _ _ state _ _ number 0 (bound_returns _ _ _ (by rfl)) (integer_returns _ _ _ _)
  · apply pure_let_returns _ _ _ "magnitude" _ (WireKit.number number.natAbs) _ _ (by rfl)
    · apply pure_if_returns
      · exact bound_returns _ _ _ (by rfl)
      · by_cases negative : number < 0
        · simp only [negative, decide_true, if_true]
          have computed := integer_sub_returns runtime
            (("negative", Effects.boolean true) :: Library.bind ["number"] [integer number]) state
            (integer 0) (.var "number") 0 number (integer_returns _ _ _ _) (bound_returns _ _ _ (by rfl))
          simpa [zero_sub, Int.natCast_natAbs, abs_of_neg negative, WireKit.number, encoded, CettaWireAtom.encode, integer] using computed
        · simp only [negative, decide_false]
          have same : (number.natAbs : Int) = number := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
          simpa [WireKit.number, encoded, CettaWireAtom.encode, same, integer] using
            (bound_returns runtime _ state (name := "number") (value := integer number) (by rfl))
    · apply pure_case_returns _ _ state _ _ _ _ _ rfl
      · apply Library.demand_call_in integer_checked OCamlIntegerAgreement.agreement
          (head := "gslt:integer:divmod") (by decide +kernel) (by rfl) (by decide +kernel)
          _ state state state _ [WireKit.number number.natAbs, WireKit.number OCaml.integerModulus.toNat] _ (by metta_literal; rfl)
        · exact ArgumentsReturn.evaluated (program := runtime) (head := "gslt:integer:divmod") (index := 0)
            (by decide +kernel) (bound_returns _ _ _ (by rfl))
            (.evaluated (by decide +kernel) (number_returns _ _ _ _) (.nil _ _))
        · exact OCamlDivisionBody.body_returns state number.natAbs OCaml.integerModulus.toNat (by decide)
      · simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,
          IntegerDivisionExecution.resultTerm, Library.bind, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
      · intro selected body found
        metta_select [IntegerDivisionExecution.resultTerm, Library.bind, encoded, CettaWireAtom.encode, WireKit.number] at found
        obtain ⟨bindingsSame, bodySame⟩ := found
        subst selected
        subst body
        have recovered := OCamlWrapRecovery.recovery_returns state (decide (number < 0)) number.natAbs
          (number.natAbs / OCaml.integerModulus.toNat) (number.natAbs % OCaml.integerModulus.toNat) number
        have same : OCamlWrapRecovery.wrapped (decide (number < 0)) (number.natAbs % OCaml.integerModulus.toNat) =
            OCaml.wrapInteger number := by
          rw [← OCaml.magnitudeWrap_eq_wrapInteger]
          simp only [OCamlWrapRecovery.wrapped, OCamlWrapRecovery.unsigned, OCaml.magnitudeWrap, decide_eq_true_eq]
        rw [same] at recovered
        simpa [OCamlWrapRecovery.body, OCamlWrapRecovery.bindings, Library.bind, WireKit.number, encoded, CettaWireAtom.encode,
          integer, OCaml.integerModulus, OCaml.integerHalf] using recovered

theorem wrap_returns (state : State) (number : Int) :
    PureReturns runtime [] state (apply "gslt:ml:wrap" [integer number]) state (integer (OCaml.wrapInteger number)) := by
  apply Library.demand_call checked (by rfl) (by decide +kernel) [] state state state [integer number] [integer number] _
    (by metta_literal; rfl)
  · exact ArgumentsReturn.evaluated (program := runtime) (caller := []) (head := "gslt:ml:wrap") (index := 0)
      (by decide +kernel) (integer_returns _ _ _ _) (.nil _ _)
  · exact wrap_body_returns state number

#print axioms wrap_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlWrapExecution
