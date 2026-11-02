import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerDivisionExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerDivisionRecovery

/-! Recursive execution of the actual doubling division helper. The
quotient measure decreases at every recursive divisor doubling.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerDivisionRecursive

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

def callBindings (number divisor : Nat) := Library.bind ["number", "divisor"] [WireKit.number number, WireKit.number divisor]

theorem positive_body_returns (state : State) (number divisor : Nat) (positive : 0 < divisor) :
    PureReturns integerLibrary.runtime (callBindings number divisor) state
      (integerLibrary.body "gslt:integer:divmod-positive") state
      (encoded (IntegerDivisionExecution.resultTerm (number / divisor) (number % divisor))) := by
  metta_literal
  apply pure_if_returns
  · exact natural_lt_returns _ _ state _ _ number divisor
      (bound_returns _ _ _ (by rfl)) (bound_returns _ _ _ (by rfl))
  · by_cases small : number < divisor
    · simp only [small, decide_true, if_true, Nat.div_eq_of_lt small, Nat.mod_eq_of_lt small]
      metta_eval with integer_checked unfolding [IntegerDivisionExecution.resultTerm, callBindings, Library.bind]
    · simp only [small, decide_false]
      have bodyIH := positive_body_returns state number (divisor + divisor) (by omega)
      apply pure_case_returns _ _ state _ _ _ _ _ rfl
      · apply Library.demand_call integer_checked (head := "gslt:integer:divmod-positive") (by rfl) (by decide +kernel)
          (callBindings number divisor) state state state _ [WireKit.number number, WireKit.number (divisor + divisor)] _ (by metta_literal; rfl)
        · exact ArgumentsReturn.evaluated (program := integerLibrary.runtime) (caller := callBindings number divisor)
            (head := "gslt:integer:divmod-positive") (index := 0) (by decide +kernel)
            (bound_returns _ _ _ (by rfl))
            (.evaluated (by decide +kernel)
              (natural_add_returns _ _ state _ _ divisor divisor
                (bound_returns _ _ _ (by rfl)) (bound_returns _ _ _ (by rfl))) (.nil _ _))
        · exact bodyIH
      · simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, IntegerDivisionExecution.resultTerm, encoded,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, callBindings, Library.bind,
          Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom]
      · intro selected body found
        metta_select [IntegerDivisionExecution.resultTerm, CettaWireAtom.encode, encoded, WireKit.number, callBindings, Library.bind] at found
        obtain ⟨bindingsSame, bodySame⟩ := found
        subst selected
        subst body
        have recovered := IntegerDivisionRecovery.recovery_returns state number divisor
          (number / (divisor + divisor)) (number % (divisor + divisor))
        have same := Mettapedia.Data.Nat.DoublingDivision.quotient_recovery number divisor positive
        have resultSame : IntegerDivisionRecovery.result divisor (number / (divisor + divisor)) (number % (divisor + divisor)) =
            IntegerDivisionExecution.resultTerm (number / divisor) (number % divisor) := by
          unfold IntegerDivisionRecovery.result IntegerDivisionExecution.resultTerm
          split <;> simp_all
        rw [resultSame] at recovered
        simpa [IntegerDivisionRecovery.body, IntegerDivisionRecovery.bindings, callBindings, Library.bind,
          WireKit.number, encoded, CettaWireAtom.encode] using recovered
termination_by number / divisor
decreasing_by
  rw [show divisor + divisor = divisor * 2 by omega, ← Nat.div_div_eq_div_mul]
  exact Nat.div_lt_self (Nat.div_pos (by omega) positive) (by decide)

theorem positive_returns (state : State) (number divisor : Nat) (positive : 0 < divisor) :
    PureReturns integerLibrary.runtime [] state
      (apply "gslt:integer:divmod-positive" [WireKit.number number, WireKit.number divisor]) state
      (encoded (IntegerDivisionExecution.resultTerm (number / divisor) (number % divisor))) := by
  apply Library.demand_call integer_checked (by rfl) (by decide +kernel) [] state state state
    [WireKit.number number, WireKit.number divisor] [WireKit.number number, WireKit.number divisor] _ (by metta_literal; rfl)
  · exact ArgumentsReturn.evaluated (program := integerLibrary.runtime) (caller := [])
      (head := "gslt:integer:divmod-positive") (index := 0) (by decide +kernel)
      (number_returns _ [] state number)
      (.evaluated (by decide +kernel) (number_returns _ [] state divisor) (.nil _ _))
  · exact positive_body_returns state number divisor positive

#print axioms positive_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerDivisionRecursive
