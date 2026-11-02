import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16Wire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16DivisionBody
import Mettapedia.Languages.MeTTa.PeTTa.BridgeDemandTransport
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16NibbleCall

/-! The actual shared hexadecimal encoder follows exact division by
sixteen, producing the compiler's canonical little-endian digit list.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16DigitsExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

private theorem integerAgreement : ProgramAgreementOn
    (fun head => head == "gslt:integer:divmod") integerLibrary.runtime wordLibrary.runtime := by
  apply Library.agreement_on word_checked
  intro head supported
  have same : head = "gslt:integer:divmod" := beq_iff_eq.mp supported
  subst head
  decide +kernel

theorem digits_body_returns (state : State) (number : Nat) :
    PureReturns wordLibrary.runtime (Library.bind ["number"] [WireKit.number number]) state
      (wordLibrary.body "gslt:word16:digits") state (encoded (Word16Wire.digitsTerm number)) := by
  metta_literal
  apply pure_if_returns
  · exact natural_lt_returns _ _ state _ _ number 0 (bound_returns _ _ _ (by rfl)) (number_returns _ _ _ _)
  · simp only [Nat.not_lt_zero, decide_false]
    apply pure_if_returns
    · exact natural_equal_returns _ _ state _ _ number 0 (bound_returns _ _ _ (by rfl)) (number_returns _ _ _ _)
    · by_cases zero : number = 0
      · subst number
        simp only [decide_true, if_true, Word16Wire.zero_digits]
        exact symbol_returns _ _ _ _
      · simp only [zero, decide_false]
        have positive : 0 < number := by omega
        have tailBody := digits_body_returns state (number / 16)
        apply pure_case_returns _ _ state _ _ _ _ _ rfl
        · apply Library.demand_call_in integer_checked integerAgreement (head := "gslt:integer:divmod")
            (by decide +kernel) (by rfl) (by decide +kernel)
            _ state state state _ [WireKit.number number, WireKit.number 16] _ (by metta_literal; rfl)
          · exact ArgumentsReturn.evaluated (program := wordLibrary.runtime) (head := "gslt:integer:divmod") (index := 0)
              (by decide +kernel) (bound_returns _ _ _ (by rfl))
              (.evaluated (by decide +kernel) (number_returns _ _ _ _) (.nil _ _))
          · exact Word16DivisionBody.body_returns state number 16 (by decide)
        · simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,
            IntegerDivisionExecution.resultTerm, Library.bind, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
        · intro selected body found
          metta_select [IntegerDivisionExecution.resultTerm, Library.bind, encoded, CettaWireAtom.encode, WireKit.number] at found
          obtain ⟨bound, sourceBody⟩ := found
          subst selected
          subst body
          rw [Word16Wire.step_digits number positive]
          apply pure_let_star_returns _ _ _ _ _ _ _ rfl
          apply pure_let_returns _ _ _ "digit" _ (encoded (Word16NibbleExecution.nibble (number % 16))) _ _ (by rfl)
          · apply Word16NibbleCall.argument_returns _ state _ ⟨number % 16, Nat.mod_lt _ (by decide)⟩
            exact bound_returns _ _ _ (by rfl)
          · apply pure_let_returns _ _ _ "tail" _ (encoded (Word16Wire.digitsTerm (number / 16))) _ _ (by rfl)
            · apply Library.demand_call word_checked (head := "gslt:word16:digits") (by rfl) (by decide +kernel)
                _ state state state _ [WireKit.number (number / 16)] _ (by metta_literal; rfl)
              · exact ArgumentsReturn.evaluated (program := wordLibrary.runtime) (head := "gslt:word16:digits") (index := 0)
                  (by decide +kernel) (bound_returns _ _ _ (by rfl)) (.nil _ _)
              · exact tailBody
            · metta_eval with word_checked
termination_by number
decreasing_by exact Nat.div_lt_self positive (by decide)

theorem digits_returns (state : State) (number : Nat) :
    PureReturns wordLibrary.runtime [] state (apply "gslt:word16:digits" [WireKit.number number]) state
      (encoded (Word16Wire.digitsTerm number)) := by
  apply Library.demand_call word_checked (by rfl) (by decide +kernel) [] state state state
    [WireKit.number number] [WireKit.number number] _ (by metta_literal; rfl)
  · exact ArgumentsReturn.evaluated (program := wordLibrary.runtime) (head := "gslt:word16:digits") (index := 0)
      (by decide +kernel) (number_returns _ _ _ _) (.nil _ _)
  · exact digits_body_returns state number

#print axioms digits_body_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16DigitsExecution
