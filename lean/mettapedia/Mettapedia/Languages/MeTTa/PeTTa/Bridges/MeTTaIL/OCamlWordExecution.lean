import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16DigitsExecution

/-! The shared hexadecimal encoder keeps its exact body and numeric
argument demand under the complete loaded OCaml service library.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlWordExecution

open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

theorem digits_body_returns (state : State) (number : Nat) :
    PureReturns runtime (Library.bind ["number"] [WireKit.number number]) state
      (wordLibrary.body "gslt:word16:digits") state (encoded (Word16Wire.digitsTerm number)) :=
  Library.lift checked (by metta_literal; decide +kernel)
    (Word16DigitsExecution.digits_body_returns state number)

theorem digits_returns (state : State) (number : Nat) :
    PureReturns runtime [] state (apply "gslt:word16:digits" [WireKit.number number]) state
      (encoded (Word16Wire.digitsTerm number)) := by
  apply captured_call_in_extension (Library.closed checked) (Library.agreement checked)
    [] [("number", WireKit.number number)] state state "gslt:word16:digits"
    [WireKit.number number] ["number"] _ (by decide +kernel) (by decide) (by decide +kernel) (by decide)
  · intro index argument found
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst argument; exact Or.inr rfl
    | succ index => simp at found
  · simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]
  · exact Word16DigitsExecution.digits_returns state number

#print axioms digits_body_returns
#print axioms digits_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlWordExecution
