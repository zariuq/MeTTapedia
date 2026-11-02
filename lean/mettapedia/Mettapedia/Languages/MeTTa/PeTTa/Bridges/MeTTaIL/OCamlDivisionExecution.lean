import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16DivisionExecution

/-! The exact shared integer division helper runs under the full loaded
OCaml library, with its numeric arguments still evaluated.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionExecution

open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

theorem divmod_returns (state : State) (number divisor : Nat) (positive : 0 < divisor) :
    PureReturns runtime [] state (apply "gslt:integer:divmod" [WireKit.number number, WireKit.number divisor]) state
      (encoded (IntegerDivisionExecution.resultTerm (number / divisor) (number % divisor))) := by
  apply captured_call_in_extension (Library.closed checked) (Library.agreement checked)
    [] [("number", WireKit.number number), ("divisor", WireKit.number divisor)] state state
    "gslt:integer:divmod" [WireKit.number number, WireKit.number divisor] ["number", "divisor"] _
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
  · intro offset argument found
    rcases offset with _ | offset
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst argument
      exact Or.inr rfl
    · rcases offset with _ | offset
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
        subst argument
        exact Or.inr rfl
      · simp at found
  · simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]
  · exact Word16DivisionExecution.divmod_returns state number divisor positive

#print axioms divmod_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionExecution
