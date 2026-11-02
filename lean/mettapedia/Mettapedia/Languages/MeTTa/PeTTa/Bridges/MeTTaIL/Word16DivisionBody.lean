import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerDivisionBody

/-! The selected division body contains no word-helper calls, so its
exact computation transports under the loaded word library unchanged.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16DivisionBody

open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

theorem body_returns (state : State) (number divisor : Nat) (positive : 0 < divisor) :
    PureReturns wordLibrary.runtime (Library.bind ["number", "divisor"] [WireKit.number number, WireKit.number divisor]) state
      (integerLibrary.body "gslt:integer:divmod") state
      (encoded (IntegerDivisionExecution.resultTerm (number / divisor) (number % divisor))) := by
  exact Library.lift word_checked (by metta_literal; decide +kernel)
    (IntegerDivisionBody.body_returns state number divisor positive)

#print axioms body_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16DivisionBody
