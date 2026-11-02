import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16DivisionBody

/-! The public division body's checked computation remains valid under
the loaded OCaml service, without changing its numeric parameter policy.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionBody

open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

theorem body_returns (state : State) (number divisor : Nat) (positive : 0 < divisor) :
    PureReturns runtime (Library.bind ["number", "divisor"] [WireKit.number number, WireKit.number divisor]) state
      (integerLibrary.body "gslt:integer:divmod") state
      (encoded (IntegerDivisionExecution.resultTerm (number / divisor) (number % divisor))) :=
  Library.lift checked (by metta_literal; decide +kernel)
    (Word16DivisionBody.body_returns state number divisor positive)

#print axioms body_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionBody
