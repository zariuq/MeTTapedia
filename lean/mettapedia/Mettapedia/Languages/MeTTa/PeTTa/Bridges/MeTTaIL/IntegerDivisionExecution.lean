import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerSource
import Mettapedia.Languages.MeTTa.PeTTa.BridgeDemandLibrary
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.NumericWireExecution
import Mettapedia.Data.Nat.DoublingDivision

/-! The actual shared nonnegative integer division helper executes its
doubling/subtraction algorithm. Integer-domain refusals remain distinct
from valid quotient/remainder results.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerDivisionExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

def resultTerm (quotient remainder : Nat) : Term := .application "IntegerDivmod" [.natural quotient, .natural remainder]

theorem positive_small_returns (state : State) (number divisor : Nat) (small : number < divisor) :
    PureReturns integerLibrary.runtime [] state
      (apply "gslt:integer:divmod-positive" [WireKit.number number, WireKit.number divisor]) state
      (encoded (resultTerm 0 number)) := by
  apply Library.demand_call integer_checked (by rfl) (by decide +kernel) [] state state state
    [WireKit.number number, WireKit.number divisor] [WireKit.number number, WireKit.number divisor] _
    (by metta_literal; rfl)
  · exact ArgumentsReturn.evaluated (program := integerLibrary.runtime) (caller := [])
      (head := "gslt:integer:divmod-positive") (index := 0) (by decide +kernel)
      (number_returns _ [] state number)
      (.evaluated (by decide +kernel) (number_returns _ [] state divisor) (.nil _ _))
  · metta_literal
    apply pure_if_returns
    · exact natural_lt_returns integerLibrary.runtime _ state _ _ number divisor
        (bound_returns _ _ _ (by rfl)) (bound_returns _ _ _ (by rfl))
    · simp only [small, decide_true, if_true]
      metta_eval with integer_checked unfolding [resultTerm, Library.bind]

#print axioms positive_small_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerDivisionExecution
