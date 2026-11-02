import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdvanceCall

/-! Completed, blocked and invalid controller values retain their entire
state under every remaining advance budget. Running is a distinct branch.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdvanceStopped

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlInstallExecution

theorem returns (state : State) (phase : String) (plan standard runner epochs : Term) (ticks quantum : Nat)
    (stopped : phase = "MlComplete" ∨ phase = "MlBlocked" ∨ phase = "MlInvalid") :
    PureReturns runtime [] state
      (apply "gslt:ml:advance" [number ticks, number quantum, encoded (machine phase plan standard runner epochs)]) state
      (encoded (machine phase plan standard runner epochs)) := by
  cases ticks with
  | zero => exact OCamlAdvanceCall.zero_returns state quantum _
  | succ ticks =>
    apply OCamlAdvanceCall.returns
    metta_literal
    apply pure_if_returns
    · exact natural_equal_returns _ _ _ _ _ (ticks + 1) 0 (bound_returns _ _ _ (by rfl)) (number_returns _ _ _ _)
    · simp only [Nat.add_one_ne_zero, decide_false, Bool.false_eq_true, if_false]
      rcases stopped with rfl | rfl | rfl <;> metta_eval with checked unfolding [machine]

#print axioms returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdvanceStopped
