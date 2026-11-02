import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlOrderExecution

/-! Evaluated numeric calls reuse the loaded ordering body. In particular,
unbounded constructor ordinals use the same exact integer implementation.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlOrderCall

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlOrderExecution

theorem returns (state : State) (caller : Subst) (left right : Atom) (first second : Int)
    (one : PureReturns runtime caller state left state (integer first))
    (two : PureReturns runtime caller state right state (integer second)) :
    PureReturns runtime caller state (apply "gslt:ml:order" [left, right]) state
      (encoded (ordering (integerOrder first second))) := by
  apply Library.demand_call checked (head := "gslt:ml:order") (by rfl) (by decide +kernel)
    caller state state state [left, right] [integer first, integer second] _ (by metta_literal; rfl)
  · exact ArgumentsReturn.evaluated (program := runtime) (head := "gslt:ml:order") (index := 0)
      (by decide +kernel) one (.evaluated (by decide +kernel) two (.nil _ _))
  · exact order_body_returns state first second

theorem natural_order (first second : Nat) : integerOrder first second =
    (if first < second then Ordering.lt else if first = second then .eq else .gt) := by
  simp only [integerOrder, Int.ofNat_lt, Int.natCast_inj]

theorem natural_returns (state : State) (caller : Subst) (left right : Atom) (first second : Nat)
    (one : PureReturns runtime caller state left state (number first))
    (two : PureReturns runtime caller state right state (number second)) :
    PureReturns runtime caller state (apply "gslt:ml:order" [left, right]) state
      (encoded (ordering (if first < second then .lt else if first = second then .eq else .gt))) := by
  simpa only [natural_order] using returns state caller left right first second one two

#print axioms returns
#print axioms natural_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlOrderCall
