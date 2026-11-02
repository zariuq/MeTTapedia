import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerWireExecution
import Mathlib.Algebra.Order.Group.Unbundled.Int

/-! Signed magnitude conversion executes through exact target integer
subtraction. Its flag is read from the caller's actual binding context.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open SpaceSemantics (Program)
open Eval BridgeKit

theorem magnitude_returns (program : Program) (caller : Subst) (state : State) (name flag : String) (value : Int)
    (readValue : caller.lookup name = some (integer value))
    (readFlag : caller.lookup flag = some (Effects.boolean (decide (value < 0)))) :
    PureReturns program caller state
      (.expression [.symbol "if", .var flag, apply "-" [integer 0, .var name], .var name]) state
      (number value.natAbs) := by
  apply pure_if_returns
  · exact bound_returns _ _ _ readFlag
  · by_cases negative : value < 0
    · simp only [negative, decide_true, if_true]
      have equal : (value.natAbs : Int) = -value := by rw [Int.natCast_natAbs, abs_of_neg negative]
      change PureReturns program caller state _ state (integer (value.natAbs : Int))
      rw [equal, show -value = 0 - value by omega]
      exact integer_sub_returns program caller state _ _ 0 value
        (integer_returns _ _ _ _) (bound_returns _ _ _ readValue)
    · simp only [negative, decide_false]
      have equal : (value.natAbs : Int) = value := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
      change PureReturns program caller state _ state (integer (value.natAbs : Int))
      rw [equal]
      exact bound_returns _ _ _ readValue

#print axioms magnitude_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit
