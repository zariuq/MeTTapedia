import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerWireExecution

/-! Signed integer and Boolean equality use the target's actual native
primitive and preserve the complete state observation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open SpaceSemantics (Program)
open Eval

theorem integer_equal_returns (program : Program) (caller : Subst) (state : State) (left right : Atom) (first second : Int)
    (one : PureReturns program caller state left state (integer first))
    (two : PureReturns program caller state right state (integer second)) :
    PureReturns program caller state (apply "==" [left, right]) state (Effects.boolean (decide (first = second))) := by
  apply native_binary_call_returns program caller state state state state "==" left right _ _ _
    (by decide) (by decide) (by rw [native_raw program "==" 0 (by decide)]; decide)
    (by rw [native_raw program "==" 1 (by decide)]; decide) one two _ (by decide)
  rw [StdLib.structural_equality]
  have same : (integer first == integer second) = decide (first = second) := by
    apply Bool.eq_iff_iff.mpr
    simp [integer]
  rw [same]

theorem boolean_equal_returns (program : Program) (caller : Subst) (state : State) (left right : Atom) (first second : Bool)
    (one : PureReturns program caller state left state (Effects.boolean first))
    (two : PureReturns program caller state right state (Effects.boolean second)) :
    PureReturns program caller state (apply "==" [left, right]) state (Effects.boolean (decide (first = second))) := by
  apply native_binary_call_returns program caller state state state state "==" left right _ _ _
    (by decide) (by decide) (by rw [native_raw program "==" 0 (by decide)]; decide)
    (by rw [native_raw program "==" 1 (by decide)]; decide) one two _ (by decide)
  cases first <;> cases second <;> rfl

#print axioms integer_equal_returns
#print axioms boolean_equal_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit
