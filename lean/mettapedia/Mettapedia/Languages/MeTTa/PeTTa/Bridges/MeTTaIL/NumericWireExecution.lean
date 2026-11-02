import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit

/-! Integer target primitives and nonnegative subtraction at the physical
number boundary. No floating conversion is used.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics (Program)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval

theorem natural_sub_returns (program : Program) (caller : Subst) (state : State) (left right : Atom) (first second : Nat)
    (bounded : second ≤ first)
    (leftReturns : PureReturns program caller state left state (number first))
    (rightReturns : PureReturns program caller state right state (number second)) :
    PureReturns program caller state (apply "-" [left, right]) state (number (first - second)) := by
  apply native_binary_call_returns program caller state state state state "-" left right _ _ _
    (by decide) (by decide) (by rw [native_raw program "-" 0 (by decide)]; decide)
    (by rw [native_raw program "-" 1 (by decide)]; decide) leftReturns rightReturns _ (by decide)
  change Except.ok (state, [Atom.grounded (.int ((first : Int) - second))]) = _
  rw [← Int.ofNat_sub bounded]
  rfl

theorem natural_gt_returns (program : Program) (caller : Subst) (state : State) (left right : Atom) (first second : Nat)
    (leftReturns : PureReturns program caller state left state (number first))
    (rightReturns : PureReturns program caller state right state (number second)) :
    PureReturns program caller state (apply ">" [left, right]) state (Effects.boolean (decide (second < first))) := by
  apply native_binary_call_returns program caller state state state state ">" left right _ _ _
    (by decide) (by decide) (by rw [native_raw program ">" 0 (by decide)]; decide)
    (by rw [native_raw program ">" 1 (by decide)]; decide) leftReturns rightReturns _ (by decide)
  change Except.ok (state, [Effects.boolean (decide ((second : Int) < first))]) = _
  simp only [Int.ofNat_lt]

#print axioms natural_sub_returns
#print axioms natural_gt_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit
