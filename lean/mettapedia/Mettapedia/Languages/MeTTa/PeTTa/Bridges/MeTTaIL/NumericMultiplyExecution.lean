import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.NumericWireExecution

/-! Exact natural multiplication through the target's integer primitive,
used by hexadecimal word decoding and arithmetic service proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open SpaceSemantics (Program)
open Eval

theorem natural_mul_returns (program : Program) (caller : Subst) (state : State) (left right : Atom) (first second : Nat)
    (leftReturns : PureReturns program caller state left state (number first))
    (rightReturns : PureReturns program caller state right state (number second)) :
    PureReturns program caller state (apply "*" [left, right]) state (number (first * second)) := by
  apply native_binary_call_returns program caller state state state state "*" left right _ _ _
    (by decide) (by decide) (by rw [native_raw program "*" 0 (by decide)]; decide)
    (by rw [native_raw program "*" 1 (by decide)]; decide) leftReturns rightReturns _ (by decide)
  change Except.ok (state, [Atom.grounded (.int ((first : Int) * second))]) = _
  rw [← Int.natCast_mul]
  rfl

#print axioms natural_mul_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit
