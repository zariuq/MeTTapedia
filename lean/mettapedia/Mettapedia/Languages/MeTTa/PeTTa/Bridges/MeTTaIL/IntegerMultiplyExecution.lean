import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerWireExecution

/-! Signed multiplication uses the target's exact native integer
operation, independently of the OCaml wrapping policy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open SpaceSemantics (Program)
open Eval

theorem integer_mul_returns (program : Program) (caller : Subst) (state : State) (left right : Atom) (first second : Int)
    (one : PureReturns program caller state left state (integer first))
    (two : PureReturns program caller state right state (integer second)) :
    PureReturns program caller state (apply "*" [left, right]) state (integer (first * second)) := by
  exact native_binary_call_returns program caller state state state state "*" left right _ _ _
    (by decide) (by decide) (by rw [native_raw program "*" 0 (by decide)]; decide)
    (by rw [native_raw program "*" 1 (by decide)]; decide) one two rfl (by decide)

#print axioms integer_mul_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit
