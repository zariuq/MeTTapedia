import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.NumericWireExecution

/-! Exact signed integer target operations. These are the target's actual
native primitives, independently of the OCaml word and wrapping policies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open SpaceSemantics (Program)
open Eval

def integer (value : Int) : Atom := .grounded (.int value)

theorem integer_returns (program : Program) (caller : Subst) (state : State) (value : Int) :
    PureReturns program caller state (integer value) state (integer value) := grounded_returns program caller state (.int value)

theorem integer_lt_returns (program : Program) (caller : Subst) (state : State) (left right : Atom) (first second : Int)
    (one : PureReturns program caller state left state (integer first))
    (two : PureReturns program caller state right state (integer second)) :
    PureReturns program caller state (apply "<" [left, right]) state (Effects.boolean (decide (first < second))) := by
  exact native_binary_call_returns program caller state state state state "<" left right _ _ _
    (by decide) (by decide) (by rw [native_raw program "<" 0 (by decide)]; decide)
    (by rw [native_raw program "<" 1 (by decide)]; decide) one two rfl (by decide)

theorem integer_sub_returns (program : Program) (caller : Subst) (state : State) (left right : Atom) (first second : Int)
    (one : PureReturns program caller state left state (integer first))
    (two : PureReturns program caller state right state (integer second)) :
    PureReturns program caller state (apply "-" [left, right]) state (integer (first - second)) := by
  exact native_binary_call_returns program caller state state state state "-" left right _ _ _
    (by decide) (by decide) (by rw [native_raw program "-" 0 (by decide)]; decide)
    (by rw [native_raw program "-" 1 (by decide)]; decide) one two rfl (by decide)

theorem integer_add_returns (program : Program) (caller : Subst) (state : State) (left right : Atom) (first second : Int)
    (one : PureReturns program caller state left state (integer first))
    (two : PureReturns program caller state right state (integer second)) :
    PureReturns program caller state (apply "+" [left, right]) state (integer (first + second)) := by
  exact native_binary_call_returns program caller state state state state "+" left right _ _ _
    (by decide) (by decide) (by rw [native_raw program "+" 0 (by decide)]; decide)
    (by rw [native_raw program "+" 1 (by decide)]; decide) one two rfl (by decide)

#print axioms integer_lt_returns
#print axioms integer_sub_returns
#print axioms integer_add_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit
