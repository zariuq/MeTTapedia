import Mettapedia.Languages.MeTTa.PeTTa.BridgeForms
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CettaWireAtom

/-!
# Wire values in bridge proofs

The CettaWire carrier's naturals, symbols and lists as PeTTa values, with the evaluation facts
every library bridge needs: reading a bound variable, natural equality, comparison, addition and
predecessor. Each holds for every program, since the arithmetic heads are native and evaluate their
arguments.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics (Program)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval

/-- A wire term as a PeTTa value. -/
abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term

/-- A natural as a PeTTa value. -/
abbrev number (value : Nat) : Atom := encoded (.natural value)

/-- An application with a literal head. -/
abbrev apply (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)

/-- **A bound variable** returns its value. -/
theorem bound_returns (program : Program) (caller : Subst) (state : State) {name : String} {value : Atom}
    (found : caller.lookup name = some value) :
    PureReturns program caller state (.var name) state value := by
  have read := variable_returns program caller state name
  simpa [applySubst, found] using read

/-- A bound variable returns any answer its value equals. -/
theorem bound_answer_returns (program : Program) (caller : Subst) (state : State) {name : String} {value answer : Atom}
    (found : caller.lookup name = some value) (same : value = answer) :
    PureReturns program caller state (.var name) state answer :=
  same ▸ bound_returns program caller state found

/-- A literal natural returns itself. -/
theorem number_returns (program : Program) (caller : Subst) (state : State) (value : Nat) :
    PureReturns program caller state (number value) state (number value) :=
  grounded_returns program caller state (.int value)

/-- A native head's argument demand is the primitive table's, in every program. -/
theorem native_raw (program : Program) (head : String) (index : Nat) (native : StdLib.known head = true) :
    argumentIsRaw program head index = StdLib.rawArgument head index := by
  simp [argumentIsRaw, native]

/-- A natural written literally in a body returns its wire value. -/
theorem literal_returns (program : Program) (caller : Subst) (state : State) (value : Nat) :
    PureReturns program caller state (.grounded (.int value)) state (number value) :=
  grounded_returns program caller state (.int value)

private theorem integer_le (state : State) (left right : Int) :
    StdLib.apply state "<=" [.grounded (.int left), .grounded (.int right)] =
      .ok (state, [Effects.boolean (decide (left ≤ right))]) := rfl

private theorem integer_lt (state : State) (left right : Int) :
    StdLib.apply state "<" [.grounded (.int left), .grounded (.int right)] =
      .ok (state, [Effects.boolean (decide (left < right))]) := rfl

private theorem integer_subtraction (state : State) (left right : Int) :
    StdLib.apply state "-" [.grounded (.int left), .grounded (.int right)] =
      .ok (state, [.grounded (.int (left - right))]) := rfl

private theorem native_binary (program : Program) (caller : Subst) (state : State) (head : String)
    (left right : Atom) (leftValue rightValue answer : Atom)
    (native : StdLib.known head = true) (notIO : ioHead head = false)
    (leftRaw : StdLib.rawArgument head 0 = false) (rightRaw : StdLib.rawArgument head 1 = false)
    (ordinary : head ∉ BridgeKit.specialForms)
    (leftReturns : PureReturns program caller state left state leftValue)
    (rightReturns : PureReturns program caller state right state rightValue)
    (computed : StdLib.apply state head [leftValue, rightValue] = .ok (state, [answer])) :
    PureReturns program caller state (apply head [left, right]) state answer :=
  native_binary_call_returns program caller state state state state head left right leftValue rightValue answer
    notIO native (by simp [argumentIsRaw, native, leftRaw]) (by simp [argumentIsRaw, native, rightRaw])
    leftReturns rightReturns computed (by simp_all [BridgeKit.specialForms])

/-- **Natural equality.** -/
theorem natural_equal_returns (program : Program) (caller : Subst) (state : State) (left right : Atom)
    (first second : Nat)
    (leftReturns : PureReturns program caller state left state (number first))
    (rightReturns : PureReturns program caller state right state (number second)) :
    PureReturns program caller state (apply "==" [left, right]) state (Effects.boolean (decide (first = second))) := by
  have tested := CettaWireAtom.equality_evaluated_returns program caller state (.natural first) (.natural second)
    left right (by rw [native_raw program "==" 0 (by decide)]; decide)
    (by rw [native_raw program "==" 1 (by decide)]; decide) leftReturns rightReturns
  simpa only [Term.natural.injEq] using tested

/-- **Natural comparison.** -/
theorem natural_le_returns (program : Program) (caller : Subst) (state : State) (left right : Atom)
    (first second : Nat)
    (leftReturns : PureReturns program caller state left state (number first))
    (rightReturns : PureReturns program caller state right state (number second)) :
    PureReturns program caller state (apply "<=" [left, right]) state (Effects.boolean (decide (first ≤ second))) := by
  apply native_binary program caller state "<=" left right _ _ _ (by decide) (by decide) (by decide) (by decide)
    (by decide) leftReturns rightReturns
  simp only [CettaWireAtom.encode, integer_le, Int.ofNat_le]

/-- **Natural addition.** -/
theorem natural_add_returns (program : Program) (caller : Subst) (state : State) (left right : Atom)
    (first second : Nat)
    (leftReturns : PureReturns program caller state left state (number first))
    (rightReturns : PureReturns program caller state right state (number second)) :
    PureReturns program caller state (apply "+" [left, right]) state (number (first + second)) := by
  apply native_binary program caller state "+" left right _ _ _ (by decide) (by decide) (by decide) (by decide)
    (by decide) leftReturns rightReturns
  simp [StdLib.integer_addition, CettaWireAtom.encode]

/-- **Predecessor** of a positive natural. -/
theorem natural_pred_returns (program : Program) (caller : Subst) (state : State) (code : Atom) (value : Nat)
    (returns : PureReturns program caller state code state (number (value + 1))) :
    PureReturns program caller state (apply "-" [code, number 1]) state (number value) := by
  apply native_binary program caller state "-" code (number 1) _ _ _ (by decide) (by decide) (by decide) (by decide)
    (by decide) returns (number_returns program caller state 1)
  have casts : ((value + 1 : Nat) : Int) - ((1 : Nat) : Int) = (value : Int) := by omega
  simp only [CettaWireAtom.encode, integer_subtraction, casts]

/-- **Natural strict comparison.** -/
theorem natural_lt_returns (program : Program) (caller : Subst) (state : State) (left right : Atom)
    (first second : Nat)
    (leftReturns : PureReturns program caller state left state (number first))
    (rightReturns : PureReturns program caller state right state (number second)) :
    PureReturns program caller state (apply "<" [left, right]) state (Effects.boolean (decide (first < second))) := by
  apply native_binary program caller state "<" left right _ _ _ (by decide) (by decide) (by decide) (by decide)
    (by decide) leftReturns rightReturns
  simp only [CettaWireAtom.encode, integer_lt, Int.ofNat_lt]

/-- **Equality of wire terms.** -/
theorem term_equal_returns (program : Program) (caller : Subst) (state : State) (left right : Atom)
    (first second : Term)
    (leftReturns : PureReturns program caller state left state (encoded first))
    (rightReturns : PureReturns program caller state right state (encoded second)) :
    PureReturns program caller state (apply "==" [left, right]) state (Effects.boolean (decide (first = second))) :=
  CettaWireAtom.equality_evaluated_returns program caller state first second left right
    (by rw [native_raw program "==" 0 (by decide)]; decide)
    (by rw [native_raw program "==" 1 (by decide)]; decide) leftReturns rightReturns

/-- **Equality of strings**, as the evaluator holds them. -/
theorem string_equal_returns (program : Program) (caller : Subst) (state : State) (left right : Atom)
    (first second : String)
    (leftReturns : PureReturns program caller state left state (.grounded (.string first)))
    (rightReturns : PureReturns program caller state right state (.grounded (.string second))) :
    PureReturns program caller state (apply "==" [left, right]) state (Effects.boolean (decide (first = second))) := by
  have equal := term_equal_returns program caller state left right (.string first) (.string second)
    leftReturns rightReturns
  simpa only [Term.string.injEq] using equal

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit
