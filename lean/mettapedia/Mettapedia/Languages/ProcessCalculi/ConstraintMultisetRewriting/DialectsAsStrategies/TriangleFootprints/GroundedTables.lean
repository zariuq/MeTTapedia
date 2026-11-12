import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.BoundVariables

/-!
# HE's grounded dispatch against PeTTa's built-ins, operation by operation

HE's grounded operations are a relation in the specification (`Spec.Eval.GroundedDispatch`). The
tree's HE source programs instantiate integer arithmetic from `OSLFCore.executeGroundedOp` (the
minimal operations of the Hyperon Experimental specification), with a success carrying no bindings
and `incorrectArgument` when the operation has no value (`HERangeSourceProgram.dispatch`,
`TypedSquareSource.multiplication`). `heDispatch` is that instantiation for all of
`executeGroundedOp`'s integer operations. PeTTa's are its primitive table `StdLib.apply`, executed
by the streaming machine's `primitive` rule.

## Agreement

* `he_outcome_exact`, `petta_int_op`: on two integers, `+`, `-`, `*`, `<`, `<=`, `>`, `>=` give the
  same atom (`intValue`): mathematical integers, booleans as grounded values in both.
* `he_executable`, `petta_known`: each is a host operation of both.

## Differences, each with its reason

* `no_overflow`: neither specification has a fixed width; `(+ 2^63-1 1)` is `2^63` in both.
* `division_only_in_he`: HE's table has `/`; PeTTa's has none (it is data unless defined).
* `modulo_sign_differs`: `(% 7 -2)` is `1` in HE (Lean's `emod`, never negative) and `-1` in
  PeTTa (`fmod`, the divisor's sign, as Prolog's `mod`).
* `division_by_zero_differs`: `(% 7 0)` has no value in HE (`incorrectArgument`, after which HE's
  machine returns the call itself, `NativeOutcomeRel.incorrectArgument`); PeTTa raises the
  `zeroDivisor` fault.
* `non_numeric_differs`, `non_ground_differs`: `(+ a 4)` and `(+ $x 4)` are HE's
  `incorrectArgument` (the call is returned unreduced) and PeTTa's `invalidArguments` fault: errors
  are data or no reduction in HE, failure in PeTTa, and neither evaluates an operation on a
  variable.
* `equality_on_symbols_differs`: `(== a a)` is no integer equality in HE (`incorrectArgument`);
  PeTTa compares any two atoms and answers `True`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace GroundedTables

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue executeGroundedOp)
open Mettapedia.Languages.MeTTa.HE (Bindings GroundedResult)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.PeTTa

/-- The names `OSLFCore.executeGroundedOp` executes on integers. -/
def heIntegerNames : List String := ["+", "-", "*", "/", "%", "<", "<=", ">", ">=", "=="]

/-- The outcome of HE's grounded call: the operation's value as one success without bindings, or
`incorrectArgument` when it has none. -/
def heOutcome (operator : Atom) (arguments : List Atom) : GroundedResult :=
  match executeGroundedOp operator arguments with
  | some value => .ok [(value, Bindings.empty)]
  | none => .incorrectArgument

/-- **HE's grounded dispatch for integer operations**, as the tree's HE source programs instantiate
it from `OSLFCore.executeGroundedOp`. -/
def heDispatch : GroundedDispatch where
  executable operator := ∃ name, operator = .symbol name ∧ name ∈ heIntegerNames
  outcome operator arguments outcome := outcome = heOutcome operator arguments

/-- The integer operations compared. -/
inductive IntOp : String → Prop
  | plus : IntOp "+"
  | minus : IntOp "-"
  | times : IntOp "*"
  | less : IntOp "<"
  | lessEqual : IntOp "<="
  | greater : IntOp ">"
  | greaterEqual : IntOp ">="

/-- The value both tables give an integer operation. -/
def intValue : String → Int → Int → Atom
  | "+", a, b => .grounded (.int (a + b))
  | "-", a, b => .grounded (.int (a - b))
  | "*", a, b => .grounded (.int (a * b))
  | "<", a, b => .grounded (.bool (decide (a < b)))
  | "<=", a, b => .grounded (.bool (decide (a ≤ b)))
  | ">", a, b => .grounded (.bool (decide (b < a)))
  | ">=", a, b => .grounded (.bool (decide (b ≤ a)))
  | _, _, _ => .symbol "unknown"

/-- An integer argument. -/
abbrev num (n : Int) : Atom := .grounded (.int n)

theorem he_int_op {op : String} (known : IntOp op) (a b : Int) :
    executeGroundedOp (.symbol op) [num a, num b] = some (intValue op a b) := by
  cases known <;> rfl

/-- **HE's outcome of an integer operation is exactly one success with the shared value.** -/
theorem he_outcome_exact {op : String} (known : IntOp op) (a b : Int) (outcome : GroundedResult) :
    heDispatch.outcome (.symbol op) [num a, num b] outcome ↔
      outcome = .ok [(intValue op a b, Bindings.empty)] := by
  change outcome = heOutcome (.symbol op) [num a, num b] ↔ _
  rw [heOutcome, he_int_op known a b]

theorem petta_int_op {op : String} (known : IntOp op) (state : Effects.State) (a b : Int) :
    StdLib.apply state op [num a, num b] = .ok (state, [intValue op a b]) := by
  cases known <;> rfl

theorem he_executable {op : String} (known : IntOp op) : heDispatch.executable (.symbol op) := by
  cases known <;> exact ⟨_, rfl, by decide⟩

theorem petta_known {op : String} (known : IntOp op) : StdLib.known op = true := by
  cases known <;> decide

theorem intValue_data {op : String} (known : IntOp op) (a b : Int) :
    ∃ value : GroundedValue, intValue op a b = .grounded value := by
  cases known <;> exact ⟨_, rfl⟩

/-! ## Differences -/

/-- **Overflow is not a difference**: neither specification has a fixed width. -/
theorem no_overflow (state : Effects.State) :
    executeGroundedOp (.symbol "+") [num 9223372036854775807, num 1] =
      some (num 9223372036854775808) ∧
    StdLib.apply state "+" [num 9223372036854775807, num 1] =
      .ok (state, [num 9223372036854775808]) :=
  ⟨rfl, rfl⟩

/-- **Division is a host operation of HE only.** -/
theorem division_only_in_he :
    heDispatch.executable (.symbol "/") ∧ executeGroundedOp (.symbol "/") [num 7, num 2] = some (num 3) ∧
      StdLib.known "/" = false :=
  ⟨⟨"/", rfl, by decide⟩, by decide, by decide⟩

/-- **The sign of a remainder differs**: HE takes Lean's `emod` (never negative), PeTTa the divisor's
sign (`fmod`). -/
theorem modulo_sign_differs (state : Effects.State) :
    executeGroundedOp (.symbol "%") [num 7, num (-2)] = some (num 1) ∧
    StdLib.apply state "%" [num 7, num (-2)] = .ok (state, [num (-1)]) :=
  ⟨by decide, rfl⟩

/-- **Division by zero: no value in HE, a fault in PeTTa.** -/
theorem division_by_zero_differs (state : Effects.State) :
    heOutcome (.symbol "%") [num 7, num 0] = .incorrectArgument ∧
    heOutcome (.symbol "/") [num 7, num 0] = .incorrectArgument ∧
    StdLib.apply state "%" [num 7, num 0] = .error .zeroDivisor :=
  ⟨by decide, by decide, rfl⟩

/-- **A non-numeric argument: HE's `incorrectArgument`, PeTTa's fault.** -/
theorem non_numeric_differs (state : Effects.State) :
    heOutcome (.symbol "+") [.symbol "a", num 4] = .incorrectArgument ∧
      StdLib.apply state "+" [.symbol "a", num 4] = .error (.invalidArguments "+") :=
  ⟨rfl, rfl⟩

/-- **A non-ground argument: HE's `incorrectArgument`, PeTTa's fault.** Neither evaluates an
operation on a variable. -/
theorem non_ground_differs (state : Effects.State) :
    heOutcome (.symbol "+") [.var "x", num 4] = .incorrectArgument ∧
      StdLib.apply state "+" [.var "x", num 4] = .error (.invalidArguments "+") :=
  ⟨rfl, rfl⟩

/-- **Equality on symbols**: no integer equality in HE; PeTTa compares any two atoms. -/
theorem equality_on_symbols_differs (state : Effects.State) :
    heOutcome (.symbol "==") [.symbol "a", .symbol "a"] = .incorrectArgument ∧
      StdLib.apply state "==" [.symbol "a", .symbol "a"] = .ok (state, [Effects.boolean true]) :=
  ⟨rfl, rfl⟩

#print axioms he_int_op
#print axioms he_outcome_exact
#print axioms petta_int_op
#print axioms no_overflow
#print axioms division_only_in_he
#print axioms modulo_sign_differs
#print axioms division_by_zero_differs
#print axioms non_numeric_differs
#print axioms non_ground_differs
#print axioms equality_on_symbols_differs

end GroundedTables

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
