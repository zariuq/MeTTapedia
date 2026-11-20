import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.BoundVariables

/-!
# HE's grounded table, as the model has it and as HE computes it, against PeTTa's built-ins

HE's grounded operations are a relation in the specification (`Spec.Eval.GroundedDispatch`). Two
instances are compared here.

* **The model's table** (`heOutcome`, `heDispatch`): the tree's HE source programs instantiate
  integer arithmetic from `OSLFCore.executeGroundedOp`, with a success carrying no bindings and
  `incorrectArgument` when the operation has no value (`HERangeSourceProgram.dispatch`,
  `TypedSquareSource.multiplication`). Its integers have no width, its `/` and `%` are Lean's `ediv`
  and `emod`, and it has no `==` on symbols. The every-run theorems of `GroundedRuns`,
  `GroundedEveryRun`, `NestedArithmetic` and `EveryRunFinishesW` are stated for any table under the
  contract below; this table is one instance of them.
* **HE's table** (`measuredOutcome`, `measuredDispatch`): the integer and Boolean operations of
  HE's standard library, operation by operation. Integers are 64-bit and a result that does not
  fit is the runtime error `IntegerOverflow`; `/` and `%` truncate toward zero (`Int.tdiv`,
  `Int.tmod`); a zero divisor is the runtime error `DivisionByZero`; `/` on anything but two numbers
  is a runtime error, while the other operations decline (`incorrectArgument`, after which HE's
  machine returns the call itself); `==` compares any two atoms; `not`, `and`, `or`, `xor` act on
  Booleans. The machine turns a runtime error `m` into the answer `(Error call m)`
  (`Completed.NativeOutcomeRel.runtimeError`). HE's floats are not modelled: the grounded values of
  the tree have no float.

## The two HE tables

* `measured_outcome_exact`, `measured_agrees`: on `+ - * < <= > >=` with two integers whose result
  fits in 64 bits, the tables give the same outcome.
* `division_agrees`, `modulo_agrees`: on `/` and `%` with a non-negative dividend and a positive
  divisor, they agree.
* `tables_part`: where they part, each with its smallest call: `(/ -7 2)` (`-3` against `-4`),
  `(% -7 2)` (`-1` against `1`), `(/ 7 0)` and `(% 7 0)` (`DivisionByZero` against no value),
  `(+ 9223372036854775807 1)` (`IntegerOverflow` against `2^63`), `(== a a)` (`True` against no
  value), `(/ a 2)` (a runtime error against no value).

## HE against PeTTa's built-ins (`StdLib.apply`)

* `he_outcome_exact`, `petta_int_op`: on two integers, `+`, `-`, `*`, `<`, `<=`, `>`, `>=` give the
  same atom (`intValue`) in the model's table and in PeTTa's.
* `modulo_sign_differs`: `(% 7 -2)` is `1` and `(% -7 2)` is `-1` in HE (the dividend's sign);
  PeTTa's `fmod` gives `-1` and `1` (the divisor's sign).
* `division_truncates`: HE's `(/ 7 2)` is `3` and `(/ -7 2)` is `-3`. The PeTTa model has no `/`
  (`petta_model_lacks_division`), while both PeTTa hosts have it; no difference is stated from
  the model.
* `division_by_zero_differs`: `(% 7 0)` and `(/ 7 0)` are HE's runtime error `DivisionByZero`;
  PeTTa raises the `zeroDivisor` fault.
* `overflow_differs`: `(+ 9223372036854775807 1)`, `(* 9223372036854775807 2)` and
  `(- -9223372036854775808 1)` are HE's runtime error `IntegerOverflow`; PeTTa's integers have no
  width.
* `equality_on_symbols_agrees`: `(== a a)` is `True` in HE and in PeTTa, and `(== a b)` is `False`.
* `non_numeric_differs`, `non_ground_differs`: `(+ a 4)` and `(+ $x 4)` are HE's
  `incorrectArgument` (the call is returned unreduced) and PeTTa's `invalidArguments` fault.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace GroundedTables

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue executeGroundedOp)
open Mettapedia.Languages.MeTTa.HE (Bindings GroundedResult)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.PeTTa
open EntryToQuery (DataAtom)

/-! ## The model's table -/

/-- The names `OSLFCore.executeGroundedOp` executes on integers. -/
def heIntegerNames : List String := ["+", "-", "*", "/", "%", "<", "<=", ">", ">=", "=="]

/-- **The model's outcome** of a grounded call: the value of `OSLFCore.executeGroundedOp` as one
success without bindings, or `incorrectArgument` when it has none. -/
def heOutcome (operator : Atom) (arguments : List Atom) : GroundedResult :=
  match executeGroundedOp operator arguments with
  | some value => .ok [(value, Bindings.empty)]
  | none => .incorrectArgument

/-- **The model's grounded dispatch for integer operations**, as the tree's HE source programs
instantiate it from `OSLFCore.executeGroundedOp`. It agrees with HE's table on integer results
that fit in 64 bits (`measured_agrees`) and parts from it at `tables_part`. -/
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

/-- **The model's outcome of an integer operation is exactly one success with the shared value**,
for every pair of integers: the model's integers have no width. -/
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

/-! ## HE's table -/

/-- The least integer HE stores (`i64::MIN`). -/
def i64Min : Int := -9223372036854775808

/-- The greatest integer HE stores (`i64::MAX`). -/
def i64Max : Int := 9223372036854775807

/-- An integer HE can store. -/
def Fits (n : Int) : Prop := i64Min ≤ n ∧ n ≤ i64Max

instance (n : Int) : Decidable (Fits n) := inferInstanceAs (Decidable (_ ∧ _))

/-- HE's checked integer result: the value when it fits, otherwise the runtime error
`IntegerOverflow`. -/
def checkedResult (n : Int) : GroundedResult :=
  if Fits n then .ok [(num n, Bindings.empty)] else .runtimeError "IntegerOverflow"

/-- A Boolean result. -/
def boolResult (value : Bool) : GroundedResult := .ok [(.grounded (.bool value), Bindings.empty)]

/-- **HE's outcome of a grounded call** for its integer and Boolean operations. -/
def measuredOutcome : Atom → List Atom → GroundedResult
  | .symbol "+", [.grounded (.int a), .grounded (.int b)] => checkedResult (a + b)
  | .symbol "-", [.grounded (.int a), .grounded (.int b)] => checkedResult (a - b)
  | .symbol "*", [.grounded (.int a), .grounded (.int b)] => checkedResult (a * b)
  | .symbol "/", [.grounded (.int a), .grounded (.int b)] =>
      if b = 0 then .runtimeError "DivisionByZero" else checkedResult (a.tdiv b)
  | .symbol "/", _ => .runtimeError "Divide expects two numbers: dividend and divisor"
  | .symbol "%", [.grounded (.int a), .grounded (.int b)] =>
      if b = 0 then .runtimeError "DivisionByZero" else .ok [(num (a.tmod b), Bindings.empty)]
  | .symbol "<", [.grounded (.int a), .grounded (.int b)] => boolResult (decide (a < b))
  | .symbol "<=", [.grounded (.int a), .grounded (.int b)] => boolResult (decide (a ≤ b))
  | .symbol ">", [.grounded (.int a), .grounded (.int b)] => boolResult (decide (b < a))
  | .symbol ">=", [.grounded (.int a), .grounded (.int b)] => boolResult (decide (b ≤ a))
  | .symbol "==", [left, right] => boolResult (decide (left = right))
  | .symbol "not", [.grounded (.bool value)] => boolResult (!value)
  | .symbol "and", [.grounded (.bool left), .grounded (.bool right)] => boolResult (left && right)
  | .symbol "or", [.grounded (.bool left), .grounded (.bool right)] => boolResult (left || right)
  | .symbol "xor", [.grounded (.bool left), .grounded (.bool right)] => boolResult (left ^^ right)
  | _, _ => .incorrectArgument

/-- The names of HE's integer and Boolean operations. -/
def measuredNames : List String :=
  ["+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "not", "and", "or", "xor"]

/-- **HE's grounded dispatch for its integer and Boolean operations.** -/
def measuredDispatch : GroundedDispatch where
  executable operator := ∃ name, operator = .symbol name ∧ name ∈ measuredNames
  outcome operator arguments outcome := outcome = measuredOutcome operator arguments

theorem measuredDispatch_minimal : measuredDispatch.minimal = none := rfl

theorem measured_executable_iff (name : String) :
    measuredDispatch.executable (.symbol name) ↔ name ∈ measuredNames := by
  constructor
  · rintro ⟨other, same, member⟩
    cases same
    exact member
  · intro member
    exact ⟨name, rfl, member⟩

/-- **HE's outcome of an integer operation whose result fits** is exactly one success with the
shared value. -/
theorem measured_outcome_exact {op : String} (known : IntOp op) (a b : Int)
    (fits : ∀ n, intValue op a b = num n → Fits n) (outcome : GroundedResult) :
    measuredDispatch.outcome (.symbol op) [num a, num b] outcome ↔
      outcome = .ok [(intValue op a b, Bindings.empty)] := by
  change outcome = measuredOutcome (.symbol op) [num a, num b] ↔ _
  cases known with
  | plus =>
      have inRange := fits (a + b) rfl
      simp [measuredOutcome, checkedResult, inRange, intValue]
  | minus =>
      have inRange := fits (a - b) rfl
      simp [measuredOutcome, checkedResult, inRange, intValue]
  | times =>
      have inRange := fits (a * b) rfl
      simp [measuredOutcome, checkedResult, inRange, intValue]
  | less => simp [measuredOutcome, boolResult, intValue]
  | lessEqual => simp [measuredOutcome, boolResult, intValue]
  | greater => simp [measuredOutcome, boolResult, intValue]
  | greaterEqual => simp [measuredOutcome, boolResult, intValue]

/-- **The tables agree on integer results that fit.** -/
theorem measured_agrees {op : String} (known : IntOp op) (a b : Int)
    (fits : ∀ n, intValue op a b = num n → Fits n) :
    measuredOutcome (.symbol op) [num a, num b] = heOutcome (.symbol op) [num a, num b] := by
  have measured := (measured_outcome_exact known a b fits
    (measuredOutcome (.symbol op) [num a, num b])).mp rfl
  rw [measured, heOutcome, he_int_op known a b]

/-- **The tables agree on `/` with a non-negative dividend that fits and a positive divisor.** -/
theorem division_agrees {a b : Int} (nonneg : 0 ≤ a) (fits : a ≤ i64Max) (positive : 0 < b) :
    measuredOutcome (.symbol "/") [num a, num b] = heOutcome (.symbol "/") [num a, num b] ∧
      heOutcome (.symbol "/") [num a, num b] = .ok [(num (a / b), Bindings.empty)] := by
  have nonzero : b ≠ 0 := Int.ne_of_gt positive
  have quotientFits : Fits (a / b) := by
    refine ⟨?_, ?_⟩
    · exact Int.le_trans (by decide) (Int.ediv_nonneg nonneg (Int.le_of_lt positive))
    · exact Int.le_trans (Int.ediv_le_self b nonneg) fits
  have model : heOutcome (.symbol "/") [num a, num b] = .ok [(num (a / b), Bindings.empty)] := by
    simp [heOutcome, executeGroundedOp,
      Mettapedia.Languages.MeTTa.OSLFCore.GroundedType.execute, nonzero]
  refine ⟨?_, model⟩
  rw [model]
  simp [measuredOutcome, nonzero, checkedResult, Int.tdiv_eq_ediv_of_nonneg nonneg, quotientFits]

/-- **The tables agree on `%` with a non-negative dividend and a positive divisor.** -/
theorem modulo_agrees {a b : Int} (nonneg : 0 ≤ a) (positive : 0 < b) :
    measuredOutcome (.symbol "%") [num a, num b] = heOutcome (.symbol "%") [num a, num b] := by
  have nonzero : b ≠ 0 := Int.ne_of_gt positive
  simp [measuredOutcome, heOutcome, executeGroundedOp,
    Mettapedia.Languages.MeTTa.OSLFCore.GroundedType.execute, nonzero,
    Int.tmod_eq_emod_of_nonneg nonneg]

/-- **Where the tables part**, each with its smallest call: truncation against `ediv` and `emod`,
runtime errors against no value, `IntegerOverflow` against an unbounded sum, `==` on symbols, and
`/` on a symbol. -/
theorem tables_part :
    (measuredOutcome (.symbol "/") [num (-7), num 2] = .ok [(num (-3), Bindings.empty)] ∧
      heOutcome (.symbol "/") [num (-7), num 2] = .ok [(num (-4), Bindings.empty)]) ∧
    (measuredOutcome (.symbol "%") [num (-7), num 2] = .ok [(num (-1), Bindings.empty)] ∧
      heOutcome (.symbol "%") [num (-7), num 2] = .ok [(num 1, Bindings.empty)]) ∧
    (measuredOutcome (.symbol "/") [num 7, num 0] = .runtimeError "DivisionByZero" ∧
      heOutcome (.symbol "/") [num 7, num 0] = .incorrectArgument) ∧
    (measuredOutcome (.symbol "%") [num 7, num 0] = .runtimeError "DivisionByZero" ∧
      heOutcome (.symbol "%") [num 7, num 0] = .incorrectArgument) ∧
    (measuredOutcome (.symbol "+") [num 9223372036854775807, num 1] =
        .runtimeError "IntegerOverflow" ∧
      heOutcome (.symbol "+") [num 9223372036854775807, num 1] =
        .ok [(num 9223372036854775808, Bindings.empty)]) ∧
    (measuredOutcome (.symbol "==") [.symbol "a", .symbol "a"] =
        .ok [(.grounded (.bool true), Bindings.empty)] ∧
      heOutcome (.symbol "==") [.symbol "a", .symbol "a"] = .incorrectArgument) ∧
    (measuredOutcome (.symbol "/") [.symbol "a", num 2] =
        .runtimeError "Divide expects two numbers: dividend and divisor" ∧
      heOutcome (.symbol "/") [.symbol "a", num 2] = .incorrectArgument) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, rfl⟩, ⟨by decide, rfl⟩⟩

/-- **`not` is a grounded operation of HE, not of the model's table**; on a Boolean it answers, on a
symbol it declines. -/
theorem not_in_measured :
    measuredDispatch.executable (.symbol "not") ∧ ¬ heDispatch.executable (.symbol "not") ∧
      measuredOutcome (.symbol "not") [.grounded (.bool true)] =
        .ok [(.grounded (.bool false), Bindings.empty)] ∧
      measuredOutcome (.symbol "not") [.symbol "Yes"] = .incorrectArgument := by
  refine ⟨⟨"not", rfl, by decide⟩, ?_, rfl, rfl⟩
  rintro ⟨name, same, member⟩
  cases same
  revert member
  decide

/-- **`cons` is no grounded operation of HE.** -/
theorem cons_not_measured : ¬ measuredDispatch.executable (.symbol "cons") := by
  rintro ⟨name, same, member⟩
  cases same
  revert member
  decide

/-! ## HE against PeTTa -/

/-- **The sign of a remainder differs**: HE truncates, so its remainder takes the dividend's sign
(`(% 7 -2)` is `1`, `(% -7 2)` is `-1`); PeTTa's `fmod` takes the divisor's sign (`-1`, `1`). -/
theorem modulo_sign_differs (state : Effects.State) :
    measuredOutcome (.symbol "%") [num 7, num (-2)] = .ok [(num 1, Bindings.empty)] ∧
    measuredOutcome (.symbol "%") [num (-7), num 2] = .ok [(num (-1), Bindings.empty)] ∧
    StdLib.apply state "%" [num 7, num (-2)] = .ok (state, [num (-1)]) ∧
    StdLib.apply state "%" [num (-7), num 2] = .ok (state, [num 1]) :=
  ⟨by decide, by decide, rfl, rfl⟩

/-- **HE's division truncates toward zero**: `(/ 7 2)` is `3` and `(/ -7 2)` is `-3`. -/
theorem division_truncates :
    measuredOutcome (.symbol "/") [num 7, num 2] = .ok [(num 3, Bindings.empty)] ∧
    measuredOutcome (.symbol "/") [num (-7), num 2] = .ok [(num (-3), Bindings.empty)] ∧
    measuredOutcome (.symbol "/") [num 7, num (-2)] = .ok [(num (-3), Bindings.empty)] :=
  ⟨by decide, by decide, by decide⟩

/-- **A gap of the PeTTa model, not a difference of the dialects**: the PeTTa model's primitive
table has no `/`, so a call of `/` is data there; both PeTTa hosts divide (`(/ 7 2)` is `3.5`). -/
theorem petta_model_lacks_division : StdLib.known "/" = false := by decide

/-- **Division by zero: HE's runtime error `DivisionByZero`, PeTTa's fault.** -/
theorem division_by_zero_differs (state : Effects.State) :
    measuredOutcome (.symbol "%") [num 7, num 0] = .runtimeError "DivisionByZero" ∧
    measuredOutcome (.symbol "/") [num 7, num 0] = .runtimeError "DivisionByZero" ∧
    StdLib.apply state "%" [num 7, num 0] = .error .zeroDivisor :=
  ⟨by decide, by decide, rfl⟩

/-- **Overflow: HE's runtime error `IntegerOverflow`, PeTTa's unbounded integers.** -/
theorem overflow_differs (state : Effects.State) :
    measuredOutcome (.symbol "+") [num 9223372036854775807, num 1] =
        .runtimeError "IntegerOverflow" ∧
    measuredOutcome (.symbol "*") [num 9223372036854775807, num 2] =
        .runtimeError "IntegerOverflow" ∧
    measuredOutcome (.symbol "-") [num (-9223372036854775808), num 1] =
        .runtimeError "IntegerOverflow" ∧
    measuredOutcome (.symbol "/") [num (-9223372036854775808), num (-1)] =
        .runtimeError "IntegerOverflow" ∧
    measuredOutcome (.symbol "+") [num 9223372036854775807, num (-1)] =
        .ok [(num 9223372036854775806, Bindings.empty)] ∧
    StdLib.apply state "+" [num 9223372036854775807, num 1] =
      .ok (state, [num 9223372036854775808]) :=
  ⟨by decide, by decide, by decide, by decide, by decide, rfl⟩

/-- **Equality on symbols agrees**: HE and PeTTa compare any two atoms; `(== a a)` is `True` and
`(== a b)` is `False` in both. -/
theorem equality_on_symbols_agrees (state : Effects.State) :
    measuredOutcome (.symbol "==") [.symbol "a", .symbol "a"] =
        .ok [(.grounded (.bool true), Bindings.empty)] ∧
    measuredOutcome (.symbol "==") [.symbol "a", .symbol "b"] =
        .ok [(.grounded (.bool false), Bindings.empty)] ∧
    StdLib.apply state "==" [.symbol "a", .symbol "a"] = .ok (state, [Effects.boolean true]) ∧
    StdLib.apply state "==" [.symbol "a", .symbol "b"] = .ok (state, [Effects.boolean false]) :=
  ⟨by decide, by decide, rfl, rfl⟩

/-- **A non-numeric argument: HE's `incorrectArgument`, PeTTa's fault.** Both of HE's tables
decline. -/
theorem non_numeric_differs (state : Effects.State) :
    measuredOutcome (.symbol "+") [.symbol "a", num 4] = .incorrectArgument ∧
      heOutcome (.symbol "+") [.symbol "a", num 4] = .incorrectArgument ∧
      StdLib.apply state "+" [.symbol "a", num 4] = .error (.invalidArguments "+") :=
  ⟨rfl, rfl, rfl⟩

/-- **A non-ground argument: HE's `incorrectArgument`, PeTTa's fault.** Neither evaluates an
operation on a variable. -/
theorem non_ground_differs (state : Effects.State) :
    measuredOutcome (.symbol "+") [.var "x", num 4] = .incorrectArgument ∧
      heOutcome (.symbol "+") [.var "x", num 4] = .incorrectArgument ∧
      StdLib.apply state "+" [.var "x", num 4] = .error (.invalidArguments "+") :=
  ⟨rfl, rfl, rfl⟩

/-! ## A grounded table and its contract -/

/-- **A read-only grounded table**: the operators it executes, and its outcome relation on a call.
Its dispatch (`GroundedTable.dispatch`) has no minimal service and emits its values fresh and raw,
as `WorldServices.readOnlyGrounded` produces them. Both HE tables are of this form
(`modelTable_dispatch`, `measuredTable_dispatch`). -/
structure GroundedTable where
  executes : Atom → Prop
  outcome : Atom → List Atom → GroundedResult → Prop

namespace GroundedTable

/-- The table as a grounded dispatch of HE's specification. -/
def dispatch (T : GroundedTable) : GroundedDispatch where
  executable := T.executes
  outcome := T.outcome

theorem dispatch_minimal (T : GroundedTable) : T.dispatch.minimal = none := rfl

/-- **The table answers `v` on a call**: it executes the operator, and its one outcome on these
arguments is one success with the value `v` and no bindings. -/
def Answers (T : GroundedTable) (operator : Atom) (arguments : List Atom) (v : Atom) : Prop :=
  T.executes operator ∧
    ∀ outcome, T.outcome operator arguments outcome ↔ outcome = .ok [(v, Bindings.empty)]

/-- **The table declines a call**: it executes the operator, and its one outcome on these arguments
is `incorrectArgument`, on which HE's machine returns the call itself. -/
def Declines (T : GroundedTable) (operator : Atom) (arguments : List Atom) : Prop :=
  T.executes operator ∧ ∀ outcome, T.outcome operator arguments outcome ↔ outcome = .incorrectArgument

/-- **The table errs on a call with the message `m`**: it executes the operator, and its one outcome
on these arguments is the runtime error `m`, which HE's machine answers as `(Error call m)`. -/
def Errs (T : GroundedTable) (operator : Atom) (arguments : List Atom) (message : String) : Prop :=
  T.executes operator ∧
    ∀ outcome, T.outcome operator arguments outcome ↔ outcome = .runtimeError message

/-- **The contract on a grounded table**: on every call of an operator it executes, the table has a
verdict. It answers one data value other than `NotReducible`, declines, or errs. The every-run
theorems of `GroundedRuns`, `GroundedEveryRun`, `NestedArithmetic` and `EveryRunFinishesW` are
stated for any table; their grounded case asks the table to answer the call with PeTTa's value.
`GroundedDifferences.verdict_every_run` reads the whole contract on one call. -/
def Contract (T : GroundedTable) : Prop :=
  ∀ operator arguments, T.executes operator →
    (∃ v, DataAtom v ∧ v ≠ Atom.notReducible ∧ T.Answers operator arguments v) ∨
      T.Declines operator arguments ∨ ∃ message, T.Errs operator arguments message

/-- An answer is unique. -/
theorem answers_unique {T : GroundedTable} {operator : Atom} {arguments : List Atom} {v w : Atom}
    (first : T.Answers operator arguments v) (second : T.Answers operator arguments w) : v = w := by
  have both := (second.2 _).mp ((first.2 _).mpr rfl)
  simp only [GroundedResult.ok.injEq, List.cons.injEq, Prod.mk.injEq, and_true] at both
  exact both

/-- The verdicts exclude each other: a call the table answers it neither declines nor errs on. -/
theorem answers_not_declines {T : GroundedTable} {operator : Atom} {arguments : List Atom} {v : Atom}
    (answers : T.Answers operator arguments v) : ¬ T.Declines operator arguments := by
  intro declines
  have both := (declines.2 _).mp ((answers.2 _).mpr rfl)
  cases both

theorem answers_not_errs {T : GroundedTable} {operator : Atom} {arguments : List Atom} {v : Atom}
    {message : String} (answers : T.Answers operator arguments v) :
    ¬ T.Errs operator arguments message := by
  intro errs
  have both := (errs.2 _).mp ((answers.2 _).mpr rfl)
  cases both

theorem declines_not_errs {T : GroundedTable} {operator : Atom} {arguments : List Atom}
    {message : String} (declines : T.Declines operator arguments) :
    ¬ T.Errs operator arguments message := by
  intro errs
  have both := (errs.2 _).mp ((declines.2 _).mpr rfl)
  cases both

end GroundedTable

open GroundedTable

/-- **The model's table**, read as a table. -/
def modelTable : GroundedTable := ⟨heDispatch.executable, heDispatch.outcome⟩

theorem modelTable_dispatch : modelTable.dispatch = heDispatch := rfl

/-- **HE's table**, read as a table. -/
def measuredTable : GroundedTable := ⟨measuredDispatch.executable, measuredDispatch.outcome⟩

theorem measuredTable_dispatch : measuredTable.dispatch = measuredDispatch := rfl

theorem measured_executable {op : String} (known : IntOp op) :
    measuredDispatch.executable (.symbol op) := by
  cases known <;> exact ⟨_, rfl, by decide⟩

/-- **The model's table answers every integer operation on two integers**, whatever their size. -/
theorem model_answers {op : String} (known : IntOp op) (a b : Int) :
    modelTable.Answers (.symbol op) [num a, num b] (intValue op a b) :=
  ⟨he_executable known, he_outcome_exact known a b⟩

/-- **HE's table answers an integer operation whose result fits in 64 bits.** -/
theorem measured_answers {op : String} (known : IntOp op) (a b : Int)
    (fits : ∀ n, intValue op a b = num n → Fits n) :
    measuredTable.Answers (.symbol op) [num a, num b] (intValue op a b) :=
  ⟨measured_executable known, measured_outcome_exact known a b fits⟩

/-- **Where the tables' verdicts part**: on `(+ 9223372036854775807 1)` the model's table answers
`9223372036854775808` and HE's table errs with `IntegerOverflow`. -/
theorem verdicts_part :
    modelTable.Answers (.symbol "+") [num 9223372036854775807, num 1] (num 9223372036854775808) ∧
      measuredTable.Errs (.symbol "+") [num 9223372036854775807, num 1] "IntegerOverflow" := by
  refine ⟨model_answers .plus _ _, measured_executable .plus, fun outcome => ?_⟩
  change outcome = measuredOutcome _ _ ↔ _
  rw [show measuredOutcome (.symbol "+") [num 9223372036854775807, num 1] =
    .runtimeError "IntegerOverflow" by decide]

/-- Every value of the tree's grounded operations is a grounded literal. -/
theorem execute_grounded {operator : Atom} {arguments : List Atom} {v : Atom}
    (executed : executeGroundedOp operator arguments = some v) : ∃ g, v = .grounded g := by
  have finish : ∀ {result : Option Atom}, result = some v →
      (∀ w, result = some w → ∃ g, w = .grounded g) → ∃ g, v = .grounded g :=
    fun same values => values v same
  unfold executeGroundedOp at executed
  refine finish executed fun w produced => ?_
  clear executed finish
  split at produced
  all_goals first
    | (simp only [Mettapedia.Languages.MeTTa.OSLFCore.GroundedType.execute] at produced
       split at produced
       all_goals first
         | (cases produced; exact ⟨_, rfl⟩)
         | cases produced
         | (split_ifs at produced
            all_goals (cases produced; exact ⟨_, rfl⟩)))
    | cases produced

/-- **The model's table meets the contract**: it answers or declines, and never errs. -/
theorem model_contract : modelTable.Contract := by
  intro operator arguments executes
  cases executed : executeGroundedOp operator arguments with
  | none =>
      refine Or.inr (Or.inl ⟨executes, fun outcome => ?_⟩)
      change outcome = heOutcome operator arguments ↔ _
      rw [heOutcome, executed]
  | some v =>
      obtain ⟨g, rfl⟩ := execute_grounded executed
      have notRefused : Atom.grounded g ≠ Atom.notReducible := fun same => by cases same
      refine Or.inl ⟨.grounded g, .grounded g, notRefused, executes, fun outcome => ?_⟩
      change outcome = heOutcome operator arguments ↔ _
      rw [heOutcome, executed]

/-- Every outcome of HE's table is one grounded value, a runtime error, or `incorrectArgument`. -/
theorem measuredOutcome_cases (operator : Atom) (arguments : List Atom) :
    (∃ g : GroundedValue, measuredOutcome operator arguments = .ok [(.grounded g, Bindings.empty)]) ∨
      (∃ message, measuredOutcome operator arguments = .runtimeError message) ∨
      measuredOutcome operator arguments = .incorrectArgument := by
  have checked : ∀ n : Int, (∃ g : GroundedValue, checkedResult n = .ok [(.grounded g, Bindings.empty)]) ∨
      (∃ message, checkedResult n = .runtimeError message) ∨ checkedResult n = .incorrectArgument := by
    intro n
    unfold checkedResult
    split_ifs
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr (Or.inl ⟨_, rfl⟩)
  unfold measuredOutcome
  split
  all_goals first
    | exact checked _
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | exact Or.inr (Or.inr rfl)
    | (split_ifs
       all_goals first
         | exact checked _
         | exact Or.inl ⟨_, rfl⟩
         | exact Or.inr (Or.inl ⟨_, rfl⟩))

/-- **HE's table meets the contract**: it answers an integer or a Boolean, declines, or errs. -/
theorem measured_contract : measuredTable.Contract := by
  intro operator arguments executes
  rcases measuredOutcome_cases operator arguments with ⟨g, computed⟩ | ⟨message, computed⟩ | computed
  · have notRefused : Atom.grounded g ≠ Atom.notReducible := fun same => by cases same
    refine Or.inl ⟨.grounded g, .grounded g, notRefused, executes, fun outcome => ?_⟩
    change outcome = measuredOutcome operator arguments ↔ _
    rw [computed]
  · refine Or.inr (Or.inr ⟨message, executes, fun outcome => ?_⟩)
    change outcome = measuredOutcome operator arguments ↔ _
    rw [computed]
  · refine Or.inr (Or.inl ⟨executes, fun outcome => ?_⟩)
    change outcome = measuredOutcome operator arguments ↔ _
    rw [computed]

/-! ## The types HE gives its grounded operations: a stated region

HE gives each grounded operation a type and checks a call against it before running the operation
(measured on hyperon-experimental 0.2.10 with three later fixes: `(get-type +)` is
`(-> Number Number Number)`; `(+ 1 True)`, `(== 5 True)`, `(< 1 True)`, `(and True 5)`, `(not 5)`,
and with `(: c Color)` also `(+ c 4)` and `(== c 5)`, are `BadArgType` errors; `(+ 1)` is
`IncorrectNumberOfArguments`). The model's machine gives grounded operations no type: it hands the
argument values to the table (`GroundedDifferences.machine_reads_no_argument_types`). So the model's
answer to a grounded call is HE's only inside the region `TypedRegion` below; its controls are in
`GroundedDifferences.Controls`. Inside the region, agreement with HE is measured on the programs of
the named theorems that state it, not proved: HE is not in Lean. -/

/-- **HE's type of each of its grounded operations**, as `get-type` prints it (measured): the
parameter types and the result type. `==` has the type variable `$t` at both parameters. -/
def measuredSignature : String → Option (List Atom × Atom)
  | "+" => some ([.symbol "Number", .symbol "Number"], .symbol "Number")
  | "-" => some ([.symbol "Number", .symbol "Number"], .symbol "Number")
  | "*" => some ([.symbol "Number", .symbol "Number"], .symbol "Number")
  | "/" => some ([.symbol "Number", .symbol "Number"], .symbol "Number")
  | "%" => some ([.symbol "Number", .symbol "Number"], .symbol "Number")
  | "<" => some ([.symbol "Number", .symbol "Number"], .symbol "Bool")
  | "<=" => some ([.symbol "Number", .symbol "Number"], .symbol "Bool")
  | ">" => some ([.symbol "Number", .symbol "Number"], .symbol "Bool")
  | ">=" => some ([.symbol "Number", .symbol "Number"], .symbol "Bool")
  | "==" => some ([.var "t", .var "t"], .symbol "Bool")
  | "not" => some ([.symbol "Bool"], .symbol "Bool")
  | "and" => some ([.symbol "Bool", .symbol "Bool"], .symbol "Bool")
  | "or" => some ([.symbol "Bool", .symbol "Bool"], .symbol "Bool")
  | "xor" => some ([.symbol "Bool", .symbol "Bool"], .symbol "Bool")
  | _ => none

/-- The rows `(: name type)` of a program, as `(name, type)`. -/
def declarationOf : Atom → Option (String × Atom)
  | .expression [.symbol ":", .symbol name, type] => some (name, type)
  | _ => none

/-- **The types an argument value has in a program**: a grounded literal its kind's type; a symbol
the types the program declares for it, none when it declares none. -/
def argumentTypes (atoms : List Atom) : Atom → List Atom
  | .grounded (.int _) => [.symbol "Number"]
  | .grounded (.bool _) => [.symbol "Bool"]
  | .grounded (.string _) => [.symbol "String"]
  | .grounded (.custom name _) => [.symbol name]
  | .symbol name => atoms.filterMap fun row => match declarationOf row with
      | some (subject, type) => if subject = name then some type else none
      | none => none
  | _ => []

/-- Whether a parameter type is a type variable. -/
def isTypeVariable : Atom → Bool
  | .var _ => true
  | _ => false

/-- The types of the arguments at the type-variable parameters. -/
def sharedTypes (atoms : List Atom) (params args : List Atom) : List Atom :=
  ((params.zip args).filter (fun p => isTypeVariable p.1)).flatMap (fun p => argumentTypes atoms p.2)

/-- The region test, computed. -/
def typedRegion (atoms : List Atom) (op : String) (args : List Atom) : Bool :=
  match measuredSignature op with
  | none => false
  | some (params, _) =>
      params.length == args.length &&
        (params.zip args).all (fun p => isTypeVariable p.1 || (argumentTypes atoms p.2).all (· == p.1)) &&
        (sharedTypes atoms params args).all fun τ => (sharedTypes atoms params args).all (· == τ)

/-- **The region outside which the model's untyped grounded calls are not HE's** (agreement inside
it is measured, not proved): the operation is one of HE's,
the call has as many arguments as its type has parameters, and each argument has no type in the
program or the type the operation declares at its position; at `==`'s type variable the typed
arguments agree. The test reads the argument values the model's machine hands to the table. HE
checks the arguments as written, before evaluating them, so an argument that is a call of a
function with a declared result type is read by that type; the region is stated on calls whose
arguments, as written, are values, calls of undeclared functions, or calls whose declared result
type is the parameter's type (as in every named theorem that states it: `(+ (* 2 3) 1)` has the
argument `(* 2 3)`, of result type `Number`). -/
def TypedRegion (atoms : List Atom) (op : String) (args : List Atom) : Prop :=
  typedRegion atoms op args = true

instance (atoms : List Atom) (op : String) (args : List Atom) : Decidable (TypedRegion atoms op args) :=
  inferInstanceAs (Decidable (_ = true))

/-- Positive and negative instances of the region, each a measured row. -/
theorem typedRegion_examples :
    TypedRegion [] "+" [num 4, num 4] ∧ TypedRegion [] "+" [.symbol "a", num 4] ∧
      TypedRegion [.expression [.symbol ":", .symbol "n", .symbol "Number"]] "+" [.symbol "n", num 4] ∧
      TypedRegion [] "==" [.symbol "a", num 5] ∧
      TypedRegion [.expression [.symbol ":", .symbol "c", .symbol "Color"]] "==" [.symbol "c", .symbol "c"] ∧
      ¬ TypedRegion [] "+" [num 1, .grounded (.bool true)] ∧ ¬ TypedRegion [] "+" [num 1] ∧
      ¬ TypedRegion [.expression [.symbol ":", .symbol "c", .symbol "Color"]] "+" [.symbol "c", num 4] ∧
      ¬ TypedRegion [] "==" [num 5, .grounded (.bool true)] ∧
      ¬ TypedRegion [.expression [.symbol ":", .symbol "c", .symbol "Color"]] "==" [.symbol "c", num 5] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

#print axioms he_int_op
#print axioms he_outcome_exact
#print axioms petta_int_op
#print axioms measured_outcome_exact
#print axioms measured_agrees
#print axioms division_agrees
#print axioms modulo_agrees
#print axioms tables_part
#print axioms not_in_measured
#print axioms cons_not_measured
#print axioms modulo_sign_differs
#print axioms division_truncates
#print axioms petta_model_lacks_division
#print axioms division_by_zero_differs
#print axioms overflow_differs
#print axioms equality_on_symbols_agrees
#print axioms non_numeric_differs
#print axioms non_ground_differs
#print axioms GroundedTable.answers_unique
#print axioms GroundedTable.answers_not_declines
#print axioms GroundedTable.answers_not_errs
#print axioms GroundedTable.declines_not_errs
#print axioms modelTable_dispatch
#print axioms measuredTable_dispatch
#print axioms model_answers
#print axioms measured_answers
#print axioms verdicts_part
#print axioms execute_grounded
#print axioms model_contract
#print axioms measuredOutcome_cases
#print axioms measured_contract
#print axioms typedRegion_examples

end GroundedTables

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
