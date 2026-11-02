import Mettapedia.Algebra.TropicalAffineSummary
import Mettapedia.Machines.KeyedImprovement

/-!
# Inferring ordered, bag and set regimes for tropical updates

State, constants, shifts and minimum expressions compile to the existing
tropical affine monoid. Exact semantic tests distinguish cap maps and shift
maps; general expressions retain ordered composition. These regime permissions
concern final values, not productive-event counts or intermediate observations.

Two separately commutative families need not commute with each other. A mixed
cap/shift batch therefore retains order unless a stronger cross-family proof
is supplied. No theorem chooses a native implementation by cost alone.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TropicalRegionInference

open Mettapedia.Algebra Tropical

abbrev Value := WithTop Nat
abbrev Code := AffineSummary (Tropical Value)

inductive Expr
  | state
  | constant (value : Value)
  | shift (amount : Nat) (body : Expr)
  | minimum (left right : Expr)
  deriving DecidableEq

def Expr.eval : Expr → Value → Value
  | .state, value => value
  | .constant literal, _ => literal
  | .shift amount body, value => body.eval value + amount
  | .minimum left right, value => min (left.eval value) (right.eval value)

def compile : Expr → Code
  | .state => 1
  | .constant value => AffineSummary.constant (trop value)
  | .shift amount body => compile body * AffineSummary.minPlus amount ⊤
  | .minimum left right =>
      let a := compile left
      let b := compile right
      ⟨a.scale + b.scale, a.offset + b.offset⟩

theorem compile_sound (expression : Expr) (value : Value) :
    (compile expression).act (trop value) = trop (expression.eval value) := by
  induction expression with
  | state => simp [compile, Expr.eval]
  | constant literal => simp [compile, Expr.eval]
  | shift amount body ih =>
    simp [compile, Expr.eval, AffineSummary.act_mul, ih, AffineSummary.act_minPlus]
  | minimum left right ihl ihr =>
    rw [Expr.eval, trop_min, ← ihl, ← ihr]
    simp [compile, AffineSummary.act, add_mul, add_add_add_comm]

def execute (code : Code) (value : Value) : Value := untrop (code.act (trop value))
def shiftOf (code : Code) : Value := untrop code.scale
def capOf (code : Code) : Value := untrop code.offset

theorem execute_formula (code : Code) (value : Value) :
    execute code value = min (value + shiftOf code) (capOf code) := by
  simp [execute, shiftOf, capOf, AffineSummary.act, add_comm, min_comm]

def capType (code : Code) : Bool := decide (shiftOf code = 0 ∨ capOf code = 0)
def shiftType (code : Code) : Bool := decide (capOf code = ⊤)

/-- The cap test is semantic and exact, including expressions whose shifted
state is made irrelevant by a zero cap. -/
theorem capType_iff (code : Code) : capType code = true ↔
    ∀ value, execute code value = min value (capOf code) := by
  simp only [capType, decide_eq_true_eq]
  constructor
  · rintro (zero | zero) value <;> simp [execute_formula, zero]
  · intro cap
    have atZero := cap 0
    simp only [execute_formula, zero_add, zero_min] at atZero
    rcases le_total (shiftOf code) (capOf code) with ordered | ordered
    · left; simpa only [min_eq_left ordered] using atZero
    · right; simpa only [min_eq_right ordered] using atZero

theorem shiftType_iff (code : Code) : shiftType code = true ↔
    ∀ value, execute code value = value + shiftOf code := by
  simp only [shiftType, decide_eq_true_eq]
  constructor
  · intro top value; simp [execute_formula, top]
  · intro shift
    have atTop := shift ⊤
    simpa [execute_formula] using atTop

theorem cap_idempotent (code : Code) (typed : capType code = true) (value : Value) :
    execute code (execute code value) = execute code value := by
  simp [(capType_iff code).mp typed]

theorem caps_commute (first second : Code) (firstTyped : capType first = true)
    (secondTyped : capType second = true) (value : Value) :
    execute second (execute first value) = execute first (execute second value) := by
  simp only [(capType_iff first).mp firstTyped, (capType_iff second).mp secondTyped]
  exact min_right_comm _ _ _

theorem shifts_commute (first second : Code) (firstTyped : shiftType first = true)
    (secondTyped : shiftType second = true) (value : Value) :
    execute second (execute first value) = execute first (execute second value) := by
  simp only [(shiftType_iff first).mp firstTyped, (shiftType_iff second).mp secondTyped]
  exact add_right_comm _ _ _

inductive Regime
  | setCaps | bagShifts | orderedAffine
  deriving DecidableEq

def inferBatch (expressions : List Expr) : Regime :=
  if expressions.all (fun expression => capType (compile expression)) then .setCaps
  else if expressions.all (fun expression => shiftType (compile expression)) then .bagShifts
  else .orderedAffine

def sourceRun (expressions : List Expr) (value : Value) : Value :=
  expressions.foldl (fun state expression => expression.eval state) value

def summarize (expressions : List Expr) : Code := (expressions.map compile).prod

theorem summarize_sound (expressions : List Expr) (value : Value) :
    (summarize expressions).act (trop value) = trop (sourceRun expressions value) := by
  induction expressions generalizing value with
  | nil => simp [summarize, sourceRun]
  | cons expression rest ih =>
    simp only [summarize, List.map_cons, List.prod_cons, AffineSummary.act_mul, compile_sound,
      sourceRun, List.foldl_cons]
    exact ih (expression.eval value)

theorem summarize_append (first second : List Expr) :
    summarize (first ++ second) = summarize first * summarize second := by
  simp [summarize]

/-- All expressions remain executable through ordered summaries, even when
neither commutative family is admitted. -/
theorem ordered_execution_exact (expressions : List Expr) (value : Value) :
    execute (summarize expressions) value = sourceRun expressions value := by
  simp [execute, summarize_sound]

theorem setBatch_members (expressions : List Expr) (typed : inferBatch expressions = .setCaps) :
    ∀ expression ∈ expressions, capType (compile expression) = true := by
  unfold inferBatch at typed
  split at typed
  next all => exact List.all_eq_true.mp all
  next => split at typed <;> cases typed

theorem bagBatch_members (expressions : List Expr) (typed : inferBatch expressions = .bagShifts) :
    ∀ expression ∈ expressions, shiftType (compile expression) = true := by
  unfold inferBatch at typed
  split at typed
  next => cases typed
  next =>
    split at typed
    next all => exact List.all_eq_true.mp all
    next => cases typed

theorem cap_batch_perm {first second : List Expr} (typed : inferBatch first = .setCaps)
    (permutation : first.Perm second) (value : Value) : sourceRun first value = sourceRun second value := by
  apply permutation.foldl_eq'
  intro a ha b hb state
  simpa only [execute, compile_sound, untrop_trop] using
    caps_commute (compile a) (compile b) (setBatch_members first typed a ha) (setBatch_members first typed b hb) state

theorem shift_batch_perm {first second : List Expr} (typed : inferBatch first = .bagShifts)
    (permutation : first.Perm second) (value : Value) : sourceRun first value = sourceRun second value := by
  apply permutation.foldl_eq'
  intro a ha b hb state
  simpa only [execute, compile_sound, untrop_trop] using
    shifts_commute (compile a) (compile b) (bagBatch_members first typed a ha) (bagBatch_members first typed b hb) state

theorem cap_duplicate_erasure (expression : Expr) (typed : capType (compile expression) = true)
    (rest : List Expr) (value : Value) :
    sourceRun (expression :: expression :: rest) value = sourceRun (expression :: rest) value := by
  have same : expression.eval (expression.eval value) = expression.eval value := by
    simpa only [execute, compile_sound, untrop_trop] using cap_idempotent (compile expression) typed value
  simp only [sourceRun, List.foldl_cons, same]

namespace Controls

def capThree : Expr := .minimum .state (.constant 3)
def shiftFive : Expr := .shift 5 .state

theorem ordinary_cap_inferred : inferBatch [capThree, .minimum .state (.constant 7)] = .setCaps := by decide
theorem ordinary_shift_inferred : inferBatch [shiftFive, .shift 2 .state] = .bagShifts := by decide
theorem zero_cap_erases_shift : capType (compile (.minimum (.shift 123 .state) (.constant 0))) = true := by decide

theorem mixed_regimes_keep_order :
    inferBatch [capThree, shiftFive] = .orderedAffine ∧
    sourceRun [capThree, shiftFive] 0 = 5 ∧ sourceRun [shiftFive, capThree] 0 = 3 := by decide

theorem final_cap_values_do_not_preserve_improvement_flags :
    let start : KeyedImprovement.Store Unit Nat := fun _ => some 10
    (KeyedImprovement.improve (KeyedImprovement.improve start () 7).1 () 5).2 = true ∧
    (KeyedImprovement.improve (KeyedImprovement.improve start () 5).1 () 7).2 = false := by decide

end Controls
end Mettapedia.Machines.TropicalRegionInference
