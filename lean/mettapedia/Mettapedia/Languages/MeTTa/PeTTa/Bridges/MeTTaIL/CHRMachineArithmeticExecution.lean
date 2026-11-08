import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineValueExecution
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Tactic.Ring

/-! The CHR machine source executes as `Mettapedia.Languages.CHR.Machine`:
integer arithmetic. Quotient and remainder come from the long division of
the magnitudes and truncate toward zero; modulo is the target's floor
remainder; expressions evaluate as `CHR.IntExpr.eval`. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Mettapedia.Languages.MeTTa.PeTTa.Eval
open Mettapedia.Languages.MeTTa.PeTTa.BridgeKit
open WireKit StrictCallKit CHRMachineSource
open Mettapedia.Languages.CHR (Value Term Environment IntOperator IntExpr Comparison ArithmeticFault)

/-! ## Integer facts -/

theorem tdiv_natAbs (a b : Int) :
    a.tdiv b = if (decide (a < 0) = decide (b < 0)) then ((a.natAbs / b.natAbs : Nat) : Int)
      else -((a.natAbs / b.natAbs : Nat) : Int) := by
  rcases a with m | m <;> rcases b with n | n <;> simp [Int.tdiv, Int.natAbs, Int.negSucc_lt_zero]
  intro different
  exact absurd ⟨fun negative => by omega, fun negative => by omega⟩ different

theorem tmod_natAbs (a b : Int) :
    a.tmod b = if a < 0 then -((a.natAbs % b.natAbs : Nat) : Int) else ((a.natAbs % b.natAbs : Nat) : Int) := by
  rcases a with m | m <;> rcases b with n | n <;> simp [Int.tmod, Int.natAbs, Int.negSucc_lt_zero]

theorem modulo_fmod (a b : Int) :
    (if b < 0 ∧ a % b ≠ 0 then a % b + b else a % b) = a.fmod b := by
  rw [Int.fmod_eq_emod]
  split_ifs <;> omega

/-! ## Encodings -/

def pairAtom (first second : Atom) : Atom := .expression [.symbol "ChrPair", first, second]

def operatorAtom : IntOperator → Atom
  | .add => .symbol "ChrAdd"
  | .subtract => .symbol "ChrSubtract"
  | .multiply => .symbol "ChrMultiply"
  | .quotient => .symbol "ChrQuotient"
  | .remainder => .symbol "ChrRemainder"
  | .modulo => .symbol "ChrModulo"

def expressionAtom : IntExpr → Atom
  | .literal value => .expression [.symbol "ChrLiteral", integer value]
  | .index index => .expression [.symbol "ChrIndex", integer index]
  | .operation operator left right =>
    .expression [.symbol "ChrOperation", operatorAtom operator, expressionAtom left, expressionAtom right]

def faultAtom : ArithmeticFault → Atom
  | .unbound index => .expression [.symbol "ChrUnbound", integer index]
  | .nonInteger value => .expression [.symbol "ChrNonInteger", valueAtom value]
  | .uninstantiated term => .expression [.symbol "ChrUninstantiated", termAtom term]
  | .divisionByZero => .symbol "ChrDivisionByZero"

def exceptAtom {α : Type} (encode : α → Atom) : Except ArithmeticFault α → Atom
  | .ok value => .expression [.symbol "ChrOk", encode value]
  | .error reason => .expression [.symbol "ChrFault", faultAtom reason]

def comparisonAtom : Comparison → Atom
  | .equal => .symbol "ChrEqual"
  | .different => .symbol "ChrDifferent"
  | .less => .symbol "ChrLess"
  | .lessEqual => .symbol "ChrLessEqual"
  | .greater => .symbol "ChrGreater"
  | .greaterEqual => .symbol "ChrGreaterEqual"

theorem boolean_decide (first second : Bool) :
    decide (Effects.boolean first = Effects.boolean second) = decide (first = second) := by
  apply decide_eq_decide.mpr
  simp [Effects.boolean]

/-! ## Magnitude and long division -/

theorem magnitude_returns (caller : Subst) (state : State) (code : Atom) (number : Int)
    (one : Returns caller state code (integer number)) :
    Returns caller state (apply "gslt:chr-machine:magnitude" [code]) (integer (number.natAbs : Int)) := by
  machine_call (.cons one .nil)
  apply pure_if_returns _ _ _ _ (decide (number < 0)) _ _ _
    (integer_lt_returns runtime _ state _ _ number 0 bound (integer_returns runtime _ state 0))
  by_cases negative : number < 0
  · simp only [negative, decide_true, ↓reduceIte]
    have same : ((number.natAbs : Nat) : Int) = 0 - number := by omega
    rw [same]
    exact integer_sub_returns runtime _ state _ _ 0 number (integer_returns runtime _ state 0) bound
  · simp only [negative, decide_false, Bool.false_eq_true, ↓reduceIte]
    have same : ((number.natAbs : Nat) : Int) = number := by omega
    rw [same]
    exact bound

theorem divide_bounded_returns (state : State) :
    ∀ (measure dividend divisor : Nat) (caller : Subst) (left right : Atom),
      dividend + 1 - divisor ≤ measure → 0 < divisor →
      Returns caller state left (integer dividend) → Returns caller state right (integer divisor) →
      Returns caller state (apply "gslt:chr-machine:divide" [left, right])
        (pairAtom (integer (dividend / divisor : Nat)) (integer (dividend % divisor : Nat)))
  | measure, dividend, divisor, caller, left, right, bounded, positive, one, two => by
    machine_call (.cons one (.cons two .nil))
    apply pure_if_returns _ _ _ _ (decide ((dividend : Int) < divisor)) _ _ _
      (integer_lt_returns runtime _ state _ _ dividend divisor bound bound)
    by_cases small : dividend < divisor
    · have cast : (dividend : Int) < divisor := by omega
      simp only [cast, decide_true, ↓reduceIte]
      rw [Nat.div_eq_of_lt small, Nat.mod_eq_of_lt small]
      exact make_returns _ _ "ChrPair" _ _ inert (.cons (integer_returns runtime _ state 0) (.cons bound .nil))
    · have cast : ¬ (dividend : Int) < divisor := by omega
      simp only [cast, decide_false, Bool.false_eq_true, ↓reduceIte]
      cases measure with
      | zero => omega
      | succ smaller =>
        have recursive := divide_bounded_returns state smaller dividend (divisor + divisor)
        have key := Nat.div_add_mod dividend (divisor + divisor)
        have below := Nat.mod_lt dividend (show divisor + divisor > 0 by omega)
        generalize dividend / (divisor + divisor) = quotient at key recursive
        generalize dividend % (divisor + divisor) = remainder at key below recursive
        machine_case (recursive _ _ _ (by omega) (by omega) bound (by
            rw [show ((divisor + divisor : Nat) : Int) = (divisor : Int) + (divisor : Int) by push_cast; ring]
            exact integer_add_returns runtime _ state _ _ divisor divisor bound bound))
          unfolding [pairAtom]
        apply pure_if_returns _ _ _ _ (decide ((remainder : Int) < divisor)) _ _ _
          (integer_lt_returns runtime _ state _ _ remainder divisor bound bound)
        by_cases low : remainder < divisor
        · have facts : dividend / divisor = quotient + quotient ∧ dividend % divisor = remainder :=
            (Nat.div_mod_unique positive).mpr ⟨by rw [← key]; ring, low⟩
          have lowCast : (remainder : Int) < divisor := by omega
          simp only [lowCast, decide_true, ↓reduceIte]
          rw [facts.1, facts.2]
          refine make_returns _ _ "ChrPair" _ _ inert (.cons ?_ (.cons bound .nil))
          rw [show ((quotient + quotient : Nat) : Int) = (quotient : Int) + (quotient : Int) by push_cast; ring]
          exact integer_add_returns runtime _ state _ _ quotient quotient bound bound
        · have facts : dividend / divisor = quotient + quotient + 1 ∧ dividend % divisor = remainder - divisor :=
            (Nat.div_mod_unique positive).mpr ⟨by rw [← key]; zify [show divisor ≤ remainder by omega]; ring,
              by omega⟩
          have highCast : ¬ (remainder : Int) < divisor := by omega
          simp only [highCast, decide_false, Bool.false_eq_true, ↓reduceIte]
          rw [facts.1, facts.2]
          refine make_returns _ _ "ChrPair" _ _ inert (.cons ?_ (.cons ?_ .nil))
          · rw [show ((quotient + quotient + 1 : Nat) : Int) = ((quotient : Int) + (quotient : Int)) + 1 by
              push_cast; ring]
            exact integer_add_returns runtime _ state _ _ _ 1
              (integer_add_returns runtime _ state _ _ quotient quotient bound bound) (integer_returns runtime _ state 1)
          · rw [show ((remainder - divisor : Nat) : Int) = (remainder : Int) - (divisor : Int) by omega]
            exact integer_sub_returns runtime _ state _ _ remainder divisor bound bound

theorem divide_returns (caller : Subst) (state : State) (left right : Atom) (dividend divisor : Nat)
    (positive : 0 < divisor) (one : Returns caller state left (integer dividend))
    (two : Returns caller state right (integer divisor)) :
    Returns caller state (apply "gslt:chr-machine:divide" [left, right])
      (pairAtom (integer (dividend / divisor : Nat)) (integer (dividend % divisor : Nat))) :=
  divide_bounded_returns state (dividend + 1 - divisor) dividend divisor caller left right le_rfl positive one two

/-- Truncating quotient and remainder. -/
theorem truncate_returns (caller : Subst) (state : State) (left right : Atom) (first second : Int)
    (nonzero : second ≠ 0) (one : Returns caller state left (integer first))
    (two : Returns caller state right (integer second)) :
    Returns caller state (apply "gslt:chr-machine:truncate" [left, right])
      (pairAtom (integer (first.tdiv second)) (integer (first.tmod second))) := by
  machine_call (.cons one (.cons two .nil))
  rw [tdiv_natAbs, tmod_natAbs]
  have divided : ∀ (caller : Subst) (left right : Atom),
      Returns caller state left (integer (first.natAbs : Int)) →
      Returns caller state right (integer (second.natAbs : Int)) →
      Returns caller state (apply "gslt:chr-machine:divide" [left, right])
        (pairAtom (integer ((first.natAbs / second.natAbs : Nat) : Int))
          (integer ((first.natAbs % second.natAbs : Nat) : Int))) :=
    fun caller left right one two => divide_returns caller state left right _ _ (by omega) one two
  generalize first.natAbs / second.natAbs = quotient at divided ⊢
  generalize first.natAbs % second.natAbs = remainder at divided ⊢
  machine_case (divided _ _ _ (magnitude_returns _ state _ first bound) (magnitude_returns _ state _ second bound))
    unfolding [pairAtom]
  refine make_returns _ _ "ChrPair" _ _ inert (.cons ?_ (.cons ?_ .nil))
  · apply pure_if_returns _ _ _ _
      (decide (Effects.boolean (decide (first < 0)) = Effects.boolean (decide (second < 0)))) _ _ _
      (equal_returns _ _ _ _ _ _
        (integer_lt_returns runtime _ state _ _ first 0 bound (integer_returns runtime _ state 0))
        (integer_lt_returns runtime _ state _ _ second 0 bound (integer_returns runtime _ state 0)))
    rw [boolean_decide]
    by_cases same : decide (first < 0) = decide (second < 0)
    · simp only [same, decide_true, ↓reduceIte]
      exact bound
    · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [show -((quotient : Nat) : Int) = 0 - ((quotient : Nat) : Int) by ring]
      exact integer_sub_returns runtime _ state _ _ 0 _ (integer_returns runtime _ state 0) bound
  · apply pure_if_returns _ _ _ _ (decide (first < 0)) _ _ _
      (integer_lt_returns runtime _ state _ _ first 0 bound (integer_returns runtime _ state 0))
    by_cases negative : first < 0
    · simp only [negative, decide_true, ↓reduceIte]
      rw [show -((remainder : Nat) : Int) = 0 - ((remainder : Nat) : Int) by ring]
      exact integer_sub_returns runtime _ state _ _ 0 _ (integer_returns runtime _ state 0) bound
    · simp only [negative, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact bound

theorem integer_decide (first second : Int) :
    decide (integer first = integer second) = decide (first = second) := by
  apply decide_eq_decide.mpr
  simp [integer]

/-! ## Operators, integer values, expressions and comparisons -/

theorem operate_returns (caller : Subst) (state : State) (code left right : Atom) (operator : IntOperator)
    (first second : Int) (zero : Returns caller state code (operatorAtom operator))
    (one : Returns caller state left (integer first)) (two : Returns caller state right (integer second)) :
    Returns caller state (apply "gslt:chr-machine:operate" [code, left, right])
      (exceptAtom integer (operator.eval first second)) := by
  machine_call (.cons zero (.cons one (.cons two .nil)))
  cases operator with
  | add =>
    machine_case (bound) unfolding [operatorAtom]
    exact make_returns _ _ "ChrOk" _ _ inert (.cons (integer_add_returns runtime _ state _ _ first second bound bound) .nil)
  | subtract =>
    machine_case (bound) unfolding [operatorAtom]
    exact make_returns _ _ "ChrOk" _ _ inert (.cons (integer_sub_returns runtime _ state _ _ first second bound bound) .nil)
  | multiply =>
    machine_case (bound) unfolding [operatorAtom]
    exact make_returns _ _ "ChrOk" _ _ inert (.cons (integer_mul_returns _ state _ _ first second bound bound) .nil)
  | quotient =>
    machine_case (bound) unfolding [operatorAtom]
    apply pure_if_returns _ _ _ _ (decide (integer second = integer 0)) _ _ _
      (equal_returns _ _ _ _ _ _ bound (integer_returns runtime _ state 0))
    rw [integer_decide]
    by_cases nonzero : second = 0
    · simp only [nonzero, decide_true, ↓reduceIte, IntOperator.eval, exceptAtom, faultAtom]
      exact make_returns _ _ "ChrFault" _ _ inert (.cons (Eval.symbol_returns runtime _ state _) .nil)
    · simp only [nonzero, decide_false, Bool.false_eq_true, ↓reduceIte, IntOperator.eval, exceptAtom]
      have truncated := fun (caller : Subst) (left right : Atom) one two =>
        truncate_returns caller state left right first second nonzero one two
      generalize first.tdiv second = quotient at truncated ⊢
      generalize first.tmod second = remainder at truncated
      machine_case (truncated _ _ _ bound bound) unfolding [pairAtom]
      exact make_returns _ _ "ChrOk" _ _ inert (.cons bound .nil)
  | remainder =>
    machine_case (bound) unfolding [operatorAtom]
    apply pure_if_returns _ _ _ _ (decide (integer second = integer 0)) _ _ _
      (equal_returns _ _ _ _ _ _ bound (integer_returns runtime _ state 0))
    rw [integer_decide]
    by_cases nonzero : second = 0
    · simp only [nonzero, decide_true, ↓reduceIte, IntOperator.eval, exceptAtom, faultAtom]
      exact make_returns _ _ "ChrFault" _ _ inert (.cons (Eval.symbol_returns runtime _ state _) .nil)
    · simp only [nonzero, decide_false, Bool.false_eq_true, ↓reduceIte, IntOperator.eval, exceptAtom]
      have truncated := fun (caller : Subst) (left right : Atom) one two =>
        truncate_returns caller state left right first second nonzero one two
      generalize first.tdiv second = quotient at truncated
      generalize first.tmod second = remainder at truncated ⊢
      machine_case (truncated _ _ _ bound bound) unfolding [pairAtom]
      exact make_returns _ _ "ChrOk" _ _ inert (.cons bound .nil)
  | modulo =>
    machine_case (bound) unfolding [operatorAtom]
    apply pure_if_returns _ _ _ _ (decide (integer second = integer 0)) _ _ _
      (equal_returns _ _ _ _ _ _ bound (integer_returns runtime _ state 0))
    rw [integer_decide]
    by_cases nonzero : second = 0
    · simp only [nonzero, decide_true, ↓reduceIte, IntOperator.eval, exceptAtom, faultAtom]
      exact make_returns _ _ "ChrFault" _ _ inert (.cons (Eval.symbol_returns runtime _ state _) .nil)
    · simp only [nonzero, decide_false, Bool.false_eq_true, ↓reduceIte, IntOperator.eval, exceptAtom]
      rw [modulo_fmod]
      exact make_returns _ _ "ChrOk" _ _ inert (.cons (integer_mod_returns _ state _ _ first second nonzero bound bound) .nil)

/-- A value as an integer, as `CHR.IntExpr.eval` reads a bound variable. -/
def integerOf : Value → Except ArithmeticFault Int
  | .integer number => .ok number
  | value => .error (.nonInteger value)

theorem integer_check_returns (caller : Subst) (state : State) (code : Atom) (value : Value)
    (one : Returns caller state code (valueAtom value)) :
    Returns caller state (apply "gslt:chr-machine:integer" [code]) (exceptAtom integer (integerOf value)) := by
  machine_call (.cons one .nil)
  cases value with
  | integer number =>
    machine_case (bound)
    apply pure_if_returns _ _ _ _ (decide ((.symbol "Number" : Atom) = .symbol "Number")) _ _ _
      (equal_returns _ _ _ _ _ _ (number_type_returns _ state _ number bound) (Eval.symbol_returns runtime _ state _))
    simp only [decide_true, ↓reduceIte, integerOf, exceptAtom]
    exact make_returns _ _ "ChrOk" _ _ inert (.cons bound .nil)
  | atom name =>
    machine_case (bound)
    apply pure_if_returns _ _ _ _ (decide ((.symbol "String" : Atom) = .symbol "Number")) _ _ _
      (equal_returns _ _ _ _ _ _ (string_type_returns _ state _ name bound) (Eval.symbol_returns runtime _ state _))
    have different : decide ((.symbol "String" : Atom) = .symbol "Number") = false := by decide
    simp only [different, Bool.false_eq_true, ↓reduceIte, integerOf, exceptAtom, faultAtom]
    exact make_returns _ _ "ChrFault" _ _ inert (.cons (make_returns _ _ "ChrNonInteger" _ _ inert (.cons bound .nil)) .nil)
  | tuple fields =>
    machine_case (bound)
    simp only [integerOf, exceptAtom, faultAtom]
    exact make_returns _ _ "ChrFault" _ _ inert (.cons (make_returns _ _ "ChrNonInteger" _ _ inert (.cons bound .nil)) .nil)

theorem eval_index (environment : Environment) (index : Nat) :
    (IntExpr.index index).eval environment =
      match Mettapedia.Languages.CHR.lookup environment index with
      | none => .error (.unbound index)
      | some value => integerOf value := by
  simp only [IntExpr.eval]
  cases Mettapedia.Languages.CHR.lookup environment index with
  | none => rfl
  | some value => cases value <;> rfl

theorem eval_returns (state : State) :
    ∀ (expression : IntExpr) (environment : Environment) (caller : Subst) (first second : Atom),
      Returns caller state first (expressionAtom expression) →
      Returns caller state second (environmentAtom environment) →
      Returns caller state (apply "gslt:chr-machine:eval" [first, second])
        (exceptAtom integer (expression.eval environment))
  | .literal value, environment, caller, first, second, one, two => by
    machine_call (.cons one (.cons two .nil))
    machine_case (bound) unfolding [expressionAtom]
    simp only [IntExpr.eval, exceptAtom]
    exact make_returns _ _ "ChrOk" _ _ inert (.cons bound .nil)
  | .index index, environment, caller, first, second, one, two => by
    machine_call (.cons one (.cons two .nil))
    machine_case (bound) unfolding [expressionAtom]
    rw [eval_index]
    have looked := lookup_returns state index environment
    cases found : Mettapedia.Languages.CHR.lookup environment index with
    | none =>
      rw [found] at looked
      machine_case (looked _ _ _ bound bound)
      simp only [exceptAtom, faultAtom]
      exact make_returns _ _ "ChrFault" _ _ inert (.cons (make_returns _ _ "ChrUnbound" _ _ inert (.cons bound .nil)) .nil)
    | some value =>
      rw [found] at looked
      machine_case (looked _ _ _ bound bound)
      exact integer_check_returns _ state _ value bound
  | .operation operator left right, environment, caller, first, second, one, two => by
    machine_call (.cons one (.cons two .nil))
    machine_case (bound) unfolding [expressionAtom]
    have leftEval := eval_returns state left environment
    cases leftResult : left.eval environment with
    | error reason =>
      rw [leftResult] at leftEval
      machine_case (leftEval _ _ _ bound bound) unfolding [exceptAtom]
      simp only [IntExpr.eval, leftResult, exceptAtom]
      exact make_returns _ _ "ChrFault" _ _ inert (.cons bound .nil)
    | ok a =>
      rw [leftResult] at leftEval
      machine_case (leftEval _ _ _ bound bound) unfolding [exceptAtom]
      have rightEval := eval_returns state right environment
      cases rightResult : right.eval environment with
      | error reason =>
        rw [rightResult] at rightEval
        machine_case (rightEval _ _ _ bound bound) unfolding [exceptAtom]
        simp only [IntExpr.eval, leftResult, rightResult, exceptAtom]
        exact make_returns _ _ "ChrFault" _ _ inert (.cons bound .nil)
      | ok b =>
        rw [rightResult] at rightEval
        machine_case (rightEval _ _ _ bound bound) unfolding [exceptAtom]
        simp only [IntExpr.eval, leftResult, rightResult]
        exact operate_returns _ state _ _ _ operator a b bound bound bound

theorem holds_returns (caller : Subst) (state : State) (code left right : Atom) (comparison : Comparison)
    (first second : Int) (zero : Returns caller state code (comparisonAtom comparison))
    (one : Returns caller state left (integer first)) (two : Returns caller state right (integer second)) :
    Returns caller state (apply "gslt:chr-machine:holds" [code, left, right])
      (Effects.boolean (comparison.holds first second)) := by
  machine_call (.cons zero (.cons one (.cons two .nil)))
  have equality : decide (first = second) = (first == second) := Bool.eq_iff_iff.mpr (by simp)
  cases comparison with
  | equal =>
    machine_case (bound) unfolding [comparisonAtom]
    simp only [Comparison.holds]
    rw [← equality, ← integer_decide]
    exact equal_returns _ state _ _ _ _ bound bound
  | different =>
    machine_case (bound) unfolding [comparisonAtom]
    simp only [Comparison.holds, bne]
    rw [← equality, ← integer_decide]
    exact not_returns _ state _ _ (equal_returns _ state _ _ _ _ bound bound)
  | less =>
    machine_case (bound) unfolding [comparisonAtom]
    exact integer_lt_returns runtime _ state _ _ first second bound bound
  | lessEqual =>
    machine_case (bound) unfolding [comparisonAtom]
    exact integer_le_returns _ state _ _ first second bound bound
  | greater =>
    machine_case (bound) unfolding [comparisonAtom]
    exact integer_gt_returns _ state _ _ first second bound bound
  | greaterEqual =>
    machine_case (bound) unfolding [comparisonAtom]
    exact integer_ge_returns _ state _ _ first second bound bound

#print axioms magnitude_returns
#print axioms operate_returns
#print axioms integer_check_returns
#print axioms eval_returns
#print axioms holds_returns
#print axioms divide_returns
#print axioms truncate_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution
