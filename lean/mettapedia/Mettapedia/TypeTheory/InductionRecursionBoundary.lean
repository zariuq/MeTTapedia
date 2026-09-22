import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-!
# Induction does not by itself license recursive equations

A seed and successor can satisfy the full natural-number-shaped predicate
induction principle without being free constructors. Boolean negation supplies
a concrete example: every Boolean is reached from false, and negation is
injective, but its two-cycle makes the usual height recursion inconsistent.

Thus extracting apparent constructors from an authored induction principle is
not sufficient evidence for admitting arbitrary structural recursion equations.
The counterexample uses a true induction principle, not an assumed false axiom.
The positive control constructs and uniquely characterizes an actual fold on
the natural numbers. These are mathematical admission boundaries, not a claim
about the behavior of any implementation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.InductionRecursionBoundary

universe u v

/-- Predicate induction for a seed and a unary operation; no constructor
disjointness or recursion principle is included in this property. -/
def PredicateInduction {A : Type u} (zero : A) (succ : A → A) : Prop :=
  ∀ predicate : A → Prop, predicate zero →
    (∀ value, predicate value → predicate (succ value)) →
    ∀ value, predicate value

/-- Predicate induction says precisely that every element is reached by some
finite iteration. It does not say that the number of iterations is unique. -/
theorem induction_iff_generated {A : Type u} (zero : A) (succ : A → A) :
    PredicateInduction zero succ ↔
      ∀ value, ∃ count : Nat, succ^[count] zero = value := by
  constructor
  · intro induction
    apply induction (fun value => ∃ count : Nat, succ^[count] zero = value)
    · exact ⟨0, rfl⟩
    · rintro value ⟨count, rfl⟩
      exact ⟨count + 1, Function.iterate_succ_apply' succ count zero⟩
  · intro generated predicate atZero atSucc value
    obtain ⟨count, rfl⟩ := generated value
    induction count with
    | zero => exact atZero
    | succ count ih =>
      rw [Function.iterate_succ_apply']
      exact atSucc _ ih

/-- False and negation satisfy the full predicate induction principle. -/
theorem boolean_induction : PredicateInduction false Bool.not := by
  intro predicate atFalse atNot value
  cases value with
  | false => exact atFalse
  | true => exact atNot false atFalse

/-- The counterexample even has an injective successor. -/
theorem boolean_successor_injective : Function.Injective Bool.not := by
  intro left right equal
  have twice := congrArg Bool.not equal
  simpa using twice

/-- What fails is freeness: the seed is itself a successor. -/
theorem boolean_seed_is_successor : Bool.not true = false := rfl

theorem boolean_cycle : Bool.not^[2] false = false := rfl

/-- A height equation counts every application of the proposed successor. -/
theorem height_iterate {A : Type u} (succ : A → A) (height : A → Nat)
    (step : ∀ value, height (succ value) = height value + 1)
    (count : Nat) (value : A) :
    height (succ^[count] value) = height value + count := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [Function.iterate_succ_apply', step, ih]
    exact Nat.add_assoc _ _ _

/-- Any positive cycle obstructs the height equations, independently of the
chosen base value. -/
theorem cycle_has_no_height {A : Type u} (succ : A → A) (value : A)
    (count : Nat) (positive : 0 < count) (cycle : succ^[count] value = value) :
    ¬ ∃ height : A → Nat,
      ∀ point, height (succ point) = height point + 1 := by
  rintro ⟨height, step⟩
  have counted := height_iterate succ height step count value
  rw [cycle] at counted
  omega

/-- The natural-number recursion equations cannot be imposed on these true
induction data. In particular, the obstruction is not a missing proof search. -/
theorem boolean_induction_does_not_admit_height :
    ¬ ∃ height : Bool → Nat, height false = 0 ∧
      ∀ value, height (Bool.not value) = height value + 1 := by
  rintro ⟨height, _base, step⟩
  exact cycle_has_no_height Bool.not false 2 (by decide) boolean_cycle
    ⟨height, step⟩

/-- A real recursively constructed fold, over free natural-number
constructors rather than an arbitrary induction presentation. -/
def natFold {B : Type v} (base : B) (step : B → B) : Nat → B
  | 0 => base
  | count + 1 => step (natFold base step count)

@[simp] theorem natFold_zero {B : Type v} (base : B) (step : B → B) :
    natFold base step 0 = base := rfl

@[simp] theorem natFold_succ {B : Type v} (base : B) (step : B → B) (count : Nat) :
    natFold base step (count + 1) = step (natFold base step count) := rfl

/-- The actual recursion equations determine the fold uniquely. -/
theorem natFold_unique {B : Type v} (base : B) (step : B → B) (candidate : Nat → B)
    (atZero : candidate 0 = base)
    (atSucc : ∀ count, candidate (count + 1) = step (candidate count)) :
    candidate = natFold base step := by
  funext count
  induction count with
  | zero => exact atZero
  | succ count ih => simp only [atSucc, natFold_succ, ih]

theorem natural_recursion_control :
    ∃ height : Nat → Nat, height 0 = 0 ∧
      ∀ value, height (value + 1) = height value + 1 :=
  ⟨natFold 0 (fun value => value + 1), rfl, fun _ => rfl⟩

theorem natural_height_values :
    natFold 0 (fun value => value + 1) 5 = 5 := rfl

#print axioms induction_iff_generated
#print axioms boolean_induction_does_not_admit_height
#print axioms natFold_unique

end Mettapedia.TypeTheory.InductionRecursionBoundary
