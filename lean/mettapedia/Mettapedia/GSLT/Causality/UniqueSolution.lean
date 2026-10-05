import Mettapedia.GSLT.Causality.StructuralModels

/-!
# Mechanisms with one solution under every surgery

Halpern, *Actual Causality* (MIT Press, 2016), §2.7 (“Causality in Nonrecursive
Models”), states the general nonrecursive reading and the point at which it
collapses to the recursive one. Two sentences fix the class defined here.

* p. 56: “In nonrecursive models, there may be more than one solution to an
  equation in a given context, or there may be none.”
* p. 57: “However, with nonrecursive models, there may be several solutions;
  AC2(a) holds if φ does not hold in at least one of them.” The same page:
  “Clearly, in the recursive case, where there is only one solution, this
  definition agrees with the definition given earlier.”

`UniqueUnderEverySurgery` is the intermediate class on which those two readings
coincide for every surgery: every setting of the endogenous keys has exactly
one solution. A context, in the sense of a separate exogenous assignment, is
not a sort of `Mechanisms`; the mechanisms are already the equations, and a
setting of endogenous keys is a surgery.

* Recursive mechanisms are in the class whenever a store exists to seed
  `surgery_exists_unique_solution`. The seed is necessary: a recursive
  signature over the empty value type has no solution.
* The inclusion is strict. `cycle` has each cell depend on the other, one
  solution under every surgery, and no rank witnessing `Recursive`.
* The class sits strictly below every mechanism. `copyLoop` has two solutions
  of the empty surgery, and `negLoop` has none.
* The class is closed under surgery, because a surgery of a surgery is one
  surgery of the original (`override`).
* What uniqueness buys, without choosing a store: a property holds of some
  solution of a surgery if and only if it holds of every solution, and each
  key has one counterfactual value.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.UniqueSolution

open Mettapedia.GSLT.Causality.StructuralModels
open Mettapedia.GSLT.Causality.ContextBindings

variable {Key : Type} {Value : Type}

/-- One solution under every surgery: every setting of the endogenous keys. -/
def UniqueUnderEverySurgery (mechanisms : Mechanisms Key Value) : Prop :=
  ∀ assignment : Key → Option Value, ∃! store, IsSolution (surgery assignment mechanisms) store

variable {mechanisms : Mechanisms Key Value}

/-- **Recursive mechanisms are in the class** once a store exists. The seed is
the store `surgery_exists_unique_solution` iterates from; the solution itself
does not depend on which store is supplied. -/
theorem recursive_unique_under_every_surgery (recursive : Recursive mechanisms)
    (seed : Key → Value) : UniqueUnderEverySurgery mechanisms :=
  fun assignment => surgery_exists_unique_solution recursive assignment seed

/-! ## The seed is necessary -/

/-- Mechanisms over the empty value type. There is no store. -/
def emptyMechanisms : Mechanisms Unit Empty :=
  fun _ store => nomatch (store ())

/-- The empty signature is recursive: every dependence claim is vacuous. -/
def emptyRecursive : Recursive emptyMechanisms where
  rank _ := 0
  bound := 1
  rank_lt _ := Nat.one_pos
  depends _ store _ _ := nomatch (store ())

/-- **A recursive signature need not lie in the class.** With no store there
is no solution, so the inclusion really does need a seed. -/
theorem empty_recursive_outside :
    Nonempty (Recursive emptyMechanisms) ∧ (UniqueUnderEverySurgery emptyMechanisms → False) := by
  refine ⟨⟨emptyRecursive⟩, ?_⟩
  intro unique
  obtain ⟨store, _, _⟩ := unique (fun _ => none)
  exact nomatch (store ())

/-! ## A mutual cycle with one solution -/

/-- Three values. The two constant maps are the only unary Boolean maps with
one fixed point, so a Boolean cycle cannot witness the strict inclusion. -/
inductive Tri where
  | a
  | b
  | c
  deriving DecidableEq

/-- The two cells of the cycle. -/
inductive Endo where
  | left
  | right
  deriving DecidableEq

/-- `left` reads `right`: `a ↦ a`, `b ↦ a`, `c ↦ c`. -/
def leftOf : Tri → Tri
  | .a => .a
  | .b => .a
  | .c => .c

/-- `right` reads `left`: `a ↦ a`, `b ↦ a`, `c ↦ b`. -/
def rightOf : Tri → Tri
  | .a => .a
  | .b => .a
  | .c => .b

/-- Each cell is the image of the other. Neither cell reads itself. -/
def cycle : Mechanisms Endo Tri
  | .left, store => leftOf (store .right)
  | .right, store => rightOf (store .left)

/-- The store with both cells `a`. -/
def bothA : Endo → Tri := fun _ => .a

theorem cycle_solution_iff (store : Endo → Tri) :
    IsSolution cycle store ↔ store .left = .a ∧ store .right = .a := by
  constructor
  · intro solution
    have leftEq := solution .left
    have rightEq := solution .right
    simp only [cycle] at leftEq rightEq
    cases hL : store .left with
    | a =>
        simp only [hL, rightOf] at rightEq
        exact ⟨rfl, rightEq⟩
    | b =>
        simp only [hL, rightOf] at rightEq
        simp only [rightEq, leftOf, hL] at leftEq
        cases leftEq
    | c =>
        simp only [hL, rightOf] at rightEq
        simp only [rightEq, leftOf, hL] at leftEq
        cases leftEq
  · rintro ⟨hL, hR⟩ key
    cases key <;> simp [cycle, leftOf, rightOf, hL, hR]

theorem cycle_empty_unique : ∃! store, IsSolution cycle store :=
  ⟨bothA, fun key => by cases key <;> rfl, fun store solution => by
    obtain ⟨hL, hR⟩ := (cycle_solution_iff store).mp solution
    funext key
    cases key with
    | left => exact hL
    | right => exact hR⟩

/-- The store surgery leaves behind. -/
def setPair (left right : Tri) : Endo → Tri
  | .left => left
  | .right => right

theorem cycle_surgery_unique (assignment : Endo → Option Tri) :
    ∃! store, IsSolution (surgery assignment cycle) store := by
  cases hL : assignment .left <;> cases hR : assignment .right
  · refine ⟨bothA, ?_, ?_⟩
    · intro key
      cases key <;> simp [surgery, cycle, leftOf, rightOf, bothA, hL, hR]
    · intro store solution
      have plain : IsSolution cycle store := by
        intro key
        have equation := solution key
        cases key <;> simpa [surgery, hL, hR] using equation
      obtain ⟨eqL, eqR⟩ := (cycle_solution_iff store).mp plain
      funext key
      cases key with
      | left => rw [eqL]; rfl
      | right => rw [eqR]; rfl
  · rename_i value
    refine ⟨setPair (leftOf value) value, ?_, ?_⟩
    · intro key
      cases key <;> simp [surgery, cycle, setPair, leftOf, hL, hR]
    · intro store solution
      have leftEq := solution .left
      have rightEq := solution .right
      simp only [surgery, hL, cycle] at leftEq
      simp only [surgery, hR] at rightEq
      funext key
      cases key <;> simp [setPair, leftEq, rightEq]
  · rename_i value
    refine ⟨setPair value (rightOf value), ?_, ?_⟩
    · intro key
      cases key <;> simp [surgery, cycle, setPair, rightOf, hL, hR]
    · intro store solution
      have leftEq := solution .left
      have rightEq := solution .right
      simp only [surgery, hL] at leftEq
      simp only [surgery, hR, cycle] at rightEq
      funext key
      cases key <;> simp [setPair, leftEq, rightEq]
  · rename_i value other
    refine ⟨setPair value other, ?_, ?_⟩
    · intro key
      cases key <;> simp [surgery, setPair, hL, hR]
    · intro store solution
      have leftEq := solution .left
      have rightEq := solution .right
      simp only [surgery, hL] at leftEq
      simp only [surgery, hR] at rightEq
      funext key
      cases key <;> simp [setPair, leftEq, rightEq]

/-- **`cycle` is in the class.** -/
theorem cycle_unique_under_every_surgery : UniqueUnderEverySurgery cycle :=
  cycle_surgery_unique

/-- `left` reads `right`: the two stores agree on `left` and differ on `right`. -/
theorem cycle_left_depends_on_right :
    ¬ DependsOnly (cycle .left) {other | other ≠ Endo.right} := by
  intro depends
  have same := depends bothA (fun key => match key with | .left => .a | .right => .c)
    (fun other member => by
      cases other with
      | left => rfl
      | right => exact absurd rfl member)
  have read : leftOf .a = leftOf .c := same
  cases read

/-- `right` reads `left`. -/
theorem cycle_right_depends_on_left :
    ¬ DependsOnly (cycle .right) {other | other ≠ Endo.left} := by
  intro depends
  have same := depends bothA (fun key => match key with | .left => .c | .right => .a)
    (fun other member => by
      cases other with
      | right => rfl
      | left => exact absurd rfl member)
  have read : rightOf .a = rightOf .c := same
  cases read

/-- **The cycle is not recursive.** A strict rank would make the lower cell
ignore the higher one, and equal ranks would make both cells ignore each
other. `leftOf` and `rightOf` are not constant. -/
theorem cycle_not_recursive (recursive : Recursive cycle) : False := by
  cases hLower : decide (recursive.rank .left < recursive.rank .right) with
  | true =>
      have lower := of_decide_eq_true hLower
      have same := recursive.depends .left bothA
        (fun key => match key with | .left => .a | .right => .c)
        (fun other smaller => by
          cases other with
          | left => exact absurd smaller (Nat.lt_irrefl _)
          | right => exact absurd (Nat.lt_trans smaller lower) (Nat.lt_irrefl _))
      have read : leftOf .a = leftOf .c := same
      cases read
  | false =>
      have notLower := of_decide_eq_false hLower
      cases hHigher : decide (recursive.rank .right < recursive.rank .left) with
      | true =>
          have higher := of_decide_eq_true hHigher
          have same := recursive.depends .right bothA
            (fun key => match key with | .left => .c | .right => .a)
            (fun other smaller => by
              cases other with
              | right => exact absurd smaller (Nat.lt_irrefl _)
              | left => exact absurd (Nat.lt_trans smaller higher) (Nat.lt_irrefl _))
          have read : rightOf .a = rightOf .c := same
          cases read
      | false =>
          have notHigher := of_decide_eq_false hHigher
          have equal : recursive.rank .left = recursive.rank .right :=
            Nat.le_antisymm (Nat.le_of_not_lt notHigher) (Nat.le_of_not_lt notLower)
          have same := recursive.depends .left bothA
            (fun key => match key with | .left => .a | .right => .c)
            (fun other smaller => by
              cases other with
              | left => exact absurd smaller (Nat.lt_irrefl _)
              | right =>
                  rw [equal] at smaller
                  exact absurd smaller (Nat.lt_irrefl _))
          have read : leftOf .a = leftOf .c := same
          cases read

/-- **The inclusion of recursive mechanisms is strict.** -/
theorem cycle_strict :
    UniqueUnderEverySurgery cycle ∧ (Recursive cycle → False) :=
  ⟨cycle_unique_under_every_surgery, cycle_not_recursive⟩

/-! ## Strictly below every mechanism -/

/-- **Copying lies outside the class**: the empty surgery has two solutions. -/
theorem copyLoop_outside : ¬ UniqueUnderEverySurgery copyLoop := by
  intro unique
  have some := unique (fun _ => none)
  rw [surgery_none] at some
  obtain ⟨_, _, only⟩ := some
  exact copyLoop_two_solutions.2.2
    ((only _ copyLoop_two_solutions.1).trans (only _ copyLoop_two_solutions.2.1).symm)

/-- **Negating lies outside the class**: the empty surgery has no solution. -/
theorem negLoop_outside : ¬ UniqueUnderEverySurgery negLoop := by
  intro unique
  have some := unique (fun _ => none)
  rw [surgery_none] at some
  obtain ⟨store, solution, _⟩ := some
  exact negLoop_no_solution store solution

/-- **The class is strictly below the general top.** -/
theorem below_every_mechanism :
    ¬ UniqueUnderEverySurgery copyLoop ∧ ¬ UniqueUnderEverySurgery negLoop :=
  ⟨copyLoop_outside, negLoop_outside⟩

/-! ## Closure -/

theorem isSolution_surgery_override (outer inner : Key → Option Value)
    (store : Key → Value) :
    IsSolution (surgery outer (surgery inner mechanisms)) store ↔
      IsSolution (surgery (override outer inner) mechanisms) store := by
  rw [← surgery_override]

/-- **The class is closed under surgery.** An outer surgery of an inner surgery
is the single surgery `override outer inner`. -/
theorem unique_closed_under_surgery (unique : UniqueUnderEverySurgery mechanisms)
    (inner : Key → Option Value) :
    UniqueUnderEverySurgery (surgery inner mechanisms) := by
  intro outer
  obtain ⟨store, solution, only⟩ := unique (override outer inner)
  refine ⟨store, (isSolution_surgery_override outer inner store).mpr solution, ?_⟩
  intro store' solution'
  exact only store' ((isSolution_surgery_override outer inner store').mp solution')

/-! ## What uniqueness buys -/

/-- **Some solution satisfies a property if and only if every solution does.**
This is the collapse in §2.7: “φ fails in one solution” and “φ fails in every
solution” are the same claim precisely on this class. The store is not chosen. -/
theorem some_solution_iff_every (unique : UniqueUnderEverySurgery mechanisms)
    (assignment : Key → Option Value) (property : (Key → Value) → Prop) :
    (∃ store, IsSolution (surgery assignment mechanisms) store ∧ property store) ↔
      ∀ store, IsSolution (surgery assignment mechanisms) store → property store := by
  constructor
  · intro ⟨store, solution, holds⟩ store' solution'
    obtain ⟨_, _, only⟩ := unique assignment
    have same : store' = store := (only store' solution').trans (only store solution).symm
    exact same ▸ holds
  · intro every
    obtain ⟨store, solution, _⟩ := unique assignment
    exact ⟨store, solution, every store solution⟩

/-- **Each key has one counterfactual value** under a surgery. The value is
named as the unique inhabitant of this property, not by choosing a store. -/
theorem counterfactual_exists_unique (unique : UniqueUnderEverySurgery mechanisms)
    (assignment : Key → Option Value) (key : Key) :
    ∃! value, ∀ store, IsSolution (surgery assignment mechanisms) store →
      store key = value := by
  obtain ⟨store, solution, only⟩ := unique assignment
  refine ⟨store key, ?holds, ?only⟩
  · intro store' solution'
    exact congrFun ((only store' solution').trans (only store solution).symm) key
  · intro value holds
    exact (holds store solution).symm

end Mettapedia.GSLT.Causality.UniqueSolution
