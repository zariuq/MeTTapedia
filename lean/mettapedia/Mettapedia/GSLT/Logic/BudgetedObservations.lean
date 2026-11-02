import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

/-!
# Weighted contextual observations

A test's positive bounded weight determines how strongly its disagreement
counts. The supremum over all tests is an ultrapseudometric. Its zero kernel
depends only on the tests, while its numerical values also depend on their
weights. Exact test transport preserves distance when it preserves weights
and covers every target test. This does not identify contextual budgets with
communication costs or with a modal bisimulation metric.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic

open Classical

universe u v w z

structure BudgetedObservations (State : Type u) where
  Test : Type v
  holds : Test → State → Prop
  weight : Test → ℝ
  positive : ∀ test, 0 < weight test
  bounded : ∀ test, weight test ≤ 1

namespace BudgetedObservations

variable {State : Type u} (tests : BudgetedObservations.{u, v} State)

noncomputable def score (test : tests.Test) (left right : State) : ℝ :=
  if tests.holds test left ↔ tests.holds test right then 0 else tests.weight test

noncomputable def distance (left right : State) : ℝ :=
  sSup (insert 0 (Set.range (fun test => tests.score test left right)))

theorem score_nonneg (test : tests.Test) (left right : State) :
    0 ≤ tests.score test left right := by
  unfold score
  split_ifs
  · exact le_rfl
  · exact (tests.positive test).le

theorem score_le_weight (test : tests.Test) (left right : State) :
    tests.score test left right ≤ tests.weight test := by
  unfold score
  split_ifs
  · exact (tests.positive test).le
  · exact le_rfl

theorem score_le_one (test : tests.Test) (left right : State) :
    tests.score test left right ≤ 1 :=
  (tests.score_le_weight test left right).trans (tests.bounded test)

private theorem scores_bounded (left right : State) :
    BddAbove (insert 0 (Set.range (fun test => tests.score test left right))) := by
  refine ⟨1, ?_⟩
  rintro _ (rfl | ⟨test, rfl⟩)
  · exact zero_le_one
  · exact tests.score_le_one test left right

theorem score_le_distance (test : tests.Test) (left right : State) :
    tests.score test left right ≤ tests.distance left right :=
  le_csSup (tests.scores_bounded left right) (.inr ⟨test, rfl⟩)

theorem distance_nonneg (left right : State) : 0 ≤ tests.distance left right :=
  le_csSup (tests.scores_bounded left right) (.inl rfl)

theorem distance_le_iff (left right : State) (bound : ℝ) :
    tests.distance left right ≤ bound ↔
      0 ≤ bound ∧ ∀ test, tests.score test left right ≤ bound := by
  simp only [distance, csSup_le_iff (tests.scores_bounded left right) (Set.insert_nonempty _ _),
    Set.forall_mem_insert, Set.forall_mem_range]

theorem distance_le_one (left right : State) : tests.distance left right ≤ 1 :=
  (tests.distance_le_iff left right 1).mpr ⟨zero_le_one, fun test => tests.score_le_one test left right⟩

theorem score_symm (test : tests.Test) (left right : State) :
    tests.score test left right = tests.score test right left := by
  simp only [score, Iff.comm]

theorem distance_symm (left right : State) : tests.distance left right = tests.distance right left := by
  exact congrArg (fun scores => sSup (insert 0 (Set.range scores)))
    (funext fun test => tests.score_symm test left right)

theorem score_ultrametric (test : tests.Test) (first middle last : State) :
    tests.score test first last ≤ max (tests.score test first middle) (tests.score test middle last) := by
  classical
  have nonneg := (tests.positive test).le
  by_cases firstHolds : tests.holds test first <;>
    by_cases middleHolds : tests.holds test middle <;>
      by_cases lastHolds : tests.holds test last <;>
        simp [score, firstHolds, middleHolds, lastHolds, nonneg]

theorem distance_ultrametric (first middle last : State) :
    tests.distance first last ≤ max (tests.distance first middle) (tests.distance middle last) := by
  apply (tests.distance_le_iff first last _).mpr
  refine ⟨(tests.distance_nonneg first middle).trans (le_max_left _ _), ?_⟩
  intro test
  exact (tests.score_ultrametric test first middle last).trans
    (max_le_max (tests.score_le_distance test first middle) (tests.score_le_distance test middle last))

theorem distance_eq_zero_iff (left right : State) :
    tests.distance left right = 0 ↔ ∀ test, tests.holds test left ↔ tests.holds test right := by
  classical
  constructor
  · intro zero test
    by_contra different
    have bounded := tests.score_le_distance test left right
    simp only [score, if_neg different, zero] at bounded
    exact (not_le_of_gt (tests.positive test)) bounded
  · intro same
    apply le_antisymm
    · exact (tests.distance_le_iff left right 0).mpr ⟨le_rfl, fun test => by simp [score, same test]⟩
    · exact tests.distance_nonneg left right

@[simp] theorem distance_self (state : State) : tests.distance state state = 0 :=
  (tests.distance_eq_zero_iff state state).mpr (fun _ => Iff.rfl)

theorem distance_congr {left left' right right' : State}
    (before : ∀ test, tests.holds test left ↔ tests.holds test left')
    (after : ∀ test, tests.holds test right ↔ tests.holds test right') :
    tests.distance left right = tests.distance left' right' := by
  simp only [distance, score, before, after]

variable {Target : Type w} (targetTests : BudgetedObservations.{w, z} Target)

/-- Every target test is accounted for, with the same declared weight. -/
theorem distance_transport (mapState : State → Target) (mapTest : tests.Test → targetTests.Test)
    (covers : Function.Surjective mapTest)
    (preserves : ∀ test state, targetTests.holds (mapTest test) (mapState state) ↔ tests.holds test state)
    (weights : ∀ test, targetTests.weight (mapTest test) = tests.weight test)
    (left right : State) :
    targetTests.distance (mapState left) (mapState right) = tests.distance left right := by
  classical
  have scores : ∀ test, targetTests.score (mapTest test) (mapState left) (mapState right) =
      tests.score test left right := by
    intro test
    simp only [score, preserves, weights]
  exact congrArg (fun values => sSup (insert 0 values))
    ((covers.range_comp _).symm.trans (congrArg Set.range (funext scores)))

end BudgetedObservations

end Mettapedia.GSLT.Logic
