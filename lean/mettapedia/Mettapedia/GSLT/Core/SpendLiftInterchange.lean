import Mettapedia.GSLT.Core.GSLTConstructions
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Spend lifts interchange strictly

Two decorations presented as spend lifts can be applied in either order,
and both orders present the same system as one lift over the product
monoid.  A cost grading in a monoid of costs and a history grading in the
free monoid of events are the motivating pair: when both are spend lifts,
recording cost and then history is the same system as recording history
and then cost, up to reassociating the state.

The hypothesis that carries the result is that the second decoration grades
a step of the first lift by reading only the underlying base step
(`StepSpend.over`).  A decoration whose grade reads the accumulator of the
first is not of that form (`accumulatorReading_not_over`), and for such a
decoration the order of the two lifts is part of the data.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

universe u v w

namespace Mettapedia.GSLT

namespace GSLT

namespace StepSpend

variable {S : GSLT} {V : Type v} {W : Type w}

/-- Grade one step by a pair of grades, one from each grading, for the same
step. -/
def prod (first : StepSpend S V) (second : StepSpend S W) :
    StepSpend S (V × W) where
  graded source target grade :=
    first.graded source target grade.1 ∧ second.graded source target grade.2
  sound := fun graded => first.sound graded.1
  resp_left := by
    intro source source' target grade equiv graded
    obtain ⟨target₁, graded₁, equiv₁⟩ := first.resp_left equiv graded.1
    obtain ⟨target₂, graded₂, equiv₂⟩ := second.resp_left equiv graded.2
    exact ⟨target₁, ⟨graded₁, second.resp_right graded₂
      (S.equations.iseqv.trans (S.equations.iseqv.symm equiv₂) equiv₁)⟩, equiv₁⟩
  resp_right := fun graded equiv =>
    ⟨first.resp_right graded.1 equiv, second.resp_right graded.2 equiv⟩

variable [Monoid V]

/-- Grade the steps of `S.spendLift first` by `second`, reading only the
underlying base step. -/
def over (second : StepSpend S W) (first : StepSpend S V) :
    StepSpend (S.spendLift first) W where
  graded source target grade :=
    second.graded source.1 target.1 grade ∧ (S.spendLift first).Step source target
  sound := fun graded => graded.2
  resp_left := by
    intro source source' target grade equiv graded
    obtain ⟨target', step', equiv'⟩ :=
      (S.spendLift first).rewrites_resp_left equiv graded.2
    obtain ⟨target₂, graded₂, equiv₂⟩ := second.resp_left equiv.1 graded.1
    exact ⟨target', ⟨second.resp_right graded₂
      (S.equations.iseqv.trans (S.equations.iseqv.symm equiv₂) equiv'.1), step'⟩,
      equiv'⟩
  resp_right := fun graded equiv =>
    ⟨second.resp_right graded.1 equiv.1,
      (S.spendLift first).rewrites_resp_right graded.2 equiv⟩

end StepSpend

section Interchange

variable {S : GSLT} {V : Type v} {W : Type w} [Monoid V] [Monoid W]
  (first : StepSpend S V) (second : StepSpend S W)

/-- Lifting by `first` and then by `second` over it is one lift by the
paired grading, after reassociating the state. -/
theorem spendLift_over_step_iff_prod {source target : (S.Term × V) × W} :
    ((S.spendLift first).spendLift (second.over first)).Step source target ↔
      (S.spendLift (first.prod second)).Step
        (source.1.1, (source.1.2, source.2)) (target.1.1, (target.1.2, target.2)) := by
  constructor
  · rintro ⟨costB, ⟨gradedB, costA, gradedA, accumulatedA⟩, accumulatedB⟩
    exact ⟨(costA, costB), ⟨gradedA, gradedB⟩,
      Prod.ext accumulatedA accumulatedB⟩
  · rintro ⟨⟨costA, costB⟩, ⟨gradedA, gradedB⟩, accumulated⟩
    exact ⟨costB, ⟨gradedB, costA, gradedA, congrArg Prod.fst accumulated⟩,
      congrArg Prod.snd accumulated⟩

/-- The equations of the iterated lift are those of the paired lift, after
reassociating the state. -/
theorem spendLift_over_equiv_iff_prod {source target : (S.Term × V) × W} :
    ((S.spendLift first).spendLift (second.over first)).Equiv source target ↔
      (S.spendLift (first.prod second)).Equiv
        (source.1.1, (source.1.2, source.2)) (target.1.1, (target.1.2, target.2)) := by
  constructor
  · rintro ⟨⟨stateEq, costAEq⟩, costBEq⟩
    exact ⟨stateEq, Prod.ext costAEq costBEq⟩
  · rintro ⟨stateEq, costEq⟩
    simp only [Prod.mk.injEq] at costEq
    exact ⟨⟨stateEq, costEq.1⟩, costEq.2⟩

/-- **Strict interchange.**  Lifting by `first` then `second` has exactly
the steps of lifting by `second` then `first`, under the state bijection
that swaps the two accumulators. -/
theorem spendLift_interchange_step_iff {state target : S.Term}
    {costA costA' : V} {costB costB' : W} :
    ((S.spendLift first).spendLift (second.over first)).Step
        ((state, costA), costB) ((target, costA'), costB') ↔
      ((S.spendLift second).spendLift (first.over second)).Step
        ((state, costB), costA) ((target, costB'), costA') := by
  constructor
  · rintro ⟨gradeB, ⟨gradedB, gradeA, gradedA, accumulatedA⟩, accumulatedB⟩
    exact ⟨gradeA, ⟨gradedA, gradeB, gradedB, accumulatedB⟩, accumulatedA⟩
  · rintro ⟨gradeA, ⟨gradedA, gradeB, gradedB, accumulatedB⟩, accumulatedA⟩
    exact ⟨gradeB, ⟨gradedB, gradeA, gradedA, accumulatedA⟩, accumulatedB⟩

/-- Erasing both accumulators sends every step of the iterated lift to a
base step: the second accumulator has no steps of its own. -/
theorem spendLift_over_erase_step {source target : (S.Term × V) × W}
    (step : ((S.spendLift first).spendLift (second.over first)).Step source target) :
    S.Step source.1.1 target.1.1 :=
  S.spendLift_erase_step first
    ((S.spendLift first).spendLift_erase_step (second.over first) step)

end Interchange

/-! ## Controls on a two-state system -/

namespace SpendLiftInterchangeControls

/-- Two states and a step between any two distinct ones. -/
def flip : GSLT where
  Term := Bool
  equations := ⟨(· = ·), eq_equivalence⟩
  rewrites := fun source target => source ≠ target
  rewrites_resp_left := by
    intro source source' target equal step
    exact ⟨target, equal ▸ step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    exact equal ▸ step

/-- Every step costs a factor of two. -/
def doubling : StepSpend flip ℕ where
  graded source target grade := source ≠ target ∧ grade = 2
  sound := fun graded => graded.1
  resp_left := by
    intro source source' target grade equal graded
    exact ⟨target, (show source' = source from equal.symm) ▸ graded, rfl⟩
  resp_right := by
    intro source target target' grade graded equal
    exact (show target = target' from equal) ▸ graded

/-- Every step records its target as an event. -/
def recordTarget : StepSpend flip (FreeMonoid Bool) where
  graded source target grade := source ≠ target ∧ grade = FreeMonoid.of target
  sound := fun graded => graded.1
  resp_left := by
    intro source source' target grade equal graded
    exact ⟨target, (show source' = source from equal.symm) ▸ graded, rfl⟩
  resp_right := by
    intro source target target' grade graded equal
    exact (show target = target' from equal) ▸ graded

/-- Positive control: one step, recorded in both orders. -/
theorem cost_then_history_step :
    ((flip.spendLift doubling).spendLift (recordTarget.over doubling)).Step
      ((false, 1), 1) ((true, 2), FreeMonoid.of true) :=
  ⟨FreeMonoid.of true, ⟨⟨Bool.false_ne_true, rfl⟩,
    2, ⟨Bool.false_ne_true, rfl⟩, rfl⟩, one_mul _⟩

theorem history_then_cost_step :
    ((flip.spendLift recordTarget).spendLift (doubling.over recordTarget)).Step
      ((false, 1), 1) ((true, FreeMonoid.of true), 2) :=
  (spendLift_interchange_step_iff doubling recordTarget).mp cost_then_history_step

/-- A grading on `flip.spendLift doubling` whose grade is the accumulated
cost of the target.  It reads the first decoration, not only the base step. -/
def accumulatorReading : StepSpend (flip.spendLift doubling) ℕ where
  graded source target grade :=
    (flip.spendLift doubling).Step source target ∧ grade = target.2
  sound := fun graded => graded.1
  resp_left := by
    intro source source' target grade equiv graded
    obtain ⟨target', step', equiv'⟩ :=
      (flip.spendLift doubling).rewrites_resp_left equiv graded.1
    exact ⟨target', ⟨step', graded.2.trans equiv'.2⟩, equiv'⟩
  resp_right := by
    intro source target target' grade graded equiv
    exact ⟨(flip.spendLift doubling).rewrites_resp_right graded.1 equiv,
      graded.2.trans equiv.2⟩

/-- Negative control: a decoration that reads the first accumulator is not
the lift of any base grading, so strict interchange does not apply to it. -/
theorem accumulatorReading_not_over :
    ¬ ∃ second : StepSpend flip ℕ, ∀ source target grade,
      accumulatorReading.graded source target grade ↔
        (second.over doubling).graded source target grade := by
  rintro ⟨second, same⟩
  have stepOne : (flip.spendLift doubling).Step (false, 1) (true, 2) :=
    ⟨2, ⟨Bool.false_ne_true, rfl⟩, rfl⟩
  have stepThree : (flip.spendLift doubling).Step (false, 3) (true, 6) :=
    ⟨2, ⟨Bool.false_ne_true, rfl⟩, rfl⟩
  have gradedSix : second.graded false true 6 :=
    ((same (false, 3) (true, 6) 6).mp ⟨stepThree, rfl⟩).1
  have wrong : accumulatorReading.graded (false, 1) (true, 2) 6 :=
    (same (false, 1) (true, 2) 6).mpr ⟨gradedSix, stepOne⟩
  exact absurd wrong.2 (by decide)

end SpendLiftInterchangeControls

end GSLT

end Mettapedia.GSLT

#print axioms Mettapedia.GSLT.GSLT.spendLift_over_step_iff_prod
#print axioms Mettapedia.GSLT.GSLT.spendLift_over_equiv_iff_prod
#print axioms Mettapedia.GSLT.GSLT.spendLift_interchange_step_iff
#print axioms Mettapedia.GSLT.GSLT.spendLift_over_erase_step
#print axioms Mettapedia.GSLT.GSLT.SpendLiftInterchangeControls.history_then_cost_step
#print axioms Mettapedia.GSLT.GSLT.SpendLiftInterchangeControls.accumulatorReading_not_over
