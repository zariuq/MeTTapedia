import Mettapedia.MachineLearning.ContinualLearning.AveragedGradientProjection

/-!
# Gradient episodic memory: the multi-constraint boundary

Lopez-Paz and Ranzato (2017), *Gradient Episodic Memory for Continual
Learning*, replace exact replay-loss constraints by one first-order
half-space per previous task (Equation (7)), then choose the closest
Euclidean direction in their intersection (Equation (8)).

Chaudhry, Ranzato, Rohrbach, and Elhoseiny (2019), *Efficient Lifelong
Learning with A-GEM*, replace that family by one averaged replay-gradient
half-space.  This file isolates the exact logical boundary between those
constructions:

* every GEM-feasible direction is feasible for the averaged constraint;
* the converse fails, even for two orthogonal replay gradients;
* in that same executable fixture, the full GEM quadratic program has a
  unique projection while the averaged projection leaves the offending
  direction unchanged;
* first-order feasibility yields finite replay retention only with an
  explicit curvature budget.

The two-dimensional fixture is deliberately nondegenerate: both replay
gradients are nonzero, their average is nonzero, and the two projections are
different.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace GradientEpisodicMemory

noncomputable section

open scoped InnerProductSpace

variable {Parameter : Type*}
  [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]

/-- The family of GEM half-spaces from Equation (7): every remembered task
has nonnegative first-order alignment with the proposed descent direction. -/
def MultiFeasible
    (references : List Parameter) (direction : Parameter) : Prop :=
  ∀ reference ∈ references, 0 ≤ ⟪reference, direction⟫_ℝ

/-- The arithmetic mean of the per-task replay gradients.  The empty mean is
zero, matching the absence of any replay constraint. -/
def meanReference (references : List Parameter) : Parameter :=
  ((references.length : ℝ)⁻¹) • references.sum

/-- The minimum-change property defining the primal GEM quadratic program
in Equation (8).  The paper's factor `1 / 2` does not change the minimizer,
so the objective is stated as squared Euclidean distance. -/
def IsMinimumChangeProjection
    (references : List Parameter) (proposed chosen : Parameter) : Prop :=
  MultiFeasible references chosen ∧
    ∀ candidate, MultiFeasible references candidate →
      ‖chosen - proposed‖ ^ 2 ≤ ‖candidate - proposed‖ ^ 2

private theorem inner_sum_nonnegative
    {references : List Parameter} {direction : Parameter}
    (feasible : MultiFeasible references direction) :
    0 ≤ ⟪references.sum, direction⟫_ℝ := by
  induction references with
  | nil =>
      simp
  | cons reference references ih =>
      rw [List.sum_cons, inner_add_left]
      exact add_nonneg
        (feasible reference (by simp))
        (ih (fun candidate membership =>
          feasible candidate (by simp [membership])))

/-- Full GEM feasibility implies feasibility for the mean replay gradient
used by the corresponding A-GEM relaxation. -/
theorem multiFeasible_implies_meanFeasible
    {references : List Parameter} {direction : Parameter}
    (feasible : MultiFeasible references direction) :
    AveragedGradientProjection.Feasible
      (meanReference references) direction := by
  rw [AveragedGradientProjection.Feasible, meanReference,
    real_inner_smul_left]
  exact mul_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg references.length))
    (inner_sum_nonnegative feasible)

/-- With one remembered task, GEM and the averaged half-space coincide
exactly. -/
theorem singleton_multiFeasible_iff
    (reference direction : Parameter) :
    MultiFeasible [reference] direction ↔
      AveragedGradientProjection.Feasible reference direction := by
  simp [MultiFeasible, AveragedGradientProjection.Feasible]

@[simp] theorem meanReference_singleton (reference : Parameter) :
    meanReference [reference] = reference := by
  simp [meanReference]

/-! ## Exact two-task separation fixture -/

abbrev SeparationPlane := EuclideanSpace ℝ (Fin 2)

noncomputable def firstReplayGradient : SeparationPlane :=
  EuclideanSpace.single 0 1

noncomputable def secondReplayGradient : SeparationPlane :=
  EuclideanSpace.single 1 1

noncomputable def twoReplayGradients : List SeparationPlane :=
  [firstReplayGradient, secondReplayGradient]

/-- The first coordinate conflicts with the first task, while the larger
second coordinate makes the averaged alignment positive. -/
noncomputable def conflictingProposal : SeparationPlane :=
  -firstReplayGradient + 2 • secondReplayGradient

/-- The full-GEM projection of `conflictingProposal` onto the intersection
of the two replay half-spaces. -/
noncomputable def fullGEMProjection : SeparationPlane :=
  2 • secondReplayGradient

theorem firstReplayGradient_inner_conflictingProposal :
    ⟪firstReplayGradient, conflictingProposal⟫_ℝ = -1 := by
  simp [firstReplayGradient, secondReplayGradient, conflictingProposal,
    EuclideanSpace.inner_single_left]

theorem secondReplayGradient_inner_conflictingProposal :
    ⟪secondReplayGradient, conflictingProposal⟫_ℝ = 2 := by
  simp [firstReplayGradient, secondReplayGradient, conflictingProposal,
    EuclideanSpace.inner_single_left]

theorem meanReference_twoReplayGradients :
    meanReference twoReplayGradients =
      (1 / 2 : ℝ) • (firstReplayGradient + secondReplayGradient) := by
  simp [meanReference, twoReplayGradients]

/-- Strict converse failure: an averaged replay constraint can be satisfied
while one remembered task has negative first-order alignment. -/
theorem meanFeasible_but_not_multiFeasible :
    AveragedGradientProjection.Feasible
        (meanReference twoReplayGradients) conflictingProposal ∧
      ¬ MultiFeasible twoReplayGradients conflictingProposal := by
  constructor
  · rw [meanReference_twoReplayGradients,
      AveragedGradientProjection.Feasible, real_inner_smul_left,
      inner_add_left,
      firstReplayGradient_inner_conflictingProposal,
      secondReplayGradient_inner_conflictingProposal]
    norm_num
  · intro feasible
    have firstFeasible :=
      feasible firstReplayGradient (by simp [twoReplayGradients])
    rw [firstReplayGradient_inner_conflictingProposal] at firstFeasible
    norm_num at firstFeasible

/-- Consequently the A-GEM projection leaves this proposal unchanged even
though it violates a full GEM constraint. -/
theorem averagedProjection_preserves_multiConstraintViolation :
    AveragedGradientProjection.project conflictingProposal
        (meanReference twoReplayGradients) = conflictingProposal ∧
      ¬ MultiFeasible twoReplayGradients
        (AveragedGradientProjection.project conflictingProposal
          (meanReference twoReplayGradients)) := by
  have separation := meanFeasible_but_not_multiFeasible
  rw [AveragedGradientProjection.project_of_feasible
    conflictingProposal (meanReference twoReplayGradients) separation.1]
  exact ⟨rfl, separation.2⟩

private theorem separationPlane_norm_sq (vector : SeparationPlane) :
    ‖vector‖ ^ 2 = vector 0 ^ 2 + vector 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_two]
  ring

theorem fullGEMProjection_feasible :
    MultiFeasible twoReplayGradients fullGEMProjection := by
  simp [MultiFeasible, twoReplayGradients, fullGEMProjection,
    firstReplayGradient, secondReplayGradient,
    EuclideanSpace.inner_single_left]

/-- The clipped direction is the global minimum-change solution of the
two-task GEM quadratic program. -/
theorem fullGEMProjection_isMinimumChange :
    IsMinimumChangeProjection twoReplayGradients conflictingProposal
      fullGEMProjection := by
  constructor
  · exact fullGEMProjection_feasible
  · intro candidate feasible
    have firstCoordinate : 0 ≤ candidate 0 := by
      have firstFeasible :=
        feasible firstReplayGradient (by simp [twoReplayGradients])
      simpa [firstReplayGradient,
        EuclideanSpace.inner_single_left] using firstFeasible
    rw [separationPlane_norm_sq, separationPlane_norm_sq]
    simp [fullGEMProjection, conflictingProposal,
      firstReplayGradient, secondReplayGradient]
    nlinarith [sq_nonneg (candidate 1 - 2)]

/-- The minimum-change solution in the separation fixture is unique. -/
theorem fullGEMProjection_unique
    (candidate : SeparationPlane)
    (feasible : MultiFeasible twoReplayGradients candidate)
    (sameCost :
      ‖candidate - conflictingProposal‖ ^ 2 =
        ‖fullGEMProjection - conflictingProposal‖ ^ 2) :
    candidate = fullGEMProjection := by
  have firstCoordinate : 0 ≤ candidate 0 := by
    have firstFeasible :=
      feasible firstReplayGradient (by simp [twoReplayGradients])
    simpa [firstReplayGradient,
      EuclideanSpace.inner_single_left] using firstFeasible
  rw [separationPlane_norm_sq, separationPlane_norm_sq] at sameCost
  simp [fullGEMProjection, conflictingProposal,
    firstReplayGradient, secondReplayGradient] at sameCost
  have firstCoordinateZero : candidate 0 = 0 := by
    nlinarith [sq_nonneg (candidate 1 - 2)]
  have secondCoordinateTwo : candidate 1 = 2 := by
    nlinarith [sq_nonneg (candidate 1 - 2)]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · simpa [fullGEMProjection, secondReplayGradient,
      PiLp.single_apply] using firstCoordinateZero
  · simpa [fullGEMProjection, secondReplayGradient,
      PiLp.single_apply] using secondCoordinateTwo

theorem fullAndAveragedProjections_differ :
    fullGEMProjection ≠
      AveragedGradientProjection.project conflictingProposal
        (meanReference twoReplayGradients) := by
  rw [averagedProjection_preserves_multiConstraintViolation.1]
  intro equality
  have coordinate :=
    congrArg (fun vector : SeparationPlane => vector 0) equality
  norm_num [fullGEMProjection, conflictingProposal,
    firstReplayGradient, secondReplayGradient,
    PiLp.single_apply] at coordinate

/-! ## The finite-step boundary -/

open Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
open Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DirectionalTaskDescent

/-- Simultaneous finite replay-loss retention follows from the GEM
first-order margins only when every task's curvature remainder fits inside
its own margin.  This is the multi-task version of the local-linearity
qualification surrounding Equations (6)--(8). -/
theorem replayLoss_nonincrease_for_all
    {Task : Type*}
    (tasks : List Task)
    (loss : Task → Parameter → ℝ)
    (parameter direction : Parameter)
    (reference : Task → Parameter)
    (curvature : Task → ℝ)
    (step : ℝ)
    (certificate :
      ∀ task ∈ tasks,
        HasDirectionalTaskUpperModelAt
          (loss task) parameter (reference task) direction
          (curvature task))
    (stepNonnegative : 0 ≤ step)
    (trust :
      ∀ task ∈ tasks,
        step * curvature task / 2 ≤
          ⟪reference task, direction⟫_ℝ) :
    ∀ task ∈ tasks,
      loss task (parameter - step • direction) ≤ loss task parameter := by
  intro task membership
  have upper := certificate task membership step stepNonnegative
  have scaledTrust :=
    mul_le_mul_of_nonneg_left (trust task membership) stepNonnegative
  nlinarith

#print axioms multiFeasible_implies_meanFeasible
#print axioms meanFeasible_but_not_multiFeasible
#print axioms averagedProjection_preserves_multiConstraintViolation
#print axioms fullGEMProjection_isMinimumChange
#print axioms fullGEMProjection_unique
#print axioms fullAndAveragedProjections_differ
#print axioms replayLoss_nonincrease_for_all

end

end GradientEpisodicMemory

end Mettapedia.MachineLearning.ContinualLearning
