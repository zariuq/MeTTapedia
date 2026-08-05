import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromGLVLocalDirectionality

/-!
# Routed CAROM: delayed GLV transition learning

Seliger, Tsimring, and Rabinovich, *Dynamical model of sequential spatial
memory: winnerless competition of patterns* (2002, arXiv:nlin/0205026),
use the slow competition-matrix equation

`V_ij' = epsilon * a_i(t) * a_j(t - tau) * (V1 - V_ij)`.

The current activity selects the successor row and the delayed activity
selects the predecessor column.  Thus a presentation of `j` followed by `i`
lowers `V_ij`; in the generalized Lotka--Volterra field this makes `i` an
invading direction at the single-species state for `j`.

This file formalizes the exact discrete relaxation step, the entries that it
can change, its continuous constant-activity flow, and the orientation of a
two-pattern transition.  A negative fixture replaces delayed activity by
current activity: it leaves the intended transition unchanged and lowers a
self-competition entry instead.

The results concern the local learning law and the induced GLV invasion
directions.  They do not claim convergence of a learned sequence under
time-varying activities, existence or robustness of a global heteroclinic
cycle, or realization by a trained routed carrier.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

namespace RoutedCarom

open Filter Topology

/-! ## Scalar and matrix learning steps -/

/-- One explicit relaxation step for a competition coefficient.  The
effective gain is `epsilon * current * delayed`. -/
noncomputable def competitionLearningStep
    (epsilon current delayed target coefficient : ℝ) : ℝ :=
  coefficient + epsilon * current * delayed * (target - coefficient)

/-- Apply the source learning law entrywise.  Rows are current successors;
columns are delayed predecessors. -/
noncomputable def competitionMatrixLearningStep
    {Pattern : Type*}
    (epsilon target : ℝ)
    (current delayed : Pattern → ℝ)
    (competition : Pattern → Pattern → ℝ) :
    Pattern → Pattern → ℝ :=
  fun successor predecessor =>
    competitionLearningStep epsilon
      (current successor) (delayed predecessor) target
      (competition successor predecessor)

theorem competitionLearningStep_eq_interpolation
    (epsilon current delayed target coefficient : ℝ) :
    competitionLearningStep epsilon current delayed target coefficient =
      (1 - epsilon * current * delayed) * coefficient +
        (epsilon * current * delayed) * target := by
  simp [competitionLearningStep]
  ring

@[simp] theorem competitionLearningStep_zero_current
    (epsilon delayed target coefficient : ℝ) :
    competitionLearningStep epsilon 0 delayed target coefficient =
      coefficient := by
  simp [competitionLearningStep]

@[simp] theorem competitionLearningStep_zero_delayed
    (epsilon current target coefficient : ℝ) :
    competitionLearningStep epsilon current 0 target coefficient =
      coefficient := by
  simp [competitionLearningStep]

@[simp] theorem competitionLearningStep_target
    (epsilon current delayed target : ℝ) :
    competitionLearningStep epsilon current delayed target target =
      target := by
  simp [competitionLearningStep]

theorem target_sub_competitionLearningStep
    (epsilon current delayed target coefficient : ℝ) :
    target -
        competitionLearningStep epsilon current delayed target coefficient =
      (1 - epsilon * current * delayed) * (target - coefficient) := by
  simp [competitionLearningStep]
  ring

/-- An entry that changed must have had both its successor and delayed
predecessor active.  This implication remains valid even when the learning
rate or target gap is zero. -/
theorem competitionMatrixLearningStep_changed_imp_active
    {Pattern : Type*}
    {epsilon target : ℝ}
    {current delayed : Pattern → ℝ}
    {competition : Pattern → Pattern → ℝ}
    {successor predecessor : Pattern}
    (hchanged :
      competitionMatrixLearningStep epsilon target current delayed competition
          successor predecessor ≠
        competition successor predecessor) :
    current successor ≠ 0 ∧ delayed predecessor ≠ 0 := by
  constructor
  · intro hzero
    apply hchanged
    simp [competitionMatrixLearningStep, hzero]
  · intro hzero
    apply hchanged
    simp [competitionMatrixLearningStep, hzero]

/-- With unit current and delayed activities, the selected matrix entry is
exactly the scalar relaxation step. -/
theorem competitionMatrixLearningStep_selected
    {Pattern : Type*}
    {epsilon target : ℝ}
    {current delayed : Pattern → ℝ}
    {competition : Pattern → Pattern → ℝ}
    {successor predecessor : Pattern}
    (hcurrent : current successor = 1)
    (hdelayed : delayed predecessor = 1) :
    competitionMatrixLearningStep epsilon target current delayed competition
        successor predecessor =
      competitionLearningStep epsilon 1 1 target
        (competition successor predecessor) := by
  simp [competitionMatrixLearningStep, hcurrent, hdelayed]

/-! ## Exact constant-activity flow -/

/-- Exact solution of `coefficient' = rate * (target - coefficient)` under
a constant effective rate. -/
noncomputable def competitionLearningFlow
    (rate target initial time : ℝ) : ℝ :=
  target + (initial - target) * Real.exp (-rate * time)

@[simp] theorem competitionLearningFlow_zero
    (rate target initial : ℝ) :
    competitionLearningFlow rate target initial 0 = initial := by
  simp [competitionLearningFlow]

theorem competitionLearningFlow_add
    (rate target initial first second : ℝ) :
    competitionLearningFlow rate target initial (first + second) =
      competitionLearningFlow rate target
        (competitionLearningFlow rate target initial first) second := by
  simp only [competitionLearningFlow]
  rw [show -rate * (first + second) =
      -rate * first + -rate * second by ring, Real.exp_add]
  ring

/-- The advertised flow solves the source learning equation at every time. -/
theorem competitionLearningFlow_hasDerivAt
    (rate target initial time : ℝ) :
    HasDerivAt (competitionLearningFlow rate target initial)
      (rate * (target -
        competitionLearningFlow rate target initial time)) time := by
  have hinner :
      HasDerivAt (fun elapsed : ℝ => -rate * elapsed) (-rate) time := by
    simpa using (hasDerivAt_id time).const_mul (-rate)
  have hexponential :
      HasDerivAt (fun elapsed : ℝ => Real.exp (-rate * elapsed))
        (Real.exp (-rate * time) * (-rate)) time := by
    have hcomposition :=
      (Real.hasDerivAt_exp (-rate * time)).comp time hinner
    have heq :
        (fun elapsed : ℝ => Real.exp (-rate * elapsed)) =ᶠ[𝓝 time]
          (Real.exp ∘ fun elapsed : ℝ => -rate * elapsed) :=
      Filter.Eventually.of_forall fun _ => rfl
    exact hcomposition.congr_of_eventuallyEq heq
  have hflow :=
    (hasDerivAt_const time target).add
      (hexponential.const_mul (initial - target))
  have hderivative :
      0 + (initial - target) *
          (Real.exp (-rate * time) * (-rate)) =
        rate * (target -
          competitionLearningFlow rate target initial time) := by
    simp [competitionLearningFlow]
    ring
  have hfunction :
      ((fun _ : ℝ => target) +
          fun elapsed : ℝ =>
            (initial - target) * Real.exp (-rate * elapsed)) =
        competitionLearningFlow rate target initial := by
    funext elapsed
    rfl
  rw [← hderivative]
  rw [← hfunction]
  exact hflow

theorem competitionLearningFlow_sub_target
    (rate target initial time : ℝ) :
    competitionLearningFlow rate target initial time - target =
      (initial - target) * Real.exp (-rate * time) := by
  simp [competitionLearningFlow]

/-- At positive rate and positive time, a coefficient initially above the
target remains above it and has moved strictly downward. -/
theorem competitionLearningFlow_strictly_between
    {rate target initial time : ℝ}
    (hrate : 0 < rate) (htime : 0 < time) (hgap : target < initial) :
    target < competitionLearningFlow rate target initial time ∧
      competitionLearningFlow rate target initial time < initial := by
  have hexp_pos : 0 < Real.exp (-rate * time) := Real.exp_pos _
  have hexp_lt_one : Real.exp (-rate * time) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  simp only [competitionLearningFlow]
  constructor <;> nlinarith

/-! ## Two-pattern transition orientation -/

def firstPatternActivity (pattern : Fin 2) : ℝ :=
  if pattern = 0 then 1 else 0

def secondPatternActivity (pattern : Fin 2) : ℝ :=
  if pattern = 1 then 1 else 0

/-- Initially every off-diagonal interaction is suppressive. -/
def twoPatternInitialCompetition (affected resident : Fin 2) : ℝ :=
  if affected = resident then 1 else 2

/-- Correct temporal learning: pattern zero was active in the delayed slot
and pattern one is active now. -/
noncomputable def delayedTransitionCompetition : Fin 2 → Fin 2 → ℝ :=
  competitionMatrixLearningStep 1 (1 / 2)
    secondPatternActivity firstPatternActivity
    twoPatternInitialCompetition

/-- Incorrect eager variant with no predecessor delay. -/
noncomputable def eagerTransitionCompetition : Fin 2 → Fin 2 → ℝ :=
  competitionMatrixLearningStep 1 (1 / 2)
    secondPatternActivity secondPatternActivity
    twoPatternInitialCompetition

theorem delayedTransitionCompetition_selected :
    delayedTransitionCompetition 1 0 = 1 / 2 := by
  norm_num [delayedTransitionCompetition, competitionMatrixLearningStep,
    competitionLearningStep, firstPatternActivity, secondPatternActivity,
    twoPatternInitialCompetition]

theorem delayedTransitionCompetition_reverse_unchanged :
    delayedTransitionCompetition 0 1 = 2 := by
  norm_num [delayedTransitionCompetition, competitionMatrixLearningStep,
    competitionLearningStep, firstPatternActivity, secondPatternActivity,
    twoPatternInitialCompetition]

/-- The learned coefficient makes pattern one invade resident pattern zero,
while the unlearned reverse coefficient remains contracting. -/
theorem delayed_learning_orients_glv_transition :
    0 < glvInvasionRate 1 1 (delayedTransitionCompetition 1 0) ∧
      glvInvasionRate 1 1 (delayedTransitionCompetition 0 1) < 0 := by
  norm_num [delayedTransitionCompetition, competitionMatrixLearningStep,
    competitionLearningStep, firstPatternActivity, secondPatternActivity,
    twoPatternInitialCompetition, glvInvasionRate]

/-- Omitting the delay fails to learn the intended transition and instead
changes the active pattern's self-competition coefficient. -/
theorem eager_activity_fails_to_encode_predecessor :
    eagerTransitionCompetition 1 0 = 2 ∧
      eagerTransitionCompetition 1 1 = 1 / 2 := by
  norm_num [eagerTransitionCompetition, competitionMatrixLearningStep,
    competitionLearningStep, secondPatternActivity,
    twoPatternInitialCompetition]

/-- Consequently, the eager update leaves the intended successor direction
contracting. -/
theorem eager_activity_keeps_intended_transition_contracting :
    glvInvasionRate 1 1 (eagerTransitionCompetition 1 0) < 0 := by
  norm_num [eagerTransitionCompetition, competitionMatrixLearningStep,
    competitionLearningStep, secondPatternActivity,
    twoPatternInitialCompetition, glvInvasionRate]

#print axioms competitionMatrixLearningStep_changed_imp_active
#print axioms competitionLearningFlow_hasDerivAt
#print axioms competitionLearningFlow_strictly_between
#print axioms delayed_learning_orients_glv_transition
#print axioms eager_activity_fails_to_encode_predecessor
#print axioms eager_activity_keeps_intended_transition_contracting

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
