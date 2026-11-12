import Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.Partitions

/-!
# Causal and statistical boundaries of trajectory reweighting

A Gibbs tilt can preserve every supported trajectory while changing the
initial law. It need not satisfy a fixed-initial control constraint.
Separately, two writes to distinct coordinates commute for every input and
can have correlated outputs when they read a common random input.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.Controls

open scoped BigOperators
open Mettapedia.InformationTheory Mettapedia.InformationTheory.FiniteRV
open Mettapedia.ProbabilityTheory.BayesianInference

def fair : Prob Bool := ⟨fun _ => 1 / 2, (fun _ => by norm_num), by norm_num [Fintype.sum_bool]⟩

def desiredWeight (initial : Bool) : ℝ := if initial then 3 else 1
def desiredCost (initial : Bool) : ℝ := -Real.log (desiredWeight initial)

theorem desired_weight (initial : Bool) : weight desiredCost 1 initial = desiredWeight initial := by
  unfold weight desiredCost
  rw [div_one, neg_neg, Real.exp_log]
  cases initial <;> norm_num [desiredWeight]

theorem desired_partition : partition fair desiredCost 1 = 2 := by
  unfold partition evidence
  simp only [desired_weight]
  norm_num [fair, desiredWeight, Fintype.sum_bool]

theorem tilted_initial_mass : (gibbs fair desiredCost 1 (by norm_num)).1 true = 3 / 4 := by
  rw [gibbs_apply, desired_weight, desired_partition]
  norm_num [fair, desiredWeight]

theorem supported_initials_unchanged :
    ∀ initial, 0 < (gibbs fair desiredCost 1 (by norm_num)).1 initial ↔ 0 < fair.1 initial :=
  gibbs_pos_iff fair desiredCost 1 (by norm_num)

theorem fixed_initial_law_violated :
    Prob.coarsen (gibbs fair desiredCost 1 (by norm_num)) id ≠ fair := by
  rw [Prob.coarsen_id]
  intro same
  have masses := congrArg (fun law : Prob Bool => law.1 true) same
  rw [tilted_initial_mass] at masses
  norm_num [fair] at masses

theorem tilt_reduces_objective :
    freeEnergy fair desiredCost 1 (gibbs fair desiredCost 1 (by norm_num)) <
      freeEnergy fair desiredCost 1 fair := by
  have supported : SupportedBy fair fair.1 := fun _ positive => positive
  have lower := gibbs_minimizes fair fair desiredCost 1 (by norm_num) supported
  apply lt_of_le_of_ne lower
  intro equal
  have same := (gibbs_unique fair fair desiredCost 1 (by norm_num) supported).mp equal.symm
  apply fixed_initial_law_violated
  rw [Prob.coarsen_id]
  exact same.symm

def leftWrite (noise : Bool) (state : Bool × Bool) : Bool × Bool := (noise, state.2)
def rightWrite (noise : Bool) (state : Bool × Bool) : Bool × Bool := (state.1, noise)

theorem left_preserves_right (noise : Bool) (state : Bool × Bool) :
    (leftWrite noise state).2 = state.2 := rfl

theorem right_preserves_left (noise : Bool) (state : Bool × Bool) :
    (rightWrite noise state).1 = state.1 := rfl

theorem writes_commute (noise : Bool) (state : Bool × Bool) :
    leftWrite noise (rightWrite noise state) = rightWrite noise (leftWrite noise state) := rfl

def sharedNoiseOutputs : Prob (Bool × Bool) :=
  Prob.coarsen fair (fun noise => leftWrite noise (rightWrite noise (false, false)))

theorem shared_noise_marginals :
    sharedNoiseOutputs ∈ fixedMarginals fair fair := by
  constructor
  · apply Subtype.ext
    funext initial
    cases initial <;> norm_num [sharedNoiseOutputs, Prob.coarsen_apply,
      pushforward_eq_sum_ite, Fintype.sum_prod_type, Fintype.sum_bool, leftWrite, rightWrite, fair]
  · apply Subtype.ext
    funext initial
    cases initial <;> norm_num [sharedNoiseOutputs, Prob.coarsen_apply,
      pushforward_eq_sum_ite, Fintype.sum_prod_type, Fintype.sum_bool, leftWrite, rightWrite, fair]

theorem shared_noise_outputs_not_independent : sharedNoiseOutputs ≠ productLaw fair fair := by
  intro same
  have masses := congrArg (fun law : Prob (Bool × Bool) => law.1 (true, true)) same
  norm_num [sharedNoiseOutputs, Prob.coarsen_apply, pushforward_eq_sum_ite, Fintype.sum_bool,
    leftWrite, rightWrite, fair, productLaw_apply] at masses

theorem commutation_does_not_imply_independence :
    (∀ noise state, leftWrite noise (rightWrite noise state) = rightWrite noise (leftWrite noise state)) ∧
      sharedNoiseOutputs ∈ fixedMarginals fair fair ∧ sharedNoiseOutputs ≠ productLaw fair fair :=
  ⟨writes_commute, shared_noise_marginals, shared_noise_outputs_not_independent⟩

end Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.Controls
