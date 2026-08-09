import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Weighted-GSLT local potentiation

This file formalizes two independent facts about the finite-dimensional
`theta = 1` mean field.

* Repeated local potentiation is monotone but its limiting face is determined
  by firing support.  Constant increments reach the ceiling after sufficiently
  many firings, whereas timing increments can remain below it even along an
  infinite firing schedule.
* With a marking held fixed, the weight drift has a scalar potential.  Once the
  marking and weight dynamics are coupled, even the one-synapse self-loop has a
  nonsymmetric Jacobian and therefore cannot be the gradient of a `C^2`
  Euclidean potential.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.LocalLearning.WeightedGSLT

open Filter Matrix
open scoped Topology

/-! ## Constant local potentiation -/

/-- Closed form after `firings` applications of a positive constant increment
with a hard ceiling. -/
noncomputable def saturatingWeight
    (initial eta ceiling : ℝ) (firings : ℕ) : ℝ :=
  min ceiling (initial + (firings : ℝ) * eta)

@[simp]
theorem saturatingWeight_zero (initial eta ceiling : ℝ)
    (hinitial : initial ≤ ceiling) :
    saturatingWeight initial eta ceiling 0 = initial := by
  simp [saturatingWeight, min_eq_right hinitial]

theorem saturatingWeight_succ (initial eta ceiling : ℝ)
    (hη : 0 ≤ eta) (firings : ℕ) :
    saturatingWeight initial eta ceiling (firings + 1) =
      min ceiling (saturatingWeight initial eta ceiling firings + eta) := by
  by_cases hsat : ceiling ≤ initial + (firings : ℝ) * eta
  · have hnext : ceiling ≤ initial + ((firings + 1 : ℕ) : ℝ) * eta := by
      norm_num [Nat.cast_add, Nat.cast_one]
      linarith
    rw [saturatingWeight, saturatingWeight, min_eq_left hsat, min_eq_left hnext]
    exact (min_eq_left (by linarith)).symm
  · have hbelow : initial + (firings : ℝ) * eta ≤ ceiling := le_of_not_ge hsat
    rw [saturatingWeight, saturatingWeight, min_eq_right hbelow]
    apply congrArg (fun value : ℝ => min ceiling value)
    norm_num [Nat.cast_add, Nat.cast_one]
    ring

theorem saturatingWeight_le_ceiling (initial eta ceiling : ℝ) (firings : ℕ) :
    saturatingWeight initial eta ceiling firings ≤ ceiling := by
  exact min_le_left _ _

theorem saturatingWeight_mono (initial eta ceiling : ℝ) (hη : 0 ≤ eta) :
    Monotone (saturatingWeight initial eta ceiling) := by
  intro m n hmn
  apply min_le_min_left
  gcongr

theorem saturatingWeight_eq_ceiling_of_enough_firings
    (initial eta ceiling : ℝ) (firings : ℕ)
    (henough : ceiling ≤ initial + (firings : ℝ) * eta) :
    saturatingWeight initial eta ceiling firings = ceiling := by
  exact min_eq_left henough

theorem saturatingWeight_stays_at_ceiling_after_threshold
    (initial eta ceiling : ℝ) (hη : 0 ≤ eta) (threshold firings : ℕ)
    (henough : ceiling ≤ initial + (threshold : ℝ) * eta)
    (hlater : threshold ≤ firings) :
    saturatingWeight initial eta ceiling firings = ceiling := by
  apply saturatingWeight_eq_ceiling_of_enough_firings
  have hcast : (threshold : ℝ) ≤ (firings : ℝ) := by exact_mod_cast hlater
  nlinarith

theorem unused_coordinate_stays_initial (initial eta ceiling : ℝ)
    (hinitial : initial ≤ ceiling) :
    saturatingWeight initial eta ceiling 0 = initial :=
  saturatingWeight_zero initial eta ceiling hinitial

example : saturatingWeight 1 (1 / 4) 2 4 = 2 := by
  norm_num [saturatingWeight]

example : saturatingWeight 1 (1 / 4) 2 0 = 1 := by
  norm_num [saturatingWeight]

/-! ## Timing-dependent potentiation -/

/-- A positive timing schedule whose `n`th cumulative increment is geometric.
It corresponds to inter-event gaps chosen so the event bump is halved at every
successive firing. -/
noncomputable def sparseTimingWeight (initial eta : ℝ) (firings : ℕ) : ℝ :=
  initial + eta * (1 - (1 / 2 : ℝ) ^ firings)

theorem sparseTimingWeight_strictly_below_limit
    (initial eta : ℝ) (hη : 0 < eta) (firings : ℕ) :
    sparseTimingWeight initial eta firings < initial + eta := by
  have hpow : 0 < (1 / 2 : ℝ) ^ firings := pow_pos (by norm_num) _
  dsimp [sparseTimingWeight]
  nlinarith

theorem infinite_firing_schedule_need_not_reach_ceiling
    (initial eta ceiling : ℝ) (hη : 0 < eta)
    (hceiling : initial + eta < ceiling) (firings : ℕ) :
    sparseTimingWeight initial eta firings < ceiling :=
  (sparseTimingWeight_strictly_below_limit initial eta hη firings).trans hceiling

theorem sparseTimingWeight_tendsto (initial eta : ℝ) :
    Tendsto (sparseTimingWeight initial eta) atTop (𝓝 (initial + eta)) := by
  change Tendsto (fun n : ℕ => initial + eta * (1 - (1 / 2 : ℝ) ^ n))
    atTop (𝓝 (initial + eta))
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsub :
      Tendsto (fun n : ℕ => 1 - (1 / 2 : ℝ) ^ n) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hpow
  have hmul :
      Tendsto (fun n : ℕ => eta * (1 - (1 / 2 : ℝ) ^ n)) atTop
        (𝓝 (eta * (1 - 0))) :=
    tendsto_const_nhds.mul hsub
  have hconst : Tendsto (fun _ : ℕ => initial) atTop (𝓝 initial) :=
    tendsto_const_nhds
  simpa only [sub_zero, mul_one] using hconst.add hmul

/-- General cumulative timing-dependent potentiation with a hard ceiling. -/
noncomputable def timingWeight
    (initial ceiling : ℝ) (bump : ℕ → ℝ) (firings : ℕ) : ℝ :=
  min ceiling (initial + ∑ k ∈ Finset.range firings, bump k)

theorem timingWeight_mono (initial ceiling : ℝ) (bump : ℕ → ℝ)
    (hbump : ∀ k, 0 ≤ bump k) :
    Monotone (timingWeight initial ceiling bump) := by
  apply monotone_nat_of_le_succ
  intro n
  apply min_le_min_left
  simp only [Finset.sum_range_succ]
  linarith [hbump n]

theorem timingWeight_le_ceiling
    (initial ceiling : ℝ) (bump : ℕ → ℝ) (firings : ℕ) :
    timingWeight initial ceiling bump firings ≤ ceiling := by
  exact min_le_left _ _

/-- Every coordinate driven by nonnegative timing increments converges, though
the limit need not be the ceiling. -/
theorem timingWeight_converges (initial ceiling : ℝ) (bump : ℕ → ℝ)
    (hbump : ∀ k, 0 ≤ bump k) :
    ∃ limit : ℝ, Tendsto (timingWeight initial ceiling bump) atTop (𝓝 limit) := by
  let limit := ⨆ n, timingWeight initial ceiling bump n
  refine ⟨limit, tendsto_atTop_ciSup (timingWeight_mono initial ceiling bump hbump) ?_⟩
  refine ⟨ceiling, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact timingWeight_le_ceiling initial ceiling bump n

/-! ## Positive frozen-marking potential -/

def frozenWeightField (eta marking weight : ℝ) : ℝ := eta * marking * weight

noncomputable def frozenWeightPotential (eta marking weight : ℝ) : ℝ :=
  eta * marking * weight ^ 2 / 2

theorem frozenWeightPotential_hasDerivAt (eta marking weight : ℝ) :
    HasDerivAt (frozenWeightPotential eta marking)
      (frozenWeightField eta marking weight) weight := by
  change HasDerivAt (fun w : ℝ => eta * marking * w ^ 2 / 2)
    (eta * marking * weight) weight
  have h := ((((hasDerivAt_id weight).pow 2).const_mul (eta * marking)).div_const 2)
  change HasDerivAt (fun w : ℝ => eta * marking * w ^ 2 / 2)
    (eta * marking * ((2 : ℝ) * weight ^ (2 - 1) * 1) / 2) weight at h
  convert h using 1
  norm_num
  ring

/-! ## Coupled field: Jacobian obstruction -/

abbrev JointState := Fin 2 → ℝ

/-- Coordinates are `(marking, weight)`.  A self-loop conserves its marking,
while each event increments the weight. -/
def jointField (eta : ℝ) (x : JointState) : JointState :=
  ![0, eta * x 0 * x 1]

/-- Analytic Jacobian of `jointField`: rows are field coordinates and columns
are state coordinates. -/
def jointJacobian (eta : ℝ) (x : JointState) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0;
     eta * x 1, eta * x 0]

theorem jointField_weight_partial_marking
    (eta marking weight : ℝ) :
    HasDerivAt (fun m : ℝ => (jointField eta ![m, weight]) 1)
      (eta * weight) marking := by
  change HasDerivAt (fun m : ℝ => eta * m * weight) (eta * weight) marking
  have h := ((hasDerivAt_id marking).const_mul eta).mul_const weight
  change HasDerivAt (fun m : ℝ => eta * m * weight) (eta * 1 * weight) marking at h
  convert h using 1
  ring

theorem jointField_weight_partial_weight
    (eta marking weight : ℝ) :
    HasDerivAt (fun w : ℝ => (jointField eta ![marking, w]) 1)
      (eta * marking) weight := by
  change HasDerivAt (fun w : ℝ => eta * marking * w) (eta * marking) weight
  simpa only [id_eq, mul_one] using
    (hasDerivAt_id weight).const_mul (eta * marking)

def IsSymmetric {n : ℕ} (jacobian : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  jacobian.transpose = jacobian

theorem jointJacobian_not_symmetric (eta : ℝ) (x : JointState)
    (hnonzero : eta * x 1 ≠ 0) :
    ¬ IsSymmetric (jointJacobian eta x) := by
  intro hsymmetric
  have hentry := congrArg (fun matrix => matrix 0 1) hsymmetric
  simp [jointJacobian] at hentry
  rcases hentry with hη | hx
  · exact hnonzero (by rw [hη, zero_mul])
  · exact hnonzero (by rw [hx, mul_zero])

/-- The two cross entries that a scalar potential's Hessian would have to match
if its gradient generated the coupled one-synapse field. -/
def MatchesJointJacobianAt (potential : JointState → ℝ) (eta : ℝ)
    (x : JointState) : Prop :=
  let em : JointState := ![1, 0]
  let ew : JointState := ![0, 1]
  fderiv ℝ (fderiv ℝ potential) x em ew = eta * x 1 ∧
    fderiv ℝ (fderiv ℝ potential) x ew em = 0

/-- No twice continuously differentiable Euclidean scalar potential can have
the coupled field's Jacobian at a point with positive learning rate and weight.
This is the finite-dimensional integrability obstruction, not a claim that the
field lacks every possible Lyapunov function. -/
theorem no_smooth_joint_potential_at (eta : ℝ) (x : JointState)
    (hnonzero : eta * x 1 ≠ 0) :
    ¬ ∃ potential : JointState → ℝ,
        ContDiff ℝ 2 potential ∧ MatchesJointJacobianAt potential eta x := by
  rintro ⟨potential, hsmooth, hmatch⟩
  let em : JointState := ![1, 0]
  let ew : JointState := ![0, 1]
  have hsymmetric :
      fderiv ℝ (fderiv ℝ potential) x em ew =
        fderiv ℝ (fderiv ℝ potential) x ew em := by
    exact hsmooth.contDiffAt.isSymmSndFDerivAt (by simp) em ew
  have hleft : fderiv ℝ (fderiv ℝ potential) x em ew = eta * x 1 := hmatch.1
  have hright : fderiv ℝ (fderiv ℝ potential) x ew em = 0 := hmatch.2
  apply hnonzero
  linarith

example : ¬ IsSymmetric (jointJacobian 1 ![1, 1]) := by
  exact jointJacobian_not_symmetric 1 ![1, 1] (by norm_num)

#print axioms saturatingWeight_succ
#print axioms saturatingWeight_stays_at_ceiling_after_threshold
#print axioms infinite_firing_schedule_need_not_reach_ceiling
#print axioms timingWeight_converges
#print axioms frozenWeightPotential_hasDerivAt
#print axioms jointField_weight_partial_marking
#print axioms jointField_weight_partial_weight
#print axioms jointJacobian_not_symmetric
#print axioms no_smooth_joint_potential_at

end Mettapedia.MachineLearning.NeuralNetworks.LocalLearning.WeightedGSLT
