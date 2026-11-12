import Mettapedia.ProbabilityTheory.BayesianInference.Variational

/-!
# Finite trajectory free energy and its Gibbs optimizer

The trajectory carrier is any finite type. Laws use the existing probability
simplex, and divergence uses the existing support-qualified finite KL sum.
The cost and reference are independent inputs. A positive temperature is
explicit; no control policy or causal realizability is inferred from a tilt.

This is the finite Gibbs identity used in Goertzel, *Trajectory Free Energy
and Integrated Organization* (2026), Section 2.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy

open scoped BigOperators
open Mettapedia.InformationTheory Mettapedia.InformationTheory.FiniteRV
open Mettapedia.ProbabilityTheory.BayesianInference

variable {Ω : Type*} [Fintype Ω]

def expectedCost (law : Prob Ω) (cost : Ω → ℝ) : ℝ := ∑ x, law.1 x * cost x

def freeEnergy (reference : Prob Ω) (cost : Ω → ℝ) (temperature : ℝ) (law : Prob Ω) : ℝ :=
  expectedCost law cost + temperature * klSum law.1 reference.1

def weight (cost : Ω → ℝ) (temperature : ℝ) (x : Ω) : ℝ :=
  Real.exp (-cost x / temperature)

omit [Fintype Ω] in
theorem weight_pos (cost : Ω → ℝ) (temperature : ℝ) (x : Ω) : 0 < weight cost temperature x :=
  Real.exp_pos _

def partition (reference : Prob Ω) (cost : Ω → ℝ) (temperature : ℝ) : ℝ :=
  evidence reference (weight cost temperature)

theorem partition_pos (reference : Prob Ω) (cost : Ω → ℝ) (temperature : ℝ) :
    0 < partition reference cost temperature := by
  obtain ⟨x, member, positive⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun x (_ : x ∈ (Finset.univ : Finset Ω)) => reference.2.1 x)).mp
      (show 0 < ∑ x, reference.1 x by rw [reference.2.2]; norm_num)
  exact lt_of_lt_of_le (mul_pos positive (weight_pos cost temperature x))
    (Finset.single_le_sum (fun y _ => mul_nonneg (reference.2.1 y) (weight_pos cost temperature y).le) member)

def gibbs (reference : Prob Ω) (cost : Ω → ℝ) (temperature : ℝ)
    (_positive : 0 < temperature) : Prob Ω :=
  posterior reference (weight cost temperature) (fun x => (weight_pos cost temperature x).le)
    (partition_pos reference cost temperature)

theorem gibbs_apply (reference : Prob Ω) (cost : Ω → ℝ) (temperature : ℝ)
    (positive : 0 < temperature) (x : Ω) :
    (gibbs reference cost temperature positive).1 x =
      reference.1 x * weight cost temperature x / partition reference cost temperature := rfl

theorem gibbs_pos_iff (reference : Prob Ω) (cost : Ω → ℝ) (temperature : ℝ)
    (positive : 0 < temperature) (x : Ω) :
    0 < (gibbs reference cost temperature positive).1 x ↔ 0 < reference.1 x := by
  rw [gibbs_apply]
  exact (div_pos_iff_of_pos_right (partition_pos reference cost temperature)).trans
    (mul_pos_iff_of_pos_right (weight_pos cost temperature x))

theorem gibbs_supported (reference : Prob Ω) (cost : Ω → ℝ) (temperature : ℝ)
    (positive : 0 < temperature) : SupportedBy (gibbs reference cost temperature positive) reference.1 :=
  fun x present => (gibbs_pos_iff reference cost temperature positive x).mp present

theorem support_weighted (reference law : Prob Ω) (cost : Ω → ℝ) (temperature : ℝ)
    (supported : SupportedBy law reference.1) :
    SupportedBy law (fun x => reference.1 x * weight cost temperature x) :=
  fun x present => mul_pos (supported x present) (weight_pos cost temperature x)

theorem scaled_variational (reference law : Prob Ω) (cost : Ω → ℝ) (temperature : ℝ)
    (positive : 0 < temperature) (supported : SupportedBy law reference.1) :
    temperature * variationalFreeEnergy reference (weight cost temperature) law =
      freeEnergy reference cost temperature law := by
  rw [variationalFreeEnergy_complexity_accuracy reference law (weight cost temperature)
    (support_weighted reference law cost temperature supported), mul_sub]
  have costIdentity : temperature * ∑ x, law.1 x * Real.log (weight cost temperature x) =
      -expectedCost law cost := by
    rw [Finset.mul_sum, expectedCost, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [weight, Real.log_exp]
    field_simp [positive.ne']
  rw [costIdentity]
  unfold freeEnergy
  ring

theorem gibbs_identity (reference law : Prob Ω) (cost : Ω → ℝ) (temperature : ℝ)
    (positive : 0 < temperature) (supported : SupportedBy law reference.1) :
    freeEnergy reference cost temperature law =
      -temperature * Real.log (partition reference cost temperature) +
        temperature * klSum law.1 (gibbs reference cost temperature positive).1 := by
  rw [← scaled_variational reference law cost temperature positive supported,
    variationalFreeEnergy_eq reference law (weight cost temperature)
      (fun x => (weight_pos cost temperature x).le) (partition_pos reference cost temperature)
      (support_weighted reference law cost temperature supported)]
  dsimp only [gibbs, partition]
  ring

theorem gibbs_value (reference : Prob Ω) (cost : Ω → ℝ) (temperature : ℝ)
    (positive : 0 < temperature) :
    freeEnergy reference cost temperature (gibbs reference cost temperature positive) =
      -temperature * Real.log (partition reference cost temperature) := by
  rw [gibbs_identity reference _ cost temperature positive (gibbs_supported reference cost temperature positive),
    klSum_self_eq_zero _ (gibbs reference cost temperature positive).2.1, mul_zero, add_zero]

theorem gibbs_minimizes (reference law : Prob Ω) (cost : Ω → ℝ) (temperature : ℝ)
    (positive : 0 < temperature) (supported : SupportedBy law reference.1) :
    freeEnergy reference cost temperature (gibbs reference cost temperature positive) ≤
      freeEnergy reference cost temperature law := by
  rw [gibbs_value, gibbs_identity reference law cost temperature positive supported]
  have divergenceNonnegative := klSumOn_nonneg Finset.univ law.1
    (gibbs reference cost temperature positive).1 (fun x _ => law.2.1 x)
    (fun x _ => (gibbs reference cost temperature positive).2.1 x)
    (fun x _ present => (gibbs_pos_iff reference cost temperature positive x).mpr (supported x present))
    (by rw [law.2.2, (gibbs reference cost temperature positive).2.2])
  exact le_add_of_nonneg_right (mul_nonneg positive.le divergenceNonnegative)

theorem freeEnergy_gap (reference law : Prob Ω) (cost : Ω → ℝ) (temperature : ℝ)
    (positive : 0 < temperature) (supported : SupportedBy law reference.1) :
    freeEnergy reference cost temperature law -
      freeEnergy reference cost temperature (gibbs reference cost temperature positive) =
        temperature * klSum law.1 (gibbs reference cost temperature positive).1 := by
  rw [gibbs_value, gibbs_identity reference law cost temperature positive supported]
  ring

theorem gibbs_unique (reference law : Prob Ω) (cost : Ω → ℝ) (temperature : ℝ)
    (positive : 0 < temperature) (supported : SupportedBy law reference.1) :
    freeEnergy reference cost temperature law =
      freeEnergy reference cost temperature (gibbs reference cost temperature positive) ↔
        law = gibbs reference cost temperature positive := by
  constructor
  · intro same
    have zero : klSum law.1 (gibbs reference cost temperature positive).1 = 0 := by
      have gap := freeEnergy_gap reference law cost temperature positive supported
      rw [same, sub_self] at gap
      exact (mul_eq_zero.mp gap.symm).resolve_left positive.ne'
    apply Subtype.ext
    funext x
    exact klSumOn_eq_zero_imp Finset.univ law.1 (gibbs reference cost temperature positive).1
      (fun y _ => law.2.1 y) (fun y _ => (gibbs reference cost temperature positive).2.1 y)
      (fun y _ present => (gibbs_pos_iff reference cost temperature positive y).mpr (supported y present))
      (by rw [law.2.2, (gibbs reference cost temperature positive).2.2]) zero x (Finset.mem_univ x)
  · rintro rfl
    rfl

theorem approximate_optimality_iff (reference law : Prob Ω) (cost : Ω → ℝ) (temperature : ℝ)
    (positive : 0 < temperature) (supported : SupportedBy law reference.1) (error : ℝ) :
    freeEnergy reference cost temperature law ≤
      freeEnergy reference cost temperature (gibbs reference cost temperature positive) + error ↔
        klSum law.1 (gibbs reference cost temperature positive).1 ≤ error / temperature := by
  rw [le_div_iff₀ positive]
  have gap := freeEnergy_gap reference law cost temperature positive supported
  constructor <;> intro bound <;> nlinarith

end Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy
