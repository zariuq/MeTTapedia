import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic

/-!
# Finite Regime-Mixture Theorems

This module isolates the first theorem family behind the higher-order Chapter 11
benchmark story.

The intended reading is:

- `w r` is posterior mass on latent regime `r`,
- `q r` is the branch query value under regime `r`,
- `mixtureValue w q` is the unresolved broad-query marginal.

The goal is to prove the first clean theoremic layer for:

- direct continuation approximation under posterior concentration,
- mixture optimality under squared loss,
- reveal/value-of-information criteria.
-/

namespace Mettapedia.Logic.PLNRegimeMixtureTheorems

open scoped BigOperators

variable {R : Type*} [Fintype R] [DecidableEq R]

/-- Finite real-valued posterior weights on latent regimes. -/
def ValidRegimeWeights (w : R → ℝ) : Prop :=
  (∀ r, 0 ≤ w r) ∧ ∑ r, w r = 1

/-- Weighted marginal query value over latent regimes. -/
def mixtureValue (w q : R → ℝ) : ℝ :=
  ∑ r, w r * q r

/-- Radius of disagreement away from a designated regime.  The empty off-branch
case is interpreted as radius `0`. -/
def branchRadiusNN (q : R → ℝ) (r0 : R) : NNReal :=
  (Finset.univ.erase r0).sup (fun r : R => (⟨|q r - q r0|, abs_nonneg _⟩ : NNReal))

/-- Real-valued view of `branchRadiusNN`. -/
def branchRadius (q : R → ℝ) (r0 : R) : ℝ :=
  (branchRadiusNN q r0 : ℝ)

/-- Expected squared loss of a constant predictor `x` against branch values `q`
under posterior weights `w`. -/
def expectedSquaredLoss (w q : R → ℝ) (x : ℝ) : ℝ :=
  ∑ r, w r * (x - q r)^2

/-- Mixture variance: the squared-loss risk of the unresolved mixture predictor. -/
def mixtureVariance (w q : R → ℝ) : ℝ :=
  expectedSquaredLoss w q (mixtureValue w q)

/-- Reveal gain relative to the unrevealed mixture predictor. -/
def revealGain (w q : R → ℝ) (c : ℝ) : ℝ :=
  mixtureVariance w q - c

theorem branchRadius_nonneg (q : R → ℝ) (r0 : R) :
    0 ≤ branchRadius q r0 := by
  exact NNReal.coe_nonneg _

theorem abs_sub_le_branchRadius
    (q : R → ℝ) (r0 r : R) (hr : r ≠ r0) :
    |q r - q r0| ≤ branchRadius q r0 := by
  have hnn :
      (⟨|q r - q r0|, abs_nonneg _⟩ : NNReal) ≤ branchRadiusNN q r0 := by
    have hmem : r ∈ Finset.univ.erase r0 := by
      simp [Finset.mem_erase, hr]
    exact Finset.le_sup (f := fun s : R => (⟨|q s - q r0|, abs_nonneg _⟩ : NNReal)) hmem
  exact_mod_cast hnn

theorem sum_weights_erase
    {w : R → ℝ} (hw : ValidRegimeWeights w) (r0 : R) :
    Finset.sum (Finset.univ.erase r0) w = 1 - w r0 := by
  rcases hw with ⟨_, hsum⟩
  have hsplit : ∑ r : R, w r = w r0 + Finset.sum (Finset.univ.erase r0) w := by
    rw [add_comm, Finset.sum_erase_add (s := Finset.univ) (f := w) (a := r0) (by simp)]
  linarith

omit [DecidableEq R] in
theorem mixtureValue_nonneg_of_unit_interval
    {w q : R → ℝ}
    (hw : ValidRegimeWeights w)
    (hq : ∀ r, 0 ≤ q r ∧ q r ≤ 1) :
    0 ≤ mixtureValue w q := by
  rcases hw with ⟨hw_nonneg, hsum⟩
  unfold mixtureValue
  exact Finset.sum_nonneg fun r _ => mul_nonneg (hw_nonneg r) (hq r).1

omit [DecidableEq R] in
theorem mixtureValue_le_one_of_unit_interval
    {w q : R → ℝ}
    (hw : ValidRegimeWeights w)
    (hq : ∀ r, 0 ≤ q r ∧ q r ≤ 1) :
    mixtureValue w q ≤ 1 := by
  rcases hw with ⟨hw_nonneg, hsum⟩
  unfold mixtureValue
  calc
    ∑ r : R, w r * q r ≤ ∑ r : R, w r * 1 := by
      exact Finset.sum_le_sum fun r _ => by
        exact mul_le_mul_of_nonneg_left (hq r).2 (hw_nonneg r)
    _ = ∑ r : R, w r := by simp
    _ = 1 := hsum

theorem mixtureValue_sub_branch_eq_sum_erase
    {w q : R → ℝ}
    (hw : ValidRegimeWeights w)
    (r0 : R) :
    mixtureValue w q - q r0 =
      Finset.sum (Finset.univ.erase r0) (fun r => w r * (q r - q r0)) := by
  rcases hw with ⟨_, hsum⟩
  calc
    mixtureValue w q - q r0
      = mixtureValue w q - (∑ r : R, w r) * q r0 := by
          simp [hsum]
    _ = mixtureValue w q - ∑ r : R, w r * q r0 := by
          rw [Finset.sum_mul]
    _ = (∑ r : R, w r * q r) - ∑ r : R, w r * q r0 := by
          rw [mixtureValue]
    _ = ∑ r : R, (w r * q r - w r * q r0) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ r : R, w r * (q r - q r0) := by
          refine Finset.sum_congr rfl ?_
          intro r _
          ring
    _ = w r0 * (q r0 - q r0) + Finset.sum (Finset.univ.erase r0) (fun r => w r * (q r - q r0)) := by
          rw [add_comm, Finset.sum_erase_add (s := Finset.univ)
            (f := fun r => w r * (q r - q r0)) (a := r0) (by simp)]
    _ = Finset.sum (Finset.univ.erase r0) (fun r => w r * (q r - q r0)) := by
          simp

theorem directApprox_error_le_residualMass_mul_branchRadius
    {w q : R → ℝ}
    (hw : ValidRegimeWeights w)
    (r0 : R) :
    |mixtureValue w q - q r0| ≤
      (1 - w r0) * branchRadius q r0 := by
  rw [mixtureValue_sub_branch_eq_sum_erase hw r0]
  rcases hw with ⟨hw_nonneg, hsum⟩
  calc
    |Finset.sum (Finset.univ.erase r0) (fun r => w r * (q r - q r0))| ≤
        Finset.sum (Finset.univ.erase r0) (fun r => |w r * (q r - q r0)|) := by
          simpa using Finset.abs_sum_le_sum_abs (f := fun r => w r * (q r - q r0))
            (s := Finset.univ.erase r0)
    _ = Finset.sum (Finset.univ.erase r0) (fun r => w r * |q r - q r0|) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          rw [abs_mul, abs_of_nonneg (hw_nonneg r)]
    _ ≤ Finset.sum (Finset.univ.erase r0) (fun r => w r * branchRadius q r0) := by
          exact Finset.sum_le_sum fun r hr => by
            exact mul_le_mul_of_nonneg_left
              (abs_sub_le_branchRadius q r0 r (by
                intro hrr
                exact Finset.mem_erase.mp hr |>.1 hrr))
              (hw_nonneg r)
    _ = Finset.sum (Finset.univ.erase r0) w * branchRadius q r0 := by
          rw [← Finset.sum_mul]
    _ = (1 - w r0) * branchRadius q r0 := by
          have hweights : ValidRegimeWeights w := ⟨hw_nonneg, hsum⟩
          rw [sum_weights_erase hweights r0]

omit [DecidableEq R] in
theorem weighted_centered_sum_eq_zero
    {w q : R → ℝ}
    (hw : ValidRegimeWeights w) :
    ∑ r : R, w r * (q r - mixtureValue w q) = 0 := by
  rcases hw with ⟨_, hsum⟩
  calc
    ∑ r : R, w r * (q r - mixtureValue w q)
      = ∑ r : R, (w r * q r - w r * mixtureValue w q) := by
          refine Finset.sum_congr rfl ?_
          intro r _
          ring
    _ = (∑ r : R, w r * q r) - ∑ r : R, w r * mixtureValue w q := by
          rw [Finset.sum_sub_distrib]
    _ = mixtureValue w q - (∑ r : R, w r) * mixtureValue w q := by
          rw [mixtureValue, Finset.sum_mul]
    _ = mixtureValue w q - mixtureValue w q := by simp [hsum]
    _ = 0 := by ring

omit [DecidableEq R] in
theorem expectedSquaredLoss_decomposition
    {w q : R → ℝ}
    (hw : ValidRegimeWeights w)
    (x : ℝ) :
    expectedSquaredLoss w q x =
      mixtureVariance w q + (x - mixtureValue w q)^2 := by
  let m := mixtureValue w q
  have hsplit :
      expectedSquaredLoss w q x =
        (∑ r : R, w r * (x - m)^2) -
          (∑ r : R, (2 * (x - m)) * (w r * (q r - m))) +
          ∑ r : R, w r * (q r - m)^2 := by
    unfold expectedSquaredLoss
    calc
      ∑ r : R, w r * (x - q r)^2
          = ∑ r : R,
              (w r * (x - m)^2 -
                (2 * (x - m)) * (w r * (q r - m)) +
                w r * (q r - m)^2) := by
              refine Finset.sum_congr rfl ?_
              intro r _
              ring_nf
      _ = (∑ r : R, w r * (x - m)^2) -
            (∑ r : R, (2 * (x - m)) * (w r * (q r - m))) +
            ∑ r : R, w r * (q r - m)^2 := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hconst :
      ∑ r : R, w r * (x - m)^2 = (x - m)^2 := by
    rcases hw with ⟨_, hsum⟩
    calc
      ∑ r : R, w r * (x - m)^2 = (∑ r : R, w r) * (x - m)^2 := by
        rw [Finset.sum_mul]
      _ = (x - m)^2 := by simp [hsum]
  have hcross :
      ∑ r : R, (2 * (x - m)) * (w r * (q r - m)) = 0 := by
    calc
      ∑ r : R, (2 * (x - m)) * (w r * (q r - m))
          = (2 * (x - m)) * ∑ r : R, w r * (q r - m) := by
              rw [Finset.mul_sum]
      _ = 0 := by
            rw [weighted_centered_sum_eq_zero hw]
            ring
  have hvar :
      mixtureVariance w q = ∑ r : R, w r * (q r - m)^2 := by
    unfold mixtureVariance expectedSquaredLoss
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [show mixtureValue w q = m by rfl]
    ring
  calc
    expectedSquaredLoss w q x
        = (x - m)^2 + ∑ r : R, w r * (q r - m)^2 := by
      rw [hsplit, hconst, hcross]
      ring
    _ = mixtureVariance w q + (x - mixtureValue w q)^2 := by
      rw [hvar, show m = mixtureValue w q by rfl]
      ring

omit [DecidableEq R] in
theorem expectedSquaredLoss_mixture_le
    {w q : R → ℝ}
    (hw : ValidRegimeWeights w)
    (x : ℝ) :
    mixtureVariance w q ≤ expectedSquaredLoss w q x := by
  rw [expectedSquaredLoss_decomposition hw x]
  nlinarith [sq_nonneg (x - mixtureValue w q)]

omit [DecidableEq R] in
theorem expectedSquaredLoss_single_regime_eq_directRisk
    {w q : R → ℝ}
    (r0 : R) :
    expectedSquaredLoss w q (q r0) =
      ∑ r : R, w r * (q r0 - q r)^2 := by
  rfl

omit [DecidableEq R] in
theorem expectedSquaredLoss_le_one_of_unit_interval
    {w q : R → ℝ}
    (hw : ValidRegimeWeights w)
    (hq : ∀ r, 0 ≤ q r ∧ q r ≤ 1)
    {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) :
    expectedSquaredLoss w q x ≤ 1 := by
  rcases hw with ⟨hw_nonneg, hsum⟩
  have hsq : ∀ r, (x - q r)^2 ≤ 1 := by
    intro r
    have hdiff_le : |x - q r| ≤ 1 := by
      have hxq_lower : -1 ≤ x - q r := by linarith [hx.1, (hq r).2]
      have hxq_upper : x - q r ≤ 1 := by linarith [hx.2, (hq r).1]
      rw [abs_le]
      constructor <;> linarith
    simpa using (sq_le_one_iff_abs_le_one (a := x - q r)).2 hdiff_le
  unfold expectedSquaredLoss
  calc
    ∑ r : R, w r * (x - q r)^2 ≤ ∑ r : R, w r * 1 := by
      exact Finset.sum_le_sum fun r _ => by
        exact mul_le_mul_of_nonneg_left (hsq r) (hw_nonneg r)
    _ = ∑ r : R, w r := by simp
    _ = 1 := hsum

omit [DecidableEq R] in
theorem mixtureVariance_le_one_of_unit_interval
    {w q : R → ℝ}
    (hw : ValidRegimeWeights w)
    (hq : ∀ r, 0 ≤ q r ∧ q r ≤ 1) :
    mixtureVariance w q ≤ 1 := by
  exact expectedSquaredLoss_le_one_of_unit_interval hw hq
    ⟨mixtureValue_nonneg_of_unit_interval hw hq, mixtureValue_le_one_of_unit_interval hw hq⟩

omit [DecidableEq R] in
theorem revealPreferred_if_cost_lt_variance
    {w q : R → ℝ} {c : ℝ}
    (hc : c < mixtureVariance w q) :
    0 < revealGain w q c := by
  simpa [revealGain] using sub_pos.mpr hc

omit [DecidableEq R] in
theorem revealPreferred_to_direct_of_cost_lt_variance
    {w q : R → ℝ} (hw : ValidRegimeWeights w) {c : ℝ} (r0 : R)
    (hc : c < mixtureVariance w q) :
    c < expectedSquaredLoss w q (q r0) := by
  have hmix := expectedSquaredLoss_mixture_le (w := w) (q := q) hw (q r0)
  unfold mixtureVariance at hmix
  exact lt_of_lt_of_le hc hmix

end Mettapedia.Logic.PLNRegimeMixtureTheorems
