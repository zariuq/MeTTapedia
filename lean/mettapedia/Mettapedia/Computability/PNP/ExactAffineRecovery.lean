import Mettapedia.Computability.PNP.AffineDecisionListFamily
import Mettapedia.Computability.PNP.SparseThresholdAffineFamily
import Mettapedia.Computability.PNP.SameRouteInterface

/-!
# P vs NP grassroots: exact-surface recovery bounds for affine candidate classes

This file turns the current exact-surface affine candidate classes into actual
finite-sampling recovery theorems.

The earlier modules proved code budgets for four explicit classes on the exact
post-switch surface:

* affine column predictors on `a`,
* bounded affine-feature predictors,
* sparse-threshold affine predictors,
* affine decision-list predictors.

Here we package the corresponding pulled-back bit families on the exact surface
and show that once the target lies in one of those classes, the weighted exact
recovery theorem from `SameRouteInterface.lean` applies immediately with the
matching bit budget.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ}

/-- The exact-surface bit family induced by affine column predictors on the
retained VV column view. -/
noncomputable def exactAffineColumnBitFamily (Z : Type*) (k : ℕ) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k) (k + 1) :=
  IndexedPredictorFamily.pullbackBitFamily
    (fun u : ExactVisiblePostSwitchSurface Z k => u.a)
    (affineColumnBitFamily k)

/-- The exact-surface bit family induced by bounded affine-feature predictors
on the retained VV column view. -/
noncomputable def exactAffineFeatureBitFamily (Z : Type*) (r k : ℕ) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k) (r * (k + 1) + 2 ^ r) :=
  IndexedPredictorFamily.pullbackBitFamily
    (fun u : ExactVisiblePostSwitchSurface Z k => u.a)
    (affineFeatureBitFamily r k)

/-- The exact-surface bit family induced by sparse-threshold affine predictors
on the retained VV column view. -/
noncomputable def exactSparseThresholdAffineBitFamily (Z : Type*) (r k : ℕ) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k) (r * (k + 3)) :=
  IndexedPredictorFamily.pullbackBitFamily
    (fun u : ExactVisiblePostSwitchSurface Z k => u.a)
    (sparseThresholdAffineBitFamily r k)

/-- The exact-surface bit family induced by affine decision-list predictors on
the retained VV column view. -/
noncomputable def exactAffineDecisionListBitFamily (Z : Type*) (r k : ℕ) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k) (r * (k + 2) + 1) :=
  IndexedPredictorFamily.pullbackBitFamily
    (fun u : ExactVisiblePostSwitchSurface Z k => u.a)
    (affineDecisionListBitFamily r k)

@[simp] theorem exactAffineColumnBitFamily_decode_encodeAffineColumnIndex
    (idx : AffineColumnCode k) :
    (exactAffineColumnBitFamily Z k).decode (encodeAffineColumnIndex idx)
      = fun u : ExactVisiblePostSwitchSurface Z k => affineColumnPredict idx.1 idx.2 u.a := by
  funext u
  have h := congrFun (affineColumnBitFamily_decode_encodeAffineColumnIndex (k := k) idx) u.a
  simpa [exactAffineColumnBitFamily, IndexedPredictorFamily.pullbackBitFamily] using h

@[simp] theorem exactAffineFeatureBitFamily_decode_code
    (code : AffineFeatureCode r k) :
    (exactAffineFeatureBitFamily Z r k).decode (affineFeatureCodeEquivBitCode r k code)
      = fun u : ExactVisiblePostSwitchSurface Z k => affineFeaturePredict code u.a := by
  funext u
  simp [exactAffineFeatureBitFamily, IndexedPredictorFamily.pullbackBitFamily, affineFeatureBitFamily]

@[simp] theorem exactSparseThresholdAffineBitFamily_decode_code
    (code : SparseThresholdAffineCode r k) :
    (exactSparseThresholdAffineBitFamily Z r k).decode
        (sparseThresholdAffineCodeEquivBitCode r k code)
      = fun u : ExactVisiblePostSwitchSurface Z k => sparseThresholdAffinePredict code u.a := by
  funext u
  simp [exactSparseThresholdAffineBitFamily, IndexedPredictorFamily.pullbackBitFamily,
    sparseThresholdAffineBitFamily]

@[simp] theorem exactAffineDecisionListBitFamily_decode_code
    (code : AffineDecisionListCode r k) :
    (exactAffineDecisionListBitFamily Z r k).decode
        (affineDecisionListCodeEquivBitCode r k code)
      = fun u : ExactVisiblePostSwitchSurface Z k => affineDecisionListPredict code u.a := by
  funext u
  simp [exactAffineDecisionListBitFamily, IndexedPredictorFamily.pullbackBitFamily,
    affineDecisionListBitFamily]

theorem exactAffineColumnRecoveryLowerBound
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ idx : AffineColumnCode k,
      target = fun u : ExactVisiblePostSwitchSurface Z k => affineColumnPredict idx.1 idx.2 u.a)
    {q : ℝ≥0∞}
    (hq :
      ∀ c : (exactAffineColumnBitFamily Z k).toEncodedFamily.BadCodes target,
        agreementMass μ target ((exactAffineColumnBitFamily Z k).decode c.1) ≤ q) :
    1 - (2 ^ (k + 1) : ℝ≥0∞) * q ^ m ≤
      (exactAffineColumnBitFamily Z k).bitExactRecoverySampleMass μ target m := by
  rcases htarget with ⟨idx, rfl⟩
  refine BitEncodedClassifierFamily.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    (F := exactAffineColumnBitFamily Z k)
    (μ := μ) (target := fun u : ExactVisiblePostSwitchSurface Z k => affineColumnPredict idx.1 idx.2 u.a)
    (m := m) ?_ hq
  refine ⟨encodeAffineColumnIndex idx, ?_⟩
  exact exactAffineColumnBitFamily_decode_encodeAffineColumnIndex (Z := Z) (k := k) idx

theorem exactAffineFeatureRecoveryLowerBound
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : AffineFeatureCode r k,
      target = fun u : ExactVisiblePostSwitchSurface Z k => affineFeaturePredict code u.a)
    {q : ℝ≥0∞}
    (hq :
      ∀ c : (exactAffineFeatureBitFamily Z r k).toEncodedFamily.BadCodes target,
        agreementMass μ target ((exactAffineFeatureBitFamily Z r k).decode c.1) ≤ q) :
    1 - (2 ^ (r * (k + 1) + 2 ^ r) : ℝ≥0∞) * q ^ m ≤
      (exactAffineFeatureBitFamily Z r k).bitExactRecoverySampleMass μ target m := by
  rcases htarget with ⟨code, rfl⟩
  refine BitEncodedClassifierFamily.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    (F := exactAffineFeatureBitFamily Z r k)
    (μ := μ) (target := fun u : ExactVisiblePostSwitchSurface Z k => affineFeaturePredict code u.a)
    (m := m) ?_ hq
  refine ⟨affineFeatureCodeEquivBitCode r k code, ?_⟩
  exact exactAffineFeatureBitFamily_decode_code (Z := Z) (r := r) (k := k) code

theorem exactSparseThresholdAffineRecoveryLowerBound
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : SparseThresholdAffineCode r k,
      target = fun u : ExactVisiblePostSwitchSurface Z k => sparseThresholdAffinePredict code u.a)
    {q : ℝ≥0∞}
    (hq :
      ∀ c : (exactSparseThresholdAffineBitFamily Z r k).toEncodedFamily.BadCodes target,
        agreementMass μ target ((exactSparseThresholdAffineBitFamily Z r k).decode c.1) ≤ q) :
    1 - (2 ^ (r * (k + 3)) : ℝ≥0∞) * q ^ m ≤
      (exactSparseThresholdAffineBitFamily Z r k).bitExactRecoverySampleMass μ target m := by
  rcases htarget with ⟨code, rfl⟩
  refine BitEncodedClassifierFamily.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    (F := exactSparseThresholdAffineBitFamily Z r k)
    (μ := μ)
    (target := fun u : ExactVisiblePostSwitchSurface Z k => sparseThresholdAffinePredict code u.a)
    (m := m) ?_ hq
  refine ⟨sparseThresholdAffineCodeEquivBitCode r k code, ?_⟩
  exact exactSparseThresholdAffineBitFamily_decode_code (Z := Z) (r := r) (k := k) code

theorem exactAffineDecisionListRecoveryLowerBound
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : AffineDecisionListCode r k,
      target = fun u : ExactVisiblePostSwitchSurface Z k => affineDecisionListPredict code u.a)
    {q : ℝ≥0∞}
    (hq :
      ∀ c : (exactAffineDecisionListBitFamily Z r k).toEncodedFamily.BadCodes target,
        agreementMass μ target ((exactAffineDecisionListBitFamily Z r k).decode c.1) ≤ q) :
    1 - (2 ^ (r * (k + 2) + 1) : ℝ≥0∞) * q ^ m ≤
      (exactAffineDecisionListBitFamily Z r k).bitExactRecoverySampleMass μ target m := by
  rcases htarget with ⟨code, rfl⟩
  refine BitEncodedClassifierFamily.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    (F := exactAffineDecisionListBitFamily Z r k)
    (μ := μ)
    (target := fun u : ExactVisiblePostSwitchSurface Z k => affineDecisionListPredict code u.a)
    (m := m) ?_ hq
  refine ⟨affineDecisionListCodeEquivBitCode r k code, ?_⟩
  exact exactAffineDecisionListBitFamily_decode_code (Z := Z) (r := r) (k := k) code

end

end Mettapedia.Computability.PNP
