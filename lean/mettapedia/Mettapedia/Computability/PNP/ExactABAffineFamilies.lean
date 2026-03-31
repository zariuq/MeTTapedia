import Mettapedia.Computability.PNP.ExactABDecisionListFamily
import Mettapedia.Computability.PNP.ExactAffineRecovery

/-!
# P vs NP grassroots: affine candidate families on the raw `(a, b)` surface

The exact post-switch surface now has one fully concrete reduced extractor:
the raw visible bit vector obtained from `(a, b)`.

This file reuses the generic affine-family machinery on top of that extractor.
So besides the plain raw decision-list family, we now get a richer exact-surface
candidate ladder on the same visible bit surface:

* bounded affine-feature predictors on the raw `(a, b)` bits,
* sparse-threshold affine predictors on the raw `(a, b)` bits,
* affine decision-list predictors on the raw `(a, b)` bits.

All three inherit explicit code budgets and weighted exact-recovery bounds.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ}

/-- The exact-surface bit family induced by bounded affine-feature predictors
on the raw exact visible bit surface `(a, b)`. -/
noncomputable def exactABAffineFeatureBitFamily (Z : Type*) (r k : ℕ) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k)
      (r * ((k + k) + 1) + 2 ^ r) :=
  IndexedPredictorFamily.pullbackBitFamily
    (exactABVisibleData (Z := Z) (k := k))
    (affineFeatureBitFamily r (k + k))

/-- The exact-surface bit family induced by sparse-threshold affine predictors
on the raw exact visible bit surface `(a, b)`. -/
noncomputable def exactABSparseThresholdAffineBitFamily (Z : Type*) (r k : ℕ) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k)
      (r * ((k + k) + 3)) :=
  IndexedPredictorFamily.pullbackBitFamily
    (exactABVisibleData (Z := Z) (k := k))
    (sparseThresholdAffineBitFamily r (k + k))

/-- The exact-surface bit family induced by affine decision-list predictors on
the raw exact visible bit surface `(a, b)`. -/
noncomputable def exactABAffineDecisionListBitFamily (Z : Type*) (r k : ℕ) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k)
      (r * ((k + k) + 2) + 1) :=
  IndexedPredictorFamily.pullbackBitFamily
    (exactABVisibleData (Z := Z) (k := k))
    (affineDecisionListBitFamily r (k + k))

/-- Exact-surface specialization: the switched family depends only on a bounded
affine-feature summary of the raw exact visible bits `(a, b)`. -/
abbrev RealizedByExactABAffineFeatureFamily
    {Z : Type*} {Index : Type*}
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  RealizedByAffineFeatureFamily (r := r) (k := k + k)
    (exactABVisibleData (Z := Z) (k := k)) G

/-- Exact-surface specialization: the switched family depends only on a
sparse-threshold affine summary of the raw exact visible bits `(a, b)`. -/
abbrev RealizedByExactABSparseThresholdAffineFamily
    {Z : Type*} {Index : Type*}
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  RealizedBySparseThresholdAffineFamily (r := r) (k := k + k)
    (exactABVisibleData (Z := Z) (k := k)) G

/-- Exact-surface specialization: the switched family depends only on an
affine decision-list summary of the raw exact visible bits `(a, b)`. -/
abbrev RealizedByExactABAffineDecisionListFamily
    {Z : Type*} {Index : Type*}
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  RealizedByAffineDecisionListFamily (r := r) (k := k + k)
    (exactABVisibleData (Z := Z) (k := k)) G

theorem exactVisibleCompressionTarget_of_realizedByExactABAffineFeatureFamily
    {Z : Type*} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByExactABAffineFeatureFamily (r := r) (Z := Z) (k := k) (Index := Index) G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G
      (r * ((k + k) + 1) + 2 ^ r) := by
  exact hasBitBudget_of_realizedByAffineFeatureFamily (r := r) (k := k + k) hreal

theorem exactVisibleCompressionTarget_of_realizedByExactABSparseThresholdAffineFamily
    {Z : Type*} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByExactABSparseThresholdAffineFamily
        (r := r) (Z := Z) (k := k) (Index := Index) G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G
      (r * ((k + k) + 3)) := by
  exact hasBitBudget_of_realizedBySparseThresholdAffineFamily (r := r) (k := k + k) hreal

theorem exactVisibleCompressionTarget_of_realizedByExactABAffineDecisionListFamily
    {Z : Type*} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByExactABAffineDecisionListFamily
        (r := r) (Z := Z) (k := k) (Index := Index) G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G
      (r * ((k + k) + 2) + 1) := by
  exact hasBitBudget_of_realizedByAffineDecisionListFamily (r := r) (k := k + k) hreal

@[simp] theorem exactABAffineFeatureBitFamily_decode_code
    (code : AffineFeatureCode r (k + k)) :
    (exactABAffineFeatureBitFamily Z r k).decode
        (affineFeatureCodeEquivBitCode r (k + k) code)
      = fun u : ExactVisiblePostSwitchSurface Z k =>
          affineFeaturePredict code (exactABVisibleData u) := by
  funext u
  change affineFeaturePredict
      ((affineFeatureCodeEquivBitCode r (k + k)).symm
        (affineFeatureCodeEquivBitCode r (k + k) code))
      (exactABVisibleData u)
      = affineFeaturePredict code (exactABVisibleData u)
  simp

@[simp] theorem exactABSparseThresholdAffineBitFamily_decode_code
    (code : SparseThresholdAffineCode r (k + k)) :
    (exactABSparseThresholdAffineBitFamily Z r k).decode
        (sparseThresholdAffineCodeEquivBitCode r (k + k) code)
      = fun u : ExactVisiblePostSwitchSurface Z k =>
          sparseThresholdAffinePredict code (exactABVisibleData u) := by
  funext u
  change sparseThresholdAffinePredict
      ((sparseThresholdAffineCodeEquivBitCode r (k + k)).symm
        (sparseThresholdAffineCodeEquivBitCode r (k + k) code))
      (exactABVisibleData u)
      = sparseThresholdAffinePredict code (exactABVisibleData u)
  simp

@[simp] theorem exactABAffineDecisionListBitFamily_decode_code
    (code : AffineDecisionListCode r (k + k)) :
    (exactABAffineDecisionListBitFamily Z r k).decode
        (affineDecisionListCodeEquivBitCode r (k + k) code)
      = fun u : ExactVisiblePostSwitchSurface Z k =>
          affineDecisionListPredict code (exactABVisibleData u) := by
  funext u
  change affineDecisionListPredict
      ((affineDecisionListCodeEquivBitCode r (k + k)).symm
        (affineDecisionListCodeEquivBitCode r (k + k) code))
      (exactABVisibleData u)
      = affineDecisionListPredict code (exactABVisibleData u)
  simp

theorem exactABAffineFeatureRecoveryLowerBound
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : AffineFeatureCode r (k + k),
      target = fun u : ExactVisiblePostSwitchSurface Z k =>
        affineFeaturePredict code (exactABVisibleData u))
    {q : ℝ≥0∞}
    (hq :
      ∀ c : (exactABAffineFeatureBitFamily Z r k).toEncodedFamily.BadCodes target,
        agreementMass μ target ((exactABAffineFeatureBitFamily Z r k).decode c.1) ≤ q) :
    1 - (2 ^ (r * ((k + k) + 1) + 2 ^ r) : ℝ≥0∞) * q ^ m ≤
      (exactABAffineFeatureBitFamily Z r k).bitExactRecoverySampleMass μ target m := by
  rcases htarget with ⟨code, rfl⟩
  refine BitEncodedClassifierFamily.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    (F := exactABAffineFeatureBitFamily Z r k)
    (μ := μ)
    (target := fun u : ExactVisiblePostSwitchSurface Z k =>
      affineFeaturePredict code (exactABVisibleData u))
    (m := m) ?_ hq
  refine ⟨affineFeatureCodeEquivBitCode r (k + k) code, ?_⟩
  exact exactABAffineFeatureBitFamily_decode_code (Z := Z) (r := r) (k := k) code

theorem exactABSparseThresholdAffineRecoveryLowerBound
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : SparseThresholdAffineCode r (k + k),
      target = fun u : ExactVisiblePostSwitchSurface Z k =>
        sparseThresholdAffinePredict code (exactABVisibleData u))
    {q : ℝ≥0∞}
    (hq :
      ∀ c : (exactABSparseThresholdAffineBitFamily Z r k).toEncodedFamily.BadCodes target,
        agreementMass μ target ((exactABSparseThresholdAffineBitFamily Z r k).decode c.1) ≤ q) :
    1 - (2 ^ (r * ((k + k) + 3)) : ℝ≥0∞) * q ^ m ≤
      (exactABSparseThresholdAffineBitFamily Z r k).bitExactRecoverySampleMass μ target m := by
  rcases htarget with ⟨code, rfl⟩
  refine BitEncodedClassifierFamily.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    (F := exactABSparseThresholdAffineBitFamily Z r k)
    (μ := μ)
    (target := fun u : ExactVisiblePostSwitchSurface Z k =>
      sparseThresholdAffinePredict code (exactABVisibleData u))
    (m := m) ?_ hq
  refine ⟨sparseThresholdAffineCodeEquivBitCode r (k + k) code, ?_⟩
  exact exactABSparseThresholdAffineBitFamily_decode_code (Z := Z) (r := r) (k := k) code

theorem exactABAffineDecisionListRecoveryLowerBound
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : AffineDecisionListCode r (k + k),
      target = fun u : ExactVisiblePostSwitchSurface Z k =>
        affineDecisionListPredict code (exactABVisibleData u))
    {q : ℝ≥0∞}
    (hq :
      ∀ c : (exactABAffineDecisionListBitFamily Z r k).toEncodedFamily.BadCodes target,
        agreementMass μ target ((exactABAffineDecisionListBitFamily Z r k).decode c.1) ≤ q) :
    1 - (2 ^ (r * ((k + k) + 2) + 1) : ℝ≥0∞) * q ^ m ≤
      (exactABAffineDecisionListBitFamily Z r k).bitExactRecoverySampleMass μ target m := by
  rcases htarget with ⟨code, rfl⟩
  refine BitEncodedClassifierFamily.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    (F := exactABAffineDecisionListBitFamily Z r k)
    (μ := μ)
    (target := fun u : ExactVisiblePostSwitchSurface Z k =>
      affineDecisionListPredict code (exactABVisibleData u))
    (m := m) ?_ hq
  refine ⟨affineDecisionListCodeEquivBitCode r (k + k) code, ?_⟩
  exact exactABAffineDecisionListBitFamily_decode_code (Z := Z) (r := r) (k := k) code

end

end Mettapedia.Computability.PNP
