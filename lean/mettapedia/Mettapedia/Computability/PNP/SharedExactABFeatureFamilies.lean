import Mettapedia.Computability.PNP.ExactABAffineFamilies
import Mettapedia.Computability.PNP.SharedAffineFeatureFamilies

/-!
# P vs NP grassroots: shared-basis families on the raw `(a, b)` surface

The raw exact visible bit surface `(a, b)` now supports two parallel ladders:

* per-predictor affine families from `ExactABAffineFamilies.lean`;
* shared-basis affine families, where one fixed feature basis is reused across
  the whole switched family and only the downstream combiner varies.

This file proves the second ladder.  On the raw `(a, b)` surface the resulting
budgets are combiner-only:

* arbitrary truth table: `2^r` bits,
* sparse-threshold combiner: `2r` bits,
* decision-list combiner: `r + 1` bits.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ}

/-- Shared affine-feature summary on the raw exact visible bit vector `(a, b)`. -/
def exactABAffineFeatureSummary
    (features : Fin r → AffineColumnCode (k + k)) :
    ExactVisiblePostSwitchSurface Z k → BitVec r :=
  fun u => affineFeatureVector features (exactABVisibleData u)

/-- Arbitrary truth-table combiner on the shared raw `(a, b)` feature basis. -/
noncomputable def sharedExactABAffineFeaturePredict
    (features : Fin r → AffineColumnCode (k + k))
    (table : BitCode (2 ^ r))
    (u : ExactVisiblePostSwitchSurface Z k) : Bool :=
  table ((Fintype.equivFinOfCardEq (by simp [BitVec] : Fintype.card (BitVec r) = 2 ^ r))
    (exactABAffineFeatureSummary (Z := Z) (k := k) features u))

/-- Sparse-threshold combiner on the shared raw `(a, b)` feature basis. -/
noncomputable def sharedExactABSparseThresholdAffinePredict
    (features : Fin r → AffineColumnCode (k + k))
    (code : SharedSparseThresholdCode r)
    (u : ExactVisiblePostSwitchSurface Z k) : Bool :=
  decide (thresholdCodeValue (r := r) code.2 ≤
    maskedAffineFeatureCount (k := k + k) features code.1 (exactABVisibleData u))

/-- Decision-list combiner on the shared raw `(a, b)` feature basis. -/
noncomputable def sharedExactABAffineDecisionListPredict
    (features : Fin r → AffineColumnCode (k + k))
    (code : SharedAffineDecisionListCode r)
    (u : ExactVisiblePostSwitchSurface Z k) : Bool :=
  match firstActiveFeature? (exactABAffineFeatureSummary (Z := Z) (k := k) features u) with
  | some j => code.1 j
  | none => code.2

/-- Shared truth-table family on the raw `(a, b)` feature basis. -/
noncomputable def sharedExactABAffineFeatureBitFamily
    (Z : Type*) (features : Fin r → AffineColumnCode (k + k)) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k) (2 ^ r) where
  decode table := sharedExactABAffineFeaturePredict (Z := Z) (k := k) features table

/-- Shared sparse-threshold family on the raw `(a, b)` feature basis. -/
noncomputable def sharedExactABSparseThresholdAffineBitFamily
    (Z : Type*) (features : Fin r → AffineColumnCode (k + k)) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k) (2 * r) where
  decode raw u :=
    let code := (sharedSparseThresholdCodeEquivBitCode r).symm raw
    sharedExactABSparseThresholdAffinePredict (Z := Z) (k := k) features code u

/-- Shared decision-list family on the raw `(a, b)` feature basis. -/
noncomputable def sharedExactABAffineDecisionListBitFamily
    (Z : Type*) (features : Fin r → AffineColumnCode (k + k)) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k) (r + 1) where
  decode raw u :=
    let code := (sharedAffineDecisionListCodeEquivBitCode r).symm raw
    sharedExactABAffineDecisionListPredict (Z := Z) (k := k) features code u

@[simp] theorem sharedExactABAffineFeatureBitFamily_decode
    (features : Fin r → AffineColumnCode (k + k)) (table : BitCode (2 ^ r)) :
    (sharedExactABAffineFeatureBitFamily Z features).decode table =
      sharedExactABAffineFeaturePredict (Z := Z) (k := k) features table := rfl

@[simp] theorem sharedExactABSparseThresholdAffineBitFamily_decode_code
    (features : Fin r → AffineColumnCode (k + k)) (code : SharedSparseThresholdCode r) :
    (sharedExactABSparseThresholdAffineBitFamily Z features).decode
        (sharedSparseThresholdCodeEquivBitCode r code) =
      sharedExactABSparseThresholdAffinePredict (Z := Z) (k := k) features code := by
  funext u
  simp [sharedExactABSparseThresholdAffineBitFamily, sharedSparseThresholdCodeEquivBitCode]

@[simp] theorem sharedExactABAffineDecisionListBitFamily_decode_code
    (features : Fin r → AffineColumnCode (k + k)) (code : SharedAffineDecisionListCode r) :
    (sharedExactABAffineDecisionListBitFamily Z features).decode
        (sharedAffineDecisionListCodeEquivBitCode r code) =
      sharedExactABAffineDecisionListPredict (Z := Z) (k := k) features code := by
  funext u
  simp [sharedExactABAffineDecisionListBitFamily, sharedAffineDecisionListCodeEquivBitCode]

/-- Exact-surface family with one shared raw `(a, b)` affine basis and an
arbitrary truth-table combiner. -/
def RealizedBySharedExactABAffineFeatureFamily
    {Index : Type*} (features : Fin r → AffineColumnCode (k + k))
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  ∀ i, ∃ table : BitCode (2 ^ r),
    G.predict i = sharedExactABAffineFeaturePredict (Z := Z) (k := k) features table

/-- Exact-surface family with one shared raw `(a, b)` affine basis and a
sparse-threshold combiner. -/
def RealizedBySharedExactABSparseThresholdAffineFamily
    {Index : Type*} (features : Fin r → AffineColumnCode (k + k))
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  ∀ i, ∃ code : SharedSparseThresholdCode r,
    G.predict i = sharedExactABSparseThresholdAffinePredict (Z := Z) (k := k) features code

/-- Exact-surface family with one shared raw `(a, b)` affine basis and a
fixed-order decision-list combiner. -/
def RealizedBySharedExactABAffineDecisionListFamily
    {Index : Type*} (features : Fin r → AffineColumnCode (k + k))
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  ∀ i, ∃ code : SharedAffineDecisionListCode r,
    G.predict i = sharedExactABAffineDecisionListPredict (Z := Z) (k := k) features code

theorem exactVisibleCompressionTarget_of_realizedBySharedExactABAffineFeatureFamily
    {Index : Type*} (features : Fin r → AffineColumnCode (k + k))
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactABAffineFeatureFamily (Z := Z) (r := r) (k := k) features G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 ^ r) := by
  refine ⟨sharedExactABAffineFeatureBitFamily Z features, ?_⟩
  intro i
  rcases hreal i with ⟨table, hi⟩
  refine ⟨table, ?_⟩
  exact (sharedExactABAffineFeatureBitFamily_decode
    (Z := Z) (r := r) (k := k) features table).trans hi.symm

theorem exactVisibleCompressionTarget_of_realizedBySharedExactABSparseThresholdAffineFamily
    {Index : Type*} (features : Fin r → AffineColumnCode (k + k))
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactABSparseThresholdAffineFamily
        (Z := Z) (r := r) (k := k) features G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * r) := by
  refine ⟨sharedExactABSparseThresholdAffineBitFamily Z features, ?_⟩
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨sharedSparseThresholdCodeEquivBitCode r code, ?_⟩
  exact (sharedExactABSparseThresholdAffineBitFamily_decode_code
    (Z := Z) (r := r) (k := k) features code).trans hi.symm

theorem exactVisibleCompressionTarget_of_realizedBySharedExactABAffineDecisionListFamily
    {Index : Type*} (features : Fin r → AffineColumnCode (k + k))
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactABAffineDecisionListFamily
        (Z := Z) (r := r) (k := k) features G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 1) := by
  refine ⟨sharedExactABAffineDecisionListBitFamily Z features, ?_⟩
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨sharedAffineDecisionListCodeEquivBitCode r code, ?_⟩
  exact (sharedExactABAffineDecisionListBitFamily_decode_code
    (Z := Z) (r := r) (k := k) features code).trans hi.symm

theorem sharedExactABAffineFeatureRecoveryLowerBound
    [Fintype Z]
    (features : Fin r → AffineColumnCode (k + k))
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ table : BitCode (2 ^ r),
      target = sharedExactABAffineFeaturePredict (Z := Z) (k := k) features table)
    {q : ℝ≥0∞}
    (hq :
      ∀ c : (sharedExactABAffineFeatureBitFamily Z features).toEncodedFamily.BadCodes target,
        agreementMass μ target ((sharedExactABAffineFeatureBitFamily Z features).decode c.1) ≤ q) :
    1 - (2 ^ (2 ^ r) : ℝ≥0∞) * q ^ m ≤
      (sharedExactABAffineFeatureBitFamily Z features).bitExactRecoverySampleMass μ target m := by
  rcases htarget with ⟨table, rfl⟩
  exact BitEncodedClassifierFamily.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    (F := sharedExactABAffineFeatureBitFamily Z features)
    (μ := μ)
    (target := sharedExactABAffineFeaturePredict (Z := Z) (k := k) features table)
    (m := m)
    ⟨table, rfl⟩
    hq

theorem sharedExactABSparseThresholdAffineRecoveryLowerBound
    [Fintype Z]
    (features : Fin r → AffineColumnCode (k + k))
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : SharedSparseThresholdCode r,
      target = sharedExactABSparseThresholdAffinePredict (Z := Z) (k := k) features code)
    {q : ℝ≥0∞}
    (hq :
      ∀ c : (sharedExactABSparseThresholdAffineBitFamily Z features).toEncodedFamily.BadCodes target,
        agreementMass μ target
          ((sharedExactABSparseThresholdAffineBitFamily Z features).decode c.1) ≤ q) :
    1 - (2 ^ (2 * r) : ℝ≥0∞) * q ^ m ≤
      (sharedExactABSparseThresholdAffineBitFamily Z features).bitExactRecoverySampleMass
        μ target m := by
  rcases htarget with ⟨code, rfl⟩
  refine BitEncodedClassifierFamily.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    (F := sharedExactABSparseThresholdAffineBitFamily Z features)
    (μ := μ)
    (target := sharedExactABSparseThresholdAffinePredict (Z := Z) (k := k) features code)
    (m := m) ?_ hq
  refine ⟨sharedSparseThresholdCodeEquivBitCode r code, ?_⟩
  exact sharedExactABSparseThresholdAffineBitFamily_decode_code
    (Z := Z) (r := r) (k := k) features code

theorem sharedExactABAffineDecisionListRecoveryLowerBound
    [Fintype Z]
    (features : Fin r → AffineColumnCode (k + k))
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : SharedAffineDecisionListCode r,
      target = sharedExactABAffineDecisionListPredict (Z := Z) (k := k) features code)
    {q : ℝ≥0∞}
    (hq :
      ∀ c : (sharedExactABAffineDecisionListBitFamily Z features).toEncodedFamily.BadCodes target,
        agreementMass μ target
          ((sharedExactABAffineDecisionListBitFamily Z features).decode c.1) ≤ q) :
    1 - (2 ^ (r + 1) : ℝ≥0∞) * q ^ m ≤
      (sharedExactABAffineDecisionListBitFamily Z features).bitExactRecoverySampleMass
        μ target m := by
  rcases htarget with ⟨code, rfl⟩
  refine BitEncodedClassifierFamily.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    (F := sharedExactABAffineDecisionListBitFamily Z features)
    (μ := μ)
    (target := sharedExactABAffineDecisionListPredict (Z := Z) (k := k) features code)
    (m := m) ?_ hq
  refine ⟨sharedAffineDecisionListCodeEquivBitCode r code, ?_⟩
  exact sharedExactABAffineDecisionListBitFamily_decode_code
    (Z := Z) (r := r) (k := k) features code

end

end Mettapedia.Computability.PNP
