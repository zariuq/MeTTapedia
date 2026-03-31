import Mettapedia.Computability.PNP.ExactAffineRecovery

/-!
# P vs NP grassroots: shared affine-feature families on the exact surface

The previous affine candidate classes allowed each predictor to carry its own
affine feature basis. This file isolates a sharper optimistic regime:

* one fixed affine feature basis is shared across the whole switched family,
* only the downstream combiner varies from predictor to predictor.

Under that hypothesis the code budget drops from "features plus combiner" to
"combiner only". On the exact post-switch surface this yields the explicit
bounds:

* arbitrary truth table on the shared feature vector: `2^r` bits,
* sparse-threshold combiner on the shared feature vector: `2r` bits,
* decision-list combiner on the shared feature vector: `r + 1` bits.

The file proves both compression and weighted recovery interfaces for these
shared-basis exact-surface families.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ}

/-- The exact shared affine-feature summary map determined by one fixed family
of `r` affine column probes. -/
def exactAffineFeatureSummary
    (features : Fin r → AffineColumnCode k) :
    ExactVisiblePostSwitchSurface Z k → BitVec r :=
  fun u => affineFeatureVector features u.a

/-- Evaluate an arbitrary truth-table combiner on the fixed exact affine
feature summary. -/
noncomputable def sharedAffineFeaturePredict
    (features : Fin r → AffineColumnCode k)
    (table : BitCode (2 ^ r))
    (u : ExactVisiblePostSwitchSurface Z k) : Bool :=
  table ((Fintype.equivFinOfCardEq (by simp [BitVec] : Fintype.card (BitVec r) = 2 ^ r))
    (exactAffineFeatureSummary (Z := Z) features u))

/-- Evaluate a sparse-threshold combiner on the fixed exact affine feature
summary. -/
abbrev SharedSparseThresholdCode (r : ℕ) := BitCode r × BitCode r

/-- Shared sparse-threshold codes have the expected `2r`-bit raw size. -/
theorem card_sharedSparseThresholdCode (r : ℕ) :
    Fintype.card (SharedSparseThresholdCode r) = 2 ^ (2 * r) := by
  calc
    Fintype.card (SharedSparseThresholdCode r) = 2 ^ r * 2 ^ r := by
      simp [SharedSparseThresholdCode]
    _ = 2 ^ (r + r) := by rw [← Nat.pow_add]
    _ = 2 ^ (2 * r) := by simp [two_mul]

/-- Noncomputably collapse the shared sparse-threshold code type to `2r` raw
bits. -/
noncomputable def sharedSparseThresholdCodeEquivBitCode (r : ℕ) :
    SharedSparseThresholdCode r ≃ BitCode (2 * r) := by
  apply Fintype.equivOfCardEq
  rw [card_sharedSparseThresholdCode, card_bitCode]

/-- Evaluate a sparse-threshold combiner on the fixed exact affine feature
summary. -/
noncomputable def sharedSparseThresholdAffinePredict
    (features : Fin r → AffineColumnCode k)
    (code : SharedSparseThresholdCode r)
    (u : ExactVisiblePostSwitchSurface Z k) : Bool :=
  decide (thresholdCodeValue (r := r) code.2 ≤
    maskedAffineFeatureCount (k := k) features code.1 u.a)

/-- Shared affine decision-list code: one response bit per feature and one
default output bit. -/
abbrev SharedAffineDecisionListCode (r : ℕ) := BitCode r × Bool

/-- Shared affine decision-list codes have the expected `r+1`-bit raw size. -/
theorem card_sharedAffineDecisionListCode (r : ℕ) :
    Fintype.card (SharedAffineDecisionListCode r) = 2 ^ (r + 1) := by
  simp [SharedAffineDecisionListCode, Nat.pow_add, Nat.mul_comm]

/-- Noncomputably collapse the shared affine decision-list code type to `r+1`
raw bits. -/
noncomputable def sharedAffineDecisionListCodeEquivBitCode (r : ℕ) :
    SharedAffineDecisionListCode r ≃ BitCode (r + 1) := by
  apply Fintype.equivOfCardEq
  rw [card_sharedAffineDecisionListCode, card_bitCode]

/-- Evaluate a fixed-order decision-list combiner on the shared affine feature
summary. -/
noncomputable def sharedAffineDecisionListPredict
    (features : Fin r → AffineColumnCode k)
    (code : SharedAffineDecisionListCode r)
    (u : ExactVisiblePostSwitchSurface Z k) : Bool :=
  match firstActiveFeature? (exactAffineFeatureSummary (Z := Z) features u) with
  | some j => code.1 j
  | none => code.2

/-- The concrete exact-surface truth-table family on one fixed affine feature
basis. -/
noncomputable def sharedAffineFeatureBitFamily
    (Z : Type*) (features : Fin r → AffineColumnCode k) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k) (2 ^ r) where
  decode table := sharedAffineFeaturePredict (Z := Z) features table

/-- The concrete exact-surface sparse-threshold family on one fixed affine
feature basis. -/
noncomputable def sharedSparseThresholdAffineBitFamily
    (Z : Type*) (features : Fin r → AffineColumnCode k) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k) (2 * r) where
  decode raw u :=
    let code := (sharedSparseThresholdCodeEquivBitCode r).symm raw
    sharedSparseThresholdAffinePredict (Z := Z) features code u

/-- The concrete exact-surface decision-list family on one fixed affine feature
basis. -/
noncomputable def sharedAffineDecisionListBitFamily
    (Z : Type*) (features : Fin r → AffineColumnCode k) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k) (r + 1) where
  decode raw u :=
    let code := (sharedAffineDecisionListCodeEquivBitCode r).symm raw
    sharedAffineDecisionListPredict (Z := Z) features code u

@[simp] theorem sharedAffineFeatureBitFamily_decode
    (features : Fin r → AffineColumnCode k) (table : BitCode (2 ^ r)) :
    (sharedAffineFeatureBitFamily Z features).decode table
      = sharedAffineFeaturePredict (Z := Z) features table := rfl

@[simp] theorem sharedSparseThresholdAffineBitFamily_decode_code
    (features : Fin r → AffineColumnCode k) (code : SharedSparseThresholdCode r) :
    (sharedSparseThresholdAffineBitFamily Z features).decode
        (sharedSparseThresholdCodeEquivBitCode r code)
      = sharedSparseThresholdAffinePredict (Z := Z) features code := by
  funext u
  simp [sharedSparseThresholdAffineBitFamily, sharedSparseThresholdCodeEquivBitCode]

@[simp] theorem sharedAffineDecisionListBitFamily_decode_code
    (features : Fin r → AffineColumnCode k) (code : SharedAffineDecisionListCode r) :
    (sharedAffineDecisionListBitFamily Z features).decode
        (sharedAffineDecisionListCodeEquivBitCode r code)
      = sharedAffineDecisionListPredict (Z := Z) features code := by
  funext u
  simp [sharedAffineDecisionListBitFamily, sharedAffineDecisionListCodeEquivBitCode]

/-- Exact-surface family whose predictors all use the same affine feature basis
and vary only by an arbitrary truth table on the resulting feature vector. -/
def RealizedBySharedExactAffineFeatureFamily
    {Index : Type*} (features : Fin r → AffineColumnCode k)
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  ∀ i, ∃ table : BitCode (2 ^ r),
    G.predict i = sharedAffineFeaturePredict (Z := Z) features table

/-- Exact-surface family whose predictors all use the same affine feature basis
and vary only by a sparse-threshold combiner. -/
def RealizedBySharedExactSparseThresholdAffineFamily
    {Index : Type*} (features : Fin r → AffineColumnCode k)
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  ∀ i, ∃ code : BitCode r × BitCode r,
    G.predict i = sharedSparseThresholdAffinePredict (Z := Z) features code

/-- Exact-surface family whose predictors all use the same affine feature basis
and vary only by a fixed-order decision list on that shared feature vector. -/
def RealizedBySharedExactAffineDecisionListFamily
    {Index : Type*} (features : Fin r → AffineColumnCode k)
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  ∀ i, ∃ code : SharedAffineDecisionListCode r,
    G.predict i = sharedAffineDecisionListPredict (Z := Z) features code

theorem exactVisibleCompressionTarget_of_realizedBySharedExactAffineFeatureFamily
    {Index : Type*} (features : Fin r → AffineColumnCode k)
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal : RealizedBySharedExactAffineFeatureFamily (Z := Z) (r := r) (k := k) features G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 ^ r) := by
  refine ⟨sharedAffineFeatureBitFamily Z features, ?_⟩
  intro i
  rcases hreal i with ⟨table, hi⟩
  refine ⟨table, ?_⟩
  exact (sharedAffineFeatureBitFamily_decode (Z := Z) (r := r) (k := k) features table).trans hi.symm

theorem exactVisibleCompressionTarget_of_realizedBySharedExactSparseThresholdAffineFamily
    {Index : Type*} (features : Fin r → AffineColumnCode k)
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactSparseThresholdAffineFamily (Z := Z) (r := r) (k := k) features G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * r) := by
  refine ⟨sharedSparseThresholdAffineBitFamily Z features, ?_⟩
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨sharedSparseThresholdCodeEquivBitCode r code, ?_⟩
  exact (sharedSparseThresholdAffineBitFamily_decode_code
    (Z := Z) (r := r) (k := k) features code).trans hi.symm

theorem exactVisibleCompressionTarget_of_realizedBySharedExactAffineDecisionListFamily
    {Index : Type*} (features : Fin r → AffineColumnCode k)
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactAffineDecisionListFamily (Z := Z) (r := r) (k := k) features G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 1) := by
  refine ⟨sharedAffineDecisionListBitFamily Z features, ?_⟩
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨sharedAffineDecisionListCodeEquivBitCode r code, ?_⟩
  exact (sharedAffineDecisionListBitFamily_decode_code
    (Z := Z) (r := r) (k := k) features code).trans hi.symm

theorem sharedExactAffineFeatureRecoveryLowerBound
    [Fintype Z]
    (features : Fin r → AffineColumnCode k)
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ table : BitCode (2 ^ r),
      target = sharedAffineFeaturePredict (Z := Z) features table)
    {q : ℝ≥0∞}
    (hq :
      ∀ c : (sharedAffineFeatureBitFamily Z features).toEncodedFamily.BadCodes target,
        agreementMass μ target ((sharedAffineFeatureBitFamily Z features).decode c.1) ≤ q) :
    1 - (2 ^ (2 ^ r) : ℝ≥0∞) * q ^ m ≤
      (sharedAffineFeatureBitFamily Z features).bitExactRecoverySampleMass μ target m := by
  rcases htarget with ⟨table, rfl⟩
  exact BitEncodedClassifierFamily.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    (F := sharedAffineFeatureBitFamily Z features)
    (μ := μ)
    (target := sharedAffineFeaturePredict (Z := Z) features table)
    (m := m)
    ⟨table, rfl⟩
    hq

theorem sharedExactSparseThresholdAffineRecoveryLowerBound
    [Fintype Z]
    (features : Fin r → AffineColumnCode k)
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : BitCode r × BitCode r,
      target = sharedSparseThresholdAffinePredict (Z := Z) features code)
    {q : ℝ≥0∞}
    (hq :
      ∀ c : (sharedSparseThresholdAffineBitFamily Z features).toEncodedFamily.BadCodes target,
        agreementMass μ target ((sharedSparseThresholdAffineBitFamily Z features).decode c.1) ≤ q) :
    1 - (2 ^ (2 * r) : ℝ≥0∞) * q ^ m ≤
      (sharedSparseThresholdAffineBitFamily Z features).bitExactRecoverySampleMass μ target m := by
  rcases htarget with ⟨code, rfl⟩
  refine BitEncodedClassifierFamily.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    (F := sharedSparseThresholdAffineBitFamily Z features)
    (μ := μ)
    (target := sharedSparseThresholdAffinePredict (Z := Z) features code)
    (m := m) ?_ hq
  refine ⟨sharedSparseThresholdCodeEquivBitCode r code, ?_⟩
  exact sharedSparseThresholdAffineBitFamily_decode_code
    (Z := Z) (r := r) (k := k) features code

theorem sharedExactAffineDecisionListRecoveryLowerBound
    [Fintype Z]
    (features : Fin r → AffineColumnCode k)
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : SharedAffineDecisionListCode r,
      target = sharedAffineDecisionListPredict (Z := Z) features code)
    {q : ℝ≥0∞}
    (hq :
      ∀ c : (sharedAffineDecisionListBitFamily Z features).toEncodedFamily.BadCodes target,
        agreementMass μ target ((sharedAffineDecisionListBitFamily Z features).decode c.1) ≤ q) :
    1 - (2 ^ (r + 1) : ℝ≥0∞) * q ^ m ≤
      (sharedAffineDecisionListBitFamily Z features).bitExactRecoverySampleMass μ target m := by
  rcases htarget with ⟨code, rfl⟩
  refine BitEncodedClassifierFamily.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    (F := sharedAffineDecisionListBitFamily Z features)
    (μ := μ)
    (target := sharedAffineDecisionListPredict (Z := Z) features code)
    (m := m) ?_ hq
  refine ⟨sharedAffineDecisionListCodeEquivBitCode r code, ?_⟩
  exact sharedAffineDecisionListBitFamily_decode_code
    (Z := Z) (r := r) (k := k) features code

end

end Mettapedia.Computability.PNP
