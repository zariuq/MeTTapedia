import Mettapedia.Computability.PNP.ExactZABDecisionListFamily
import Mettapedia.Computability.PNP.SharedAffineFeatureFamilies

/-!
# P vs NP grassroots: shared-basis families on `(zfeat(z), a, b)`

The manuscript-facing local input is `u = (z, a, b)`.  The previous exact
`z+a+b` route used the full visible bit vector directly.  This file isolates the
sharper optimistic regime in which:

* one shared extractor `zfeat : Z → BitVec r` fixes the `z`-side bits,
* one fixed affine basis on the combined bits `(zfeat(z), a, b)` is reused
  across the whole switched family,
* and only the downstream combiner varies.

Under that hypothesis the code budget again drops to the combiner only.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {p r k : ℕ}

/-- Shared affine-feature summary on the exact visible bit vector
`(zfeat(z), a, b)`. -/
def exactZABAffineFeatureSummary
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k))) :
    ExactVisiblePostSwitchSurface Z k → BitVec p :=
  fun u => affineFeatureVector features (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u)

/-- Arbitrary truth-table combiner on the shared `(zfeat(z), a, b)` feature basis. -/
noncomputable def sharedExactZABAffineFeaturePredict
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (table : BitCode (2 ^ p))
    (u : ExactVisiblePostSwitchSurface Z k) : Bool :=
  table ((Fintype.equivFinOfCardEq (by simp [BitVec] : Fintype.card (BitVec p) = 2 ^ p))
    (exactZABAffineFeatureSummary (Z := Z) (p := p) (r := r) (k := k) zfeat features u))

/-- Sparse-threshold combiner on the shared `(zfeat(z), a, b)` feature basis. -/
noncomputable def sharedExactZABSparseThresholdAffinePredict
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (code : SharedSparseThresholdCode p)
    (u : ExactVisiblePostSwitchSurface Z k) : Bool :=
  decide (thresholdCodeValue (r := p) code.2 ≤
    maskedAffineFeatureCount (k := r + (k + k)) features code.1
      (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u))

/-- Decision-list combiner on the shared `(zfeat(z), a, b)` feature basis. -/
noncomputable def sharedExactZABAffineDecisionListPredict
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (code : SharedAffineDecisionListCode p)
    (u : ExactVisiblePostSwitchSurface Z k) : Bool :=
  match firstActiveFeature?
      (exactZABAffineFeatureSummary (Z := Z) (p := p) (r := r) (k := k) zfeat features u) with
  | some j => code.1 j
  | none => code.2

/-- Shared truth-table family on the exact visible bit basis `(zfeat(z), a, b)`. -/
noncomputable def sharedExactZABAffineFeatureBitFamily
    (Z : Type*) (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k))) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k) (2 ^ p) where
  decode table := sharedExactZABAffineFeaturePredict (Z := Z) (p := p) (r := r) (k := k)
    zfeat features table

/-- Shared sparse-threshold family on the exact visible bit basis `(zfeat(z), a, b)`. -/
noncomputable def sharedExactZABSparseThresholdAffineBitFamily
    (Z : Type*) (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k))) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k) (2 * p) where
  decode raw u :=
    let code := (sharedSparseThresholdCodeEquivBitCode p).symm raw
    sharedExactZABSparseThresholdAffinePredict (Z := Z) (p := p) (r := r) (k := k)
      zfeat features code u

/-- Shared decision-list family on the exact visible bit basis `(zfeat(z), a, b)`. -/
noncomputable def sharedExactZABAffineDecisionListBitFamily
    (Z : Type*) (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k))) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k) (p + 1) where
  decode raw u :=
    let code := (sharedAffineDecisionListCodeEquivBitCode p).symm raw
    sharedExactZABAffineDecisionListPredict (Z := Z) (p := p) (r := r) (k := k)
      zfeat features code u

@[simp] theorem sharedExactZABAffineFeatureBitFamily_decode
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (table : BitCode (2 ^ p)) :
    (sharedExactZABAffineFeatureBitFamily Z zfeat features).decode table =
      sharedExactZABAffineFeaturePredict (Z := Z) (p := p) (r := r) (k := k)
        zfeat features table := rfl

@[simp] theorem sharedExactZABSparseThresholdAffineBitFamily_decode_code
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (code : SharedSparseThresholdCode p) :
    (sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).decode
        (sharedSparseThresholdCodeEquivBitCode p code) =
      sharedExactZABSparseThresholdAffinePredict (Z := Z) (p := p) (r := r) (k := k)
        zfeat features code := by
  funext u
  simp [sharedExactZABSparseThresholdAffineBitFamily, sharedSparseThresholdCodeEquivBitCode]

@[simp] theorem sharedExactZABAffineDecisionListBitFamily_decode_code
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (code : SharedAffineDecisionListCode p) :
    (sharedExactZABAffineDecisionListBitFamily Z zfeat features).decode
        (sharedAffineDecisionListCodeEquivBitCode p code) =
      sharedExactZABAffineDecisionListPredict (Z := Z) (p := p) (r := r) (k := k)
        zfeat features code := by
  funext u
  simp [sharedExactZABAffineDecisionListBitFamily, sharedAffineDecisionListCodeEquivBitCode]

/-- Exact-surface family with one shared `(zfeat(z), a, b)` affine basis and an
arbitrary truth-table combiner. -/
def RealizedBySharedExactZABAffineFeatureFamily
    {Index : Type*}
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  ∀ i, ∃ table : BitCode (2 ^ p),
    G.predict i =
      sharedExactZABAffineFeaturePredict (Z := Z) (p := p) (r := r) (k := k)
        zfeat features table

/-- Exact-surface family with one shared `(zfeat(z), a, b)` affine basis and a
sparse-threshold combiner. -/
def RealizedBySharedExactZABSparseThresholdAffineFamily
    {Index : Type*}
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  ∀ i, ∃ code : SharedSparseThresholdCode p,
    G.predict i =
      sharedExactZABSparseThresholdAffinePredict (Z := Z) (p := p) (r := r) (k := k)
        zfeat features code

/-- Exact-surface family with one shared `(zfeat(z), a, b)` affine basis and a
fixed-order decision-list combiner. -/
def RealizedBySharedExactZABAffineDecisionListFamily
    {Index : Type*}
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  ∀ i, ∃ code : SharedAffineDecisionListCode p,
    G.predict i =
      sharedExactZABAffineDecisionListPredict (Z := Z) (p := p) (r := r) (k := k)
        zfeat features code

theorem exactVisibleCompressionTarget_of_realizedBySharedExactZABAffineFeatureFamily
    {Index : Type*}
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactZABAffineFeatureFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 ^ p) := by
  refine ⟨sharedExactZABAffineFeatureBitFamily Z zfeat features, ?_⟩
  intro i
  rcases hreal i with ⟨table, hi⟩
  refine ⟨table, ?_⟩
  exact (sharedExactZABAffineFeatureBitFamily_decode
    (Z := Z) (p := p) (r := r) (k := k) zfeat features table).trans hi.symm

theorem exactVisibleCompressionTarget_of_realizedBySharedExactZABSparseThresholdAffineFamily
    {Index : Type*}
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactZABSparseThresholdAffineFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * p) := by
  refine ⟨sharedExactZABSparseThresholdAffineBitFamily Z zfeat features, ?_⟩
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨sharedSparseThresholdCodeEquivBitCode p code, ?_⟩
  exact (sharedExactZABSparseThresholdAffineBitFamily_decode_code
    (Z := Z) (p := p) (r := r) (k := k) zfeat features code).trans hi.symm

theorem exactVisibleCompressionTarget_of_realizedBySharedExactZABAffineDecisionListFamily
    {Index : Type*}
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactZABAffineDecisionListFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (p + 1) := by
  refine ⟨sharedExactZABAffineDecisionListBitFamily Z zfeat features, ?_⟩
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨sharedAffineDecisionListCodeEquivBitCode p code, ?_⟩
  exact (sharedExactZABAffineDecisionListBitFamily_decode_code
    (Z := Z) (p := p) (r := r) (k := k) zfeat features code).trans hi.symm

theorem sharedExactZABAffineFeatureRecoveryLowerBound
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ table : BitCode (2 ^ p),
      target = sharedExactZABAffineFeaturePredict (Z := Z) (p := p) (r := r) (k := k)
        zfeat features table)
    {q : ℝ≥0∞}
    (hq :
      ∀ c : (sharedExactZABAffineFeatureBitFamily Z zfeat features).toEncodedFamily.BadCodes target,
        agreementMass μ target ((sharedExactZABAffineFeatureBitFamily Z zfeat features).decode c.1) ≤ q) :
    1 - (2 ^ (2 ^ p) : ℝ≥0∞) * q ^ m ≤
      (sharedExactZABAffineFeatureBitFamily Z zfeat features).bitExactRecoverySampleMass μ target m := by
  rcases htarget with ⟨table, rfl⟩
  exact BitEncodedClassifierFamily.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    (F := sharedExactZABAffineFeatureBitFamily Z zfeat features)
    (μ := μ)
    (target := sharedExactZABAffineFeaturePredict (Z := Z) (p := p) (r := r) (k := k)
      zfeat features table)
    (m := m)
    ⟨table, rfl⟩
    hq

theorem sharedExactZABSparseThresholdAffineRecoveryLowerBound
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : SharedSparseThresholdCode p,
      target = sharedExactZABSparseThresholdAffinePredict (Z := Z) (p := p) (r := r) (k := k)
        zfeat features code)
    {q : ℝ≥0∞}
    (hq :
      ∀ c :
        (sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).toEncodedFamily.BadCodes target,
        agreementMass μ target
          ((sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).decode c.1) ≤ q) :
    1 - (2 ^ (2 * p) : ℝ≥0∞) * q ^ m ≤
      (sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).bitExactRecoverySampleMass
        μ target m := by
  rcases htarget with ⟨code, rfl⟩
  refine BitEncodedClassifierFamily.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    (F := sharedExactZABSparseThresholdAffineBitFamily Z zfeat features)
    (μ := μ)
    (target := sharedExactZABSparseThresholdAffinePredict (Z := Z) (p := p) (r := r) (k := k)
      zfeat features code)
    (m := m) ?_ hq
  refine ⟨sharedSparseThresholdCodeEquivBitCode p code, ?_⟩
  exact sharedExactZABSparseThresholdAffineBitFamily_decode_code
    (Z := Z) (p := p) (r := r) (k := k) zfeat features code

theorem sharedExactZABAffineDecisionListRecoveryLowerBound
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : SharedAffineDecisionListCode p,
      target = sharedExactZABAffineDecisionListPredict (Z := Z) (p := p) (r := r) (k := k)
        zfeat features code)
    {q : ℝ≥0∞}
    (hq :
      ∀ c :
        (sharedExactZABAffineDecisionListBitFamily Z zfeat features).toEncodedFamily.BadCodes target,
        agreementMass μ target
          ((sharedExactZABAffineDecisionListBitFamily Z zfeat features).decode c.1) ≤ q) :
    1 - (2 ^ (p + 1) : ℝ≥0∞) * q ^ m ≤
      (sharedExactZABAffineDecisionListBitFamily Z zfeat features).bitExactRecoverySampleMass
        μ target m := by
  rcases htarget with ⟨code, rfl⟩
  refine BitEncodedClassifierFamily.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    (F := sharedExactZABAffineDecisionListBitFamily Z zfeat features)
    (μ := μ)
    (target := sharedExactZABAffineDecisionListPredict (Z := Z) (p := p) (r := r) (k := k)
      zfeat features code)
    (m := m) ?_ hq
  refine ⟨sharedAffineDecisionListCodeEquivBitCode p code, ?_⟩
  exact sharedExactZABAffineDecisionListBitFamily_decode_code
    (Z := Z) (p := p) (r := r) (k := k) zfeat features code

end

end Mettapedia.Computability.PNP
