import Mettapedia.Computability.PNP.CanonicalZABRecoveryInterface
import Mettapedia.Computability.PNP.ExactZABERMRoute

/-!
# P vs NP grassroots: ERM into the canonical exact `(zfeat(z), a, b)` route

This file closes the administrative gap between the honest ERM wrapper on the
raw exact `z+a+b` decision-list family and the final canonical route.

Once the wrapper is really "ERM over this one exact local class", the canonical
code witness is not extra data: it is exactly the ERM-selected decision-list
code at each index.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

/-- The canonical exact decision-list code chosen by ERM for each indexed
sample. -/
noncomputable def canonicalZABDecisionListERMCode
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    Index → SharedAffineDecisionListCode (r + (k + k)) :=
  fun i =>
    (sharedAffineDecisionListCodeEquivBitCode (r + (k + k))).symm
      ((rawExactZABDecisionListBitFamily Z r k zfeat).empiricalRiskCode (samples i))

theorem exactZABDecisionListERMFamily_eq_canonicalZABCodeFamily
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    exactZABDecisionListERMFamily (Z := Z) (r := r) (k := k) zfeat samples =
      canonicalZABCodeFamily
        (Z := Z) (r := r) (k := k) zfeat
        (canonicalZABDecisionListERMCode
          (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples) := by
  unfold exactZABDecisionListERMFamily canonicalZABCodeFamily canonicalZABDecisionListERMCode
  simp [BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
    BitEncodedClassifierFamily.empiricalRiskPredictor,
    BitEncodedClassifierFamily.empiricalRiskCode,
    rawExactZABDecisionListBitFamily,
    sharedAffineDecisionListCodeEquivBitCode]

theorem canonicalZABDecisionListERMCandidateData
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    CanonicalZABDecisionListCandidateData
      (Z := Z) (r := r) (k := k) (Index := Index)
      zfeat
      (exactZABDecisionListERMFamily (Z := Z) (r := r) (k := k) zfeat samples) := by
  exact candidateData_of_eq_canonicalZABCodeFamily
    (Z := Z) (r := r) (k := k) (Index := Index)
    (canonicalZABDecisionListERMCode
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples)
    (exactZABDecisionListERMFamily_eq_canonicalZABCodeFamily
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples)

theorem canonicalZABDecisionListERMCompressionTarget
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (exactZABDecisionListERMFamily (Z := Z) (r := r) (k := k) zfeat samples)
      (r + 2 * k + 1) := by
  exact
    (canonicalZABDecisionListERMCandidateData
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples).compressionTarget

section

variable [Fintype Z]

noncomputable def canonicalZABDecisionListERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes
            ((exactZABDecisionListERMFamily
              (Z := Z) (r := r) (k := k) zfeat samples).predict i),
          agreementMass μ
            ((exactZABDecisionListERMFamily
              (Z := Z) (r := r) (k := k) zfeat samples).predict i)
            ((rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1) ≤ q) :
    CanonicalZABDecisionListRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ zfeat
      (exactZABDecisionListERMFamily (Z := Z) (r := r) (k := k) zfeat samples) q := by
  refine ⟨
    canonicalZABDecisionListERMCode
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples,
    exactZABDecisionListERMFamily_eq_canonicalZABCodeFamily
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples,
    hq
  ⟩

theorem canonicalZABDecisionListERMRecoveryLowerBound
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes
            ((exactZABDecisionListERMFamily
              (Z := Z) (r := r) (k := k) zfeat samples).predict i),
          agreementMass μ
            ((exactZABDecisionListERMFamily
              (Z := Z) (r := r) (k := k) zfeat samples).predict i)
            ((rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1) ≤ q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r + 2 * k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactZABDecisionListBitFamily Z r k zfeat).bitExactRecoverySampleMass
        μ
        ((exactZABDecisionListERMFamily
          (Z := Z) (r := r) (k := k) zfeat samples).predict i)
        m := by
  exact
    (canonicalZABDecisionListERMRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat samples q hq).recoveryLowerBound i m

end

end

end Mettapedia.Computability.PNP
