import Mettapedia.Computability.PNP.BitFamilyERM
import Mettapedia.Computability.PNP.ExactZABTargetInterface

/-!
# P vs NP grassroots: ERM over the shared `z+a+b` decision-list class

The manuscript's constructive local object is an ERM wrapper on a fixed local
hypothesis class.  This file instantiates that pattern for the new shared
`z+a+b` decision-list family.

Once the wrapper is honestly specified as ERM over this one class, the code
witness is no longer separate: it is just the ERM-selected code.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

/-- The indexed exact-surface family obtained by running ERM inside the shared
`z+a+b` decision-list class. -/
noncomputable def exactZABDecisionListERMFamily
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleSwitchedFamily Z k Index :=
  (rawExactZABDecisionListBitFamily Z r k zfeat).indexedEmpiricalRiskFamily samples

theorem exactZABDecisionListERMTargetData
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactZABDecisionListTargetData
      (Z := Z) (r := r) (k := k) (Index := Index)
      zfeat
      (exactZABDecisionListERMFamily (Z := Z) (r := r) (k := k) zfeat samples) := by
  refine ⟨?_⟩
  intro i
  let code : SharedAffineDecisionListCode (r + (k + k)) :=
    (sharedAffineDecisionListCodeEquivBitCode (r + (k + k))).symm
      ((rawExactZABDecisionListBitFamily Z r k zfeat).empiricalRiskCode (samples i))
  refine ⟨code, ?_⟩
  funext u
  simp [exactZABDecisionListERMFamily,
    BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
    BitEncodedClassifierFamily.empiricalRiskPredictor,
    BitEncodedClassifierFamily.empiricalRiskCode,
    rawExactZABDecisionListBitFamily,
    code,
    sharedAffineDecisionListCodeEquivBitCode]

theorem exactZABDecisionListERMCompressionTarget
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (exactZABDecisionListERMFamily (Z := Z) (r := r) (k := k) zfeat samples)
      (r + (k + k) + 1) := by
  exact
    (exactZABDecisionListERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples).compressionTarget

theorem exactZABDecisionListERMCompressionTarget_twoMul
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (exactZABDecisionListERMFamily (Z := Z) (r := r) (k := k) zfeat samples)
      (r + 2 * k + 1) := by
  exact
    (exactZABDecisionListERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples).compressionTarget_twoMul

section

variable [Fintype Z]

theorem exactZABDecisionListERMRecoveryData
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
    ExactZABDecisionListRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ zfeat
      (exactZABDecisionListERMFamily (Z := Z) (r := r) (k := k) zfeat samples) q := by
  refine ⟨?_, hq⟩
  exact
    (exactZABDecisionListERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples).realized

theorem exactZABDecisionListERMRecoveryLowerBound
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
    1 - (2 ^ (r + (k + k) + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactZABDecisionListBitFamily Z r k zfeat).bitExactRecoverySampleMass
        μ
        ((exactZABDecisionListERMFamily
          (Z := Z) (r := r) (k := k) zfeat samples).predict i)
        m := by
  exact
    (exactZABDecisionListERMRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ zfeat samples q hq).recoveryLowerBound i m

theorem exactZABDecisionListERMRecoveryLowerBound_twoMul
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
    (exactZABDecisionListERMRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ zfeat samples q hq).recoveryLowerBound_twoMul i m

end

end

end Mettapedia.Computability.PNP
