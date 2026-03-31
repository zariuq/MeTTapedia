import Mettapedia.Computability.PNP.BitFamilyERM
import Mettapedia.Computability.PNP.SharedExactZABTargetInterface

/-!
# P vs NP grassroots: ERM over shared-basis `(zfeat(z), a, b)` classes

This file applies the generic ERM transport layer to the shared-basis exact
`z+a+b` families.  If the wrapper is honestly choosing from one fixed shared
feature basis and one fixed downstream combiner class, then the selected code is
again the route witness.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

noncomputable def sharedExactZABAffineDecisionListERMFamily
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleSwitchedFamily Z k Index :=
  (sharedExactZABAffineDecisionListBitFamily Z zfeat features).indexedEmpiricalRiskFamily samples

theorem sharedExactZABAffineDecisionListERMTargetData
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    SharedExactZABDecisionListTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features
      (sharedExactZABAffineDecisionListERMFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features samples) := by
  refine ⟨?_⟩
  intro i
  let code : SharedAffineDecisionListCode p :=
    (sharedAffineDecisionListCodeEquivBitCode p).symm
      ((sharedExactZABAffineDecisionListBitFamily Z zfeat features).empiricalRiskCode (samples i))
  refine ⟨code, ?_⟩
  funext u
  simp [sharedExactZABAffineDecisionListERMFamily,
    BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
    BitEncodedClassifierFamily.empiricalRiskPredictor,
    BitEncodedClassifierFamily.empiricalRiskCode,
    sharedExactZABAffineDecisionListBitFamily,
    code,
    sharedAffineDecisionListCodeEquivBitCode]

theorem sharedExactZABAffineDecisionListERMCompressionTarget
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (sharedExactZABAffineDecisionListERMFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features samples)
      (p + 1) := by
  exact
    (sharedExactZABAffineDecisionListERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples).compressionTarget

section

variable [Fintype Z]

theorem sharedExactZABAffineDecisionListERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactZABAffineDecisionListBitFamily Z zfeat features).toEncodedFamily.BadCodes
            ((sharedExactZABAffineDecisionListERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i),
          agreementMass μ
            ((sharedExactZABAffineDecisionListERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i)
            ((sharedExactZABAffineDecisionListBitFamily Z zfeat features).decode c.1) ≤ q) :
    SharedExactZABDecisionListRecoveryData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      μ zfeat features
      (sharedExactZABAffineDecisionListERMFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features samples) q := by
  refine ⟨?_, hq⟩
  exact
    (sharedExactZABAffineDecisionListERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples).realized

theorem sharedExactZABAffineDecisionListERMRecoveryLowerBound
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactZABAffineDecisionListBitFamily Z zfeat features).toEncodedFamily.BadCodes
            ((sharedExactZABAffineDecisionListERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i),
          agreementMass μ
            ((sharedExactZABAffineDecisionListERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i)
            ((sharedExactZABAffineDecisionListBitFamily Z zfeat features).decode c.1) ≤ q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (p + 1) : ℝ≥0∞) * q ^ m ≤
      (sharedExactZABAffineDecisionListBitFamily Z zfeat features).bitExactRecoverySampleMass
        μ
        ((sharedExactZABAffineDecisionListERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i)
        m := by
  exact
    (sharedExactZABAffineDecisionListERMRecoveryData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      μ zfeat features samples q hq).recoveryLowerBound i m

end

end

end Mettapedia.Computability.PNP
