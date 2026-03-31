import Mettapedia.Computability.PNP.SharedExactZABFeatureFamilies

/-!
# P vs NP grassroots: target interfaces for the shared-basis `(zfeat(z), a, b)` route

This file packages the shared-basis route on the full manuscript-facing local
bits `(zfeat(z), a, b)`.

Once one fixed shared extractor and one fixed affine basis are supplied, the
remaining burden is just the choice of downstream combiner family.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

structure SharedExactZABAffineFeatureTargetData
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (G : ExactVisibleSwitchedFamily Z k Index) where
  realized :
    RealizedBySharedExactZABAffineFeatureFamily
      (Z := Z) (p := p) (r := r) (k := k) zfeat features G

structure SharedExactZABSparseThresholdTargetData
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (G : ExactVisibleSwitchedFamily Z k Index) where
  realized :
    RealizedBySharedExactZABSparseThresholdAffineFamily
      (Z := Z) (p := p) (r := r) (k := k) zfeat features G

structure SharedExactZABDecisionListTargetData
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (G : ExactVisibleSwitchedFamily Z k Index) where
  realized :
    RealizedBySharedExactZABAffineDecisionListFamily
      (Z := Z) (p := p) (r := r) (k := k) zfeat features G

section

theorem SharedExactZABAffineFeatureTargetData.compressionTarget
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 ^ p) := by
  exact exactVisibleCompressionTarget_of_realizedBySharedExactZABAffineFeatureFamily
    (Z := Z) (p := p) (r := r) (k := k) zfeat features h.realized

theorem SharedExactZABSparseThresholdTargetData.compressionTarget
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABSparseThresholdTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * p) := by
  exact exactVisibleCompressionTarget_of_realizedBySharedExactZABSparseThresholdAffineFamily
    (Z := Z) (p := p) (r := r) (k := k) zfeat features h.realized

theorem SharedExactZABDecisionListTargetData.compressionTarget
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABDecisionListTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (p + 1) := by
  exact exactVisibleCompressionTarget_of_realizedBySharedExactZABAffineDecisionListFamily
    (Z := Z) (p := p) (r := r) (k := k) zfeat features h.realized

end

structure SharedExactZABDecisionListRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  realized :
    RealizedBySharedExactZABAffineDecisionListFamily
      (Z := Z) (p := p) (r := r) (k := k) zfeat features G
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactZABAffineDecisionListBitFamily Z zfeat features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactZABAffineDecisionListBitFamily Z zfeat features).decode c.1) ≤ q

section

variable [Fintype Z]

theorem SharedExactZABDecisionListRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q) :
    SharedExactZABDecisionListTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features G := by
  exact ⟨h.realized⟩

theorem SharedExactZABDecisionListRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (p + 1) := by
  exact (h.targetData).compressionTarget

theorem SharedExactZABDecisionListRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (p + 1) : ℝ≥0∞) * q ^ m ≤
      (sharedExactZABAffineDecisionListBitFamily Z zfeat features).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  exact sharedExactZABAffineDecisionListRecoveryLowerBound
    (Z := Z) (p := p) (r := r) (k := k) zfeat features
    (μ := μ)
    (target := G.predict i)
    (m := m)
    (h.realized i)
    (h.agreement_le i)

end

end

end Mettapedia.Computability.PNP
