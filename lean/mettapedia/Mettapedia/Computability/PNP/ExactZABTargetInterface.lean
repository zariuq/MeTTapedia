import Mettapedia.Computability.PNP.ExactZABDecisionListFamily

/-!
# P vs NP grassroots: target interfaces for the shared `z+a+b` decision-list route

This file packages the new manuscript-shaped candidate route:

* one fixed shared extractor `zfeat : Z → BitVec r`,
* one fixed-order decision-list family on the exact visible bits `(zfeat z, a, b)`,
* and, when needed, one uniform bad-code agreement bound.

This keeps the remaining burden explicit: exhibit the actual switched family as
one such realized family, then control the bad-code agreement mass.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

structure ExactZABDecisionListTargetData
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index) where
  realized :
    RealizedByRawExactZABDecisionListFamily (Z := Z) (r := r) (k := k) zfeat G

section

theorem ExactZABDecisionListTargetData.compressionTarget
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : ExactZABDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) zfeat G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + (k + k) + 1) := by
  exact exactVisibleCompressionTarget_of_realizedByRawExactZABDecisionListFamily
    (Z := Z) (r := r) (k := k) (Index := Index) zfeat h.realized

theorem ExactZABDecisionListTargetData.compressionTarget_twoMul
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : ExactZABDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) zfeat G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 2 * k + 1) := by
  exact exactVisibleCompressionTarget_of_realizedByRawExactZABDecisionListFamily_twoMul
    (Z := Z) (r := r) (k := k) (Index := Index) zfeat h.realized

end

structure ExactZABDecisionListRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  realized :
    RealizedByRawExactZABDecisionListFamily (Z := Z) (r := r) (k := k) zfeat G
  agreement_le :
    ∀ i,
      ∀ c :
        (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes (G.predict i),
        agreementMass μ (G.predict i)
          ((rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1) ≤ q

section

variable [Fintype Z]

theorem ExactZABDecisionListRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactZABDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) zfeat G := by
  exact ⟨h.realized⟩

theorem ExactZABDecisionListRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + (k + k) + 1) := by
  exact (h.targetData).compressionTarget

theorem ExactZABDecisionListRecoveryData.compressionTarget_twoMul
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 2 * k + 1) := by
  exact (h.targetData).compressionTarget_twoMul

theorem ExactZABDecisionListRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r + (k + k) + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactZABDecisionListBitFamily Z r k zfeat).bitExactRecoverySampleMass μ (G.predict i) m := by
  exact rawExactZABDecisionListRecoveryLowerBound
    (Z := Z) (r := r) (k := k) zfeat
    (μ := μ)
    (target := G.predict i)
    (m := m)
    (h.realized i)
    (h.agreement_le i)

theorem ExactZABDecisionListRecoveryData.recoveryLowerBound_twoMul
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r + 2 * k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactZABDecisionListBitFamily Z r k zfeat).bitExactRecoverySampleMass μ (G.predict i) m := by
  exact rawExactZABDecisionListRecoveryLowerBound_twoMul
    (Z := Z) (r := r) (k := k) zfeat
    (μ := μ)
    (target := G.predict i)
    (m := m)
    (h.realized i)
    (h.agreement_le i)

end

end

end Mettapedia.Computability.PNP
