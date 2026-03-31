import Mettapedia.Computability.PNP.CanonicalZABERMRoute

/-!
# P vs NP grassroots: final ERM interface for the canonical exact `(zfeat(z), a, b)` route

This file packages the last manuscript-facing ingredients in the most natural
ERM form:

* one shared extractor `zfeat`,
* one labeled sample assignment,
* one proof that the switched family is exactly the ERM wrapper on those
  samples,
* and one bad-code agreement bound.

Once those are supplied, the canonical exact compression and recovery
consequences follow automatically.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

structure CanonicalZABERMRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool
  exact_family :
    G = exactZABDecisionListERMFamily (Z := Z) (r := r) (k := k) zfeat samples
  agreement_le :
    ∀ i,
      ∀ c :
        (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes (G.predict i),
        agreementMass μ (G.predict i)
          ((rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1) ≤ q

section

variable [Fintype Z]

theorem CanonicalZABERMRecoveryData.candidateData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    CanonicalZABDecisionListCandidateData
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat G := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact canonicalZABDecisionListERMCandidateData
    (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples

theorem CanonicalZABERMRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (r + 2 * k + 1) := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact canonicalZABDecisionListERMCompressionTarget
    (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples

theorem CanonicalZABERMRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r + 2 * k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactZABDecisionListBitFamily Z r k zfeat).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact canonicalZABDecisionListERMRecoveryLowerBound
    (Z := Z) (r := r) (k := k) (Index := Index)
    μ zfeat samples q agreement_le i m

end

end

end Mettapedia.Computability.PNP
