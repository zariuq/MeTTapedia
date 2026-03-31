import Mettapedia.Computability.PNP.CanonicalZABCodeWitness

/-!
# P vs NP grassroots: final recovery interface for the canonical exact `(zfeat(z), a, b)` route

This file packages the last generic ingredients of the direct exact `z+a+b`
route:

* one shared extractor `zfeat`,
* one explicit exact decision-list code assignment per index,
* one corresponding agreement-mass upper bound.

Once those data are supplied, both the exact visible compression target and the
weighted exact-recovery lower bound follow automatically.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

structure CanonicalZABDecisionListRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  codes : Index → SharedAffineDecisionListCode (r + (k + k))
  exact_family :
    G = canonicalZABCodeFamily (Z := Z) (r := r) (k := k) zfeat codes
  agreement_le :
    ∀ i,
      ∀ c :
        (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes (G.predict i),
        agreementMass μ (G.predict i)
          ((rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1) ≤ q

section

variable [Fintype Z]

theorem CanonicalZABDecisionListRecoveryData.candidateData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    CanonicalZABDecisionListCandidateData
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat G := by
  exact candidateData_of_eq_canonicalZABCodeFamily
    (Z := Z) (r := r) (k := k) (Index := Index) h.codes h.exact_family

theorem CanonicalZABDecisionListRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (r + 2 * k + 1) := by
  exact (h.candidateData).compressionTarget

theorem CanonicalZABDecisionListRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r + 2 * k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactZABDecisionListBitFamily Z r k zfeat).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  exact (h.candidateData).recoveryLowerBound (μ := μ) (i := i) (m := m) (hq := h.agreement_le i)

end

end

end Mettapedia.Computability.PNP
