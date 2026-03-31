import Mettapedia.Computability.PNP.CanonicalABCodeWitness

/-!
# P vs NP grassroots: final recovery interface for the canonical raw `(a, b)` route

This file packages the last generic ingredient of the current route:

* one explicit raw `(a, b)` decision-list code assignment per index, and
* one corresponding agreement-mass upper bound.

Once those data are supplied, both the exact visible compression target and the
weighted exact-recovery lower bound follow automatically.  So instantiating this
interface is the last candidate-specific burden before the route leaves generic
background theory and enters the actual switched-family theorem.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {k : ℕ} {Index : Type*}

structure CanonicalABDecisionListRecoveryData
    [Inhabited Z] [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  codes : Index → SharedAffineDecisionListCode (k + k)
  exact_family : G = canonicalABCodeFamily (Z := Z) (k := k) codes
  agreement_le :
    ∀ i,
      ∀ c : (rawExactABDecisionListBitFamily Z k).toEncodedFamily.BadCodes (G.predict i),
        agreementMass μ (G.predict i) ((rawExactABDecisionListBitFamily Z k).decode c.1) ≤ q

section

variable [Inhabited Z] [Fintype Z]

theorem CanonicalABDecisionListRecoveryData.candidateData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h : CanonicalABDecisionListRecoveryData (Z := Z) (k := k) (Index := Index) μ G q) :
    CanonicalABDecisionListCandidateData (Z := Z) (k := k) (Index := Index) G := by
  exact candidateData_of_eq_canonicalABCodeFamily
    (Z := Z) (k := k) (Index := Index) h.codes h.exact_family

theorem CanonicalABDecisionListRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h : CanonicalABDecisionListRecoveryData (Z := Z) (k := k) (Index := Index) μ G q) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * k + 1) := by
  exact (h.candidateData).compressionTarget

theorem CanonicalABDecisionListRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h : CanonicalABDecisionListRecoveryData (Z := Z) (k := k) (Index := Index) μ G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 * k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactABDecisionListBitFamily Z k).bitExactRecoverySampleMass μ (G.predict i) m := by
  exact (h.candidateData).recoveryLowerBound (μ := μ) (i := i) (m := m) (hq := h.agreement_le i)

end

end

end Mettapedia.Computability.PNP
