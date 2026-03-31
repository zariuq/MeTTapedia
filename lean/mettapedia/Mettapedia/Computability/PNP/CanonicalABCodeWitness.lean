import Mettapedia.Computability.PNP.CanonicalABCandidateInterface

/-!
# P vs NP grassroots: explicit code witnesses for the canonical raw `(a, b)` route

This file reduces the canonical raw-bit route to the simplest concrete witness:
an explicit assignment of one raw `(a, b)` decision-list code to each index.

If the switched family is exactly the family induced by such a code assignment,
then the canonical candidate-data package, compression theorem, and per-index
recovery theorem all follow automatically.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {k : ℕ} {Index : Type*}

/-- The exact-surface switched family induced by one raw `(a, b)` decision-list
code for each index. -/
noncomputable def canonicalABCodeFamily
    (codes : Index → SharedAffineDecisionListCode (k + k)) :
    ExactVisibleSwitchedFamily Z k Index where
  predict i u := abDecisionListPredict (k := k) (codes i) (abVisibleData u)

theorem canonicalABCodeFamily_invariant
    (codes : Index → SharedAffineDecisionListCode (k + k)) :
    ABVisibleInvariant (Z := Z) (k := k) (canonicalABCodeFamily (Z := Z) (k := k) codes) := by
  intro i u v huv
  cases u
  cases v
  cases huv
  rfl

section

variable [Inhabited Z]

theorem canonicalABCodeFamily_realized
    (codes : Index → SharedAffineDecisionListCode (k + k)) :
    RealizedByABDecisionListFamily (k := k)
      (liftToABVisibleFamily (Z := Z) (k := k) (canonicalABCodeFamily (Z := Z) (k := k) codes)) := by
  intro i
  refine ⟨codes i, ?_⟩
  funext x
  cases x
  rfl

/-- Explicit code assignments automatically instantiate the canonical candidate
data package. -/
def canonicalABDecisionListCandidateData_of_codes
    (codes : Index → SharedAffineDecisionListCode (k + k)) :
    CanonicalABDecisionListCandidateData
      (Z := Z) (k := k) (Index := Index) (canonicalABCodeFamily (Z := Z) (k := k) codes) where
  invariant := canonicalABCodeFamily_invariant (Z := Z) (k := k) codes
  realized := canonicalABCodeFamily_realized (Z := Z) (k := k) codes

theorem exactVisibleCompressionTarget_canonicalABCodeFamily
    (codes : Index → SharedAffineDecisionListCode (k + k)) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (canonicalABCodeFamily (Z := Z) (k := k) codes) (2 * k + 1) := by
  exact
    CanonicalABDecisionListCandidateData.compressionTarget
      (canonicalABDecisionListCandidateData_of_codes
        (Z := Z) (k := k) (Index := Index) codes)

theorem candidateData_of_eq_canonicalABCodeFamily
    {G : ExactVisibleSwitchedFamily Z k Index}
    (codes : Index → SharedAffineDecisionListCode (k + k))
    (hG : G = canonicalABCodeFamily (Z := Z) (k := k) codes) :
    CanonicalABDecisionListCandidateData (Z := Z) (k := k) (Index := Index) G := by
  subst hG
  exact canonicalABDecisionListCandidateData_of_codes (Z := Z) (k := k) (Index := Index) codes

theorem canonicalABCodeFamily_recoveryLowerBound
    [Fintype Z]
    (codes : Index → SharedAffineDecisionListCode (k + k))
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (i : Index) (m : ℕ)
    {q : ℝ≥0∞}
    (hq :
      ∀ c :
        (rawExactABDecisionListBitFamily Z k).toEncodedFamily.BadCodes
          ((canonicalABCodeFamily (Z := Z) (k := k) codes).predict i),
        agreementMass μ ((canonicalABCodeFamily (Z := Z) (k := k) codes).predict i)
          ((rawExactABDecisionListBitFamily Z k).decode c.1) ≤ q) :
    1 - (2 ^ (2 * k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactABDecisionListBitFamily Z k).bitExactRecoverySampleMass
        μ ((canonicalABCodeFamily (Z := Z) (k := k) codes).predict i) m := by
  exact
    CanonicalABDecisionListCandidateData.recoveryLowerBound
      (canonicalABDecisionListCandidateData_of_codes
        (Z := Z) (k := k) (Index := Index) codes)
      μ i m hq

end

end

end Mettapedia.Computability.PNP
