import Mettapedia.Computability.PNP.CanonicalZABCandidateInterface

/-!
# P vs NP grassroots: explicit code witnesses for the canonical exact `(zfeat(z), a, b)` route

This file reduces the direct exact `z+a+b` route to the simplest concrete
witness: one exact decision-list code per index.

If the switched family is exactly the family induced by such a code assignment,
then the canonical candidate package, compression theorem, and per-index
recovery theorem all follow automatically.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

/-- The exact-surface switched family induced by one exact `(zfeat(z), a, b)`
decision-list code for each index. -/
noncomputable def canonicalZABCodeFamily
    (zfeat : Z → BitVec r)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k))) :
    ExactVisibleSwitchedFamily Z k Index where
  predict i u := rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat (codes i) u

theorem canonicalZABCodeFamily_realized
    (zfeat : Z → BitVec r)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k))) :
    RealizedByRawExactZABDecisionListFamily
      (Z := Z) (r := r) (k := k) zfeat
      (canonicalZABCodeFamily (Z := Z) (r := r) (k := k) zfeat codes) := by
  intro i
  exact ⟨codes i, rfl⟩

/-- Explicit code assignments automatically instantiate the canonical exact
candidate package. -/
def canonicalZABDecisionListCandidateData_of_codes
    (zfeat : Z → BitVec r)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k))) :
    CanonicalZABDecisionListCandidateData
      (Z := Z) (r := r) (k := k) (Index := Index)
      zfeat (canonicalZABCodeFamily (Z := Z) (r := r) (k := k) zfeat codes) where
  realized := canonicalZABCodeFamily_realized (Z := Z) (r := r) (k := k) zfeat codes

theorem exactVisibleCompressionTarget_canonicalZABCodeFamily
    (zfeat : Z → BitVec r)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k))) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (canonicalZABCodeFamily (Z := Z) (r := r) (k := k) zfeat codes)
      (r + 2 * k + 1) := by
  exact
    CanonicalZABDecisionListCandidateData.compressionTarget
      (canonicalZABDecisionListCandidateData_of_codes
        (Z := Z) (r := r) (k := k) (Index := Index) zfeat codes)

theorem candidateData_of_eq_canonicalZABCodeFamily
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (codes : Index → SharedAffineDecisionListCode (r + (k + k)))
    (hG : G = canonicalZABCodeFamily (Z := Z) (r := r) (k := k) zfeat codes) :
    CanonicalZABDecisionListCandidateData
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat G := by
  subst hG
  exact canonicalZABDecisionListCandidateData_of_codes
    (Z := Z) (r := r) (k := k) (Index := Index) zfeat codes

theorem canonicalZABCodeFamily_recoveryLowerBound
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k)))
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (i : Index) (m : ℕ)
    {q : ℝ≥0∞}
    (hq :
      ∀ c :
        (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes
          ((canonicalZABCodeFamily (Z := Z) (r := r) (k := k) zfeat codes).predict i),
        agreementMass μ
          ((canonicalZABCodeFamily (Z := Z) (r := r) (k := k) zfeat codes).predict i)
          ((rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1) ≤ q) :
    1 - (2 ^ (r + 2 * k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactZABDecisionListBitFamily Z r k zfeat).bitExactRecoverySampleMass
        μ ((canonicalZABCodeFamily (Z := Z) (r := r) (k := k) zfeat codes).predict i) m := by
  exact
    CanonicalZABDecisionListCandidateData.recoveryLowerBound
      (canonicalZABDecisionListCandidateData_of_codes
        (Z := Z) (r := r) (k := k) (Index := Index) zfeat codes)
      μ i m hq

end

end Mettapedia.Computability.PNP
