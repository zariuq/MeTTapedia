import Mettapedia.Computability.PNP.CanonicalZABTargetRoute

/-!
# P vs NP grassroots: canonical exact `(zfeat(z), a, b)` candidate interface

This file packages the most concrete manuscript-facing exact-surface route into
one data object.

The remaining burden is:

* one shared extractor `zfeat`,
* realization of the switched family by fixed-order decision lists on the raw
  exact visible bits `(zfeat(z), a, b)`.

From that package we recover:

* the exact visible compression target with budget `r + 2k + 1`,
* for each indexed predictor, one concrete exact `(zfeat(z), a, b)`
  decision-list representation,
* the corresponding weighted exact-recovery lower bound.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

structure CanonicalZABDecisionListCandidateData
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index) where
  realized :
    RealizedByRawExactZABDecisionListFamily
      (Z := Z) (r := r) (k := k) zfeat G

section

theorem CanonicalZABDecisionListCandidateData.compressionTarget
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      CanonicalZABDecisionListCandidateData
        (Z := Z) (r := r) (k := k) (Index := Index) zfeat G) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (r + 2 * k + 1) := by
  exact exactVisibleCompressionTarget_of_canonicalZABDecisionList_twoMul
    (Z := Z) (r := r) (k := k) (Index := Index) zfeat h.realized

theorem CanonicalZABDecisionListCandidateData.target_eq_rawExactZABDecisionList
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      CanonicalZABDecisionListCandidateData
        (Z := Z) (r := r) (k := k) (Index := Index) zfeat G)
    (i : Index) :
    ∃ code : SharedAffineDecisionListCode (r + (k + k)),
      G.predict i =
        rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code := by
  exact h.realized i

theorem CanonicalZABDecisionListCandidateData.recoveryLowerBound
    [Fintype Z]
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      CanonicalZABDecisionListCandidateData
        (Z := Z) (r := r) (k := k) (Index := Index) zfeat G)
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (i : Index) (m : ℕ)
    {q : ℝ≥0∞}
    (hq :
      ∀ c :
        (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes (G.predict i),
        agreementMass μ (G.predict i)
          ((rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1) ≤ q) :
    1 - (2 ^ (r + 2 * k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactZABDecisionListBitFamily Z r k zfeat).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  rcases h.target_eq_rawExactZABDecisionList i with ⟨code, hcode⟩
  exact rawExactZABDecisionListRecoveryLowerBound_twoMul
    (Z := Z) (r := r) (k := k) zfeat (μ := μ) (target := G.predict i) (m := m)
    ⟨code, hcode⟩ hq

end

end

end Mettapedia.Computability.PNP
