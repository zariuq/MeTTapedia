import Mettapedia.Computability.PNP.CanonicalABTargetRoute

/-!
# P vs NP grassroots: canonical raw `(a, b)` candidate interface

This file packages the most concrete current exact-surface route into one data
object.

The burden is now:

* quotient invariance under the reduced raw visible surface `(a, b)`,
* realization of the lifted reduced family by fixed-order decision lists on the
  raw visible bits.

From that package we recover:

* the exact visible compression target with budget `2k + 1`,
* for each indexed predictor, a concrete raw `(a, b)` decision-list
  representation,
* the corresponding weighted exact-recovery lower bound for that predictor.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {k : ℕ} {Index : Type*}

structure CanonicalABDecisionListCandidateData
    [Inhabited Z]
    (G : ExactVisibleSwitchedFamily Z k Index) where
  invariant : ABVisibleInvariant (Z := Z) (k := k) G
  realized :
    RealizedByABDecisionListFamily (k := k)
      (liftToABVisibleFamily (Z := Z) (k := k) G)

section

variable [Inhabited Z]

theorem CanonicalABDecisionListCandidateData.compressionTarget
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : CanonicalABDecisionListCandidateData (Z := Z) (k := k) (Index := Index) G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * k + 1) := by
  exact exactVisibleCompressionTarget_of_invariant_and_canonicalABDecisionList_twoMul
    (Z := Z) (k := k) h.invariant h.realized

theorem CanonicalABDecisionListCandidateData.target_eq_abDecisionList
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : CanonicalABDecisionListCandidateData (Z := Z) (k := k) (Index := Index) G)
    (i : Index) :
    ∃ code : SharedAffineDecisionListCode (k + k),
      G.predict i = fun u => abDecisionListPredict (k := k) code (abVisibleData u) := by
  rcases h.realized i with ⟨code, hi⟩
  refine ⟨code, ?_⟩
  funext u
  calc
    G.predict i u = (liftToABVisibleFamily (Z := Z) (k := k) G).predict i (abVisibleData u) := by
      exact factorsThrough_abVisibleData_of_invariant (Z := Z) (k := k) h.invariant i u
    _ = abDecisionListPredict (k := k) code (abVisibleData u) := by
      exact congrFun hi (abVisibleData u)

theorem CanonicalABDecisionListCandidateData.recoveryLowerBound
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : CanonicalABDecisionListCandidateData (Z := Z) (k := k) (Index := Index) G)
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (i : Index) (m : ℕ)
    {q : ℝ≥0∞}
    (hq :
      ∀ c : (rawExactABDecisionListBitFamily Z k).toEncodedFamily.BadCodes (G.predict i),
        agreementMass μ (G.predict i) ((rawExactABDecisionListBitFamily Z k).decode c.1) ≤ q) :
    1 - (2 ^ (2 * k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactABDecisionListBitFamily Z k).bitExactRecoverySampleMass μ (G.predict i) m := by
  rcases h.target_eq_abDecisionList i with ⟨code, hcode⟩
  exact rawExactABDecisionListRecoveryLowerBound_of_factorsThrough_ab_twoMul
    (Z := Z) (k := k) (μ := μ) (target := G.predict i) (m := m)
    ⟨code, hcode⟩ hq

end

end

end Mettapedia.Computability.PNP
