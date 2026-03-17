import Mettapedia.Logic.PLNFirstOrder.QuantifierSemantics
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Third-Order Quantifier Semantics (PLN Chapter-11 style)

This file makes the "distribution over second-order uncertainty" layer explicit.

- Second-order uncertainty: a probability distribution over latent outcomes, each
  carrying an `BinaryEvidence` value.
- Third-order quantifier model: assigns one such second-order uncertainty object
  to each domain element.

It then provides:
1. a third-order/weakness bridge theorem to current `forAllEval` semantics
   (under explicit pointwise assumptions),
2. a confidence-degradation theorem:
   universal confidence is bounded by finite-observation confidence.
-/

namespace Mettapedia.Logic.PLNFirstOrder

open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal
open scoped BigOperators

/-! ## Second-order uncertainty objects -/

/-- A second-order uncertainty object:
distribution over latent outcomes, each mapped to an `BinaryEvidence` value. -/
structure SecondOrderUncertainty (Ω : Type*) [Fintype Ω] where
  posterior : PMF Ω
  evidenceOf : Ω → BinaryEvidence

namespace SecondOrderUncertainty

variable {Ω : Type*} [Fintype Ω]

/-- Expected evidence induced by a second-order uncertainty object. -/
noncomputable def expectedEvidence (S : SecondOrderUncertainty Ω) : BinaryEvidence :=
  ⟨∑ ω, S.posterior ω * (S.evidenceOf ω).pos,
   ∑ ω, S.posterior ω * (S.evidenceOf ω).neg⟩

end SecondOrderUncertainty

/-! ## Third-order quantifier object -/

/-- Third-order quantifier semantics:
each domain element gets its own second-order uncertainty object. -/
structure ThirdOrderQuantifierModel (U Ω : Type*) [Fintype Ω] where
  secondOrder : U → SecondOrderUncertainty Ω

namespace ThirdOrderQuantifierModel

variable {U Ω : Type*} [Fintype Ω]

/-- The point-level evidence (second-order expectation) for one domain element. -/
noncomputable def pointEvidence (M : ThirdOrderQuantifierModel U Ω) (u : U) : BinaryEvidence :=
  (M.secondOrder u).expectedEvidence

/-- Universal (all-domain) extensional evidence view for third-order objects. -/
noncomputable def forAllEvidenceUniversal
    (M : ThirdOrderQuantifierModel U Ω) : BinaryEvidence :=
  sInf { e | ∃ u : U, e = pointEvidence M u }

/-- Finite-observation extensional evidence view for third-order objects. -/
noncomputable def forAllEvidenceObserved
    (M : ThirdOrderQuantifierModel U Ω)
    (obs : Finset U) : BinaryEvidence :=
  sInf { e | ∃ u ∈ obs, e = pointEvidence M u }

/-- Confidence view for universal evidence. -/
noncomputable def forAllConfidenceUniversal
    (M : ThirdOrderQuantifierModel U Ω) (κ : ℝ≥0∞) : ℝ≥0∞ :=
  BinaryEvidence.toConfidence κ (forAllEvidenceUniversal M)

/-- Confidence view for finite-observation evidence. -/
noncomputable def forAllConfidenceObserved
    (M : ThirdOrderQuantifierModel U Ω)
    (κ : ℝ≥0∞) (obs : Finset U) : ℝ≥0∞ :=
  BinaryEvidence.toConfidence κ (forAllEvidenceObserved M obs)

lemma total_mono {e e' : BinaryEvidence} (h : e ≤ e') : e.total ≤ e'.total := by
  exact add_le_add h.1 h.2

/-- Universal evidence is always below finite-observation evidence
(`sInf` over larger set is smaller). -/
theorem forAllEvidenceUniversal_le_observed
    (M : ThirdOrderQuantifierModel U Ω) (obs : Finset U) :
    forAllEvidenceUniversal M ≤ forAllEvidenceObserved M obs := by
  unfold forAllEvidenceUniversal forAllEvidenceObserved
  refine le_sInf ?_
  intro e he
  rcases he with ⟨u, huObs, rfl⟩
  exact sInf_le ⟨u, rfl⟩

/-- If all domain elements are observed, observed evidence is below universal evidence. -/
theorem forAllEvidenceObserved_le_universal_of_all
    (M : ThirdOrderQuantifierModel U Ω) (obs : Finset U)
    (hobs : ∀ u : U, u ∈ obs) :
    forAllEvidenceObserved M obs ≤ forAllEvidenceUniversal M := by
  unfold forAllEvidenceUniversal forAllEvidenceObserved
  refine le_sInf ?_
  intro e he
  rcases he with ⟨u, rfl⟩
  exact sInf_le ⟨u, hobs u, rfl⟩

/-- Positive fixture: full observation recovers universal evidence exactly. -/
theorem forAllEvidenceObserved_univ_eq_universal
    [Fintype U]
    (M : ThirdOrderQuantifierModel U Ω) :
    forAllEvidenceObserved M Finset.univ = forAllEvidenceUniversal M := by
  apply le_antisymm
  · exact forAllEvidenceObserved_le_universal_of_all (M := M) (obs := Finset.univ)
      (hobs := by intro u; simp)
  · exact forAllEvidenceUniversal_le_observed (M := M) (obs := Finset.univ)

/-- Negative fixture: empty observation set yields top (vacuous `sInf` on empty set). -/
theorem forAllEvidenceObserved_empty_eq_top
    (M : ThirdOrderQuantifierModel U Ω) :
    forAllEvidenceObserved M (∅ : Finset U) = ⊤ := by
  unfold forAllEvidenceObserved
  have hempty : ({ e : BinaryEvidence | ∃ u ∈ (∅ : Finset U), e = pointEvidence M u } : Set BinaryEvidence) = ∅ := by
    ext e
    simp
  rw [hempty, sInf_empty]

/-- Confidence degradation theorem:
universal quantifier confidence is bounded by finite-observation confidence. -/
theorem confidence_universal_le_observed
    (M : ThirdOrderQuantifierModel U Ω)
    (κ : ℝ≥0∞)
    (hκ_nonzero : κ ≠ 0) (hκ_ne_top : κ ≠ ⊤)
    (obs : Finset U)
    (hObsTotal_ne_top : (forAllEvidenceObserved M obs).total ≠ ⊤) :
    forAllConfidenceUniversal M κ ≤ forAllConfidenceObserved M κ obs := by
  unfold forAllConfidenceUniversal forAllConfidenceObserved
  apply BinaryEvidence.confidence_monotone_in_total
  · exact hκ_nonzero
  · exact hκ_ne_top
  · exact hObsTotal_ne_top
  · exact total_mono (forAllEvidenceUniversal_le_observed (M := M) (obs := obs))

section Weakness

variable [Fintype U]

/-- SatisfyingSet induced by third-order expected evidence. -/
noncomputable def satisfyingSet (M : ThirdOrderQuantifierModel U Ω) : SatisfyingSet U :=
  ⟨pointEvidence M⟩

/-- Third-order universal quantifier evaluated through current weakness semantics. -/
noncomputable def forAllEvalWeakness
    (M : ThirdOrderQuantifierModel U Ω)
    (μ : Mettapedia.Algebra.QuantaleWeakness.WeightFunction U BinaryEvidence) : BinaryEvidence :=
  forAllEval (satisfyingSet M) μ

/-- Explicit assumptions for bridging to current weakness semantics. -/
structure WeaknessBridgeAssumptions
    (M : ThirdOrderQuantifierModel U Ω)
    (S : SatisfyingSet U) : Prop where
  pointwise_match : ∀ u : U, pointEvidence M u = S.pred u

/-- Bridge theorem:
under explicit pointwise assumptions, third-order weakness semantics equals the
current PLN weakness quantifier semantics. -/
theorem forAllEvalWeakness_eq_forAllEval_of_assumptions
    (M : ThirdOrderQuantifierModel U Ω)
    (μ : Mettapedia.Algebra.QuantaleWeakness.WeightFunction U BinaryEvidence)
    (S : SatisfyingSet U)
    (hA : WeaknessBridgeAssumptions M S) :
    forAllEvalWeakness M μ = forAllEval S μ := by
  unfold forAllEvalWeakness forAllEval
  have hdiag :
      SatisfyingSet.diagonal (satisfyingSet M) = SatisfyingSet.diagonal S := by
    ext uv
    constructor <;> intro h
    · rw [SatisfyingSet.mem_diagonal] at h ⊢
      simpa [satisfyingSet, hA.pointwise_match uv.1, hA.pointwise_match uv.2] using h
    · rw [SatisfyingSet.mem_diagonal] at h ⊢
      simpa [satisfyingSet, hA.pointwise_match uv.1, hA.pointwise_match uv.2] using h
  simp [hdiag]

/-- Confidence-level corollary of the weakness bridge. -/
theorem forAllEvalWeakness_confidence_eq_of_assumptions
    (M : ThirdOrderQuantifierModel U Ω)
    (μ : Mettapedia.Algebra.QuantaleWeakness.WeightFunction U BinaryEvidence)
    (S : SatisfyingSet U)
    (κ : ℝ≥0∞)
    (hA : WeaknessBridgeAssumptions M S) :
    BinaryEvidence.toConfidence κ (forAllEvalWeakness M μ) =
      BinaryEvidence.toConfidence κ (forAllEval S μ) := by
  simp [forAllEvalWeakness_eq_forAllEval_of_assumptions (M := M) (μ := μ) (S := S) hA]

end Weakness

end ThirdOrderQuantifierModel

end Mettapedia.Logic.PLNFirstOrder
