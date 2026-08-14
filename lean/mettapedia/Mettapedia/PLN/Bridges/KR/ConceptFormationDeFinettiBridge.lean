import Mettapedia.PLN.Bridges.KR.ConceptFormationITVBridge
import Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge

/-!
# de Finetti Adapter for Credal Concept Formation

This module is the honest handoff between the de Finetti/projective-credal
adapter layer and the finite credal concept-formation ITV bridge.

It does not construct a de Finetti process semantics for formed concepts.  It
states the exact theorem available once a caller supplies the gluing map from a
Bernoulli mixture to a compatible precise completion of the finite gate
projective specification.
-/

namespace Mettapedia.PLN.Bridges.KR.ConceptFormationDeFinettiBridge

open MeasureTheory
open Mettapedia.KR.ConceptOntology
open Mettapedia.KR.ConceptGeometry.AbstractInheritance
open Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti
open Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge
open Mettapedia.ProbabilityTheory.ImpreciseProbability
open Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal
open Mettapedia.PLN.Bridges.KR.ConceptFormationITVBridge
open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth
open Mettapedia.PLN.TruthValues.PLNTruthTower
attribute [local instance] Classical.propDecidable

universe uΩ u v w x y

section Adapter

variable {Ω : Type uΩ} [MeasurableSpace Ω]
variable {Obs : Type u} {Obj : Type v} {Attr : Type w} {Q : Type x} {Gate : Type y}
variable [AddCommMonoid Q] [Preorder Q]
variable [Fintype Gate] [Nonempty Gate]
variable [Fintype Obj] [Fintype Attr]

/- Once a de Finetti/projective-credal specialization is explicitly glued to
the finite gate specification, its determination criterion for a formed-concept
query is exactly the KR lower/upper gap criterion. -/
omit [Fintype Gate] [Nonempty Gate] in
theorem deFinettiGateSpec_determinesConceptFormationGamble_iff_noGap
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := PUnit) (Global := Gate) X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate))
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    D.projectiveSpec.determinesGlobalGamble
        (ObservationEncoder.conceptFormationGamble S Γ σ A) ↔
      ¬ (A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
          A ∉ ObservationEncoder.lowerConceptFamily S Γ σ) := by
  rw [hSpec]
  exact
    ObservationEncoder.gateCredalProjectiveSpec_determinesGlobalGamble_conceptFormationGamble_iff
      S Γ σ A

/- The same glued de Finetti/projective-credal specialization has strict
global width exactly when the candidate concept is permissively formed by some
gate but not robustly formed by all gates. -/
omit [Fintype Gate] [Nonempty Gate] in
theorem deFinettiGateSpec_hasStrictGlobalWidth_conceptFormationGamble_iff_gap
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := PUnit) (Global := Gate) X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate))
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    D.projectiveSpec.hasStrictGlobalWidth
        (ObservationEncoder.conceptFormationGamble S Γ σ A) ↔
      A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
        A ∉ ObservationEncoder.lowerConceptFamily S Γ σ := by
  rw [hSpec]
  exact
    ObservationEncoder.gateCredalProjectiveSpec_hasStrictGlobalWidth_conceptFormationGamble_iff
      S Γ σ A

omit [Fintype Gate] [Nonempty Gate] in
/-- Compatibility with the current finite gate-credal specification is a
strong boundary condition: every representing mixture completion is forced to
be a Dirac prevision at some active gate.  Thus this adapter is an explicit
finite-gate handoff, not a hidden de Finetti process semantics for formed
concepts. -/
theorem deFinettiGateSpec_completion_eq_dirac_of_compatible
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := PUnit) (Global := Gate) X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate))
    (M : BernoulliMixture) (hRep : Represents M X μ) :
    ∃ g : Gate, D.completionOfMixture M = PrecisePrevision.dirac g := by
  have hP :
      D.completionOfMixture M ∈
        (gateCredalProjectiveSpec (Gate := Gate)).projectiveLimitCredalSet := by
    simpa [hSpec] using D.mixtureCompatible M hRep
  have hGate :
      D.completionOfMixture M ∈ gateCredalSet (Gate := Gate) := by
    simpa [gateCredalProjectiveSpec] using hP
  rcases (show ∃ g : Gate, PrecisePrevision.dirac g = D.completionOfMixture M by
    simpa [gateCredalSet] using hGate) with ⟨g, hg⟩
  exact ⟨g, hg.symm⟩

omit [Fintype Gate] [Nonempty Gate] in
/-- Active-gate readout form of
`deFinettiGateSpec_completion_eq_dirac_of_compatible`: on a concept-formation
gamble, a compatible de Finetti mixture completion evaluates exactly like
choosing one admissible gate. -/
theorem deFinettiGateSpec_completion_conceptFormationGamble_eq_activeGate
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := PUnit) (Global := Gate) X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate))
    (M : BernoulliMixture) (hRep : Represents M X μ)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    ∃ g : Gate,
      (D.completionOfMixture M)
          (ObservationEncoder.conceptFormationGamble S Γ σ A) =
        if A ∈
            Mettapedia.KR.ConceptGeometry.AbstractInheritance.finiteConceptFamily
              (Γ g) (ObservationEncoder.aggregate S σ)
        then 1 else 0 := by
  rcases deFinettiGateSpec_completion_eq_dirac_of_compatible
      X μ D hSpec M hRep with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  rw [hg]
  simp [ObservationEncoder.conceptFormationGamble]

omit [Fintype Gate] [Nonempty Gate] in
/-- Constructive endpoint form of the gap canary.  If a candidate concept is
formed by some admissible gate but not robustly by all gates, then the glued
finite-gate specification has two compatible precise completions that evaluate
the concept-formation gamble as `1` and `0`.  The gap is therefore a real
credal spread, not a display artifact. -/
theorem deFinettiGateSpec_gap_has_endpoint_completions
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := PUnit) (Global := Gate) X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate))
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (hGap :
      A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
        A ∉ ObservationEncoder.lowerConceptFamily S Γ σ) :
    ∃ P Q : PrecisePrevision Gate,
      P ∈ D.projectiveSpec.projectiveLimitCredalSet ∧
      Q ∈ D.projectiveSpec.projectiveLimitCredalSet ∧
      P (ObservationEncoder.conceptFormationGamble S Γ σ A) = 1 ∧
      Q (ObservationEncoder.conceptFormationGamble S Γ σ A) = 0 := by
  rcases hGap with ⟨hUpper, hNotLower⟩
  rcases (ObservationEncoder.mem_upperConceptFamily_iff S Γ σ A).mp hUpper with
    ⟨gTrue, hTrue⟩
  have hFalseEx :
      ∃ gFalse : Gate,
        A ∉ Mettapedia.KR.ConceptGeometry.AbstractInheritance.finiteConceptFamily
          (Γ gFalse) (ObservationEncoder.aggregate S σ) := by
    by_contra hNoFalse
    exact hNotLower
      ((ObservationEncoder.mem_lowerConceptFamily_iff S Γ σ A).mpr
        (fun g => by
          by_contra hNot
          exact hNoFalse ⟨g, hNot⟩))
  rcases hFalseEx with ⟨gFalse, hFalse⟩
  refine ⟨PrecisePrevision.dirac gTrue, PrecisePrevision.dirac gFalse, ?_, ?_, ?_, ?_⟩
  · rw [hSpec, gateCredalProjectiveSpec,
      identityCredalProjectiveSpec_projectiveLimitCredalSet]
    exact ⟨gTrue, rfl⟩
  · rw [hSpec, gateCredalProjectiveSpec,
      identityCredalProjectiveSpec_projectiveLimitCredalSet]
    exact ⟨gFalse, rfl⟩
  · simp [ObservationEncoder.conceptFormationGamble, hTrue]
  · simp [ObservationEncoder.conceptFormationGamble, hFalse]

omit [Fintype Gate] [Nonempty Gate] in
/-- Strict-width form of the endpoint canary.  At the de Finetti adapter
boundary, strict projective width for a formed-concept query supplies two
compatible finite-gate completions evaluating the same concept-formation
gamble as `1` and `0`. -/
theorem deFinettiGateSpec_strictWidth_has_endpoint_completions
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := PUnit) (Global := Gate) X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate))
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (hStrict :
      D.projectiveSpec.hasStrictGlobalWidth
        (ObservationEncoder.conceptFormationGamble S Γ σ A)) :
    ∃ P Q : PrecisePrevision Gate,
      P ∈ D.projectiveSpec.projectiveLimitCredalSet ∧
      Q ∈ D.projectiveSpec.projectiveLimitCredalSet ∧
      P (ObservationEncoder.conceptFormationGamble S Γ σ A) = 1 ∧
      Q (ObservationEncoder.conceptFormationGamble S Γ σ A) = 0 := by
  have hGap :
      A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
        A ∉ ObservationEncoder.lowerConceptFamily S Γ σ :=
    (deFinettiGateSpec_hasStrictGlobalWidth_conceptFormationGamble_iff_gap
      X μ D hSpec S Γ σ A).mp hStrict
  exact
    deFinettiGateSpec_gap_has_endpoint_completions
      X μ D hSpec S Γ σ A hGap

/-- Displayed PLN readout of a strict-width de Finetti adapter gap.  The
finite-gate/projective concept-formation ITV becomes the full semantic
interval, with width `1` and credibility `0`. -/
theorem conceptFormationWidthComplementITV_deFinettiStrictWidth_gapReadout
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := PUnit) (Global := Gate) X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate))
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (hStrict :
      D.projectiveSpec.hasStrictGlobalWidth
        (ObservationEncoder.conceptFormationGamble S Γ σ A)) :
    (conceptFormationWidthComplementITV S Γ σ A).lower = 0 ∧
      (conceptFormationWidthComplementITV S Γ σ A).upper = 1 ∧
      (conceptFormationWidthComplementITV S Γ σ A).width = 1 ∧
      (conceptFormationWidthComplementITV S Γ σ A).credibility = 0 ∧
      (conceptFormationWidthComplementITV S Γ σ A).strength = (1 / 2 : ℝ) := by
  have hGap :
      A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
        A ∉ ObservationEncoder.lowerConceptFamily S Γ σ :=
    (deFinettiGateSpec_hasStrictGlobalWidth_conceptFormationGamble_iff_gap
      X μ D hSpec S Γ σ A).mp hStrict
  exact conceptFormationWidthComplementITV_gap_readout S Γ σ A hGap

/-- Typed counterpart of
`conceptFormationWidthComplementITV_deFinettiStrictWidth_gapReadout`. -/
theorem conceptFormationTypedWidthComplementITV_deFinettiStrictWidth_gapReadout
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := PUnit) (Global := Gate) X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate))
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (hStrict :
      D.projectiveSpec.hasStrictGlobalWidth
        (ObservationEncoder.conceptFormationGamble S Γ σ A)) :
    (conceptFormationTypedWidthComplementITV S Γ σ A).lower = 0 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).upper = 1 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).width = 1 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 0 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint = (1 / 2 : ℝ) := by
  have hGap :
      A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
        A ∉ ObservationEncoder.lowerConceptFamily S Γ σ :=
    (deFinettiGateSpec_hasStrictGlobalWidth_conceptFormationGamble_iff_gap
      X μ D hSpec S Γ σ A).mp hStrict
  exact conceptFormationTypedWidthComplementITV_gap_readout S Γ σ A hGap

/-- At the glued de Finetti adapter boundary, strict projective width is
equivalent to the untyped PLN ITV showing the full concept-formation interval.
This rules out reading the `[0,1]` display as a mere presentation convention:
it is exactly the strict-width case for the glued finite-gate specification. -/
theorem conceptFormationWidthComplementITV_deFinettiStrictWidth_fullReadout_iff
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := PUnit) (Global := Gate) X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate))
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    ((conceptFormationWidthComplementITV S Γ σ A).lower = 0 ∧
      (conceptFormationWidthComplementITV S Γ σ A).upper = 1 ∧
      (conceptFormationWidthComplementITV S Γ σ A).width = 1 ∧
      (conceptFormationWidthComplementITV S Γ σ A).credibility = 0 ∧
      (conceptFormationWidthComplementITV S Γ σ A).strength = (1 / 2 : ℝ)) ↔
      D.projectiveSpec.hasStrictGlobalWidth
        (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  constructor
  · intro hReadout
    have hGap :
        A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
          A ∉ ObservationEncoder.lowerConceptFamily S Γ σ :=
      (conceptFormationWidthComplementITV_fullReadout_iff_gap S Γ σ A).mp
        hReadout
    exact
      (deFinettiGateSpec_hasStrictGlobalWidth_conceptFormationGamble_iff_gap
        X μ D hSpec S Γ σ A).mpr hGap
  · intro hStrict
    exact
      conceptFormationWidthComplementITV_deFinettiStrictWidth_gapReadout
        X μ D hSpec S Γ σ A hStrict

/-- Typed counterpart of
`conceptFormationWidthComplementITV_deFinettiStrictWidth_fullReadout_iff`. -/
theorem conceptFormationTypedWidthComplementITV_deFinettiStrictWidth_fullReadout_iff
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := PUnit) (Global := Gate) X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate))
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    ((conceptFormationTypedWidthComplementITV S Γ σ A).lower = 0 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).upper = 1 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).width = 1 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 0 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint = (1 / 2 : ℝ)) ↔
      D.projectiveSpec.hasStrictGlobalWidth
        (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  constructor
  · intro hReadout
    have hGap :
        A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
          A ∉ ObservationEncoder.lowerConceptFamily S Γ σ :=
      (conceptFormationTypedWidthComplementITV_fullReadout_iff_gap S Γ σ A).mp
        hReadout
    exact
      (deFinettiGateSpec_hasStrictGlobalWidth_conceptFormationGamble_iff_gap
        X μ D hSpec S Γ σ A).mpr hGap
  · intro hStrict
    exact
      conceptFormationTypedWidthComplementITV_deFinettiStrictWidth_gapReadout
        X μ D hSpec S Γ σ A hStrict

/-- At the glued de Finetti adapter boundary, positive displayed width (and
credibility below `1`) is equivalent to strict projective width for the
formed-concept query.  This is the compact nontriviality readout: it does not
need the full `[0,1]` display tuple to detect that the adapter is genuinely
credal rather than point-valued. -/
theorem conceptFormationWidthComplementITV_deFinettiStrictWidth_width_pos_iff
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := PUnit) (Global := Gate) X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate))
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (0 < (conceptFormationWidthComplementITV S Γ σ A).width ∧
      (conceptFormationWidthComplementITV S Γ σ A).credibility < 1) ↔
      D.projectiveSpec.hasStrictGlobalWidth
        (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  constructor
  · intro hDisplay
    have hGap :
        A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
          A ∉ ObservationEncoder.lowerConceptFamily S Γ σ :=
      (conceptFormationWidthComplementITV_width_pos_iff_gap S Γ σ A).mp
        hDisplay
    exact
      (deFinettiGateSpec_hasStrictGlobalWidth_conceptFormationGamble_iff_gap
        X μ D hSpec S Γ σ A).mpr hGap
  · intro hStrict
    have hGap :
        A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
          A ∉ ObservationEncoder.lowerConceptFamily S Γ σ :=
      (deFinettiGateSpec_hasStrictGlobalWidth_conceptFormationGamble_iff_gap
        X μ D hSpec S Γ σ A).mp hStrict
    exact
      (conceptFormationWidthComplementITV_width_pos_iff_gap S Γ σ A).mpr hGap

/-- Typed counterpart of
`conceptFormationWidthComplementITV_deFinettiStrictWidth_width_pos_iff`. -/
theorem conceptFormationTypedWidthComplementITV_deFinettiStrictWidth_width_pos_iff
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := PUnit) (Global := Gate) X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate))
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (0 < (conceptFormationTypedWidthComplementITV S Γ σ A).width ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).credibility < 1) ↔
      D.projectiveSpec.hasStrictGlobalWidth
        (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  constructor
  · intro hDisplay
    have hGap :
        A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
          A ∉ ObservationEncoder.lowerConceptFamily S Γ σ :=
      (conceptFormationTypedWidthComplementITV_width_pos_iff_gap S Γ σ A).mp
        hDisplay
    exact
      (deFinettiGateSpec_hasStrictGlobalWidth_conceptFormationGamble_iff_gap
        X μ D hSpec S Γ σ A).mpr hGap
  · intro hStrict
    have hGap :
        A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
          A ∉ ObservationEncoder.lowerConceptFamily S Γ σ :=
      (deFinettiGateSpec_hasStrictGlobalWidth_conceptFormationGamble_iff_gap
        X μ D hSpec S Γ σ A).mp hStrict
    exact
      (conceptFormationTypedWidthComplementITV_width_pos_iff_gap S Γ σ A).mpr hGap

/-! ### Finite-prefix de Finetti concept-formation readouts -/

/-- Source data for reading a concept-formation query through an imprecise
Bernoulli-mixture finite-prefix projective specification.

This is the process-family-facing specialization of the generic
`conceptFormationWidthComplementITVSourceOfSpec`; the gate type is the finite
Bool prefix `Fin n → Bool`. -/
noncomputable def conceptFormationDeFinettiPrefixWidthComplementITVSource
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    ProjectiveCredalWidthComplementITVSource PUnit (Fin n → Bool) :=
  conceptFormationWidthComplementITVSourceOfSpec
    (bernoulliMixturePrefixProjectiveSpec C n hLaw)
    (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion C n hLaw hC)
    S Γ σ A

/-- Untyped PLN ITV for a concept-formation query under an imprecise
Bernoulli-mixture finite-prefix projective specification. -/
noncomputable def conceptFormationDeFinettiPrefixWidthComplementITV
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) : ITV :=
  projectiveCredalWidthComplementITV
    (conceptFormationDeFinettiPrefixWidthComplementITVSource
      C n hLaw hC S Γ σ A)

/-- Typed PLN ITV for a concept-formation query under an imprecise
Bernoulli-mixture finite-prefix projective specification. -/
noncomputable def conceptFormationDeFinettiPrefixTypedWidthComplementITV
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    TypedITV (projectiveCredalWidthComplementITVSemantics PUnit (Fin n → Bool)) :=
  TypedITV.fromProjectiveCredalWidthComplement
    (conceptFormationDeFinettiPrefixWidthComplementITVSource
      C n hLaw hC S Γ σ A)

/-- A finite-prefix de Finetti concept-formation gamble is projectively
determined exactly when every admissible Bernoulli mixture gives the same
prevision to that formed-concept query. -/
theorem conceptFormationDeFinettiPrefixProjectiveSpec_determinesGlobalGamble_iff_mixtureAgreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (bernoulliMixturePrefixProjectiveSpec C n hLaw).determinesGlobalGamble
        (ObservationEncoder.conceptFormationGamble S Γ σ A) ↔
      ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
        ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
          (hLaw M hM).toPrecisePrevision
              (ObservationEncoder.conceptFormationGamble S Γ σ A) =
            (hLaw N hN).toPrecisePrevision
              (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
  bernoulliMixturePrefixProjectiveSpec_determinesGlobalGamble_iff_mixtureAgreement
    C n hLaw (ObservationEncoder.conceptFormationGamble S Γ σ A)

/-- The finite-prefix de Finetti concept-formation gamble has strict
projective width exactly when admissible Bernoulli mixtures do not all agree on
that formed-concept query. -/
theorem conceptFormationDeFinettiPrefixProjectiveSpec_hasStrictGlobalWidth_iff_not_mixtureAgreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (bernoulliMixturePrefixProjectiveSpec C n hLaw).hasStrictGlobalWidth
        (ObservationEncoder.conceptFormationGamble S Γ σ A) ↔
      ¬ ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
        ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
          (hLaw M hM).toPrecisePrevision
              (ObservationEncoder.conceptFormationGamble S Γ σ A) =
            (hLaw N hN).toPrecisePrevision
              (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
  bernoulliMixturePrefixProjectiveSpec_hasStrictGlobalWidth_iff_not_mixtureAgreement
    C n hLaw (ObservationEncoder.conceptFormationGamble S Γ σ A)

/-- If all admissible Bernoulli mixtures agree on the concept-formation
gamble, the finite-prefix de Finetti concept-formation ITV is exact. -/
theorem conceptFormationDeFinettiPrefixWidthComplementITV_exact_of_mixtureAgreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (hAgree : ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
      ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
        (hLaw M hM).toPrecisePrevision
            (ObservationEncoder.conceptFormationGamble S Γ σ A) =
          (hLaw N hN).toPrecisePrevision
            (ObservationEncoder.conceptFormationGamble S Γ σ A)) :
    (conceptFormationDeFinettiPrefixWidthComplementITV
        C n hLaw hC S Γ σ A).lower =
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n hLaw hC S Γ σ A).upper ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
        C n hLaw hC S Γ σ A).width = 0 ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
        C n hLaw hC S Γ σ A).credibility = 1 ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
        C n hLaw hC S Γ σ A).strength =
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n hLaw hC S Γ σ A).lower := by
  have hDet :
      (bernoulliMixturePrefixProjectiveSpec C n hLaw).determinesGlobalGamble
        (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
    bernoulliMixturePrefixProjectiveSpec_determinesGlobalGamble_of_mixtureAgreement
      C n hLaw (ObservationEncoder.conceptFormationGamble S Γ σ A) hAgree
  exact
    conceptFormationWidthComplementITVOfSpec_exact_of_determines
      (bernoulliMixturePrefixProjectiveSpec C n hLaw)
      (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion C n hLaw hC)
      S Γ σ A hDet

/-- Typed counterpart of
`conceptFormationDeFinettiPrefixWidthComplementITV_exact_of_mixtureAgreement`. -/
theorem conceptFormationDeFinettiPrefixTypedWidthComplementITV_exact_of_mixtureAgreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (hAgree : ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
      ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
        (hLaw M hM).toPrecisePrevision
            (ObservationEncoder.conceptFormationGamble S Γ σ A) =
          (hLaw N hN).toPrecisePrevision
            (ObservationEncoder.conceptFormationGamble S Γ σ A)) :
    (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n hLaw hC S Γ σ A).lower =
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n hLaw hC S Γ σ A).upper ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n hLaw hC S Γ σ A).width = 0 ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n hLaw hC S Γ σ A).credibility = 1 ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n hLaw hC S Γ σ A).midpoint =
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n hLaw hC S Γ σ A).lower := by
  have hDet :
      (bernoulliMixturePrefixProjectiveSpec C n hLaw).determinesGlobalGamble
        (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
    bernoulliMixturePrefixProjectiveSpec_determinesGlobalGamble_of_mixtureAgreement
      C n hLaw (ObservationEncoder.conceptFormationGamble S Γ σ A) hAgree
  exact
    conceptFormationTypedWidthComplementITVOfSpec_exact_of_determines
      (bernoulliMixturePrefixProjectiveSpec C n hLaw)
      (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion C n hLaw hC)
      S Γ σ A hDet

/-- Untyped exactness is equivalent to mixture agreement on the
concept-formation gamble.  The reverse direction uses strict projective width
as the canary: if mixtures disagree, the displayed width is positive, so the
ITV cannot be point-valued. -/
theorem conceptFormationDeFinettiPrefixWidthComplementITV_exact_iff_mixtureAgreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    ((conceptFormationDeFinettiPrefixWidthComplementITV
        C n hLaw hC S Γ σ A).lower =
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n hLaw hC S Γ σ A).upper ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
        C n hLaw hC S Γ σ A).width = 0 ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
        C n hLaw hC S Γ σ A).credibility = 1 ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
        C n hLaw hC S Γ σ A).strength =
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n hLaw hC S Γ σ A).lower) ↔
      ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
        ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
          (hLaw M hM).toPrecisePrevision
              (ObservationEncoder.conceptFormationGamble S Γ σ A) =
            (hLaw N hN).toPrecisePrevision
              (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  constructor
  · intro hExact
    rcases hExact with ⟨_, hWidth, _, _⟩
    by_contra hNotAgree
    have hNotDet :
        ¬ (bernoulliMixturePrefixProjectiveSpec C n hLaw).determinesGlobalGamble
            (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
      intro hDet
      exact hNotAgree
        ((conceptFormationDeFinettiPrefixProjectiveSpec_determinesGlobalGamble_iff_mixtureAgreement
          C n hLaw S Γ σ A).mp hDet)
    have hStrict :
        (bernoulliMixturePrefixProjectiveSpec C n hLaw).hasStrictGlobalWidth
          (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
      (ProjectiveLocalCredalSpec.hasStrictGlobalWidth_iff_not_determinesGlobalGamble
        (bernoulliMixturePrefixProjectiveSpec C n hLaw)
        (ObservationEncoder.conceptFormationGamble S Γ σ A)).mpr hNotDet
    have hPosOfSpec :
        0 < (conceptFormationWidthComplementITVOfSpec
          (bernoulliMixturePrefixProjectiveSpec C n hLaw)
          (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
            C n hLaw hC)
          S Γ σ A).width :=
      (conceptFormationWidthComplementITVOfSpec_width_pos_of_strictWidth
        (bernoulliMixturePrefixProjectiveSpec C n hLaw)
        (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
          C n hLaw hC)
        S Γ σ A hStrict).1
    have hWidthOfSpec :
        (conceptFormationWidthComplementITVOfSpec
          (bernoulliMixturePrefixProjectiveSpec C n hLaw)
          (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
            C n hLaw hC)
          S Γ σ A).width = 0 := by
      simpa [conceptFormationDeFinettiPrefixWidthComplementITV,
        conceptFormationDeFinettiPrefixWidthComplementITVSource,
        conceptFormationWidthComplementITVOfSpec] using hWidth
    have hImpossible : (0 : ℝ) < 0 := by
      rw [hWidthOfSpec] at hPosOfSpec
      exact hPosOfSpec
    exact (lt_irrefl (0 : ℝ)) hImpossible
  · intro hAgree
    exact
      conceptFormationDeFinettiPrefixWidthComplementITV_exact_of_mixtureAgreement
        C n hLaw hC S Γ σ A hAgree

/-- Typed exactness is equivalent to mixture agreement on the
concept-formation gamble. -/
theorem conceptFormationDeFinettiPrefixTypedWidthComplementITV_exact_iff_mixtureAgreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    ((conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n hLaw hC S Γ σ A).lower =
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n hLaw hC S Γ σ A).upper ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n hLaw hC S Γ σ A).width = 0 ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n hLaw hC S Γ σ A).credibility = 1 ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n hLaw hC S Γ σ A).midpoint =
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n hLaw hC S Γ σ A).lower) ↔
      ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
        ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
          (hLaw M hM).toPrecisePrevision
              (ObservationEncoder.conceptFormationGamble S Γ σ A) =
            (hLaw N hN).toPrecisePrevision
              (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  constructor
  · intro hExact
    rcases hExact with ⟨_, hWidth, _, _⟩
    by_contra hNotAgree
    have hNotDet :
        ¬ (bernoulliMixturePrefixProjectiveSpec C n hLaw).determinesGlobalGamble
            (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
      intro hDet
      exact hNotAgree
        ((conceptFormationDeFinettiPrefixProjectiveSpec_determinesGlobalGamble_iff_mixtureAgreement
          C n hLaw S Γ σ A).mp hDet)
    have hStrict :
        (bernoulliMixturePrefixProjectiveSpec C n hLaw).hasStrictGlobalWidth
          (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
      (ProjectiveLocalCredalSpec.hasStrictGlobalWidth_iff_not_determinesGlobalGamble
        (bernoulliMixturePrefixProjectiveSpec C n hLaw)
        (ObservationEncoder.conceptFormationGamble S Γ σ A)).mpr hNotDet
    have hPosOfSpec :
        0 < (conceptFormationTypedWidthComplementITVOfSpec
          (bernoulliMixturePrefixProjectiveSpec C n hLaw)
          (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
            C n hLaw hC)
          S Γ σ A).width :=
      (conceptFormationTypedWidthComplementITVOfSpec_width_pos_of_strictWidth
        (bernoulliMixturePrefixProjectiveSpec C n hLaw)
        (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
          C n hLaw hC)
        S Γ σ A hStrict).1
    have hWidthOfSpec :
        (conceptFormationTypedWidthComplementITVOfSpec
          (bernoulliMixturePrefixProjectiveSpec C n hLaw)
          (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
            C n hLaw hC)
          S Γ σ A).width = 0 := by
      simpa [conceptFormationDeFinettiPrefixTypedWidthComplementITV,
        conceptFormationDeFinettiPrefixWidthComplementITVSource,
        conceptFormationTypedWidthComplementITVOfSpec] using hWidth
    have hImpossible : (0 : ℝ) < 0 := by
      rw [hWidthOfSpec] at hPosOfSpec
      exact hPosOfSpec
    exact (lt_irrefl (0 : ℝ)) hImpossible
  · intro hAgree
    exact
      conceptFormationDeFinettiPrefixTypedWidthComplementITV_exact_of_mixtureAgreement
        C n hLaw hC S Γ σ A hAgree

/-- If two admissible Bernoulli mixtures disagree on the concept-formation
gamble, the finite-prefix de Finetti concept-formation ITV has positive width
and sub-maximal credibility. -/
theorem conceptFormationDeFinettiPrefixWidthComplementITV_width_pos_of_mixtureDisagreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C)
    (hlt :
      (hLaw M hM).toPrecisePrevision
          (ObservationEncoder.conceptFormationGamble S Γ σ A) <
        (hLaw N hN).toPrecisePrevision
          (ObservationEncoder.conceptFormationGamble S Γ σ A)) :
    0 < (conceptFormationDeFinettiPrefixWidthComplementITV
        C n hLaw hC S Γ σ A).width ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
        C n hLaw hC S Γ σ A).credibility < 1 := by
  have hStrict :
      (bernoulliMixturePrefixProjectiveSpec C n hLaw).hasStrictGlobalWidth
        (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
    bernoulliMixturePrefixProjectiveSpec_hasStrictGlobalWidth_of_mixtureDisagreement
      C n hLaw (ObservationEncoder.conceptFormationGamble S Γ σ A) hM hN hlt
  exact
    conceptFormationWidthComplementITVOfSpec_width_pos_of_strictWidth
      (bernoulliMixturePrefixProjectiveSpec C n hLaw)
      (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion C n hLaw hC)
      S Γ σ A hStrict

/-- Typed counterpart of
`conceptFormationDeFinettiPrefixWidthComplementITV_width_pos_of_mixtureDisagreement`. -/
theorem conceptFormationDeFinettiPrefixTypedWidthComplementITV_width_pos_of_mixtureDisagreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C)
    (hlt :
      (hLaw M hM).toPrecisePrevision
          (ObservationEncoder.conceptFormationGamble S Γ σ A) <
        (hLaw N hN).toPrecisePrevision
          (ObservationEncoder.conceptFormationGamble S Γ σ A)) :
    0 < (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n hLaw hC S Γ σ A).width ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n hLaw hC S Γ σ A).credibility < 1 := by
  have hStrict :
      (bernoulliMixturePrefixProjectiveSpec C n hLaw).hasStrictGlobalWidth
        (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
    bernoulliMixturePrefixProjectiveSpec_hasStrictGlobalWidth_of_mixtureDisagreement
      C n hLaw (ObservationEncoder.conceptFormationGamble S Γ σ A) hM hN hlt
  exact
    conceptFormationTypedWidthComplementITVOfSpec_width_pos_of_strictWidth
      (bernoulliMixturePrefixProjectiveSpec C n hLaw)
      (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion C n hLaw hC)
      S Γ σ A hStrict

/-- The untyped finite-prefix de Finetti concept-formation ITV has positive
displayed width (and credibility below `1`) exactly when admissible mixtures do
not all agree on the concept-formation gamble. -/
theorem conceptFormationDeFinettiPrefixWidthComplementITV_width_pos_iff_not_mixtureAgreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (0 < (conceptFormationDeFinettiPrefixWidthComplementITV
        C n hLaw hC S Γ σ A).width ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
        C n hLaw hC S Γ σ A).credibility < 1) ↔
      ¬ ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
        ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
          (hLaw M hM).toPrecisePrevision
              (ObservationEncoder.conceptFormationGamble S Γ σ A) =
            (hLaw N hN).toPrecisePrevision
              (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  constructor
  · intro hDisplay hAgree
    rcases hDisplay with ⟨hWidthPos, _⟩
    have hExact :=
      conceptFormationDeFinettiPrefixWidthComplementITV_exact_of_mixtureAgreement
        C n hLaw hC S Γ σ A hAgree
    have hWidth0 :
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n hLaw hC S Γ σ A).width = 0 :=
      hExact.2.1
    have hImpossible : (0 : ℝ) < 0 := by
      rw [hWidth0] at hWidthPos
      exact hWidthPos
    exact (lt_irrefl (0 : ℝ)) hImpossible
  · intro hNotAgree
    have hStrict :
        (bernoulliMixturePrefixProjectiveSpec C n hLaw).hasStrictGlobalWidth
          (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
      (conceptFormationDeFinettiPrefixProjectiveSpec_hasStrictGlobalWidth_iff_not_mixtureAgreement
        C n hLaw S Γ σ A).mpr hNotAgree
    exact
      conceptFormationWidthComplementITVOfSpec_width_pos_of_strictWidth
        (bernoulliMixturePrefixProjectiveSpec C n hLaw)
        (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
          C n hLaw hC)
        S Γ σ A hStrict

/-- Typed counterpart of
`conceptFormationDeFinettiPrefixWidthComplementITV_width_pos_iff_not_mixtureAgreement`. -/
theorem conceptFormationDeFinettiPrefixTypedWidthComplementITV_width_pos_iff_not_mixtureAgreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (0 < (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n hLaw hC S Γ σ A).width ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n hLaw hC S Γ σ A).credibility < 1) ↔
      ¬ ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
        ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
          (hLaw M hM).toPrecisePrevision
              (ObservationEncoder.conceptFormationGamble S Γ σ A) =
            (hLaw N hN).toPrecisePrevision
              (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  constructor
  · intro hDisplay hAgree
    rcases hDisplay with ⟨hWidthPos, _⟩
    have hExact :=
      conceptFormationDeFinettiPrefixTypedWidthComplementITV_exact_of_mixtureAgreement
        C n hLaw hC S Γ σ A hAgree
    have hWidth0 :
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n hLaw hC S Γ σ A).width = 0 :=
      hExact.2.1
    have hImpossible : (0 : ℝ) < 0 := by
      rw [hWidth0] at hWidthPos
      exact hWidthPos
    exact (lt_irrefl (0 : ℝ)) hImpossible
  · intro hNotAgree
    have hStrict :
        (bernoulliMixturePrefixProjectiveSpec C n hLaw).hasStrictGlobalWidth
          (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
      (conceptFormationDeFinettiPrefixProjectiveSpec_hasStrictGlobalWidth_iff_not_mixtureAgreement
        C n hLaw S Γ σ A).mpr hNotAgree
    exact
      conceptFormationTypedWidthComplementITVOfSpec_width_pos_of_strictWidth
        (bernoulliMixturePrefixProjectiveSpec C n hLaw)
        (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
          C n hLaw hC)
        S Γ σ A hStrict

/-! ### Canonical external process-law readouts -/

/-- Canonical external-process reading of the finite-prefix de Finetti
concept-formation ITV.  The displayed PLN interval coordinates are exactly the
finite-cylinder lower/upper/width/width-complement/midpoint envelopes of the
canonical external `Bool^ℕ` process-law family generated by the same Bernoulli
mixture credal set. -/
theorem conceptFormationDeFinettiPrefixWidthComplementITV_canonicalExternalProcessLaw_readout
    (C : Set BernoulliMixture) (n : ℕ) (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (conceptFormationDeFinettiPrefixWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).lower =
        externalPathLawPrefixLowerEnvelope
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).upper =
        externalPathLawPrefixUpperEnvelope
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).width =
        externalPathLawPrefixEnvelopeWidth
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).credibility =
        externalPathLawPrefixEnvelopeWidthComplement
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).strength =
        externalPathLawPrefixEnvelopeMidpoint
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n
          (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  let Y := ObservationEncoder.conceptFormationGamble S Γ σ A
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc
      (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).lower =
          impreciseDeFinettiPrefixLowerEnvelope C n
            (fun M _ => bernoulliMixturePrefixLaw_analytic M n) Y := by
            simp [conceptFormationDeFinettiPrefixWidthComplementITV,
              conceptFormationDeFinettiPrefixWidthComplementITVSource,
              conceptFormationWidthComplementITVSourceOfSpec,
              ProjectiveCredalWidthComplementITVSource.finite, Y]
      _ = externalPathLawPrefixLowerEnvelope
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n Y := by
            exact
              (bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixLowerEnvelope_eq_impreciseDeFinetti
                C hC n Y).symm
  · calc
      (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).upper =
          impreciseDeFinettiPrefixUpperEnvelope C n
            (fun M _ => bernoulliMixturePrefixLaw_analytic M n) Y := by
            simp [conceptFormationDeFinettiPrefixWidthComplementITV,
              conceptFormationDeFinettiPrefixWidthComplementITVSource,
              conceptFormationWidthComplementITVSourceOfSpec,
              ProjectiveCredalWidthComplementITVSource.finite,
              impreciseDeFinettiPrefixUpperEnvelope, Y]
      _ = externalPathLawPrefixUpperEnvelope
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n Y := by
            exact
              (bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixUpperEnvelope_eq_impreciseDeFinetti
                C hC n Y).symm
  · calc
      (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).width =
          impreciseDeFinettiPrefixEnvelopeWidth C n
            (fun M _ => bernoulliMixturePrefixLaw_analytic M n) Y := by
            simp [conceptFormationDeFinettiPrefixWidthComplementITV,
              conceptFormationDeFinettiPrefixWidthComplementITVSource,
              conceptFormationWidthComplementITVSourceOfSpec,
              ProjectiveCredalWidthComplementITVSource.finite, Y]
      _ = externalPathLawPrefixEnvelopeWidth
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n Y := by
            unfold impreciseDeFinettiPrefixEnvelopeWidth
              externalPathLawPrefixEnvelopeWidth
            rw [
              ← bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixCredalSet_eq_impreciseDeFinetti
                C n]
  · calc
      (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).credibility =
          impreciseDeFinettiPrefixEnvelopeWidthComplement C n
            (fun M _ => bernoulliMixturePrefixLaw_analytic M n) Y := by
            simp [conceptFormationDeFinettiPrefixWidthComplementITV,
              conceptFormationDeFinettiPrefixWidthComplementITVSource,
              conceptFormationWidthComplementITVSourceOfSpec,
              ProjectiveCredalWidthComplementITVSource.finite, Y]
      _ = externalPathLawPrefixEnvelopeWidthComplement
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n Y := by
            exact
              (bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixWidthComplement_eq_impreciseDeFinetti
                C hC n Y).symm
  · calc
      (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).strength =
          impreciseDeFinettiPrefixEnvelopeMidpoint C n
            (fun M _ => bernoulliMixturePrefixLaw_analytic M n) Y := by
            simp [conceptFormationDeFinettiPrefixWidthComplementITV,
              conceptFormationDeFinettiPrefixWidthComplementITVSource,
              conceptFormationWidthComplementITVSourceOfSpec,
              ProjectiveCredalWidthComplementITVSource.finite, Y]
      _ = externalPathLawPrefixEnvelopeMidpoint
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n Y := by
            exact
              (bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixMidpoint_eq_impreciseDeFinetti
                C hC n Y).symm

/-- Typed counterpart of
`conceptFormationDeFinettiPrefixWidthComplementITV_canonicalExternalProcessLaw_readout`. -/
theorem conceptFormationDeFinettiPrefixTypedWidthComplementITV_canonicalExternalProcessLaw_readout
    (C : Set BernoulliMixture) (n : ℕ) (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).lower =
        externalPathLawPrefixLowerEnvelope
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).upper =
        externalPathLawPrefixUpperEnvelope
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).width =
        externalPathLawPrefixEnvelopeWidth
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).credibility =
        externalPathLawPrefixEnvelopeWidthComplement
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).midpoint =
        externalPathLawPrefixEnvelopeMidpoint
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n
          (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  let Y := ObservationEncoder.conceptFormationGamble S Γ σ A
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).lower =
          impreciseDeFinettiPrefixLowerEnvelope C n
            (fun M _ => bernoulliMixturePrefixLaw_analytic M n) Y := by
            simp [conceptFormationDeFinettiPrefixTypedWidthComplementITV,
              conceptFormationDeFinettiPrefixWidthComplementITVSource,
              conceptFormationWidthComplementITVSourceOfSpec,
              ProjectiveCredalWidthComplementITVSource.finite, Y]
      _ = externalPathLawPrefixLowerEnvelope
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n Y := by
            exact
              (bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixLowerEnvelope_eq_impreciseDeFinetti
                C hC n Y).symm
  · calc
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).upper =
          impreciseDeFinettiPrefixUpperEnvelope C n
            (fun M _ => bernoulliMixturePrefixLaw_analytic M n) Y := by
            simp [conceptFormationDeFinettiPrefixTypedWidthComplementITV,
              conceptFormationDeFinettiPrefixWidthComplementITVSource,
              conceptFormationWidthComplementITVSourceOfSpec,
              ProjectiveCredalWidthComplementITVSource.finite,
              impreciseDeFinettiPrefixUpperEnvelope, Y]
      _ = externalPathLawPrefixUpperEnvelope
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n Y := by
            exact
              (bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixUpperEnvelope_eq_impreciseDeFinetti
                C hC n Y).symm
  · calc
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).width =
          impreciseDeFinettiPrefixEnvelopeWidth C n
            (fun M _ => bernoulliMixturePrefixLaw_analytic M n) Y := by
            simp [conceptFormationDeFinettiPrefixTypedWidthComplementITV,
              conceptFormationDeFinettiPrefixWidthComplementITVSource,
              conceptFormationWidthComplementITVSourceOfSpec,
              ProjectiveCredalWidthComplementITVSource.finite, Y]
      _ = externalPathLawPrefixEnvelopeWidth
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n Y := by
            unfold impreciseDeFinettiPrefixEnvelopeWidth
              externalPathLawPrefixEnvelopeWidth
            rw [
              ← bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixCredalSet_eq_impreciseDeFinetti
                C n]
  · calc
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).credibility =
          impreciseDeFinettiPrefixEnvelopeWidthComplement C n
            (fun M _ => bernoulliMixturePrefixLaw_analytic M n) Y := by
            simp [conceptFormationDeFinettiPrefixTypedWidthComplementITV,
              conceptFormationDeFinettiPrefixWidthComplementITVSource,
              conceptFormationWidthComplementITVSourceOfSpec,
              ProjectiveCredalWidthComplementITVSource.finite, Y]
      _ = externalPathLawPrefixEnvelopeWidthComplement
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n Y := by
            exact
              (bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixWidthComplement_eq_impreciseDeFinetti
                C hC n Y).symm
  · calc
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).midpoint =
          impreciseDeFinettiPrefixEnvelopeMidpoint C n
            (fun M _ => bernoulliMixturePrefixLaw_analytic M n) Y := by
            simp [conceptFormationDeFinettiPrefixTypedWidthComplementITV,
              conceptFormationDeFinettiPrefixWidthComplementITVSource,
              conceptFormationWidthComplementITVSourceOfSpec,
              ProjectiveCredalWidthComplementITVSource.finite, Y]
      _ = externalPathLawPrefixEnvelopeMidpoint
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n Y := by
            exact
              (bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixMidpoint_eq_impreciseDeFinetti
                C hC n Y).symm

/-- Agreement of all canonical external `Bool^ℕ` process laws on the
formed-concept finite cylinder is exactly agreement of the generating
Bernoulli mixtures on the same concept-formation gamble.  This is the
process-law version of the mixture-agreement criterion, not a new semantics. -/
theorem conceptFormationDeFinettiPrefix_canonicalExternalProcessAgreement_iff_mixtureAgreement
    (C : Set BernoulliMixture) (n : ℕ)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (∀ E : ExternalBoolProcessLaw (ℕ → Bool),
        ∀ _hE : E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
        ∀ F : ExternalBoolProcessLaw (ℕ → Bool),
        ∀ _hF : F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
          E.prefixPrevision n
              (ObservationEncoder.conceptFormationGamble S Γ σ A) =
            F.prefixPrevision n
              (ObservationEncoder.conceptFormationGamble S Γ σ A)) ↔
      ∀ M : BernoulliMixture, ∀ _hM : M ∈ C,
        ∀ N : BernoulliMixture, ∀ _hN : N ∈ C,
          (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision
              (ObservationEncoder.conceptFormationGamble S Γ σ A) =
            (bernoulliMixturePrefixLaw_analytic N n).toPrecisePrevision
              (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  let Y := ObservationEncoder.conceptFormationGamble S Γ σ A
  constructor
  · intro hProcess M hM N hN
    have hAgree :
        (bernoulliMixtureCanonicalExternalBoolProcessLaw M).prefixPrevision n Y =
          (bernoulliMixtureCanonicalExternalBoolProcessLaw N).prefixPrevision n Y :=
      hProcess
        (bernoulliMixtureCanonicalExternalBoolProcessLaw M) ⟨M, hM, rfl⟩
        (bernoulliMixtureCanonicalExternalBoolProcessLaw N) ⟨N, hN, rfl⟩
    calc
      (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision Y =
          (bernoulliMixtureCanonicalExternalBoolProcessLaw M).prefixPrevision n Y := by
            symm
            exact bernoulliMixtureCanonicalExternalProcessRealization M n Y
      _ = (bernoulliMixtureCanonicalExternalBoolProcessLaw N).prefixPrevision n Y :=
            hAgree
      _ = (bernoulliMixturePrefixLaw_analytic N n).toPrecisePrevision Y := by
            exact bernoulliMixtureCanonicalExternalProcessRealization N n Y
  · intro hMixture E hE F hF
    rcases hE with ⟨M, hM, rfl⟩
    rcases hF with ⟨N, hN, rfl⟩
    calc
      (bernoulliMixtureCanonicalExternalBoolProcessLaw M).prefixPrevision n Y =
          (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision Y := by
            exact bernoulliMixtureCanonicalExternalProcessRealization M n Y
      _ = (bernoulliMixturePrefixLaw_analytic N n).toPrecisePrevision Y :=
            hMixture M hM N hN
      _ = (bernoulliMixtureCanonicalExternalBoolProcessLaw N).prefixPrevision n Y := by
            symm
            exact bernoulliMixtureCanonicalExternalProcessRealization N n Y

/-- A strict analytic mixture disagreement gives an explicit pair of
canonical external `Bool^ℕ` process laws that disagree on the formed-concept
finite cylinder.  This is the constructive positive canary behind the
agreement criterion: the process-law witness is not inferred from a display
interval; it is built from the two disagreeing Bernoulli mixtures. -/
theorem conceptFormationDeFinettiPrefix_canonicalExternalProcessDisagreement_of_mixtureDisagreement
    (C : Set BernoulliMixture) (n : ℕ)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C)
    (hlt :
      (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision
          (ObservationEncoder.conceptFormationGamble S Γ σ A) <
        (bernoulliMixturePrefixLaw_analytic N n).toPrecisePrevision
          (ObservationEncoder.conceptFormationGamble S Γ σ A)) :
    ∃ E : ExternalBoolProcessLaw (ℕ → Bool),
      E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
        ∃ F : ExternalBoolProcessLaw (ℕ → Bool),
          F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
            E.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A) <
              F.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  let Y := ObservationEncoder.conceptFormationGamble S Γ σ A
  refine
    ⟨bernoulliMixtureCanonicalExternalBoolProcessLaw M, ⟨M, hM, rfl⟩,
      bernoulliMixtureCanonicalExternalBoolProcessLaw N, ⟨N, hN, rfl⟩, ?_⟩
  calc
    (bernoulliMixtureCanonicalExternalBoolProcessLaw M).prefixPrevision n Y =
        (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision Y := by
          exact bernoulliMixtureCanonicalExternalProcessRealization M n Y
    _ < (bernoulliMixturePrefixLaw_analytic N n).toPrecisePrevision Y := hlt
    _ = (bernoulliMixtureCanonicalExternalBoolProcessLaw N).prefixPrevision n Y := by
          symm
          exact bernoulliMixtureCanonicalExternalProcessRealization N n Y

/-- Canonical external process-law disagreement has a positive witness exactly
when the process-law family does not agree on the formed-concept finite
cylinder.  This turns the negated agreement boundary into an explicit strict
pair of process laws, with the order oriented toward the smaller prevision. -/
theorem conceptFormationDeFinettiPrefix_existsCanonicalExternalProcessDisagreement_iff_not_agreement
    (C : Set BernoulliMixture) (n : ℕ)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (∃ E : ExternalBoolProcessLaw (ℕ → Bool),
      E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
        ∃ F : ExternalBoolProcessLaw (ℕ → Bool),
          F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
            E.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A) <
              F.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A)) ↔
      ¬ ∀ E : ExternalBoolProcessLaw (ℕ → Bool),
        ∀ _hE : E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
        ∀ F : ExternalBoolProcessLaw (ℕ → Bool),
        ∀ _hF : F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
          E.prefixPrevision n
              (ObservationEncoder.conceptFormationGamble S Γ σ A) =
            F.prefixPrevision n
              (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  let Y := ObservationEncoder.conceptFormationGamble S Γ σ A
  constructor
  · rintro ⟨E, hE, F, hF, hlt⟩ hAgree
    have hEq : E.prefixPrevision n Y = F.prefixPrevision n Y :=
      hAgree E hE F hF
    rw [hEq] at hlt
    exact (lt_irrefl _) hlt
  · intro hNotAgree
    by_contra hNoStrict
    apply hNotAgree
    intro E hE F hF
    by_contra hNe
    rcases lt_or_gt_of_ne hNe with hlt | hgt
    · exact hNoStrict ⟨E, hE, F, hF, hlt⟩
    · exact hNoStrict ⟨F, hF, E, hE, hgt⟩

/-- If two canonical external process laws in the generated family strictly
disagree on the formed-concept finite cylinder, the displayed untyped PLN
finite-prefix ITV has positive width and sub-maximal credibility. -/
theorem conceptFormationDeFinettiPrefixWidthComplementITV_width_pos_of_canonicalExternalProcessDisagreement
    (C : Set BernoulliMixture) (n : ℕ) (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (hDisagree :
      ∃ E : ExternalBoolProcessLaw (ℕ → Bool),
        E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
          ∃ F : ExternalBoolProcessLaw (ℕ → Bool),
            F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
              E.prefixPrevision n
                  (ObservationEncoder.conceptFormationGamble S Γ σ A) <
                F.prefixPrevision n
                  (ObservationEncoder.conceptFormationGamble S Γ σ A)) :
    0 < (conceptFormationDeFinettiPrefixWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).width ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).credibility < 1 := by
  rw [conceptFormationDeFinettiPrefixWidthComplementITV_width_pos_iff_not_mixtureAgreement]
  intro hMixtureAgree
  have hAgree :
      ∀ E : ExternalBoolProcessLaw (ℕ → Bool),
        ∀ _hE : E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
        ∀ F : ExternalBoolProcessLaw (ℕ → Bool),
        ∀ _hF : F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
          E.prefixPrevision n
              (ObservationEncoder.conceptFormationGamble S Γ σ A) =
            F.prefixPrevision n
              (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
    (conceptFormationDeFinettiPrefix_canonicalExternalProcessAgreement_iff_mixtureAgreement
      C n S Γ σ A).mpr hMixtureAgree
  rcases hDisagree with ⟨E, hE, F, hF, hlt⟩
  have hEq :
      E.prefixPrevision n
          (ObservationEncoder.conceptFormationGamble S Γ σ A) =
        F.prefixPrevision n
          (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
    hAgree E hE F hF
  rw [hEq] at hlt
  exact (lt_irrefl _) hlt

/-- The displayed untyped PLN finite-prefix ITV has positive width exactly
when the canonical external process-law family contains a strict disagreement
on the formed-concept finite cylinder.  This is the positive-witness version
of the non-agreement criterion. -/
theorem conceptFormationDeFinettiPrefixWidthComplementITV_width_pos_iff_existsCanonicalExternalProcessDisagreement
    (C : Set BernoulliMixture) (n : ℕ) (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (0 < (conceptFormationDeFinettiPrefixWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).width ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).credibility < 1) ↔
      ∃ E : ExternalBoolProcessLaw (ℕ → Bool),
        E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
          ∃ F : ExternalBoolProcessLaw (ℕ → Bool),
            F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
              E.prefixPrevision n
                  (ObservationEncoder.conceptFormationGamble S Γ σ A) <
                F.prefixPrevision n
                  (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  exact
    ((conceptFormationDeFinettiPrefixWidthComplementITV_width_pos_iff_not_mixtureAgreement
      C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n) hC S Γ σ A).trans
      (not_congr
        (conceptFormationDeFinettiPrefix_canonicalExternalProcessAgreement_iff_mixtureAgreement
          C n S Γ σ A)).symm).trans
      (conceptFormationDeFinettiPrefix_existsCanonicalExternalProcessDisagreement_iff_not_agreement
        C n S Γ σ A).symm

/-- Typed counterpart of
`conceptFormationDeFinettiPrefixWidthComplementITV_width_pos_of_canonicalExternalProcessDisagreement`. -/
theorem conceptFormationDeFinettiPrefixTypedWidthComplementITV_width_pos_of_canonicalExternalProcessDisagreement
    (C : Set BernoulliMixture) (n : ℕ) (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (hDisagree :
      ∃ E : ExternalBoolProcessLaw (ℕ → Bool),
        E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
          ∃ F : ExternalBoolProcessLaw (ℕ → Bool),
            F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
              E.prefixPrevision n
                  (ObservationEncoder.conceptFormationGamble S Γ σ A) <
                F.prefixPrevision n
                  (ObservationEncoder.conceptFormationGamble S Γ σ A)) :
    0 < (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).width ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).credibility < 1 := by
  rw [conceptFormationDeFinettiPrefixTypedWidthComplementITV_width_pos_iff_not_mixtureAgreement]
  intro hMixtureAgree
  have hAgree :
      ∀ E : ExternalBoolProcessLaw (ℕ → Bool),
        ∀ _hE : E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
        ∀ F : ExternalBoolProcessLaw (ℕ → Bool),
        ∀ _hF : F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
          E.prefixPrevision n
              (ObservationEncoder.conceptFormationGamble S Γ σ A) =
            F.prefixPrevision n
              (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
    (conceptFormationDeFinettiPrefix_canonicalExternalProcessAgreement_iff_mixtureAgreement
      C n S Γ σ A).mpr hMixtureAgree
  rcases hDisagree with ⟨E, hE, F, hF, hlt⟩
  have hEq :
      E.prefixPrevision n
          (ObservationEncoder.conceptFormationGamble S Γ σ A) =
        F.prefixPrevision n
          (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
    hAgree E hE F hF
  rw [hEq] at hlt
  exact (lt_irrefl _) hlt

/-- Typed counterpart of
`conceptFormationDeFinettiPrefixWidthComplementITV_width_pos_iff_existsCanonicalExternalProcessDisagreement`. -/
theorem conceptFormationDeFinettiPrefixTypedWidthComplementITV_width_pos_iff_existsCanonicalExternalProcessDisagreement
    (C : Set BernoulliMixture) (n : ℕ) (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (0 < (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).width ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).credibility < 1) ↔
      ∃ E : ExternalBoolProcessLaw (ℕ → Bool),
        E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
          ∃ F : ExternalBoolProcessLaw (ℕ → Bool),
            F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
              E.prefixPrevision n
                  (ObservationEncoder.conceptFormationGamble S Γ σ A) <
                F.prefixPrevision n
                  (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  exact
    ((conceptFormationDeFinettiPrefixTypedWidthComplementITV_width_pos_iff_not_mixtureAgreement
      C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n) hC S Γ σ A).trans
      (not_congr
        (conceptFormationDeFinettiPrefix_canonicalExternalProcessAgreement_iff_mixtureAgreement
          C n S Γ σ A)).symm).trans
      (conceptFormationDeFinettiPrefix_existsCanonicalExternalProcessDisagreement_iff_not_agreement
        C n S Γ σ A).symm

/-- The analytic finite-prefix de Finetti concept-formation query is
projectively determined exactly when all canonical external process laws agree
on the corresponding formed-concept finite cylinder. -/
theorem conceptFormationDeFinettiPrefixProjectiveSpec_determinesGlobalGamble_iff_canonicalExternalProcessAgreement
    (C : Set BernoulliMixture) (n : ℕ)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (bernoulliMixturePrefixProjectiveSpec C n
        (fun M _ => bernoulliMixturePrefixLaw_analytic M n)).determinesGlobalGamble
        (ObservationEncoder.conceptFormationGamble S Γ σ A) ↔
      ∀ E : ExternalBoolProcessLaw (ℕ → Bool),
        ∀ _hE : E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
        ∀ F : ExternalBoolProcessLaw (ℕ → Bool),
        ∀ _hF : F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
          E.prefixPrevision n
              (ObservationEncoder.conceptFormationGamble S Γ σ A) =
            F.prefixPrevision n
              (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  rw [conceptFormationDeFinettiPrefixProjectiveSpec_determinesGlobalGamble_iff_mixtureAgreement]
  exact
    (conceptFormationDeFinettiPrefix_canonicalExternalProcessAgreement_iff_mixtureAgreement
      C n S Γ σ A).symm

/-- The analytic finite-prefix de Finetti concept-formation query is
projectively determined exactly when there is no strict disagreement between
canonical external process laws on the formed-concept finite cylinder.  This is
the exactness side of the explicit process-law boundary. -/
theorem conceptFormationDeFinettiPrefixProjectiveSpec_determinesGlobalGamble_iff_noCanonicalExternalProcessDisagreement
    (C : Set BernoulliMixture) (n : ℕ)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (bernoulliMixturePrefixProjectiveSpec C n
        (fun M _ => bernoulliMixturePrefixLaw_analytic M n)).determinesGlobalGamble
        (ObservationEncoder.conceptFormationGamble S Γ σ A) ↔
      ¬ ∃ E : ExternalBoolProcessLaw (ℕ → Bool),
        E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
          ∃ F : ExternalBoolProcessLaw (ℕ → Bool),
            F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
              E.prefixPrevision n
                  (ObservationEncoder.conceptFormationGamble S Γ σ A) <
                F.prefixPrevision n
                  (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  constructor
  · intro hDet hDisagree
    have hAgree :
        ∀ E : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hE : E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
          ∀ F : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hF : F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
            E.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A) =
              F.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
      (conceptFormationDeFinettiPrefixProjectiveSpec_determinesGlobalGamble_iff_canonicalExternalProcessAgreement
        C n S Γ σ A).mp hDet
    have hNotAgree :
        ¬ ∀ E : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hE : E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
          ∀ F : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hF : F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
            E.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A) =
              F.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
      (conceptFormationDeFinettiPrefix_existsCanonicalExternalProcessDisagreement_iff_not_agreement
        C n S Γ σ A).mp hDisagree
    exact hNotAgree hAgree
  · intro hNoDisagree
    apply
      (conceptFormationDeFinettiPrefixProjectiveSpec_determinesGlobalGamble_iff_canonicalExternalProcessAgreement
        C n S Γ σ A).mpr
    by_contra hNotAgree
    exact hNoDisagree
      ((conceptFormationDeFinettiPrefix_existsCanonicalExternalProcessDisagreement_iff_not_agreement
        C n S Γ σ A).mpr hNotAgree)

/-- The displayed untyped finite-prefix de Finetti concept-formation ITV is
exact exactly when there is no strict disagreement between canonical external
process laws on the formed-concept finite cylinder. -/
theorem conceptFormationDeFinettiPrefixWidthComplementITV_exact_iff_noCanonicalExternalProcessDisagreement
    (C : Set BernoulliMixture) (n : ℕ) (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    ((conceptFormationDeFinettiPrefixWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).lower =
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).upper ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).width = 0 ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).credibility = 1 ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).strength =
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).lower) ↔
      ¬ ∃ E : ExternalBoolProcessLaw (ℕ → Bool),
        E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
          ∃ F : ExternalBoolProcessLaw (ℕ → Bool),
            F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
              E.prefixPrevision n
                  (ObservationEncoder.conceptFormationGamble S Γ σ A) <
                F.prefixPrevision n
                  (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  have hExactAgreement :
      ((conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).lower =
          (conceptFormationDeFinettiPrefixWidthComplementITV
            C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
            hC S Γ σ A).upper ∧
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).width = 0 ∧
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).credibility = 1 ∧
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).strength =
          (conceptFormationDeFinettiPrefixWidthComplementITV
            C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
            hC S Γ σ A).lower) ↔
        ∀ E : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hE : E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
          ∀ F : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hF : F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
            E.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A) =
              F.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
    (conceptFormationDeFinettiPrefixWidthComplementITV_exact_iff_mixtureAgreement
      C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n) hC S Γ σ A).trans
      (conceptFormationDeFinettiPrefix_canonicalExternalProcessAgreement_iff_mixtureAgreement
        C n S Γ σ A).symm
  constructor
  · intro hExact hDisagree
    have hNotAgree :
        ¬ ∀ E : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hE : E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
          ∀ F : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hF : F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
            E.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A) =
              F.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
      (conceptFormationDeFinettiPrefix_existsCanonicalExternalProcessDisagreement_iff_not_agreement
        C n S Γ σ A).mp hDisagree
    exact hNotAgree (hExactAgreement.mp hExact)
  · intro hNoDisagree
    apply hExactAgreement.mpr
    by_contra hNotAgree
    exact hNoDisagree
      ((conceptFormationDeFinettiPrefix_existsCanonicalExternalProcessDisagreement_iff_not_agreement
        C n S Γ σ A).mpr hNotAgree)

/-- Typed counterpart of
`conceptFormationDeFinettiPrefixWidthComplementITV_exact_iff_noCanonicalExternalProcessDisagreement`. -/
theorem conceptFormationDeFinettiPrefixTypedWidthComplementITV_exact_iff_noCanonicalExternalProcessDisagreement
    (C : Set BernoulliMixture) (n : ℕ) (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    ((conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).lower =
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).upper ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).width = 0 ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).credibility = 1 ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).midpoint =
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).lower) ↔
      ¬ ∃ E : ExternalBoolProcessLaw (ℕ → Bool),
        E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
          ∃ F : ExternalBoolProcessLaw (ℕ → Bool),
            F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
              E.prefixPrevision n
                  (ObservationEncoder.conceptFormationGamble S Γ σ A) <
                F.prefixPrevision n
                  (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  have hExactAgreement :
      ((conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).lower =
          (conceptFormationDeFinettiPrefixTypedWidthComplementITV
            C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
            hC S Γ σ A).upper ∧
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).width = 0 ∧
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).credibility = 1 ∧
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).midpoint =
          (conceptFormationDeFinettiPrefixTypedWidthComplementITV
            C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
            hC S Γ σ A).lower) ↔
        ∀ E : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hE : E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
          ∀ F : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hF : F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
            E.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A) =
              F.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
    (conceptFormationDeFinettiPrefixTypedWidthComplementITV_exact_iff_mixtureAgreement
      C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n) hC S Γ σ A).trans
      (conceptFormationDeFinettiPrefix_canonicalExternalProcessAgreement_iff_mixtureAgreement
        C n S Γ σ A).symm
  constructor
  · intro hExact hDisagree
    have hNotAgree :
        ¬ ∀ E : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hE : E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
          ∀ F : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hF : F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
            E.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A) =
              F.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
      (conceptFormationDeFinettiPrefix_existsCanonicalExternalProcessDisagreement_iff_not_agreement
        C n S Γ σ A).mp hDisagree
    exact hNotAgree (hExactAgreement.mp hExact)
  · intro hNoDisagree
    apply hExactAgreement.mpr
    by_contra hNotAgree
    exact hNoDisagree
      ((conceptFormationDeFinettiPrefix_existsCanonicalExternalProcessDisagreement_iff_not_agreement
        C n S Γ σ A).mpr hNotAgree)

/-- The analytic finite-prefix de Finetti concept-formation query has strict
projective width exactly when the canonical external process-law family does
not agree on that formed-concept finite cylinder. -/
theorem conceptFormationDeFinettiPrefixProjectiveSpec_hasStrictGlobalWidth_iff_not_canonicalExternalProcessAgreement
    (C : Set BernoulliMixture) (n : ℕ)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (bernoulliMixturePrefixProjectiveSpec C n
        (fun M _ => bernoulliMixturePrefixLaw_analytic M n)).hasStrictGlobalWidth
        (ObservationEncoder.conceptFormationGamble S Γ σ A) ↔
      ¬ ∀ E : ExternalBoolProcessLaw (ℕ → Bool),
        ∀ _hE : E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
        ∀ F : ExternalBoolProcessLaw (ℕ → Bool),
        ∀ _hF : F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
          E.prefixPrevision n
              (ObservationEncoder.conceptFormationGamble S Γ σ A) =
            F.prefixPrevision n
              (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  rw [conceptFormationDeFinettiPrefixProjectiveSpec_hasStrictGlobalWidth_iff_not_mixtureAgreement]
  exact
    not_congr
      (conceptFormationDeFinettiPrefix_canonicalExternalProcessAgreement_iff_mixtureAgreement
        C n S Γ σ A).symm

/-- The analytic finite-prefix de Finetti concept-formation query has strict
projective width exactly when the canonical external process-law family
contains an explicit strict disagreement on the formed-concept finite cylinder. -/
theorem conceptFormationDeFinettiPrefixProjectiveSpec_hasStrictGlobalWidth_iff_existsCanonicalExternalProcessDisagreement
    (C : Set BernoulliMixture) (n : ℕ)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (bernoulliMixturePrefixProjectiveSpec C n
        (fun M _ => bernoulliMixturePrefixLaw_analytic M n)).hasStrictGlobalWidth
        (ObservationEncoder.conceptFormationGamble S Γ σ A) ↔
      ∃ E : ExternalBoolProcessLaw (ℕ → Bool),
        E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
          ∃ F : ExternalBoolProcessLaw (ℕ → Bool),
            F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
              E.prefixPrevision n
                  (ObservationEncoder.conceptFormationGamble S Γ σ A) <
                F.prefixPrevision n
                  (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  exact
    (conceptFormationDeFinettiPrefixProjectiveSpec_hasStrictGlobalWidth_iff_not_canonicalExternalProcessAgreement
      C n S Γ σ A).trans
      (conceptFormationDeFinettiPrefix_existsCanonicalExternalProcessDisagreement_iff_not_agreement
        C n S Γ σ A).symm

/-- The displayed untyped PLN interval has positive width exactly when the
canonical external process-law family disagrees on the formed-concept finite
cylinder. -/
theorem conceptFormationDeFinettiPrefixWidthComplementITV_width_pos_iff_not_canonicalExternalProcessAgreement
    (C : Set BernoulliMixture) (n : ℕ) (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (0 < (conceptFormationDeFinettiPrefixWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).width ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).credibility < 1) ↔
      ¬ ∀ E : ExternalBoolProcessLaw (ℕ → Bool),
        ∀ _hE : E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
        ∀ F : ExternalBoolProcessLaw (ℕ → Bool),
        ∀ _hF : F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
          E.prefixPrevision n
              (ObservationEncoder.conceptFormationGamble S Γ σ A) =
            F.prefixPrevision n
              (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  rw [conceptFormationDeFinettiPrefixWidthComplementITV_width_pos_iff_not_mixtureAgreement]
  exact
    not_congr
      (conceptFormationDeFinettiPrefix_canonicalExternalProcessAgreement_iff_mixtureAgreement
        C n S Γ σ A).symm

/-- Typed counterpart of
`conceptFormationDeFinettiPrefixWidthComplementITV_width_pos_iff_not_canonicalExternalProcessAgreement`. -/
theorem conceptFormationDeFinettiPrefixTypedWidthComplementITV_width_pos_iff_not_canonicalExternalProcessAgreement
    (C : Set BernoulliMixture) (n : ℕ) (hC : C.Nonempty)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : (Fin n → Bool) → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (0 < (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).width ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
        C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
        hC S Γ σ A).credibility < 1) ↔
      ¬ ∀ E : ExternalBoolProcessLaw (ℕ → Bool),
        ∀ _hE : E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
        ∀ F : ExternalBoolProcessLaw (ℕ → Bool),
        ∀ _hF : F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
          E.prefixPrevision n
              (ObservationEncoder.conceptFormationGamble S Γ σ A) =
            F.prefixPrevision n
              (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  rw [conceptFormationDeFinettiPrefixTypedWidthComplementITV_width_pos_iff_not_mixtureAgreement]
  exact
    not_congr
      (conceptFormationDeFinettiPrefix_canonicalExternalProcessAgreement_iff_mixtureAgreement
        C n S Γ σ A).symm

/-- If a de Finetti specialization has been explicitly glued to the same
finite gate projective specification used by credal concept formation, then a
representing Bernoulli mixture supplies the compatible precise completion used
by the untyped PLN ITV readout.

The hypothesis `hSpec` is the boundary marker: without an actual adapter from
mixtures to gate completions, no de Finetti claim is being made about formed
concepts. -/
theorem conceptFormationWidthComplementITV_deFinettiMixtureReadout_of_determines
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := PUnit) (Global := Gate) X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate))
    (M : BernoulliMixture) (hRep : Represents M X μ)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (hDet :
      (gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (ObservationEncoder.conceptFormationGamble S Γ σ A)) :
    (conceptFormationWidthComplementITV S Γ σ A).lower =
        (D.completionOfMixture M)
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationWidthComplementITV S Γ σ A).upper =
        (D.completionOfMixture M)
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationWidthComplementITV S Γ σ A).width = 0 ∧
      (conceptFormationWidthComplementITV S Γ σ A).credibility = 1 ∧
      (conceptFormationWidthComplementITV S Γ σ A).strength =
        (D.completionOfMixture M)
          (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  have hP :
      D.completionOfMixture M ∈
        (gateCredalProjectiveSpec (Gate := Gate)).projectiveLimitCredalSet := by
    simpa [hSpec] using D.mixtureCompatible M hRep
  exact
    conceptFormationWidthComplementITV_preciseCompletionReadout_of_determines
      S Γ σ A (D.completionOfMixture M) hP hDet

/-- A concept-family no-gap hypothesis is the user-facing criterion for the
untyped de Finetti mixture readout: no lower/upper gap implies the finite
concept-formation ITV collapses to the mixture-induced compatible precise
completion. -/
theorem conceptFormationWidthComplementITV_deFinettiMixtureReadout_of_noGap
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := PUnit) (Global := Gate) X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate))
    (M : BernoulliMixture) (hRep : Represents M X μ)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (hNoGap :
      ¬ (A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
          A ∉ ObservationEncoder.lowerConceptFamily S Γ σ)) :
    (conceptFormationWidthComplementITV S Γ σ A).lower =
        (D.completionOfMixture M)
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationWidthComplementITV S Γ σ A).upper =
        (D.completionOfMixture M)
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationWidthComplementITV S Γ σ A).width = 0 ∧
      (conceptFormationWidthComplementITV S Γ σ A).credibility = 1 ∧
      (conceptFormationWidthComplementITV S Γ σ A).strength =
        (D.completionOfMixture M)
          (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  have hDet :
      (gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
    (ObservationEncoder.gateCredalProjectiveSpec_determinesGlobalGamble_conceptFormationGamble_iff
      S Γ σ A).mpr hNoGap
  exact
    conceptFormationWidthComplementITV_deFinettiMixtureReadout_of_determines
      X μ D hSpec M hRep S Γ σ A hDet

/-- The untyped de Finetti mixture readout is exact exactly in the no-gap case.
The forward direction uses the displayed ITV width as the canary: if a
permissive-but-not-robust concept gap remains, the finite gate envelope has
nonzero width, so the point-valued mixture readout cannot be the whole truth. -/
theorem conceptFormationWidthComplementITV_deFinettiMixtureExactReadout_iff_noGap
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := PUnit) (Global := Gate) X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate))
    (M : BernoulliMixture) (hRep : Represents M X μ)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    ((conceptFormationWidthComplementITV S Γ σ A).lower =
        (D.completionOfMixture M)
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationWidthComplementITV S Γ σ A).upper =
        (D.completionOfMixture M)
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationWidthComplementITV S Γ σ A).width = 0 ∧
      (conceptFormationWidthComplementITV S Γ σ A).credibility = 1 ∧
      (conceptFormationWidthComplementITV S Γ σ A).strength =
        (D.completionOfMixture M)
          (ObservationEncoder.conceptFormationGamble S Γ σ A)) ↔
      ¬ (A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
          A ∉ ObservationEncoder.lowerConceptFamily S Γ σ) := by
  constructor
  · intro hReadout
    rcases hReadout with ⟨hLower, hUpper, hWidth, hCred, hStrength⟩
    have hExact :
        (conceptFormationWidthComplementITV S Γ σ A).lower =
            (conceptFormationWidthComplementITV S Γ σ A).upper ∧
          (conceptFormationWidthComplementITV S Γ σ A).width = 0 ∧
          (conceptFormationWidthComplementITV S Γ σ A).credibility = 1 ∧
          (conceptFormationWidthComplementITV S Γ σ A).strength =
            (conceptFormationWidthComplementITV S Γ σ A).lower :=
      ⟨hLower.trans hUpper.symm, hWidth, hCred, hStrength.trans hLower.symm⟩
    exact (conceptFormationWidthComplementITV_exact_iff_noGap S Γ σ A).mp hExact
  · intro hNoGap
    exact
      conceptFormationWidthComplementITV_deFinettiMixtureReadout_of_noGap
        X μ D hSpec M hRep S Γ σ A hNoGap

/-- Typed counterpart of
`conceptFormationWidthComplementITV_deFinettiMixtureReadout_of_determines`.
The displayed typed endpoints and midpoint read exactly the mixture-induced
compatible precise-completion value once the de Finetti specialization has been
glued to the finite gate projective specification. -/
theorem conceptFormationTypedWidthComplementITV_deFinettiMixtureReadout_of_determines
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := PUnit) (Global := Gate) X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate))
    (M : BernoulliMixture) (hRep : Represents M X μ)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (hDet :
      (gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (ObservationEncoder.conceptFormationGamble S Γ σ A)) :
    (conceptFormationTypedWidthComplementITV S Γ σ A).lower =
        (D.completionOfMixture M)
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).upper =
        (D.completionOfMixture M)
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).width = 0 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 1 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint =
        (D.completionOfMixture M)
          (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  have hP :
      D.completionOfMixture M ∈
        (gateCredalProjectiveSpec (Gate := Gate)).projectiveLimitCredalSet := by
    simpa [hSpec] using D.mixtureCompatible M hRep
  exact
    conceptFormationTypedWidthComplementITV_preciseCompletionReadout_of_determines
      S Γ σ A (D.completionOfMixture M) hP hDet

/-- Typed counterpart of
`conceptFormationWidthComplementITV_deFinettiMixtureReadout_of_noGap`. -/
theorem conceptFormationTypedWidthComplementITV_deFinettiMixtureReadout_of_noGap
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := PUnit) (Global := Gate) X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate))
    (M : BernoulliMixture) (hRep : Represents M X μ)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (hNoGap :
      ¬ (A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
          A ∉ ObservationEncoder.lowerConceptFamily S Γ σ)) :
    (conceptFormationTypedWidthComplementITV S Γ σ A).lower =
        (D.completionOfMixture M)
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).upper =
        (D.completionOfMixture M)
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).width = 0 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 1 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint =
        (D.completionOfMixture M)
          (ObservationEncoder.conceptFormationGamble S Γ σ A) := by
  have hDet :
      (gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (ObservationEncoder.conceptFormationGamble S Γ σ A) :=
    (ObservationEncoder.gateCredalProjectiveSpec_determinesGlobalGamble_conceptFormationGamble_iff
      S Γ σ A).mpr hNoGap
  exact
    conceptFormationTypedWidthComplementITV_deFinettiMixtureReadout_of_determines
      X μ D hSpec M hRep S Γ σ A hDet

/-- Typed counterpart of
`conceptFormationWidthComplementITV_deFinettiMixtureExactReadout_iff_noGap`. -/
theorem conceptFormationTypedWidthComplementITV_deFinettiMixtureExactReadout_iff_noGap
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := PUnit) (Global := Gate) X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate))
    (M : BernoulliMixture) (hRep : Represents M X μ)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    ((conceptFormationTypedWidthComplementITV S Γ σ A).lower =
        (D.completionOfMixture M)
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).upper =
        (D.completionOfMixture M)
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).width = 0 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 1 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint =
        (D.completionOfMixture M)
          (ObservationEncoder.conceptFormationGamble S Γ σ A)) ↔
      ¬ (A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
          A ∉ ObservationEncoder.lowerConceptFamily S Γ σ) := by
  constructor
  · intro hReadout
    rcases hReadout with ⟨hLower, hUpper, hWidth, hCred, hMidpoint⟩
    have hExact :
        (conceptFormationTypedWidthComplementITV S Γ σ A).lower =
            (conceptFormationTypedWidthComplementITV S Γ σ A).upper ∧
          (conceptFormationTypedWidthComplementITV S Γ σ A).width = 0 ∧
          (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 1 ∧
          (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint =
            (conceptFormationTypedWidthComplementITV S Γ σ A).lower :=
      ⟨hLower.trans hUpper.symm, hWidth, hCred, hMidpoint.trans hLower.symm⟩
    exact (conceptFormationTypedWidthComplementITV_exact_iff_noGap S Γ σ A).mp hExact
  · intro hNoGap
    exact
      conceptFormationTypedWidthComplementITV_deFinettiMixtureReadout_of_noGap
        X μ D hSpec M hRep S Γ σ A hNoGap

/-- Positive/negative boundary theorem for the glued de Finetti readout.
Either the lower/upper concept-family gap is absent and the mixture-induced
readout is exact, or the gap is present and the displayed ITV is the full
uncertainty interval. -/
theorem conceptFormationWidthComplementITV_deFinettiMixtureBoundary_dichotomy
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := PUnit) (Global := Gate) X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate))
    (M : BernoulliMixture) (hRep : Represents M X μ)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (¬ (A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
          A ∉ ObservationEncoder.lowerConceptFamily S Γ σ) ∧
      (conceptFormationWidthComplementITV S Γ σ A).lower =
          (D.completionOfMixture M)
            (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
        (conceptFormationWidthComplementITV S Γ σ A).upper =
          (D.completionOfMixture M)
            (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
        (conceptFormationWidthComplementITV S Γ σ A).width = 0 ∧
        (conceptFormationWidthComplementITV S Γ σ A).credibility = 1 ∧
        (conceptFormationWidthComplementITV S Γ σ A).strength =
          (D.completionOfMixture M)
            (ObservationEncoder.conceptFormationGamble S Γ σ A)) ∨
      ((A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
          A ∉ ObservationEncoder.lowerConceptFamily S Γ σ) ∧
        (conceptFormationWidthComplementITV S Γ σ A).lower = 0 ∧
          (conceptFormationWidthComplementITV S Γ σ A).upper = 1 ∧
          (conceptFormationWidthComplementITV S Γ σ A).width = 1 ∧
          (conceptFormationWidthComplementITV S Γ σ A).credibility = 0 ∧
          (conceptFormationWidthComplementITV S Γ σ A).strength = (1 / 2 : ℝ)) := by
  by_cases hGap :
      A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
        A ∉ ObservationEncoder.lowerConceptFamily S Γ σ
  · right
    exact ⟨hGap, conceptFormationWidthComplementITV_gap_readout S Γ σ A hGap⟩
  · left
    exact
      ⟨hGap,
        conceptFormationWidthComplementITV_deFinettiMixtureReadout_of_noGap
          X μ D hSpec M hRep S Γ σ A hGap⟩

/-- Typed counterpart of
`conceptFormationWidthComplementITV_deFinettiMixtureBoundary_dichotomy`. -/
theorem conceptFormationTypedWidthComplementITV_deFinettiMixtureBoundary_dichotomy
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := PUnit) (Global := Gate) X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate))
    (M : BernoulliMixture) (hRep : Represents M X μ)
    (S : ObservationEncoder Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (¬ (A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
          A ∉ ObservationEncoder.lowerConceptFamily S Γ σ) ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).lower =
          (D.completionOfMixture M)
            (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).upper =
          (D.completionOfMixture M)
            (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).width = 0 ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 1 ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint =
          (D.completionOfMixture M)
            (ObservationEncoder.conceptFormationGamble S Γ σ A)) ∨
      ((A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
          A ∉ ObservationEncoder.lowerConceptFamily S Γ σ) ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).lower = 0 ∧
          (conceptFormationTypedWidthComplementITV S Γ σ A).upper = 1 ∧
          (conceptFormationTypedWidthComplementITV S Γ σ A).width = 1 ∧
          (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 0 ∧
          (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint = (1 / 2 : ℝ)) := by
  by_cases hGap :
      A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
        A ∉ ObservationEncoder.lowerConceptFamily S Γ σ
  · right
    exact ⟨hGap,
      conceptFormationTypedWidthComplementITV_gap_readout S Γ σ A hGap⟩
  · left
    exact
      ⟨hGap,
        conceptFormationTypedWidthComplementITV_deFinettiMixtureReadout_of_noGap
          X μ D hSpec M hRep S Γ σ A hGap⟩

end Adapter

/-! ## Proof-carrying profile -/

/-- Compact profile for the finite-prefix de Finetti handoff into credal
concept formation.  The agreement fields expose the exact/width-zero case; the
disagreement fields expose the honest positive-width case. -/
structure ConceptFormationDeFinettiPrefixBridgeProfile where
  determinesIffMixtureAgreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) →
      (hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (bernoulliMixturePrefixProjectiveSpec C n hLaw).determinesGlobalGamble
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ↔
        ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
          ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
            (hLaw M hM).toPrecisePrevision
                (ObservationEncoder.conceptFormationGamble S Γ σ A) =
              (hLaw N hN).toPrecisePrevision
                (ObservationEncoder.conceptFormationGamble S Γ σ A)
  strictWidthIffNotMixtureAgreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) →
      (hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (bernoulliMixturePrefixProjectiveSpec C n hLaw).hasStrictGlobalWidth
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ↔
        ¬ ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
          ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
            (hLaw M hM).toPrecisePrevision
                (ObservationEncoder.conceptFormationGamble S Γ σ A) =
              (hLaw N hN).toPrecisePrevision
                (ObservationEncoder.conceptFormationGamble S Γ σ A)
  untypedExactIffMixtureAgreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) →
      (hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n) →
      (hC : C.Nonempty) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      ((conceptFormationDeFinettiPrefixWidthComplementITV
          C n hLaw hC S Γ σ A).lower =
          (conceptFormationDeFinettiPrefixWidthComplementITV
            C n hLaw hC S Γ σ A).upper ∧
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n hLaw hC S Γ σ A).width = 0 ∧
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n hLaw hC S Γ σ A).credibility = 1 ∧
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n hLaw hC S Γ σ A).strength =
          (conceptFormationDeFinettiPrefixWidthComplementITV
            C n hLaw hC S Γ σ A).lower) ↔
        ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
          ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
            (hLaw M hM).toPrecisePrevision
                (ObservationEncoder.conceptFormationGamble S Γ σ A) =
              (hLaw N hN).toPrecisePrevision
                (ObservationEncoder.conceptFormationGamble S Γ σ A)
  typedExactIffMixtureAgreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) →
      (hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n) →
      (hC : C.Nonempty) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      ((conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n hLaw hC S Γ σ A).lower =
          (conceptFormationDeFinettiPrefixTypedWidthComplementITV
            C n hLaw hC S Γ σ A).upper ∧
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n hLaw hC S Γ σ A).width = 0 ∧
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n hLaw hC S Γ σ A).credibility = 1 ∧
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n hLaw hC S Γ σ A).midpoint =
          (conceptFormationDeFinettiPrefixTypedWidthComplementITV
            C n hLaw hC S Γ σ A).lower) ↔
        ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
          ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
            (hLaw M hM).toPrecisePrevision
                (ObservationEncoder.conceptFormationGamble S Γ σ A) =
              (hLaw N hN).toPrecisePrevision
                (ObservationEncoder.conceptFormationGamble S Γ σ A)
  untypedExactIffNoCanonicalExternalProcessDisagreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) → (hC : C.Nonempty) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      ((conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).lower =
          (conceptFormationDeFinettiPrefixWidthComplementITV
            C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
            hC S Γ σ A).upper ∧
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).width = 0 ∧
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).credibility = 1 ∧
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).strength =
          (conceptFormationDeFinettiPrefixWidthComplementITV
            C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
            hC S Γ σ A).lower) ↔
        ¬ ∃ E : ExternalBoolProcessLaw (ℕ → Bool),
          E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
            ∃ F : ExternalBoolProcessLaw (ℕ → Bool),
              F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
                E.prefixPrevision n
                    (ObservationEncoder.conceptFormationGamble S Γ σ A) <
                  F.prefixPrevision n
                    (ObservationEncoder.conceptFormationGamble S Γ σ A)
  typedExactIffNoCanonicalExternalProcessDisagreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) → (hC : C.Nonempty) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      ((conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).lower =
          (conceptFormationDeFinettiPrefixTypedWidthComplementITV
            C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
            hC S Γ σ A).upper ∧
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).width = 0 ∧
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).credibility = 1 ∧
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).midpoint =
          (conceptFormationDeFinettiPrefixTypedWidthComplementITV
            C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
            hC S Γ σ A).lower) ↔
        ¬ ∃ E : ExternalBoolProcessLaw (ℕ → Bool),
          E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
            ∃ F : ExternalBoolProcessLaw (ℕ → Bool),
              F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
                E.prefixPrevision n
                    (ObservationEncoder.conceptFormationGamble S Γ σ A) <
                  F.prefixPrevision n
                    (ObservationEncoder.conceptFormationGamble S Γ σ A)
  untypedWidthPosIffNotMixtureAgreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) →
      (hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n) →
      (hC : C.Nonempty) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (0 < (conceptFormationDeFinettiPrefixWidthComplementITV
          C n hLaw hC S Γ σ A).width ∧
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n hLaw hC S Γ σ A).credibility < 1) ↔
        ¬ ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
          ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
            (hLaw M hM).toPrecisePrevision
                (ObservationEncoder.conceptFormationGamble S Γ σ A) =
              (hLaw N hN).toPrecisePrevision
                (ObservationEncoder.conceptFormationGamble S Γ σ A)
  typedWidthPosIffNotMixtureAgreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) →
      (hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n) →
      (hC : C.Nonempty) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (0 < (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n hLaw hC S Γ σ A).width ∧
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n hLaw hC S Γ σ A).credibility < 1) ↔
        ¬ ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
          ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
            (hLaw M hM).toPrecisePrevision
                (ObservationEncoder.conceptFormationGamble S Γ σ A) =
              (hLaw N hN).toPrecisePrevision
                (ObservationEncoder.conceptFormationGamble S Γ σ A)
  untypedCanonicalExternalProcessReadout :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) → (hC : C.Nonempty) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).lower =
          externalPathLawPrefixLowerEnvelope
            (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n
            (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).upper =
          externalPathLawPrefixUpperEnvelope
            (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n
            (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).width =
          externalPathLawPrefixEnvelopeWidth
            (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n
            (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).credibility =
          externalPathLawPrefixEnvelopeWidthComplement
            (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n
            (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).strength =
          externalPathLawPrefixEnvelopeMidpoint
            (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n
            (ObservationEncoder.conceptFormationGamble S Γ σ A)
  typedCanonicalExternalProcessReadout :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) → (hC : C.Nonempty) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).lower =
          externalPathLawPrefixLowerEnvelope
            (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n
            (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).upper =
          externalPathLawPrefixUpperEnvelope
            (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n
            (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).width =
          externalPathLawPrefixEnvelopeWidth
            (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n
            (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).credibility =
          externalPathLawPrefixEnvelopeWidthComplement
            (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n
            (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).midpoint =
          externalPathLawPrefixEnvelopeMidpoint
            (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n
            (ObservationEncoder.conceptFormationGamble S Γ σ A)
  canonicalExternalProcessAgreementIffMixtureAgreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (∀ E : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hE : E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
          ∀ F : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hF : F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
            E.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A) =
              F.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A)) ↔
        ∀ M : BernoulliMixture, ∀ _hM : M ∈ C,
          ∀ N : BernoulliMixture, ∀ _hN : N ∈ C,
            (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision
                (ObservationEncoder.conceptFormationGamble S Γ σ A) =
              (bernoulliMixturePrefixLaw_analytic N n).toPrecisePrevision
                (ObservationEncoder.conceptFormationGamble S Γ σ A)
  determinesIffCanonicalExternalProcessAgreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (bernoulliMixturePrefixProjectiveSpec C n
          (fun M _ => bernoulliMixturePrefixLaw_analytic M n)).determinesGlobalGamble
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ↔
        ∀ E : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hE : E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
          ∀ F : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hF : F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
            E.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A) =
              F.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A)
  determinesIffNoCanonicalExternalProcessDisagreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (bernoulliMixturePrefixProjectiveSpec C n
          (fun M _ => bernoulliMixturePrefixLaw_analytic M n)).determinesGlobalGamble
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ↔
        ¬ ∃ E : ExternalBoolProcessLaw (ℕ → Bool),
          E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
            ∃ F : ExternalBoolProcessLaw (ℕ → Bool),
              F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
                E.prefixPrevision n
                    (ObservationEncoder.conceptFormationGamble S Γ σ A) <
                  F.prefixPrevision n
                    (ObservationEncoder.conceptFormationGamble S Γ σ A)
  untypedWidthPosIffNotCanonicalExternalProcessAgreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) → (hC : C.Nonempty) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (0 < (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).width ∧
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).credibility < 1) ↔
        ¬ ∀ E : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hE : E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
          ∀ F : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hF : F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
            E.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A) =
              F.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A)
  typedWidthPosIffNotCanonicalExternalProcessAgreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) → (hC : C.Nonempty) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (0 < (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).width ∧
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).credibility < 1) ↔
        ¬ ∀ E : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hE : E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
          ∀ F : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hF : F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
            E.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A) =
              F.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A)
  strictGlobalWidthIffExistsCanonicalExternalProcessDisagreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (bernoulliMixturePrefixProjectiveSpec C n
          (fun M _ => bernoulliMixturePrefixLaw_analytic M n)).hasStrictGlobalWidth
          (ObservationEncoder.conceptFormationGamble S Γ σ A) ↔
        ∃ E : ExternalBoolProcessLaw (ℕ → Bool),
          E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
            ∃ F : ExternalBoolProcessLaw (ℕ → Bool),
              F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
                E.prefixPrevision n
                    (ObservationEncoder.conceptFormationGamble S Γ σ A) <
                  F.prefixPrevision n
                    (ObservationEncoder.conceptFormationGamble S Γ σ A)
  canonicalExternalProcessDisagreementIffNotAgreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (∃ E : ExternalBoolProcessLaw (ℕ → Bool),
        E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
          ∃ F : ExternalBoolProcessLaw (ℕ → Bool),
            F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
              E.prefixPrevision n
                  (ObservationEncoder.conceptFormationGamble S Γ σ A) <
                F.prefixPrevision n
                  (ObservationEncoder.conceptFormationGamble S Γ σ A)) ↔
        ¬ ∀ E : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hE : E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
          ∀ F : ExternalBoolProcessLaw (ℕ → Bool),
          ∀ _hF : F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C,
            E.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A) =
              F.prefixPrevision n
                (ObservationEncoder.conceptFormationGamble S Γ σ A)
  canonicalExternalProcessDisagreementOfMixtureDisagreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      {M N : BernoulliMixture} → (hM : M ∈ C) → (hN : N ∈ C) →
      (hlt :
        (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision
            (ObservationEncoder.conceptFormationGamble S Γ σ A) <
          (bernoulliMixturePrefixLaw_analytic N n).toPrecisePrevision
            (ObservationEncoder.conceptFormationGamble S Γ σ A)) →
      ∃ E : ExternalBoolProcessLaw (ℕ → Bool),
        E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
          ∃ F : ExternalBoolProcessLaw (ℕ → Bool),
            F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
              E.prefixPrevision n
                  (ObservationEncoder.conceptFormationGamble S Γ σ A) <
                F.prefixPrevision n
                  (ObservationEncoder.conceptFormationGamble S Γ σ A)
  untypedWidthPosOfCanonicalExternalProcessDisagreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) → (hC : C.Nonempty) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (hDisagree :
        ∃ E : ExternalBoolProcessLaw (ℕ → Bool),
          E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
            ∃ F : ExternalBoolProcessLaw (ℕ → Bool),
              F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
                E.prefixPrevision n
                    (ObservationEncoder.conceptFormationGamble S Γ σ A) <
                  F.prefixPrevision n
                    (ObservationEncoder.conceptFormationGamble S Γ σ A)) →
      0 < (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).width ∧
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).credibility < 1
  untypedWidthPosIffExistsCanonicalExternalProcessDisagreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) → (hC : C.Nonempty) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (0 < (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).width ∧
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).credibility < 1) ↔
        ∃ E : ExternalBoolProcessLaw (ℕ → Bool),
          E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
            ∃ F : ExternalBoolProcessLaw (ℕ → Bool),
              F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
                E.prefixPrevision n
                    (ObservationEncoder.conceptFormationGamble S Γ σ A) <
                  F.prefixPrevision n
                    (ObservationEncoder.conceptFormationGamble S Γ σ A)
  typedWidthPosOfCanonicalExternalProcessDisagreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) → (hC : C.Nonempty) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (hDisagree :
        ∃ E : ExternalBoolProcessLaw (ℕ → Bool),
          E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
            ∃ F : ExternalBoolProcessLaw (ℕ → Bool),
              F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
                E.prefixPrevision n
                    (ObservationEncoder.conceptFormationGamble S Γ σ A) <
                  F.prefixPrevision n
                    (ObservationEncoder.conceptFormationGamble S Γ σ A)) →
      0 < (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).width ∧
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).credibility < 1
  typedWidthPosIffExistsCanonicalExternalProcessDisagreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) → (hC : C.Nonempty) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (0 < (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).width ∧
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
          hC S Γ σ A).credibility < 1) ↔
        ∃ E : ExternalBoolProcessLaw (ℕ → Bool),
          E ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
            ∃ F : ExternalBoolProcessLaw (ℕ → Bool),
              F ∈ bernoulliMixtureCanonicalExternalBoolProcessLawSet C ∧
                E.prefixPrevision n
                    (ObservationEncoder.conceptFormationGamble S Γ σ A) <
                  F.prefixPrevision n
                    (ObservationEncoder.conceptFormationGamble S Γ σ A)
  untypedExactOfMixtureAgreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) →
      (hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n) →
      (hC : C.Nonempty) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (hAgree : ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
        ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
          (hLaw M hM).toPrecisePrevision
              (ObservationEncoder.conceptFormationGamble S Γ σ A) =
            (hLaw N hN).toPrecisePrevision
              (ObservationEncoder.conceptFormationGamble S Γ σ A)) →
      (conceptFormationDeFinettiPrefixWidthComplementITV
          C n hLaw hC S Γ σ A).lower =
          (conceptFormationDeFinettiPrefixWidthComplementITV
            C n hLaw hC S Γ σ A).upper ∧
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n hLaw hC S Γ σ A).width = 0 ∧
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n hLaw hC S Γ σ A).credibility = 1 ∧
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n hLaw hC S Γ σ A).strength =
          (conceptFormationDeFinettiPrefixWidthComplementITV
            C n hLaw hC S Γ σ A).lower
  typedExactOfMixtureAgreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) →
      (hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n) →
      (hC : C.Nonempty) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (hAgree : ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
        ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
          (hLaw M hM).toPrecisePrevision
              (ObservationEncoder.conceptFormationGamble S Γ σ A) =
            (hLaw N hN).toPrecisePrevision
              (ObservationEncoder.conceptFormationGamble S Γ σ A)) →
      (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n hLaw hC S Γ σ A).lower =
          (conceptFormationDeFinettiPrefixTypedWidthComplementITV
            C n hLaw hC S Γ σ A).upper ∧
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n hLaw hC S Γ σ A).width = 0 ∧
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n hLaw hC S Γ σ A).credibility = 1 ∧
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n hLaw hC S Γ σ A).midpoint =
          (conceptFormationDeFinettiPrefixTypedWidthComplementITV
            C n hLaw hC S Γ σ A).lower
  untypedWidthPosOfMixtureDisagreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) →
      (hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n) →
      (hC : C.Nonempty) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      {M N : BernoulliMixture} → (hM : M ∈ C) → (hN : N ∈ C) →
      (hlt :
        (hLaw M hM).toPrecisePrevision
            (ObservationEncoder.conceptFormationGamble S Γ σ A) <
          (hLaw N hN).toPrecisePrevision
            (ObservationEncoder.conceptFormationGamble S Γ σ A)) →
      0 < (conceptFormationDeFinettiPrefixWidthComplementITV
          C n hLaw hC S Γ σ A).width ∧
        (conceptFormationDeFinettiPrefixWidthComplementITV
          C n hLaw hC S Γ σ A).credibility < 1
  typedWidthPosOfMixtureDisagreement :
    ∀ {Obs Obj Attr Q : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Obj] [Fintype Attr],
      (C : Set BernoulliMixture) → (n : ℕ) →
      (hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n) →
      (hC : C.Nonempty) →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : (Fin n → Bool) → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      {M N : BernoulliMixture} → (hM : M ∈ C) → (hN : N ∈ C) →
      (hlt :
        (hLaw M hM).toPrecisePrevision
            (ObservationEncoder.conceptFormationGamble S Γ σ A) <
          (hLaw N hN).toPrecisePrevision
          (ObservationEncoder.conceptFormationGamble S Γ σ A)) →
      0 < (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n hLaw hC S Γ σ A).width ∧
        (conceptFormationDeFinettiPrefixTypedWidthComplementITV
          C n hLaw hC S Γ σ A).credibility < 1
  untypedGluedMixtureExactReadoutIffNoGap :
    ∀ {Ω Obs Obj Attr Q Gate : Type} [MeasurableSpace Ω]
      [AddCommMonoid Q] [Preorder Q] [Fintype Gate] [Nonempty Gate]
      [Fintype Obj] [Fintype Attr],
      (X : ℕ → Ω → Bool) → (μ : Measure Ω) →
      (D : DeFinettiProjectiveCredalSpecialization
        (Window := PUnit) (Global := Gate) X μ) →
      (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate)) →
      (M : BernoulliMixture) → Represents M X μ →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : Gate → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      ((conceptFormationWidthComplementITV S Γ σ A).lower =
          (D.completionOfMixture M)
            (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
        (conceptFormationWidthComplementITV S Γ σ A).upper =
          (D.completionOfMixture M)
            (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
        (conceptFormationWidthComplementITV S Γ σ A).width = 0 ∧
        (conceptFormationWidthComplementITV S Γ σ A).credibility = 1 ∧
        (conceptFormationWidthComplementITV S Γ σ A).strength =
          (D.completionOfMixture M)
            (ObservationEncoder.conceptFormationGamble S Γ σ A)) ↔
        ¬ (A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
            A ∉ ObservationEncoder.lowerConceptFamily S Γ σ)
  typedGluedMixtureExactReadoutIffNoGap :
    ∀ {Ω Obs Obj Attr Q Gate : Type} [MeasurableSpace Ω]
      [AddCommMonoid Q] [Preorder Q] [Fintype Gate] [Nonempty Gate]
      [Fintype Obj] [Fintype Attr],
      (X : ℕ → Ω → Bool) → (μ : Measure Ω) →
      (D : DeFinettiProjectiveCredalSpecialization
        (Window := PUnit) (Global := Gate) X μ) →
      (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate)) →
      (M : BernoulliMixture) → Represents M X μ →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : Gate → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      ((conceptFormationTypedWidthComplementITV S Γ σ A).lower =
          (D.completionOfMixture M)
            (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).upper =
          (D.completionOfMixture M)
            (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).width = 0 ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 1 ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint =
          (D.completionOfMixture M)
            (ObservationEncoder.conceptFormationGamble S Γ σ A)) ↔
        ¬ (A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
            A ∉ ObservationEncoder.lowerConceptFamily S Γ σ)
  untypedGluedMixtureBoundaryDichotomy :
    ∀ {Ω Obs Obj Attr Q Gate : Type} [MeasurableSpace Ω]
      [AddCommMonoid Q] [Preorder Q] [Fintype Gate] [Nonempty Gate]
      [Fintype Obj] [Fintype Attr],
      (X : ℕ → Ω → Bool) → (μ : Measure Ω) →
      (D : DeFinettiProjectiveCredalSpecialization
        (Window := PUnit) (Global := Gate) X μ) →
      (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate)) →
      (M : BernoulliMixture) → Represents M X μ →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : Gate → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (¬ (A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
            A ∉ ObservationEncoder.lowerConceptFamily S Γ σ) ∧
        (conceptFormationWidthComplementITV S Γ σ A).lower =
            (D.completionOfMixture M)
              (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
          (conceptFormationWidthComplementITV S Γ σ A).upper =
            (D.completionOfMixture M)
              (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
          (conceptFormationWidthComplementITV S Γ σ A).width = 0 ∧
          (conceptFormationWidthComplementITV S Γ σ A).credibility = 1 ∧
          (conceptFormationWidthComplementITV S Γ σ A).strength =
            (D.completionOfMixture M)
              (ObservationEncoder.conceptFormationGamble S Γ σ A)) ∨
        ((A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
            A ∉ ObservationEncoder.lowerConceptFamily S Γ σ) ∧
          (conceptFormationWidthComplementITV S Γ σ A).lower = 0 ∧
            (conceptFormationWidthComplementITV S Γ σ A).upper = 1 ∧
            (conceptFormationWidthComplementITV S Γ σ A).width = 1 ∧
            (conceptFormationWidthComplementITV S Γ σ A).credibility = 0 ∧
            (conceptFormationWidthComplementITV S Γ σ A).strength = (1 / 2 : ℝ))
  typedGluedMixtureBoundaryDichotomy :
    ∀ {Ω Obs Obj Attr Q Gate : Type} [MeasurableSpace Ω]
      [AddCommMonoid Q] [Preorder Q] [Fintype Gate] [Nonempty Gate]
      [Fintype Obj] [Fintype Attr],
      (X : ℕ → Ω → Bool) → (μ : Measure Ω) →
      (D : DeFinettiProjectiveCredalSpecialization
        (Window := PUnit) (Global := Gate) X μ) →
      (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Gate)) →
      (M : BernoulliMixture) → Represents M X μ →
      (S : ObservationEncoder Obs Obj Attr Q) →
      (Γ : Gate → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (¬ (A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
            A ∉ ObservationEncoder.lowerConceptFamily S Γ σ) ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).lower =
            (D.completionOfMixture M)
              (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
          (conceptFormationTypedWidthComplementITV S Γ σ A).upper =
            (D.completionOfMixture M)
              (ObservationEncoder.conceptFormationGamble S Γ σ A) ∧
          (conceptFormationTypedWidthComplementITV S Γ σ A).width = 0 ∧
          (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 1 ∧
          (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint =
            (D.completionOfMixture M)
              (ObservationEncoder.conceptFormationGamble S Γ σ A)) ∨
        ((A ∈ ObservationEncoder.upperConceptFamily S Γ σ ∧
            A ∉ ObservationEncoder.lowerConceptFamily S Γ σ) ∧
          (conceptFormationTypedWidthComplementITV S Γ σ A).lower = 0 ∧
            (conceptFormationTypedWidthComplementITV S Γ σ A).upper = 1 ∧
            (conceptFormationTypedWidthComplementITV S Γ σ A).width = 1 ∧
            (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 0 ∧
            (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint = (1 / 2 : ℝ))

/-- Public profile for the finite-prefix de Finetti concept-formation bridge. -/
noncomputable def conceptFormationDeFinettiPrefixBridgeProfile :
    ConceptFormationDeFinettiPrefixBridgeProfile where
  determinesIffMixtureAgreement :=
    conceptFormationDeFinettiPrefixProjectiveSpec_determinesGlobalGamble_iff_mixtureAgreement
  strictWidthIffNotMixtureAgreement :=
    conceptFormationDeFinettiPrefixProjectiveSpec_hasStrictGlobalWidth_iff_not_mixtureAgreement
  untypedExactIffMixtureAgreement :=
    conceptFormationDeFinettiPrefixWidthComplementITV_exact_iff_mixtureAgreement
  typedExactIffMixtureAgreement :=
    conceptFormationDeFinettiPrefixTypedWidthComplementITV_exact_iff_mixtureAgreement
  untypedExactIffNoCanonicalExternalProcessDisagreement :=
    conceptFormationDeFinettiPrefixWidthComplementITV_exact_iff_noCanonicalExternalProcessDisagreement
  typedExactIffNoCanonicalExternalProcessDisagreement :=
    conceptFormationDeFinettiPrefixTypedWidthComplementITV_exact_iff_noCanonicalExternalProcessDisagreement
  untypedWidthPosIffNotMixtureAgreement :=
    conceptFormationDeFinettiPrefixWidthComplementITV_width_pos_iff_not_mixtureAgreement
  typedWidthPosIffNotMixtureAgreement :=
    conceptFormationDeFinettiPrefixTypedWidthComplementITV_width_pos_iff_not_mixtureAgreement
  untypedExactOfMixtureAgreement :=
    conceptFormationDeFinettiPrefixWidthComplementITV_exact_of_mixtureAgreement
  typedExactOfMixtureAgreement :=
    conceptFormationDeFinettiPrefixTypedWidthComplementITV_exact_of_mixtureAgreement
  untypedWidthPosOfMixtureDisagreement :=
    conceptFormationDeFinettiPrefixWidthComplementITV_width_pos_of_mixtureDisagreement
  typedWidthPosOfMixtureDisagreement :=
    conceptFormationDeFinettiPrefixTypedWidthComplementITV_width_pos_of_mixtureDisagreement
  untypedCanonicalExternalProcessReadout :=
    conceptFormationDeFinettiPrefixWidthComplementITV_canonicalExternalProcessLaw_readout
  typedCanonicalExternalProcessReadout :=
    conceptFormationDeFinettiPrefixTypedWidthComplementITV_canonicalExternalProcessLaw_readout
  canonicalExternalProcessAgreementIffMixtureAgreement :=
    conceptFormationDeFinettiPrefix_canonicalExternalProcessAgreement_iff_mixtureAgreement
  determinesIffCanonicalExternalProcessAgreement :=
    conceptFormationDeFinettiPrefixProjectiveSpec_determinesGlobalGamble_iff_canonicalExternalProcessAgreement
  determinesIffNoCanonicalExternalProcessDisagreement :=
    conceptFormationDeFinettiPrefixProjectiveSpec_determinesGlobalGamble_iff_noCanonicalExternalProcessDisagreement
  untypedWidthPosIffNotCanonicalExternalProcessAgreement :=
    conceptFormationDeFinettiPrefixWidthComplementITV_width_pos_iff_not_canonicalExternalProcessAgreement
  typedWidthPosIffNotCanonicalExternalProcessAgreement :=
    conceptFormationDeFinettiPrefixTypedWidthComplementITV_width_pos_iff_not_canonicalExternalProcessAgreement
  strictGlobalWidthIffExistsCanonicalExternalProcessDisagreement :=
    conceptFormationDeFinettiPrefixProjectiveSpec_hasStrictGlobalWidth_iff_existsCanonicalExternalProcessDisagreement
  canonicalExternalProcessDisagreementIffNotAgreement :=
    conceptFormationDeFinettiPrefix_existsCanonicalExternalProcessDisagreement_iff_not_agreement
  canonicalExternalProcessDisagreementOfMixtureDisagreement :=
    conceptFormationDeFinettiPrefix_canonicalExternalProcessDisagreement_of_mixtureDisagreement
  untypedWidthPosOfCanonicalExternalProcessDisagreement :=
    conceptFormationDeFinettiPrefixWidthComplementITV_width_pos_of_canonicalExternalProcessDisagreement
  untypedWidthPosIffExistsCanonicalExternalProcessDisagreement :=
    conceptFormationDeFinettiPrefixWidthComplementITV_width_pos_iff_existsCanonicalExternalProcessDisagreement
  typedWidthPosOfCanonicalExternalProcessDisagreement :=
    conceptFormationDeFinettiPrefixTypedWidthComplementITV_width_pos_of_canonicalExternalProcessDisagreement
  typedWidthPosIffExistsCanonicalExternalProcessDisagreement :=
    conceptFormationDeFinettiPrefixTypedWidthComplementITV_width_pos_iff_existsCanonicalExternalProcessDisagreement
  untypedGluedMixtureExactReadoutIffNoGap :=
    conceptFormationWidthComplementITV_deFinettiMixtureExactReadout_iff_noGap
  typedGluedMixtureExactReadoutIffNoGap :=
    conceptFormationTypedWidthComplementITV_deFinettiMixtureExactReadout_iff_noGap
  untypedGluedMixtureBoundaryDichotomy :=
    conceptFormationWidthComplementITV_deFinettiMixtureBoundary_dichotomy
  typedGluedMixtureBoundaryDichotomy :=
    conceptFormationTypedWidthComplementITV_deFinettiMixtureBoundary_dichotomy

end Mettapedia.PLN.Bridges.KR.ConceptFormationDeFinettiBridge
