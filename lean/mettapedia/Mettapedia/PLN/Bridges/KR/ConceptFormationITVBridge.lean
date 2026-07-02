import Mettapedia.KR.ConceptOntology.CredalFormation
import Mettapedia.PLN.TruthValues.PLNTruthTower

/-!
# Credal Concept Formation as PLN Width-Complement ITVs

This bridge turns the KR-side credal concept-formation gamble into the PLN
interval-truth-value surface that uses credal width-complement as credibility.

It is deliberately finite and projective: the uncertainty is over the finite
gate family already used by `gateCredalProjectiveSpec`. It does not assert a
full de-Finetti process semantics for formed concepts.
-/

namespace Mettapedia.PLN.Bridges.KR.ConceptFormationITVBridge

open Mettapedia.KR.ConceptOntology
open Mettapedia.KR.ConceptGeometry.AbstractInheritance
open Mettapedia.ProbabilityTheory.ImpreciseProbability
open Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal
open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth
open Mettapedia.PLN.TruthValues.PLNTruthTower
attribute [local instance] Classical.propDecidable

universe u v w x y z

section ObservationSurface

variable {Obs : Type u} {Obj : Type v} {Attr : Type w} {Q : Type x} {Gate : Type y}
variable [AddCommMonoid Q] [Preorder Q]
variable [Fintype Gate] [Nonempty Gate]
variable [Fintype Obj] [Fintype Attr]

/-- Generic source data for viewing a concept-formation gamble through an
arbitrary finite-global projective credal specification.  The existing
`conceptFormationWidthComplementITVSource` below is the identity-gate special
case. -/
noncomputable def conceptFormationWidthComplementITVSourceOfSpec
    {Window : Type z} [LE Window]
    (spec : ProjectiveLocalCredalSpec Window Gate)
    (compatible : spec.hasCompatibleCompletion)
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    ProjectiveCredalWidthComplementITVSource Window Gate :=
  ProjectiveCredalWidthComplementITVSource.finite
    spec compatible
    (ObservationSurface.conceptFormationGamble S Γ σ A)
    (ObservationSurface.conceptFormationGamble_in_unit S Γ σ A)

/-- Untyped PLN ITV for a concept-formation gamble under an arbitrary
finite-global projective credal specification. -/
noncomputable def conceptFormationWidthComplementITVOfSpec
    {Window : Type z} [LE Window]
    (spec : ProjectiveLocalCredalSpec Window Gate)
    (compatible : spec.hasCompatibleCompletion)
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) : ITV :=
  projectiveCredalWidthComplementITV
    (conceptFormationWidthComplementITVSourceOfSpec spec compatible S Γ σ A)

/-- Typed PLN ITV for a concept-formation gamble under an arbitrary
finite-global projective credal specification. -/
noncomputable def conceptFormationTypedWidthComplementITVOfSpec
    {Window : Type z} [LE Window]
    (spec : ProjectiveLocalCredalSpec Window Gate)
    (compatible : spec.hasCompatibleCompletion)
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    TypedITV (projectiveCredalWidthComplementITVSemantics Window Gate) :=
  TypedITV.fromProjectiveCredalWidthComplement
    (conceptFormationWidthComplementITVSourceOfSpec spec compatible S Γ σ A)

/-- Source data for the PLN width-complement ITV obtained from an
observation-level credal concept-formation gamble. -/
noncomputable def conceptFormationWidthComplementITVSource
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    ProjectiveCredalWidthComplementITVSource PUnit Gate :=
  ProjectiveCredalWidthComplementITVSource.finite
    (gateCredalProjectiveSpec (Gate := Gate))
    (gateCredalProjectiveSpec_hasCompatibleCompletion (Gate := Gate))
    (ObservationSurface.conceptFormationGamble S Γ σ A)
    (ObservationSurface.conceptFormationGamble_in_unit S Γ σ A)

/-- The untyped PLN ITV for a credal concept-formation gamble. -/
noncomputable def conceptFormationWidthComplementITV
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) : ITV :=
  projectiveCredalWidthComplementITV
    (conceptFormationWidthComplementITVSource S Γ σ A)

/-- The typed PLN ITV for a credal concept-formation gamble. -/
noncomputable def conceptFormationTypedWidthComplementITV
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    TypedITV (projectiveCredalWidthComplementITVSemantics PUnit Gate) :=
  TypedITV.fromProjectiveCredalWidthComplement
    (conceptFormationWidthComplementITVSource S Γ σ A)

@[simp] theorem conceptFormationWidthComplementITV_lower
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (conceptFormationWidthComplementITV S Γ σ A).lower =
      if A ∈ ObservationSurface.lowerConceptFamily S Γ σ then 1 else 0 := by
  unfold conceptFormationWidthComplementITV conceptFormationWidthComplementITVSource
  rw [projectiveCredalWidthComplementITV_lower]
  exact ObservationSurface.globalNaturalExtension_conceptFormationGamble_eq S Γ σ A

@[simp] theorem conceptFormationWidthComplementITV_upper
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (conceptFormationWidthComplementITV S Γ σ A).upper =
      if A ∈ ObservationSurface.upperConceptFamily S Γ σ then 1 else 0 := by
  unfold conceptFormationWidthComplementITV conceptFormationWidthComplementITVSource
  dsimp [projectiveCredalWidthComplementITV,
    ProjectiveCredalWidthComplementITVSource.finite]
  simpa [gateCredalProjectiveSpec,
    ObservationSurface.conceptFormationGamble,
    ObservationSurface.upperConceptFamily] using
    ObservationSurface.upperEnvelope_conceptFormationGamble_eq S Γ σ A

@[simp] theorem conceptFormationWidthComplementITV_width
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (conceptFormationWidthComplementITV S Γ σ A).width =
      if A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
          A ∉ ObservationSurface.lowerConceptFamily S Γ σ then 1 else 0 := by
  unfold conceptFormationWidthComplementITV conceptFormationWidthComplementITVSource
  rw [projectiveCredalWidthComplementITV_width]
  exact ObservationSurface.globalEnvelopeWidth_conceptFormationGamble_eq S Γ σ A

@[simp] theorem conceptFormationWidthComplementITV_credibility
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (conceptFormationWidthComplementITV S Γ σ A).credibility =
      if A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
          A ∉ ObservationSurface.lowerConceptFamily S Γ σ then 0 else 1 := by
  unfold conceptFormationWidthComplementITV conceptFormationWidthComplementITVSource
  rw [projectiveCredalWidthComplementITV_credibility]
  exact ObservationSurface.globalEnvelopeWidthComplement_conceptFormationGamble_eq S Γ σ A

@[simp] theorem conceptFormationWidthComplementITV_strength
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (conceptFormationWidthComplementITV S Γ σ A).strength =
      if A ∈ ObservationSurface.lowerConceptFamily S Γ σ then 1
      else if A ∈ ObservationSurface.upperConceptFamily S Γ σ then (1 / 2 : ℝ) else 0 := by
  unfold conceptFormationWidthComplementITV conceptFormationWidthComplementITVSource
  rw [projectiveCredalWidthComplementITV_strength]
  exact ObservationSurface.globalEnvelopeMidpoint_conceptFormationGamble_eq S Γ σ A

/-- The concept-formation ITV uses the width-complement convention: uncertainty
width plus displayed credibility is exactly one. -/
theorem conceptFormationWidthComplementITV_width_add_credibility
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (conceptFormationWidthComplementITV S Γ σ A).width +
        (conceptFormationWidthComplementITV S Γ σ A).credibility = 1 := by
  exact projectiveCredalWidthComplementITV_width_add_credibility
    (conceptFormationWidthComplementITVSource S Γ σ A)

/-- Generic exactness theorem for concept-formation ITVs under any finite
projective credal specification: if the spec determines the
concept-formation gamble, the displayed width is zero and credibility is one. -/
theorem conceptFormationWidthComplementITVOfSpec_exact_of_determines
    {Window : Type z} [LE Window]
    (spec : ProjectiveLocalCredalSpec Window Gate)
    (compatible : spec.hasCompatibleCompletion)
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (hDet :
      spec.determinesGlobalGamble
        (ObservationSurface.conceptFormationGamble S Γ σ A)) :
    (conceptFormationWidthComplementITVOfSpec spec compatible S Γ σ A).lower =
        (conceptFormationWidthComplementITVOfSpec spec compatible S Γ σ A).upper ∧
      (conceptFormationWidthComplementITVOfSpec spec compatible S Γ σ A).width = 0 ∧
      (conceptFormationWidthComplementITVOfSpec spec compatible S Γ σ A).credibility = 1 ∧
      (conceptFormationWidthComplementITVOfSpec spec compatible S Γ σ A).strength =
        (conceptFormationWidthComplementITVOfSpec spec compatible S Γ σ A).lower := by
  let src := conceptFormationWidthComplementITVSourceOfSpec spec compatible S Γ σ A
  change (projectiveCredalWidthComplementITV src).lower =
        (projectiveCredalWidthComplementITV src).upper ∧
      (projectiveCredalWidthComplementITV src).width = 0 ∧
      (projectiveCredalWidthComplementITV src).credibility = 1 ∧
      (projectiveCredalWidthComplementITV src).strength =
        (projectiveCredalWidthComplementITV src).lower
  rcases compatible with ⟨P, hP⟩
  have hLU :
      (projectiveCredalWidthComplementITV src).lower =
        (projectiveCredalWidthComplementITV src).upper := by
    rw [projectiveCredalWidthComplementITV_lower,
      projectiveCredalWidthComplementITV_upper]
    exact
      spec.globalLowerUpperEnvelope_eq_of_determines
        (⟨P, hP⟩ : spec.hasCompatibleCompletion) src.gamble
        src.bddBelow src.bddAbove hP hDet
  have hWidthSpec :
      spec.globalEnvelopeWidth src.gamble = 0 :=
    spec.globalEnvelopeWidth_eq_zero_of_determines
      (⟨P, hP⟩ : spec.hasCompatibleCompletion) src.gamble
      src.bddBelow src.bddAbove hP hDet
  have hWidth :
      (projectiveCredalWidthComplementITV src).width = 0 := by
    rw [projectiveCredalWidthComplementITV_width]
    exact hWidthSpec
  have hCred :
      (projectiveCredalWidthComplementITV src).credibility = 1 := by
    have hAdd := projectiveCredalWidthComplementITV_width_add_credibility src
    rw [hWidth] at hAdd
    linarith
  have hMid :
      spec.globalEnvelopeMidpoint src.gamble = P src.gamble :=
    spec.globalEnvelopeMidpoint_eq_of_determines
      (⟨P, hP⟩ : spec.hasCompatibleCompletion) src.gamble
      src.bddBelow src.bddAbove hP hDet
  have hLower :
      spec.globalNaturalExtension src.gamble = P src.gamble :=
    spec.globalNaturalExtension_eq_of_determines
      (⟨P, hP⟩ : spec.hasCompatibleCompletion) src.gamble
      src.bddBelow hP hDet
  have hStrength :
      (projectiveCredalWidthComplementITV src).strength =
        (projectiveCredalWidthComplementITV src).lower := by
    rw [projectiveCredalWidthComplementITV_strength,
      projectiveCredalWidthComplementITV_lower]
    change spec.globalEnvelopeMidpoint src.gamble =
      spec.globalNaturalExtension src.gamble
    rw [hMid, hLower]
  exact ⟨hLU, hWidth, hCred, hStrength⟩

/-- Typed counterpart of
`conceptFormationWidthComplementITVOfSpec_exact_of_determines`. -/
theorem conceptFormationTypedWidthComplementITVOfSpec_exact_of_determines
    {Window : Type z} [LE Window]
    (spec : ProjectiveLocalCredalSpec Window Gate)
    (compatible : spec.hasCompatibleCompletion)
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (hDet :
      spec.determinesGlobalGamble
        (ObservationSurface.conceptFormationGamble S Γ σ A)) :
    (conceptFormationTypedWidthComplementITVOfSpec spec compatible S Γ σ A).lower =
        (conceptFormationTypedWidthComplementITVOfSpec spec compatible S Γ σ A).upper ∧
      (conceptFormationTypedWidthComplementITVOfSpec spec compatible S Γ σ A).width = 0 ∧
      (conceptFormationTypedWidthComplementITVOfSpec spec compatible S Γ σ A).credibility = 1 ∧
      (conceptFormationTypedWidthComplementITVOfSpec spec compatible S Γ σ A).midpoint =
        (conceptFormationTypedWidthComplementITVOfSpec spec compatible S Γ σ A).lower := by
  let src := conceptFormationWidthComplementITVSourceOfSpec spec compatible S Γ σ A
  change (TypedITV.fromProjectiveCredalWidthComplement src).lower =
        (TypedITV.fromProjectiveCredalWidthComplement src).upper ∧
      (TypedITV.fromProjectiveCredalWidthComplement src).width = 0 ∧
      (TypedITV.fromProjectiveCredalWidthComplement src).credibility = 1 ∧
      (TypedITV.fromProjectiveCredalWidthComplement src).midpoint =
        (TypedITV.fromProjectiveCredalWidthComplement src).lower
  rcases compatible with ⟨P, hP⟩
  have hLU :
      (TypedITV.fromProjectiveCredalWidthComplement src).lower =
        (TypedITV.fromProjectiveCredalWidthComplement src).upper := by
    rw [TypedITV.fromProjectiveCredalWidthComplement_lower,
      TypedITV.fromProjectiveCredalWidthComplement_upper]
    exact
      spec.globalLowerUpperEnvelope_eq_of_determines
        (⟨P, hP⟩ : spec.hasCompatibleCompletion) src.gamble
        src.bddBelow src.bddAbove hP hDet
  have hWidthSpec :
      spec.globalEnvelopeWidth src.gamble = 0 :=
    spec.globalEnvelopeWidth_eq_zero_of_determines
      (⟨P, hP⟩ : spec.hasCompatibleCompletion) src.gamble
      src.bddBelow src.bddAbove hP hDet
  have hWidth :
      (TypedITV.fromProjectiveCredalWidthComplement src).width = 0 := by
    rw [TypedITV.fromProjectiveCredalWidthComplement_width]
    exact hWidthSpec
  have hCred :
      (TypedITV.fromProjectiveCredalWidthComplement src).credibility = 1 := by
    rw [TypedITV.fromProjectiveCredalWidthComplement_credibility]
    have hAdd := projectiveCredalWidthComplementITV_width_add_credibility src
    rw [projectiveCredalWidthComplementITV_width,
      projectiveCredalWidthComplementITV_credibility] at hAdd
    change spec.globalEnvelopeWidth src.gamble +
      spec.globalEnvelopeWidthComplement src.gamble = 1 at hAdd
    rw [hWidthSpec] at hAdd
    change spec.globalEnvelopeWidthComplement src.gamble = 1
    linarith
  have hMid :
      spec.globalEnvelopeMidpoint src.gamble = P src.gamble :=
    spec.globalEnvelopeMidpoint_eq_of_determines
      (⟨P, hP⟩ : spec.hasCompatibleCompletion) src.gamble
      src.bddBelow src.bddAbove hP hDet
  have hLower :
      spec.globalNaturalExtension src.gamble = P src.gamble :=
    spec.globalNaturalExtension_eq_of_determines
      (⟨P, hP⟩ : spec.hasCompatibleCompletion) src.gamble
      src.bddBelow hP hDet
  have hMidpoint :
      (TypedITV.fromProjectiveCredalWidthComplement src).midpoint =
        (TypedITV.fromProjectiveCredalWidthComplement src).lower := by
    rw [TypedITV.fromProjectiveCredalWidthComplement_midpoint,
      TypedITV.fromProjectiveCredalWidthComplement_lower]
    change spec.globalEnvelopeMidpoint src.gamble =
      spec.globalNaturalExtension src.gamble
    rw [hMid, hLower]
  exact ⟨hLU, hWidth, hCred, hMidpoint⟩

/-- Generic positive-width theorem for concept-formation ITVs under any finite
projective credal specification.  Strict projective width gives positive
displayed width and hence credibility below one. -/
theorem conceptFormationWidthComplementITVOfSpec_width_pos_of_strictWidth
    {Window : Type z} [LE Window]
    (spec : ProjectiveLocalCredalSpec Window Gate)
    (compatible : spec.hasCompatibleCompletion)
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (hStrict :
      spec.hasStrictGlobalWidth
        (ObservationSurface.conceptFormationGamble S Γ σ A)) :
    0 < (conceptFormationWidthComplementITVOfSpec spec compatible S Γ σ A).width ∧
      (conceptFormationWidthComplementITVOfSpec spec compatible S Γ σ A).credibility < 1 := by
  let src := conceptFormationWidthComplementITVSourceOfSpec spec compatible S Γ σ A
  change 0 < (projectiveCredalWidthComplementITV src).width ∧
      (projectiveCredalWidthComplementITV src).credibility < 1
  have hWidthPos :
      0 < (projectiveCredalWidthComplementITV src).width := by
    rw [projectiveCredalWidthComplementITV_width]
    exact
      spec.globalEnvelopeWidth_pos_of_strictWidth src.gamble
        src.bddBelow src.bddAbove hStrict
  have hCredLt :
      (projectiveCredalWidthComplementITV src).credibility < 1 := by
    rw [projectiveCredalWidthComplementITV_credibility]
    exact
      credalEnvelopeWidthComplement_lt_one_of_strictWidth
        spec.projectiveLimitCredalSet src.gamble
        src.bddBelow src.bddAbove hStrict
  exact ⟨hWidthPos, hCredLt⟩

/-- Typed counterpart of
`conceptFormationWidthComplementITVOfSpec_width_pos_of_strictWidth`. -/
theorem conceptFormationTypedWidthComplementITVOfSpec_width_pos_of_strictWidth
    {Window : Type z} [LE Window]
    (spec : ProjectiveLocalCredalSpec Window Gate)
    (compatible : spec.hasCompatibleCompletion)
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (hStrict :
      spec.hasStrictGlobalWidth
        (ObservationSurface.conceptFormationGamble S Γ σ A)) :
    0 < (conceptFormationTypedWidthComplementITVOfSpec spec compatible S Γ σ A).width ∧
      (conceptFormationTypedWidthComplementITVOfSpec spec compatible S Γ σ A).credibility < 1 := by
  let src := conceptFormationWidthComplementITVSourceOfSpec spec compatible S Γ σ A
  change 0 < (TypedITV.fromProjectiveCredalWidthComplement src).width ∧
      (TypedITV.fromProjectiveCredalWidthComplement src).credibility < 1
  have hWidthPos :
      0 < (TypedITV.fromProjectiveCredalWidthComplement src).width := by
    rw [TypedITV.fromProjectiveCredalWidthComplement_width]
    exact
      spec.globalEnvelopeWidth_pos_of_strictWidth src.gamble
        src.bddBelow src.bddAbove hStrict
  have hCredLt :
      (TypedITV.fromProjectiveCredalWidthComplement src).credibility < 1 := by
    rw [TypedITV.fromProjectiveCredalWidthComplement_credibility]
    exact
      credalEnvelopeWidthComplement_lt_one_of_strictWidth
        spec.projectiveLimitCredalSet src.gamble
        src.bddBelow src.bddAbove hStrict
  exact ⟨hWidthPos, hCredLt⟩

@[simp] theorem conceptFormationTypedWidthComplementITV_lower
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (conceptFormationTypedWidthComplementITV S Γ σ A).lower =
      if A ∈ ObservationSurface.lowerConceptFamily S Γ σ then 1 else 0 := by
  unfold conceptFormationTypedWidthComplementITV conceptFormationWidthComplementITVSource
  rw [TypedITV.fromProjectiveCredalWidthComplement_lower]
  exact ObservationSurface.globalNaturalExtension_conceptFormationGamble_eq S Γ σ A

@[simp] theorem conceptFormationTypedWidthComplementITV_upper
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (conceptFormationTypedWidthComplementITV S Γ σ A).upper =
      if A ∈ ObservationSurface.upperConceptFamily S Γ σ then 1 else 0 := by
  unfold conceptFormationTypedWidthComplementITV conceptFormationWidthComplementITVSource
  dsimp [TypedITV.fromProjectiveCredalWidthComplement, TypedITV.upper,
    TypedITV.value, projectiveCredalWidthComplementITVSemantics,
    projectiveCredalWidthComplementITV,
    ProjectiveCredalWidthComplementITVSource.finite]
  simpa [gateCredalProjectiveSpec,
    ObservationSurface.conceptFormationGamble,
    ObservationSurface.upperConceptFamily] using
    ObservationSurface.upperEnvelope_conceptFormationGamble_eq S Γ σ A

@[simp] theorem conceptFormationTypedWidthComplementITV_width
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (conceptFormationTypedWidthComplementITV S Γ σ A).width =
      if A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
          A ∉ ObservationSurface.lowerConceptFamily S Γ σ then 1 else 0 := by
  unfold conceptFormationTypedWidthComplementITV conceptFormationWidthComplementITVSource
  rw [TypedITV.fromProjectiveCredalWidthComplement_width]
  exact ObservationSurface.globalEnvelopeWidth_conceptFormationGamble_eq S Γ σ A

@[simp] theorem conceptFormationTypedWidthComplementITV_credibility
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (conceptFormationTypedWidthComplementITV S Γ σ A).credibility =
      if A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
          A ∉ ObservationSurface.lowerConceptFamily S Γ σ then 0 else 1 := by
  unfold conceptFormationTypedWidthComplementITV conceptFormationWidthComplementITVSource
  rw [TypedITV.fromProjectiveCredalWidthComplement_credibility]
  exact ObservationSurface.globalEnvelopeWidthComplement_conceptFormationGamble_eq S Γ σ A

@[simp] theorem conceptFormationTypedWidthComplementITV_midpoint
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint =
      if A ∈ ObservationSurface.lowerConceptFamily S Γ σ then 1
      else if A ∈ ObservationSurface.upperConceptFamily S Γ σ then (1 / 2 : ℝ) else 0 := by
  unfold conceptFormationTypedWidthComplementITV conceptFormationWidthComplementITVSource
  rw [TypedITV.fromProjectiveCredalWidthComplement_midpoint]
  exact ObservationSurface.globalEnvelopeMidpoint_conceptFormationGamble_eq S Γ σ A

/-- One citation theorem for the untyped PLN readout of credal concept
formation. -/
theorem conceptFormationWidthComplementITV_readout
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    ((conceptFormationWidthComplementITV S Γ σ A).lower =
        if A ∈ ObservationSurface.lowerConceptFamily S Γ σ then 1 else 0) ∧
      ((conceptFormationWidthComplementITV S Γ σ A).upper =
        if A ∈ ObservationSurface.upperConceptFamily S Γ σ then 1 else 0) ∧
      ((conceptFormationWidthComplementITV S Γ σ A).width =
        if A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
            A ∉ ObservationSurface.lowerConceptFamily S Γ σ then 1 else 0) ∧
      ((conceptFormationWidthComplementITV S Γ σ A).credibility =
        if A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
            A ∉ ObservationSurface.lowerConceptFamily S Γ σ then 0 else 1) ∧
      ((conceptFormationWidthComplementITV S Γ σ A).strength =
        if A ∈ ObservationSurface.lowerConceptFamily S Γ σ then 1
        else if A ∈ ObservationSurface.upperConceptFamily S Γ σ then (1 / 2 : ℝ) else 0) := by
  exact ⟨conceptFormationWidthComplementITV_lower S Γ σ A,
    conceptFormationWidthComplementITV_upper S Γ σ A,
    conceptFormationWidthComplementITV_width S Γ σ A,
    conceptFormationWidthComplementITV_credibility S Γ σ A,
    conceptFormationWidthComplementITV_strength S Γ σ A⟩

/-- One citation theorem for the typed PLN readout of credal concept
formation. -/
theorem conceptFormationTypedWidthComplementITV_readout
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    ((conceptFormationTypedWidthComplementITV S Γ σ A).lower =
        if A ∈ ObservationSurface.lowerConceptFamily S Γ σ then 1 else 0) ∧
      ((conceptFormationTypedWidthComplementITV S Γ σ A).upper =
        if A ∈ ObservationSurface.upperConceptFamily S Γ σ then 1 else 0) ∧
      ((conceptFormationTypedWidthComplementITV S Γ σ A).width =
        if A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
            A ∉ ObservationSurface.lowerConceptFamily S Γ σ then 1 else 0) ∧
      ((conceptFormationTypedWidthComplementITV S Γ σ A).credibility =
        if A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
            A ∉ ObservationSurface.lowerConceptFamily S Γ σ then 0 else 1) ∧
      ((conceptFormationTypedWidthComplementITV S Γ σ A).midpoint =
        if A ∈ ObservationSurface.lowerConceptFamily S Γ σ then 1
        else if A ∈ ObservationSurface.upperConceptFamily S Γ σ then (1 / 2 : ℝ) else 0) := by
  exact ⟨conceptFormationTypedWidthComplementITV_lower S Γ σ A,
    conceptFormationTypedWidthComplementITV_upper S Γ σ A,
    conceptFormationTypedWidthComplementITV_width S Γ σ A,
    conceptFormationTypedWidthComplementITV_credibility S Γ σ A,
    conceptFormationTypedWidthComplementITV_midpoint S Γ σ A⟩

/-- If the finite gate process determines the concept-formation gamble, the
untyped displayed PLN ITV is exact: lower and upper coincide, width is zero,
credibility is one, and the displayed strength is the lower endpoint. -/
theorem conceptFormationWidthComplementITV_exact_of_determines
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (hDet :
      (gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (ObservationSurface.conceptFormationGamble S Γ σ A)) :
    (conceptFormationWidthComplementITV S Γ σ A).lower =
        (conceptFormationWidthComplementITV S Γ σ A).upper ∧
      (conceptFormationWidthComplementITV S Γ σ A).width = 0 ∧
      (conceptFormationWidthComplementITV S Γ σ A).credibility = 1 ∧
      (conceptFormationWidthComplementITV S Γ σ A).strength =
        (conceptFormationWidthComplementITV S Γ σ A).lower := by
  have hNoGap :
      ¬ (A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
          A ∉ ObservationSurface.lowerConceptFamily S Γ σ) :=
    (ObservationSurface.gateCredalProjectiveSpec_determinesGlobalGamble_conceptFormationGamble_iff
      S Γ σ A).mp hDet
  by_cases hLower : A ∈ ObservationSurface.lowerConceptFamily S Γ σ
  · have hUpper : A ∈ ObservationSurface.upperConceptFamily S Γ σ :=
      ObservationSurface.lowerConceptFamily_subset_upperConceptFamily S Γ σ hLower
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [hLower, hUpper]
    · simp [hLower, hUpper]
    · simp [hLower, hUpper]
    · rw [conceptFormationWidthComplementITV_strength,
        conceptFormationWidthComplementITV_lower]
      simp [hLower]
  · have hUpper : A ∉ ObservationSurface.upperConceptFamily S Γ σ := by
      intro hUpper
      exact hNoGap ⟨hUpper, hLower⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [hLower, hUpper]
    · simp [hLower, hUpper]
    · simp [hLower, hUpper]
    · rw [conceptFormationWidthComplementITV_strength,
        conceptFormationWidthComplementITV_lower]
      simp [hLower, hUpper]

/-- If the finite gate process determines the concept-formation gamble, the
typed displayed PLN ITV is exact: lower and upper coincide, width is zero,
credibility is one, and the displayed midpoint is the lower endpoint. -/
theorem conceptFormationTypedWidthComplementITV_exact_of_determines
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (hDet :
      (gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (ObservationSurface.conceptFormationGamble S Γ σ A)) :
    (conceptFormationTypedWidthComplementITV S Γ σ A).lower =
        (conceptFormationTypedWidthComplementITV S Γ σ A).upper ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).width = 0 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 1 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint =
        (conceptFormationTypedWidthComplementITV S Γ σ A).lower := by
  have hNoGap :
      ¬ (A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
          A ∉ ObservationSurface.lowerConceptFamily S Γ σ) :=
    (ObservationSurface.gateCredalProjectiveSpec_determinesGlobalGamble_conceptFormationGamble_iff
      S Γ σ A).mp hDet
  by_cases hLower : A ∈ ObservationSurface.lowerConceptFamily S Γ σ
  · have hUpper : A ∈ ObservationSurface.upperConceptFamily S Γ σ :=
      ObservationSurface.lowerConceptFamily_subset_upperConceptFamily S Γ σ hLower
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [hLower, hUpper]
    · simp [hLower, hUpper]
    · simp [hLower, hUpper]
    · rw [conceptFormationTypedWidthComplementITV_midpoint,
        conceptFormationTypedWidthComplementITV_lower]
      simp [hLower]
  · have hUpper : A ∉ ObservationSurface.upperConceptFamily S Γ σ := by
      intro hUpper
      exact hNoGap ⟨hUpper, hLower⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [hLower, hUpper]
    · simp [hLower, hUpper]
    · simp [hLower, hUpper]
    · rw [conceptFormationTypedWidthComplementITV_midpoint,
        conceptFormationTypedWidthComplementITV_lower]
      simp [hLower, hUpper]

/-- The untyped concept-formation ITV is exact exactly when the finite gate
process has no lower/upper formed-concept gap.  This is the negative canary for
the bridge: a permissive-but-not-robust concept forces nonzero width, so exact
readout cannot be claimed. -/
theorem conceptFormationWidthComplementITV_exact_iff_noGap
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    ((conceptFormationWidthComplementITV S Γ σ A).lower =
        (conceptFormationWidthComplementITV S Γ σ A).upper ∧
      (conceptFormationWidthComplementITV S Γ σ A).width = 0 ∧
      (conceptFormationWidthComplementITV S Γ σ A).credibility = 1 ∧
      (conceptFormationWidthComplementITV S Γ σ A).strength =
        (conceptFormationWidthComplementITV S Γ σ A).lower) ↔
      ¬ (A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
          A ∉ ObservationSurface.lowerConceptFamily S Γ σ) := by
  classical
  constructor
  · intro hExact
    by_contra hNoGap
    have hGap :
        A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
          A ∉ ObservationSurface.lowerConceptFamily S Γ σ :=
      hNoGap
    have hWidth := hExact.2.1
    rw [conceptFormationWidthComplementITV_width] at hWidth
    simp [hGap] at hWidth
  · intro hNoGap
    have hDet :
        (gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (ObservationSurface.conceptFormationGamble S Γ σ A) :=
      (ObservationSurface.gateCredalProjectiveSpec_determinesGlobalGamble_conceptFormationGamble_iff
        S Γ σ A).mpr hNoGap
    exact conceptFormationWidthComplementITV_exact_of_determines S Γ σ A hDet

/-- Typed counterpart of
`conceptFormationWidthComplementITV_exact_iff_noGap`. -/
theorem conceptFormationTypedWidthComplementITV_exact_iff_noGap
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    ((conceptFormationTypedWidthComplementITV S Γ σ A).lower =
        (conceptFormationTypedWidthComplementITV S Γ σ A).upper ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).width = 0 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 1 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint =
        (conceptFormationTypedWidthComplementITV S Γ σ A).lower) ↔
      ¬ (A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
          A ∉ ObservationSurface.lowerConceptFamily S Γ σ) := by
  classical
  constructor
  · intro hExact
    by_contra hNoGap
    have hGap :
        A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
          A ∉ ObservationSurface.lowerConceptFamily S Γ σ :=
      hNoGap
    have hWidth := hExact.2.1
    rw [conceptFormationTypedWidthComplementITV_width] at hWidth
    simp [hGap] at hWidth
  · intro hNoGap
    have hDet :
        (gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (ObservationSurface.conceptFormationGamble S Γ σ A) :=
      (ObservationSurface.gateCredalProjectiveSpec_determinesGlobalGamble_conceptFormationGamble_iff
        S Γ σ A).mpr hNoGap
    exact conceptFormationTypedWidthComplementITV_exact_of_determines S Γ σ A hDet

/-- Gap readout for the untyped concept-formation ITV.  A concept formed by
some admissible gate but not robustly by all gates displays as the full
semantic interval: lower `0`, upper `1`, width `1`, credibility `0`, and
midpoint strength `1/2`. -/
theorem conceptFormationWidthComplementITV_gap_readout
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (hGap :
      A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
        A ∉ ObservationSurface.lowerConceptFamily S Γ σ) :
    (conceptFormationWidthComplementITV S Γ σ A).lower = 0 ∧
      (conceptFormationWidthComplementITV S Γ σ A).upper = 1 ∧
      (conceptFormationWidthComplementITV S Γ σ A).width = 1 ∧
      (conceptFormationWidthComplementITV S Γ σ A).credibility = 0 ∧
      (conceptFormationWidthComplementITV S Γ σ A).strength = (1 / 2 : ℝ) := by
  rcases hGap with ⟨hUpper, hNotLower⟩
  exact ⟨by simp [hNotLower], by simp [hUpper], by simp [hUpper, hNotLower],
    by simp [hUpper, hNotLower], by
      rw [conceptFormationWidthComplementITV_strength]
      simp [hUpper, hNotLower]⟩

/-- Typed counterpart of `conceptFormationWidthComplementITV_gap_readout`. -/
theorem conceptFormationTypedWidthComplementITV_gap_readout
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (hGap :
      A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
        A ∉ ObservationSurface.lowerConceptFamily S Γ σ) :
    (conceptFormationTypedWidthComplementITV S Γ σ A).lower = 0 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).upper = 1 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).width = 1 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 0 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint = (1 / 2 : ℝ) := by
  rcases hGap with ⟨hUpper, hNotLower⟩
  exact ⟨by simp [hNotLower], by simp [hUpper], by simp [hUpper, hNotLower],
    by simp [hUpper, hNotLower], by
      rw [conceptFormationTypedWidthComplementITV_midpoint]
      simp [hUpper, hNotLower]⟩

/-- The untyped concept-formation ITV has the full displayed uncertainty
readout exactly in the lower/upper concept-family gap case.  This is the
full-width counterpart to `conceptFormationWidthComplementITV_exact_iff_noGap`:
the display is `[0,1]` precisely when some gate forms the concept and another
compatible gate does not. -/
theorem conceptFormationWidthComplementITV_fullReadout_iff_gap
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    ((conceptFormationWidthComplementITV S Γ σ A).lower = 0 ∧
      (conceptFormationWidthComplementITV S Γ σ A).upper = 1 ∧
      (conceptFormationWidthComplementITV S Γ σ A).width = 1 ∧
      (conceptFormationWidthComplementITV S Γ σ A).credibility = 0 ∧
      (conceptFormationWidthComplementITV S Γ σ A).strength = (1 / 2 : ℝ)) ↔
      A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
        A ∉ ObservationSurface.lowerConceptFamily S Γ σ := by
  constructor
  · intro hReadout
    rcases hReadout with ⟨_, _, hWidth, _, _⟩
    rw [conceptFormationWidthComplementITV_width] at hWidth
    split_ifs at hWidth with hGap
    · exact hGap
    · norm_num at hWidth
  · intro hGap
    exact conceptFormationWidthComplementITV_gap_readout S Γ σ A hGap

/-- Typed counterpart of
`conceptFormationWidthComplementITV_fullReadout_iff_gap`. -/
theorem conceptFormationTypedWidthComplementITV_fullReadout_iff_gap
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    ((conceptFormationTypedWidthComplementITV S Γ σ A).lower = 0 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).upper = 1 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).width = 1 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 0 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint = (1 / 2 : ℝ)) ↔
      A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
        A ∉ ObservationSurface.lowerConceptFamily S Γ σ := by
  constructor
  · intro hReadout
    rcases hReadout with ⟨_, _, hWidth, _, _⟩
    rw [conceptFormationTypedWidthComplementITV_width] at hWidth
    split_ifs at hWidth with hGap
    · exact hGap
    · norm_num at hWidth
  · intro hGap
    exact conceptFormationTypedWidthComplementITV_gap_readout S Γ σ A hGap

/-- The untyped concept-formation ITV has positive displayed width (and
credibility below `1`) exactly in the lower/upper concept-family gap case. -/
theorem conceptFormationWidthComplementITV_width_pos_iff_gap
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (0 < (conceptFormationWidthComplementITV S Γ σ A).width ∧
      (conceptFormationWidthComplementITV S Γ σ A).credibility < 1) ↔
      A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
        A ∉ ObservationSurface.lowerConceptFamily S Γ σ := by
  constructor
  · intro hDisplay
    rcases hDisplay with ⟨hWidth, _⟩
    rw [conceptFormationWidthComplementITV_width] at hWidth
    split_ifs at hWidth with hGap
    · exact hGap
    · norm_num at hWidth
  · intro hGap
    rcases conceptFormationWidthComplementITV_gap_readout S Γ σ A hGap with
      ⟨_, _, hWidth, hCred, _⟩
    exact ⟨by rw [hWidth]; norm_num, by rw [hCred]; norm_num⟩

/-- Typed counterpart of
`conceptFormationWidthComplementITV_width_pos_iff_gap`. -/
theorem conceptFormationTypedWidthComplementITV_width_pos_iff_gap
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (0 < (conceptFormationTypedWidthComplementITV S Γ σ A).width ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).credibility < 1) ↔
      A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
        A ∉ ObservationSurface.lowerConceptFamily S Γ σ := by
  constructor
  · intro hDisplay
    rcases hDisplay with ⟨hWidth, _⟩
    rw [conceptFormationTypedWidthComplementITV_width] at hWidth
    split_ifs at hWidth with hGap
    · exact hGap
    · norm_num at hWidth
  · intro hGap
    rcases conceptFormationTypedWidthComplementITV_gap_readout S Γ σ A hGap with
      ⟨_, _, hWidth, hCred, _⟩
    exact ⟨by rw [hWidth]; norm_num, by rw [hCred]; norm_num⟩

/-- Under finite-gate determination, the untyped PLN ITV readout is not merely
point-valued: its lower endpoint, upper endpoint, and midpoint strength all
equal the value assigned by any compatible precise completion to the
concept-formation gamble. -/
theorem conceptFormationWidthComplementITV_preciseCompletionReadout_of_determines
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (P : PrecisePrevision Gate)
    (hP :
      P ∈ (gateCredalProjectiveSpec (Gate := Gate)).projectiveLimitCredalSet)
    (hDet :
      (gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (ObservationSurface.conceptFormationGamble S Γ σ A)) :
    (conceptFormationWidthComplementITV S Γ σ A).lower =
        P (ObservationSurface.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationWidthComplementITV S Γ σ A).upper =
        P (ObservationSurface.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationWidthComplementITV S Γ σ A).width = 0 ∧
      (conceptFormationWidthComplementITV S Γ σ A).credibility = 1 ∧
      (conceptFormationWidthComplementITV S Γ σ A).strength =
        P (ObservationSurface.conceptFormationGamble S Γ σ A) := by
  let Spec := gateCredalProjectiveSpec (Gate := Gate)
  let X := ObservationSurface.conceptFormationGamble S Γ σ A
  have hBddBelow :
      BddBelow ((fun P' : PrecisePrevision Gate => P' X) ''
        Spec.projectiveLimitCredalSet) :=
    finite_credalRange_bddBelow Spec.projectiveLimitCredalSet X
  have hBddAbove :
      BddAbove ((fun P' : PrecisePrevision Gate => P' X) ''
        Spec.projectiveLimitCredalSet) :=
    finite_credalRange_bddAbove Spec.projectiveLimitCredalSet X
  have hNE : Spec.globalNaturalExtension X = P X :=
    Spec.globalNaturalExtension_eq_of_determines
      (gateCredalProjectiveSpec_hasCompatibleCompletion (Gate := Gate))
      X hBddBelow hP hDet
  have hWidth : Spec.globalEnvelopeWidth X = 0 :=
    Spec.globalEnvelopeWidth_eq_zero_of_determines
      (gateCredalProjectiveSpec_hasCompatibleCompletion (Gate := Gate))
      X hBddBelow hBddAbove hP hDet
  have hMid : Spec.globalEnvelopeMidpoint X = P X :=
    Spec.globalEnvelopeMidpoint_eq_of_determines
      (gateCredalProjectiveSpec_hasCompatibleCompletion (Gate := Gate))
      X hBddBelow hBddAbove hP hDet
  have hCred : Spec.globalEnvelopeWidthComplement X = 1 := by
    unfold ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement
    unfold ProjectiveLocalCredalSpec.globalEnvelopeWidth at hWidth
    unfold credalEnvelopeWidthComplement
    rw [hWidth]
    norm_num
  have hLowerUpper :
      Spec.globalNaturalExtension X =
        upperEnvelope Spec.projectiveLimitCredalSet X :=
    Spec.globalLowerUpperEnvelope_eq_of_determines
      (gateCredalProjectiveSpec_hasCompatibleCompletion (Gate := Gate))
      X hBddBelow hBddAbove hP hDet
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc
      (conceptFormationWidthComplementITV S Γ σ A).lower =
          Spec.globalNaturalExtension X := by
        simp [conceptFormationWidthComplementITV,
          conceptFormationWidthComplementITVSource,
          ProjectiveCredalWidthComplementITVSource.finite, Spec, X]
      _ = P X := hNE
  · calc
      (conceptFormationWidthComplementITV S Γ σ A).upper =
          upperEnvelope Spec.projectiveLimitCredalSet X := by
        simp [conceptFormationWidthComplementITV,
          conceptFormationWidthComplementITVSource,
          ProjectiveCredalWidthComplementITVSource.finite, Spec, X]
      _ = Spec.globalNaturalExtension X := by rw [← hLowerUpper]
      _ = P X := hNE
  · calc
      (conceptFormationWidthComplementITV S Γ σ A).width =
          Spec.globalEnvelopeWidth X := by
        simp [conceptFormationWidthComplementITV,
          conceptFormationWidthComplementITVSource,
          ProjectiveCredalWidthComplementITVSource.finite, Spec, X]
      _ = 0 := hWidth
  · calc
      (conceptFormationWidthComplementITV S Γ σ A).credibility =
          Spec.globalEnvelopeWidthComplement X := by
        simp [conceptFormationWidthComplementITV,
          conceptFormationWidthComplementITVSource,
          ProjectiveCredalWidthComplementITVSource.finite, Spec, X]
      _ = 1 := hCred
  · calc
      (conceptFormationWidthComplementITV S Γ σ A).strength =
          Spec.globalEnvelopeMidpoint X := by
        simp [conceptFormationWidthComplementITV,
          conceptFormationWidthComplementITVSource,
          ProjectiveCredalWidthComplementITVSource.finite, Spec, X]
      _ = P X := hMid

/-- Typed counterpart of
`conceptFormationWidthComplementITV_preciseCompletionReadout_of_determines`.
Under finite-gate determination, the typed PLN ITV endpoints and midpoint all
read the same compatible precise-completion value. -/
theorem conceptFormationTypedWidthComplementITV_preciseCompletionReadout_of_determines
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr)
    (P : PrecisePrevision Gate)
    (hP :
      P ∈ (gateCredalProjectiveSpec (Gate := Gate)).projectiveLimitCredalSet)
    (hDet :
      (gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (ObservationSurface.conceptFormationGamble S Γ σ A)) :
    (conceptFormationTypedWidthComplementITV S Γ σ A).lower =
        P (ObservationSurface.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).upper =
        P (ObservationSurface.conceptFormationGamble S Γ σ A) ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).width = 0 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 1 ∧
      (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint =
        P (ObservationSurface.conceptFormationGamble S Γ σ A) := by
  let Spec := gateCredalProjectiveSpec (Gate := Gate)
  let X := ObservationSurface.conceptFormationGamble S Γ σ A
  have hBddBelow :
      BddBelow ((fun P' : PrecisePrevision Gate => P' X) ''
        Spec.projectiveLimitCredalSet) :=
    finite_credalRange_bddBelow Spec.projectiveLimitCredalSet X
  have hBddAbove :
      BddAbove ((fun P' : PrecisePrevision Gate => P' X) ''
        Spec.projectiveLimitCredalSet) :=
    finite_credalRange_bddAbove Spec.projectiveLimitCredalSet X
  have hNE : Spec.globalNaturalExtension X = P X :=
    Spec.globalNaturalExtension_eq_of_determines
      (gateCredalProjectiveSpec_hasCompatibleCompletion (Gate := Gate))
      X hBddBelow hP hDet
  have hWidth : Spec.globalEnvelopeWidth X = 0 :=
    Spec.globalEnvelopeWidth_eq_zero_of_determines
      (gateCredalProjectiveSpec_hasCompatibleCompletion (Gate := Gate))
      X hBddBelow hBddAbove hP hDet
  have hMid : Spec.globalEnvelopeMidpoint X = P X :=
    Spec.globalEnvelopeMidpoint_eq_of_determines
      (gateCredalProjectiveSpec_hasCompatibleCompletion (Gate := Gate))
      X hBddBelow hBddAbove hP hDet
  have hCred : Spec.globalEnvelopeWidthComplement X = 1 := by
    unfold ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement
    unfold ProjectiveLocalCredalSpec.globalEnvelopeWidth at hWidth
    unfold credalEnvelopeWidthComplement
    rw [hWidth]
    norm_num
  have hLowerUpper :
      Spec.globalNaturalExtension X =
        upperEnvelope Spec.projectiveLimitCredalSet X :=
    Spec.globalLowerUpperEnvelope_eq_of_determines
      (gateCredalProjectiveSpec_hasCompatibleCompletion (Gate := Gate))
      X hBddBelow hBddAbove hP hDet
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc
      (conceptFormationTypedWidthComplementITV S Γ σ A).lower =
          Spec.globalNaturalExtension X := by
        simp [conceptFormationTypedWidthComplementITV,
          conceptFormationWidthComplementITVSource,
          ProjectiveCredalWidthComplementITVSource.finite, Spec, X]
      _ = P X := hNE
  · calc
      (conceptFormationTypedWidthComplementITV S Γ σ A).upper =
          upperEnvelope Spec.projectiveLimitCredalSet X := by
        simp [conceptFormationTypedWidthComplementITV,
          conceptFormationWidthComplementITVSource,
          ProjectiveCredalWidthComplementITVSource.finite, Spec, X]
      _ = Spec.globalNaturalExtension X := by rw [← hLowerUpper]
      _ = P X := hNE
  · calc
      (conceptFormationTypedWidthComplementITV S Γ σ A).width =
          Spec.globalEnvelopeWidth X := by
        simp [conceptFormationTypedWidthComplementITV,
          conceptFormationWidthComplementITVSource,
          ProjectiveCredalWidthComplementITVSource.finite, Spec, X]
      _ = 0 := hWidth
  · calc
      (conceptFormationTypedWidthComplementITV S Γ σ A).credibility =
          Spec.globalEnvelopeWidthComplement X := by
        simp [conceptFormationTypedWidthComplementITV,
          conceptFormationWidthComplementITVSource,
          ProjectiveCredalWidthComplementITVSource.finite, Spec, X]
      _ = 1 := hCred
  · calc
      (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint =
          Spec.globalEnvelopeMidpoint X := by
        simp [conceptFormationTypedWidthComplementITV,
          conceptFormationWidthComplementITVSource,
          ProjectiveCredalWidthComplementITVSource.finite, Spec, X]
      _ = P X := hMid

end ObservationSurface

/-! ## Proof-carrying profile -/

/-- Compact profile for the finite/projective PLN ITV readout of credal concept
formation.  This packages the bridge as one citation handle while keeping the
finite-gate boundary explicit. -/
structure ConceptFormationITVBridgeProfile where
  untypedReadout :
    ∀ {Obs Obj Attr Q Gate : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Gate] [Nonempty Gate] [Fintype Obj] [Fintype Attr],
      (S : ObservationSurface Obs Obj Attr Q) →
      (Γ : Gate → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      ((conceptFormationWidthComplementITV S Γ σ A).lower =
          if A ∈ ObservationSurface.lowerConceptFamily S Γ σ then 1 else 0) ∧
        ((conceptFormationWidthComplementITV S Γ σ A).upper =
          if A ∈ ObservationSurface.upperConceptFamily S Γ σ then 1 else 0) ∧
        ((conceptFormationWidthComplementITV S Γ σ A).width =
          if A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
              A ∉ ObservationSurface.lowerConceptFamily S Γ σ then 1 else 0) ∧
        ((conceptFormationWidthComplementITV S Γ σ A).credibility =
          if A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
              A ∉ ObservationSurface.lowerConceptFamily S Γ σ then 0 else 1) ∧
        ((conceptFormationWidthComplementITV S Γ σ A).strength =
          if A ∈ ObservationSurface.lowerConceptFamily S Γ σ then 1
          else if A ∈ ObservationSurface.upperConceptFamily S Γ σ then (1 / 2 : ℝ) else 0)
  typedReadout :
    ∀ {Obs Obj Attr Q Gate : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Gate] [Nonempty Gate] [Fintype Obj] [Fintype Attr],
      (S : ObservationSurface Obs Obj Attr Q) →
      (Γ : Gate → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      ((conceptFormationTypedWidthComplementITV S Γ σ A).lower =
          if A ∈ ObservationSurface.lowerConceptFamily S Γ σ then 1 else 0) ∧
        ((conceptFormationTypedWidthComplementITV S Γ σ A).upper =
          if A ∈ ObservationSurface.upperConceptFamily S Γ σ then 1 else 0) ∧
        ((conceptFormationTypedWidthComplementITV S Γ σ A).width =
          if A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
              A ∉ ObservationSurface.lowerConceptFamily S Γ σ then 1 else 0) ∧
        ((conceptFormationTypedWidthComplementITV S Γ σ A).credibility =
          if A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
              A ∉ ObservationSurface.lowerConceptFamily S Γ σ then 0 else 1) ∧
        ((conceptFormationTypedWidthComplementITV S Γ σ A).midpoint =
          if A ∈ ObservationSurface.lowerConceptFamily S Γ σ then 1
          else if A ∈ ObservationSurface.upperConceptFamily S Γ σ then (1 / 2 : ℝ) else 0)
  widthAddCredibility :
    ∀ {Obs Obj Attr Q Gate : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Gate] [Nonempty Gate] [Fintype Obj] [Fintype Attr],
      (S : ObservationSurface Obs Obj Attr Q) →
      (Γ : Gate → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (conceptFormationWidthComplementITV S Γ σ A).width +
          (conceptFormationWidthComplementITV S Γ σ A).credibility = 1
  untypedExactOfDetermines :
    ∀ {Obs Obj Attr Q Gate : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Gate] [Nonempty Gate] [Fintype Obj] [Fintype Attr],
      (S : ObservationSurface Obs Obj Attr Q) →
      (Γ : Gate → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (hDet :
        (gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (ObservationSurface.conceptFormationGamble S Γ σ A)) →
      (conceptFormationWidthComplementITV S Γ σ A).lower =
          (conceptFormationWidthComplementITV S Γ σ A).upper ∧
        (conceptFormationWidthComplementITV S Γ σ A).width = 0 ∧
        (conceptFormationWidthComplementITV S Γ σ A).credibility = 1 ∧
        (conceptFormationWidthComplementITV S Γ σ A).strength =
          (conceptFormationWidthComplementITV S Γ σ A).lower
  typedExactOfDetermines :
    ∀ {Obs Obj Attr Q Gate : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Gate] [Nonempty Gate] [Fintype Obj] [Fintype Attr],
      (S : ObservationSurface Obs Obj Attr Q) →
      (Γ : Gate → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (hDet :
        (gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (ObservationSurface.conceptFormationGamble S Γ σ A)) →
      (conceptFormationTypedWidthComplementITV S Γ σ A).lower =
          (conceptFormationTypedWidthComplementITV S Γ σ A).upper ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).width = 0 ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 1 ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint =
          (conceptFormationTypedWidthComplementITV S Γ σ A).lower
  untypedExactIffNoGap :
    ∀ {Obs Obj Attr Q Gate : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Gate] [Nonempty Gate] [Fintype Obj] [Fintype Attr],
      (S : ObservationSurface Obs Obj Attr Q) →
      (Γ : Gate → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      ((conceptFormationWidthComplementITV S Γ σ A).lower =
          (conceptFormationWidthComplementITV S Γ σ A).upper ∧
        (conceptFormationWidthComplementITV S Γ σ A).width = 0 ∧
        (conceptFormationWidthComplementITV S Γ σ A).credibility = 1 ∧
        (conceptFormationWidthComplementITV S Γ σ A).strength =
          (conceptFormationWidthComplementITV S Γ σ A).lower) ↔
        ¬ (A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
          A ∉ ObservationSurface.lowerConceptFamily S Γ σ)
  typedExactIffNoGap :
    ∀ {Obs Obj Attr Q Gate : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Gate] [Nonempty Gate] [Fintype Obj] [Fintype Attr],
      (S : ObservationSurface Obs Obj Attr Q) →
      (Γ : Gate → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      ((conceptFormationTypedWidthComplementITV S Γ σ A).lower =
          (conceptFormationTypedWidthComplementITV S Γ σ A).upper ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).width = 0 ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 1 ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint =
          (conceptFormationTypedWidthComplementITV S Γ σ A).lower) ↔
        ¬ (A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
          A ∉ ObservationSurface.lowerConceptFamily S Γ σ)
  untypedFullReadoutIffGap :
    ∀ {Obs Obj Attr Q Gate : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Gate] [Nonempty Gate] [Fintype Obj] [Fintype Attr],
      (S : ObservationSurface Obs Obj Attr Q) →
      (Γ : Gate → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      ((conceptFormationWidthComplementITV S Γ σ A).lower = 0 ∧
        (conceptFormationWidthComplementITV S Γ σ A).upper = 1 ∧
        (conceptFormationWidthComplementITV S Γ σ A).width = 1 ∧
        (conceptFormationWidthComplementITV S Γ σ A).credibility = 0 ∧
        (conceptFormationWidthComplementITV S Γ σ A).strength = (1 / 2 : ℝ)) ↔
        A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
          A ∉ ObservationSurface.lowerConceptFamily S Γ σ
  typedFullReadoutIffGap :
    ∀ {Obs Obj Attr Q Gate : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Gate] [Nonempty Gate] [Fintype Obj] [Fintype Attr],
      (S : ObservationSurface Obs Obj Attr Q) →
      (Γ : Gate → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      ((conceptFormationTypedWidthComplementITV S Γ σ A).lower = 0 ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).upper = 1 ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).width = 1 ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 0 ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint =
          (1 / 2 : ℝ)) ↔
        A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
          A ∉ ObservationSurface.lowerConceptFamily S Γ σ
  untypedWidthPosIffGap :
    ∀ {Obs Obj Attr Q Gate : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Gate] [Nonempty Gate] [Fintype Obj] [Fintype Attr],
      (S : ObservationSurface Obs Obj Attr Q) →
      (Γ : Gate → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (0 < (conceptFormationWidthComplementITV S Γ σ A).width ∧
        (conceptFormationWidthComplementITV S Γ σ A).credibility < 1) ↔
        A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
          A ∉ ObservationSurface.lowerConceptFamily S Γ σ
  typedWidthPosIffGap :
    ∀ {Obs Obj Attr Q Gate : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Gate] [Nonempty Gate] [Fintype Obj] [Fintype Attr],
      (S : ObservationSurface Obs Obj Attr Q) →
      (Γ : Gate → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (0 < (conceptFormationTypedWidthComplementITV S Γ σ A).width ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).credibility < 1) ↔
        A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
          A ∉ ObservationSurface.lowerConceptFamily S Γ σ
  untypedGapReadout :
    ∀ {Obs Obj Attr Q Gate : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Gate] [Nonempty Gate] [Fintype Obj] [Fintype Attr],
      (S : ObservationSurface Obs Obj Attr Q) →
      (Γ : Gate → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (hGap :
        A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
          A ∉ ObservationSurface.lowerConceptFamily S Γ σ) →
      (conceptFormationWidthComplementITV S Γ σ A).lower = 0 ∧
        (conceptFormationWidthComplementITV S Γ σ A).upper = 1 ∧
        (conceptFormationWidthComplementITV S Γ σ A).width = 1 ∧
        (conceptFormationWidthComplementITV S Γ σ A).credibility = 0 ∧
        (conceptFormationWidthComplementITV S Γ σ A).strength = (1 / 2 : ℝ)
  typedGapReadout :
    ∀ {Obs Obj Attr Q Gate : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Gate] [Nonempty Gate] [Fintype Obj] [Fintype Attr],
      (S : ObservationSurface Obs Obj Attr Q) →
      (Γ : Gate → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (hGap :
        A ∈ ObservationSurface.upperConceptFamily S Γ σ ∧
          A ∉ ObservationSurface.lowerConceptFamily S Γ σ) →
      (conceptFormationTypedWidthComplementITV S Γ σ A).lower = 0 ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).upper = 1 ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).width = 1 ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 0 ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint = (1 / 2 : ℝ)
  untypedPreciseCompletionReadoutOfDetermines :
    ∀ {Obs Obj Attr Q Gate : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Gate] [Nonempty Gate] [Fintype Obj] [Fintype Attr],
      (S : ObservationSurface Obs Obj Attr Q) →
      (Γ : Gate → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (P : PrecisePrevision Gate) →
      P ∈ (gateCredalProjectiveSpec (Gate := Gate)).projectiveLimitCredalSet →
      (hDet :
        (gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (ObservationSurface.conceptFormationGamble S Γ σ A)) →
      (conceptFormationWidthComplementITV S Γ σ A).lower =
          P (ObservationSurface.conceptFormationGamble S Γ σ A) ∧
        (conceptFormationWidthComplementITV S Γ σ A).upper =
          P (ObservationSurface.conceptFormationGamble S Γ σ A) ∧
        (conceptFormationWidthComplementITV S Γ σ A).width = 0 ∧
        (conceptFormationWidthComplementITV S Γ σ A).credibility = 1 ∧
        (conceptFormationWidthComplementITV S Γ σ A).strength =
          P (ObservationSurface.conceptFormationGamble S Γ σ A)
  typedPreciseCompletionReadoutOfDetermines :
    ∀ {Obs Obj Attr Q Gate : Type} [AddCommMonoid Q] [Preorder Q]
      [Fintype Gate] [Nonempty Gate] [Fintype Obj] [Fintype Attr],
      (S : ObservationSurface Obs Obj Attr Q) →
      (Γ : Gate → EvidenceGate Q) → (σ : Multiset Obs) →
      (A : DualConcept Obj Attr) →
      (P : PrecisePrevision Gate) →
      P ∈ (gateCredalProjectiveSpec (Gate := Gate)).projectiveLimitCredalSet →
      (hDet :
        (gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (ObservationSurface.conceptFormationGamble S Γ σ A)) →
      (conceptFormationTypedWidthComplementITV S Γ σ A).lower =
          P (ObservationSurface.conceptFormationGamble S Γ σ A) ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).upper =
          P (ObservationSurface.conceptFormationGamble S Γ σ A) ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).width = 0 ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).credibility = 1 ∧
        (conceptFormationTypedWidthComplementITV S Γ σ A).midpoint =
          P (ObservationSurface.conceptFormationGamble S Γ σ A)

/-- Public profile for the finite/projective PLN ITV bridge over credal concept
formation. -/
noncomputable def conceptFormationITVBridgeProfile :
    ConceptFormationITVBridgeProfile where
  untypedReadout := conceptFormationWidthComplementITV_readout
  typedReadout := conceptFormationTypedWidthComplementITV_readout
  widthAddCredibility := conceptFormationWidthComplementITV_width_add_credibility
  untypedExactOfDetermines := conceptFormationWidthComplementITV_exact_of_determines
  typedExactOfDetermines := conceptFormationTypedWidthComplementITV_exact_of_determines
  untypedExactIffNoGap := conceptFormationWidthComplementITV_exact_iff_noGap
  typedExactIffNoGap := conceptFormationTypedWidthComplementITV_exact_iff_noGap
  untypedFullReadoutIffGap := conceptFormationWidthComplementITV_fullReadout_iff_gap
  typedFullReadoutIffGap := conceptFormationTypedWidthComplementITV_fullReadout_iff_gap
  untypedWidthPosIffGap := conceptFormationWidthComplementITV_width_pos_iff_gap
  typedWidthPosIffGap := conceptFormationTypedWidthComplementITV_width_pos_iff_gap
  untypedGapReadout := conceptFormationWidthComplementITV_gap_readout
  typedGapReadout := conceptFormationTypedWidthComplementITV_gap_readout
  untypedPreciseCompletionReadoutOfDetermines :=
    conceptFormationWidthComplementITV_preciseCompletionReadout_of_determines
  typedPreciseCompletionReadoutOfDetermines :=
    conceptFormationTypedWidthComplementITV_preciseCompletionReadout_of_determines

end Mettapedia.PLN.Bridges.KR.ConceptFormationITVBridge
