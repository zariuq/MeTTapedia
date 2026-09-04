import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedDerivationSoundness
import Mettapedia.OSLF.Framework.SelectedNativeTypeDemandImage

/-!
# Selected-image adequacy for the PeTTa call-guard native calculus

The complete call-guard demand selects exactly two profiled endpoints for
each authored cold rewrite root.  This module identifies that finite semantic
coordinate with exact demand positions and the generated formation and
introduction rows.

Representability here is intentionally proof relevant: a witness retains the
exact selected position.  It is not the false claim that every fact in an
arbitrary external carrier model has a closed generated derivation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSelectedAdequacy

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeDemand
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedSemanticDecoding
open Mettapedia.OSLF.Framework.SelectedNativeTypeDisplayedSemantics
open Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedIntroduction
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileFormationSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileIntroductionSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedModel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedDerivationSoundness

/-- Mathematical coordinate of the selected image: one authored cold root
and one of its two constant universe endpoints. -/
structure RootEndpoint where
  root : Fin coldSource.language.rewrites.length
  code : CarrierUniverseSignature.Code
deriving DecidableEq

/-- The intrinsically typed and grounded occurrence denoted by one endpoint
coordinate. -/
def RootEndpoint.occurrence (endpoint : RootEndpoint) :
    ProfiledRewriteOccurrence coldSource :=
  profiledRoot endpoint.root endpoint.code

/-- Every selected root has one local profile slot, so its complete profile
wire is the singleton containing its endpoint code. -/
@[simp] theorem profiledRoot_choices
    (root : Fin coldSource.language.rewrites.length)
    (code : CarrierUniverseSignature.Code) :
    (profiledRoot root code).choices = [code] := by
  fin_cases root <;> cases code <;> rfl

/-- The full call-guard demand represents every authored root at both star
and box.  The witness retains the exact list occurrence selected by the
generator. -/
theorem fullDemand_representable (endpoint : RootEndpoint) :
    Representable demand endpoint.occurrence := by
  rw [representable_iff_mem]
  rcases endpoint with ⟨root, code⟩
  change profiledRoot root code ∈ selectedOccurrences
  rw [selectedOccurrences, List.mem_flatMap]
  refine ⟨root, List.mem_finRange root, ?_⟩
  cases code <;> simp

/-- Coverage contract required by source-to-typed admission: every authored
root is represented at both selected universe endpoints. -/
def CoversEveryRootEndpoint
    (candidate : SelectedNativeTypeDemand coldSource) : Prop :=
  ∀ endpoint : RootEndpoint, Representable candidate endpoint.occurrence

/-- The qualified call-guard demand satisfies the complete selected-image
coverage contract. -/
theorem fullDemand_coversEveryRootEndpoint :
    CoversEveryRootEndpoint demand :=
  fullDemand_representable

/-- Conversely, every position in the full demand comes from an exact
authored-root/endpoint coordinate.  Thus the selected list invents no third
kind of profiled occurrence. -/
theorem selectedSlot_has_rootEndpoint
    (slot : SelectedNativeTypeContextualCalculus.Occurrence demand) :
    ∃ endpoint : RootEndpoint,
      occurrenceAt demand slot = endpoint.occurrence := by
  have membership : occurrenceAt demand slot ∈ selectedOccurrences := by
    change demand.occurrences.get slot ∈ demand.occurrences
    exact List.get_mem demand.occurrences slot
  rw [selectedOccurrences, List.mem_flatMap] at membership
  obtain ⟨root, _rootMembership, pairMembership⟩ := membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at pairMembership
  rcases pairMembership with starExact | boxExact
  · exact ⟨⟨root, .star⟩, starExact⟩
  · exact ⟨⟨root, .box⟩, boxExact⟩

/-- One selected endpoint is represented not only in the demand, but by the
exact formation and guarded-introduction rows stored in the validated
generated calculus. -/
structure GeneratedEndpointRepresentation (endpoint : RootEndpoint) where
  slot : SelectedNativeTypeContextualCalculus.Occurrence demand
  occurrenceExact : occurrenceAt demand slot = endpoint.occurrence
  formationLookup :
    generated.1.lookupRule?
        (ContextualInference.lowerRule
          (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
            demand slot)).id =
      some (ContextualInference.lowerRule
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
          demand slot))
  introductionLookup :
    generated.1.lookupRule?
        (ContextualInference.lowerRule
          (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
            guardProfile slot)).id =
      some (ContextualInference.lowerRule
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
          guardProfile slot))

/-- All thirty intended endpoint coordinates have exact generated formation
and introduction rows. -/
theorem generatedEndpoint_representable (endpoint : RootEndpoint) :
    Nonempty (GeneratedEndpointRepresentation endpoint) := by
  obtain ⟨representation⟩ := fullDemand_representable endpoint
  exact ⟨
    { slot := representation.slot
      occurrenceExact := representation.occurrenceExact
      formationLookup := generated_formationRule_lookup representation.slot
      introductionLookup :=
        generated_introductionRule_lookup representation.slot }
  ⟩

/-- The modal constructor attached to a represented endpoint is recognized by
the fail-closed generated syntax decoder at that exact occurrence position. -/
theorem selectedEndpoint_modal_representable (endpoint : RootEndpoint)
    (family : Pattern) :
    ∃ representation : GeneratedEndpointRepresentation endpoint,
      decodeApplication? demand
          (modalType demand representation.slot family) =
        some
          ({ head := .modal representation.slot
             arguments := [family] } : ApplicationView demand) := by
  obtain ⟨representation⟩ := generatedEndpoint_representable endpoint
  exact ⟨representation,
    decodeApplication_modalType representation.slot family⟩

/-- Canonical generated judgment asserting membership in the modal former at
one exact selected occurrence. -/
def modalMembershipJudgment
    (slot : SelectedNativeTypeContextualCalculus.Occurrence demand)
    (variableContext relationContext : ContextSchema)
    (focus family : Pattern) : Pattern :=
  encodeGeneratedSequent
    { variableContext
      relationContext
      conclusion := .typingClaim (focusCarrier slot) focus
        (modalType demand slot family) }

@[simp] theorem decode_modalMembershipJudgment
    (slot : SelectedNativeTypeContextualCalculus.Occurrence demand)
    (variableContext relationContext : ContextSchema)
    (focus family : Pattern) :
    decodeGeneratedSequent? demand
        (modalMembershipJudgment slot variableContext relationContext
          focus family) =
      some
        { variableContext
          relationContext
          conclusion := .typingClaim (focusCarrier slot) focus
            (modalType demand slot family) } := by
  simp [modalMembershipJudgment]

/-- Covered reflection for any successfully decoded generated judgment: the
decoder reconstructs the exact wire, while arbitrary-derivation soundness
supplies its independently defined displayed meaning. -/
theorem generated_derivation_decoded_reflection
    (model : CarrierModel) {goal : Pattern}
    (derivation : Derivation generated goal)
    {view : GeneratedSequentView demand}
    (decoded : decodeGeneratedSequent? demand goal = some view) :
    encodeGeneratedSequent view = goal ∧
      JudgmentMeaning model (encodeGeneratedSequent view) := by
  have wireExact :=
    encodeGeneratedSequent_of_decodeGeneratedSequent?_eq_some decoded
  refine ⟨wireExact, ?_⟩
  rw [wireExact]
  exact generated_derivation_sound model derivation

/-- No-invention crown for the selected modal image.  A derivation of a
selected modal-membership judgment has independent meaning and its occurrence
comes from one exact authored root and endpoint code. -/
theorem generated_modalDerivation_no_invention
    (model : CarrierModel)
    (slot : SelectedNativeTypeContextualCalculus.Occurrence demand)
    (variableContext relationContext : ContextSchema)
    (focus family : Pattern)
    (derivation : Derivation generated
      (modalMembershipJudgment slot variableContext relationContext
        focus family)) :
    ∃ endpoint : RootEndpoint,
      occurrenceAt demand slot = endpoint.occurrence ∧
        JudgmentMeaning model
          (modalMembershipJudgment slot variableContext relationContext
            focus family) := by
  obtain ⟨endpoint, occurrenceExact⟩ := selectedSlot_has_rootEndpoint slot
  exact ⟨endpoint, occurrenceExact,
    generated_derivation_sound model derivation⟩

/-! ## Negative profile and stale-wire controls -/

/-- Every box endpoint remains intrinsically well formed—its record contains
the exact root typing and grounding proof—but the all-star profile does not
represent it. -/
theorem allStar_omits_box
    (root : Fin coldSource.language.rewrites.length) :
    ¬ Representable allStarDemand (profiledRoot root .box) := by
  rw [representable_iff_mem]
  intro membership
  change profiledRoot root .box ∈ allStarOccurrences at membership
  rw [allStarOccurrences] at membership
  obtain ⟨otherRoot, _otherMembership, occurrenceExact⟩ :=
    List.mem_map.mp membership
  have choicesExact :=
    congrArg ProfiledRewriteOccurrence.choices occurrenceExact
  simp only [profiledRoot_choices] at choicesExact
  cases choicesExact

/-- Removing the selected box endpoints invalidates the coverage contract
used by source-to-typed admission. -/
theorem allStar_not_coversEveryRootEndpoint :
    ¬ CoversEveryRootEndpoint allStarDemand := by
  intro coverage
  exact allStar_omits_box ⟨0, by decide⟩
    (coverage ⟨⟨0, by decide⟩, .box⟩)

/-- The second full-demand slot is the box endpoint of the first authored
root. -/
private def fullFirstBox :
    SelectedNativeTypeContextualCalculus.Occurrence demand :=
  ⟨1, by
    change 1 < selectedOccurrences.length
    rw [selectedOccurrences_count]
    omega⟩

/-- The second all-star slot is instead the star endpoint of the second
authored root. -/
private def allStarSecondStar :
    SelectedNativeTypeContextualCalculus.Occurrence allStarDemand :=
  ⟨1, by
    change 1 < allStarOccurrences.length
    rw [allStarOccurrences_count]
    omega⟩

/-- Positional labels alone can alias across two different demand profiles.
Artifact identity must therefore retain the generating demand. -/
theorem positional_modal_labels_alias :
    encodeHead (.modal fullFirstBox) =
      encodeHead (.modal allStarSecondStar) :=
  rfl

private theorem fullFirstBox_exact :
    occurrenceAt demand fullFirstBox =
      profiledRoot ⟨0, by decide⟩ .box :=
  rfl

private theorem allStarSecondStar_exact :
    occurrenceAt allStarDemand allStarSecondStar =
      profiledRoot ⟨1, by decide⟩ .star :=
  rfl

/-- The aliased raw labels denote distinct profiled occurrences when decoded
under their respective demands.  Demand-indexed decoding prevents the alias
from becoming semantic identity. -/
theorem positional_alias_semantics_distinct :
    occurrenceAt demand fullFirstBox ≠
      occurrenceAt allStarDemand allStarSecondStar := by
  rw [fullFirstBox_exact, allStarSecondStar_exact]
  intro occurrenceExact
  have choicesExact :=
    congrArg ProfiledRewriteOccurrence.choices occurrenceExact
  simp only [profiledRoot_choices] at choicesExact
  cases choicesExact

#print axioms profiledRoot_choices
#print axioms fullDemand_representable
#print axioms fullDemand_coversEveryRootEndpoint
#print axioms selectedSlot_has_rootEndpoint
#print axioms generatedEndpoint_representable
#print axioms selectedEndpoint_modal_representable
#print axioms generated_derivation_decoded_reflection
#print axioms generated_modalDerivation_no_invention
#print axioms allStar_omits_box
#print axioms allStar_not_coversEveryRootEndpoint
#print axioms positional_modal_labels_alias
#print axioms positional_alias_semantics_distinct

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSelectedAdequacy
