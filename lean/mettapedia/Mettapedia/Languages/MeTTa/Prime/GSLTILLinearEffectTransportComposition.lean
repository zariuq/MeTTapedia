import Mettapedia.Languages.MeTTa.Prime.GSLTILInteractionTransportComposition
import Mettapedia.Languages.MeTTa.Prime.GSLTILLinearEffectTransport

/-!
# Composition laws for GSLT-IL linear-effect transport

Interaction transport already composes at the proof-relevant event and path
levels.  Linear effects obey the same law: mapping twice is mapping once by the
composite site and resource maps.  Successive occurrence transport retains two
provenance wrappers, while composite transport retains one; an explicit
equivalence removes or restores exactly that wrapper and no occurrence data.

These laws make resource separation stable under a pipeline of represented
language routes.  They do not infer a target execution or a parallel schedule:
those remain capabilities supplied by the target language.
-/

namespace Mettapedia.Languages.MeTTa.Prime.GSLTILLinearEffectTransportComposition

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Languages.MeTTa.Prime.GSLTILInteractionTransport
open Mettapedia.Languages.MeTTa.Prime.GSLTILInteractionTransportComposition
open Mettapedia.Languages.MeTTa.Prime.GSLTILLinearEffectTransport
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionEffectAnalysis

universe uSite₀ uSite₁ uSite₂ uResource₀ uResource₁ uResource₂ uEvent

/-! ## Algebraic identity and composition -/

@[simp] theorem mapLinearEffect_id
    {Site : Type uSite₀} {Resource : Type uResource₀}
    (effect : LinearEffect Site Resource) :
    mapLinearEffect id id effect = effect := by
  cases effect
  simp [mapLinearEffect]

@[simp] theorem mapLinearEffect_comp
    {Site₀ : Type uSite₀} {Site₁ : Type uSite₁} {Site₂ : Type uSite₂}
    {Resource₀ : Type uResource₀} {Resource₁ : Type uResource₁}
    {Resource₂ : Type uResource₂}
    (firstSite : Site₀ → Site₁) (secondSite : Site₁ → Site₂)
    (firstResource : Resource₀ → Resource₁)
    (secondResource : Resource₁ → Resource₂)
    (effect : LinearEffect Site₀ Resource₀) :
    mapLinearEffect secondSite secondResource
        (mapLinearEffect firstSite firstResource effect) =
      mapLinearEffect (secondSite ∘ firstSite)
        (secondResource ∘ firstResource) effect := by
  cases effect
  simp [mapLinearEffect, Multiset.map_map]

theorem mapPairSeparation_comp_data
    {Site₀ : Type uSite₀} {Site₁ : Type uSite₁} {Site₂ : Type uSite₂}
    {Resource₀ : Type uResource₀} {Resource₁ : Type uResource₁}
    {Resource₂ : Type uResource₂}
    (firstSite : Site₀ → Site₁) (secondSite : Site₁ → Site₂)
    (firstResource : Resource₀ → Resource₁)
    (secondResource : Resource₁ → Resource₂)
    {source : Multiset Resource₀}
    {left right : LinearEffect Site₀ Resource₀}
    (separation : PairSeparation source left right) :
    (mapPairSeparation secondSite secondResource
        (mapPairSeparation firstSite firstResource separation)).frame =
        (mapPairSeparation (secondSite ∘ firstSite)
          (secondResource ∘ firstResource) separation).frame ∧
      (source.map firstResource).map secondResource =
        source.map (secondResource ∘ firstResource) := by
  constructor <;> simp [mapPairSeparation, Multiset.map_map]

/-! ## Proof-relevant occurrence composition -/

/-- Flatten the two provenance wrappers of successive occurrence transport. -/
def flattenTransportedOccurrence
    {first middle last : GSLT}
    (earlier : OperationalTranslation first middle)
    (later : OperationalTranslation middle last)
    (presentation : InteractionPresentation.{uSite₀, uEvent} first) :
    Occurrence (transportedPresentation later
      (transportedPresentation earlier presentation)) →
      Occurrence (transportedPresentation
        (OperationalTranslation.comp earlier later) presentation)
  | ⟨_, ⟨site, _, .ofSource (.ofSource evidence)⟩⟩ =>
      ⟨_, ⟨site, _, .ofSource evidence⟩⟩

/-- Restore the two provenance wrappers of successive occurrence transport. -/
def expandTransportedOccurrence
    {first middle last : GSLT}
    (earlier : OperationalTranslation first middle)
    (later : OperationalTranslation middle last)
    (presentation : InteractionPresentation.{uSite₀, uEvent} first) :
    Occurrence (transportedPresentation
      (OperationalTranslation.comp earlier later) presentation) →
      Occurrence (transportedPresentation later
        (transportedPresentation earlier presentation))
  | ⟨_, ⟨site, _, .ofSource evidence⟩⟩ =>
      ⟨_, ⟨site, _, .ofSource (.ofSource evidence)⟩⟩

/-- Successive and composite occurrence transport retain exactly equivalent
source sites, endpoints, and event evidence. -/
def transportedOccurrenceCompEquiv
    {first middle last : GSLT}
    (earlier : OperationalTranslation first middle)
    (later : OperationalTranslation middle last)
    (presentation : InteractionPresentation.{uSite₀, uEvent} first) :
    Occurrence (transportedPresentation later
      (transportedPresentation earlier presentation)) ≃
      Occurrence (transportedPresentation
        (OperationalTranslation.comp earlier later) presentation) where
  toFun := flattenTransportedOccurrence earlier later presentation
  invFun := expandTransportedOccurrence earlier later presentation
  left_inv := by
    intro occurrence
    obtain ⟨source, enabled⟩ := occurrence
    obtain ⟨site, target, event⟩ := enabled
    cases event with
    | ofSource inner => cases inner; rfl
  right_inv := by
    intro occurrence
    obtain ⟨source, enabled⟩ := occurrence
    obtain ⟨site, target, event⟩ := enabled
    cases event
    rfl

@[simp] theorem flatten_transportOccurrence_twice
    {first middle last : GSLT}
    (earlier : OperationalTranslation first middle)
    (later : OperationalTranslation middle last)
    (presentation : InteractionPresentation.{uSite₀, uEvent} first)
    (occurrence : Occurrence presentation) :
    flattenTransportedOccurrence earlier later presentation
        (transportOccurrence later (transportedPresentation earlier presentation)
          (transportOccurrence earlier presentation occurrence)) =
      transportOccurrence (OperationalTranslation.comp earlier later)
        presentation occurrence := by
  obtain ⟨source, enabled⟩ := occurrence
  obtain ⟨site, target, evidence⟩ := enabled
  rfl

@[simp] theorem sourceOccurrence_flatten
    {first middle last : GSLT}
    (earlier : OperationalTranslation first middle)
    (later : OperationalTranslation middle last)
    (presentation : InteractionPresentation.{uSite₀, uEvent} first)
    (occurrence : Occurrence (transportedPresentation later
      (transportedPresentation earlier presentation))) :
    sourceOccurrence (OperationalTranslation.comp earlier later) presentation
        (flattenTransportedOccurrence earlier later presentation occurrence) =
      sourceOccurrence earlier presentation
        (sourceOccurrence later (transportedPresentation earlier presentation)
          occurrence) := by
  obtain ⟨source, enabled⟩ := occurrence
  obtain ⟨site, target, event⟩ := enabled
  cases event with
  | ofSource inner => cases inner; rfl

/-! ## Effect analyses compose through the occurrence equivalence -/

@[simp] theorem transportedEffectAnalysis_comp
    {first middle last : GSLT}
    (earlier : OperationalTranslation first middle)
    (later : OperationalTranslation middle last)
    (presentation : InteractionPresentation.{uSite₀, uEvent} first)
    {Resource₀ : Type uResource₀} {Resource₁ : Type uResource₁}
    {Resource₂ : Type uResource₂}
    (analysis : OccurrenceEffectAnalysis presentation Resource₀)
    (firstResource : Resource₀ → Resource₁)
    (secondResource : Resource₁ → Resource₂)
    (occurrence : Occurrence (transportedPresentation later
      (transportedPresentation earlier presentation))) :
    (transportedEffectAnalysis later
        (transportedPresentation earlier presentation)
        (transportedEffectAnalysis earlier presentation analysis firstResource)
        secondResource).effect occurrence =
      (transportedEffectAnalysis (OperationalTranslation.comp earlier later)
        presentation analysis (secondResource ∘ firstResource)).effect
          (flattenTransportedOccurrence earlier later presentation occurrence) := by
  change mapLinearEffect id secondResource
      (mapLinearEffect id firstResource
        (analysis.effect
          (sourceOccurrence earlier presentation
            (sourceOccurrence later (transportedPresentation earlier presentation)
              occurrence)))) =
    mapLinearEffect id (secondResource ∘ firstResource)
      (analysis.effect
        (sourceOccurrence (OperationalTranslation.comp earlier later)
          presentation
          (flattenTransportedOccurrence earlier later presentation occurrence)))
  rw [sourceOccurrence_flatten]
  exact mapLinearEffect_comp id id firstResource secondResource _

/-! ## Negative reflection boundary -/

namespace Canary

/-- Distinct intermediate resource effects may become indistinguishable after
a later non-injective resource map. -/
def intermediateFalse : LinearEffect Unit Bool where
  site := ()
  consumed := {false}
  produced := 0

def intermediateTrue : LinearEffect Unit Bool where
  site := ()
  consumed := {true}
  produced := 0

theorem intermediate_effects_are_distinct :
    intermediateFalse ≠ intermediateTrue := by
  intro equal
  have consumedEqual := congrArg LinearEffect.consumed equal
  simp [intermediateFalse, intermediateTrue] at consumedEqual

/-- Functorial transport preserves forward composition but does not reflect
distinctions erased by a later route. -/
theorem final_effects_can_coincide :
    mapLinearEffect id (fun _ : Bool => ()) intermediateFalse =
      mapLinearEffect id (fun _ : Bool => ()) intermediateTrue := by
  simp [intermediateFalse, intermediateTrue, mapLinearEffect]

end Canary

#print axioms mapLinearEffect_id
#print axioms mapLinearEffect_comp
#print axioms mapPairSeparation_comp_data
#print axioms transportedOccurrenceCompEquiv
#print axioms flatten_transportOccurrence_twice
#print axioms sourceOccurrence_flatten
#print axioms transportedEffectAnalysis_comp
#print axioms Canary.intermediate_effects_are_distinct
#print axioms Canary.final_effects_can_coincide

end Mettapedia.Languages.MeTTa.Prime.GSLTILLinearEffectTransportComposition
