import Mettapedia.Languages.MeTTa.Prime.GSLTILInteractionTransport
import Mettapedia.Languages.MeTTa.Prime.NativeInteractionEffectAnalysis

/-!
# Linear-effect transport along GSLT-IL routes

Operational transport preserves authenticated occurrences, but target-native
parallelism additionally depends on linear resources.  The correct sufficient
condition is occurrence-linear transport: source inventories and event effects
are mapped by the same multiset homomorphism.

Resource-name injectivity is not required.  A non-injective map still retains
multiplicity: two source occurrences become two target occurrences with the
same name.  What destroys separation is contraction, where the transported
inventory contains fewer occurrences than the homomorphic image.

This module constructs the derived transported effect analysis and proves
separation preservation for it.  It deliberately does not identify that
derived analysis with any independently authored target-native analysis; such
an identification requires a separate agreement capability.
-/

namespace Mettapedia.Languages.MeTTa.Prime.GSLTILLinearEffectTransport

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Languages.MeTTa.Prime.GSLTILInteractionTransport
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionEffectAnalysis

universe uSite uTargetSite uEvent uSourceResource uTargetResource

/-- Map the exact consumed and produced occurrence multisets.  Site identity
is retained because transported interaction presentations retain source sites. -/
def mapLinearEffect
    {SourceSite : Type uSite} {TargetSite : Type uTargetSite}
    {SourceResource : Type uSourceResource}
    {TargetResource : Type uTargetResource}
    (siteMap : SourceSite → TargetSite)
    (resourceMap : SourceResource → TargetResource)
    (effect : LinearEffect SourceSite SourceResource) :
    LinearEffect TargetSite TargetResource where
  site := siteMap effect.site
  consumed := effect.consumed.map resourceMap
  produced := effect.produced.map resourceMap

/-- Linear multiset transport preserves proof-relevant pair separation.  No
injectivity premise is needed because `Multiset.map` preserves occurrences. -/
def mapPairSeparation
    {SourceSite : Type uSite} {TargetSite : Type uTargetSite}
    {SourceResource : Type uSourceResource}
    {TargetResource : Type uTargetResource}
    (siteMap : SourceSite → TargetSite)
    (resourceMap : SourceResource → TargetResource)
    {source : Multiset SourceResource}
    {left right : LinearEffect SourceSite SourceResource}
    (separation : PairSeparation source left right) :
    PairSeparation (source.map resourceMap)
      (mapLinearEffect siteMap resourceMap left)
      (mapLinearEffect siteMap resourceMap right) where
  frame := separation.frame.map resourceMap
  source_eq := by
    calc
      source.map resourceMap =
          (left.consumed + right.consumed + separation.frame).map
            resourceMap :=
        congrArg (Multiset.map resourceMap) separation.source_eq
      _ =
          (mapLinearEffect siteMap resourceMap left).consumed +
            (mapLinearEffect siteMap resourceMap right).consumed +
              separation.frame.map resourceMap := by
        simp [mapLinearEffect]

/-! ## Transported occurrence analysis -/

/-- Transport one packaged source occurrence, retaining its exact evidence. -/
def transportOccurrence
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source) :
    Occurrence presentation →
      Occurrence (transportedPresentation translation presentation)
  | ⟨first, ⟨site, last, evidence⟩⟩ =>
      ⟨translation.mapTerm first,
        ⟨site, translation.mapTerm last, .ofSource evidence⟩⟩

/-- Recover the retained source occurrence from a transported occurrence. -/
def sourceOccurrence
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source) :
    Occurrence (transportedPresentation translation presentation) →
      Occurrence presentation
  | ⟨_, ⟨_, _, .ofSource evidence⟩⟩ =>
      ⟨_, ⟨_, _, evidence⟩⟩

@[simp] theorem sourceOccurrence_transportOccurrence
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source)
    (occurrence : Occurrence presentation) :
    sourceOccurrence translation presentation
        (transportOccurrence translation presentation occurrence) =
      occurrence := by
  cases occurrence with
  | mk first enabled =>
      cases enabled
      rfl

/-- The transported presentation inherits an exact effect analysis by mapping
the resources of the source occurrence retained in every transported event. -/
def transportedEffectAnalysis
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source)
    {SourceResource : Type uSourceResource}
    {TargetResource : Type uTargetResource}
    (analysis : OccurrenceEffectAnalysis presentation SourceResource)
    (resourceMap : SourceResource → TargetResource) :
    OccurrenceEffectAnalysis
      (transportedPresentation translation presentation) TargetResource where
  effect := fun occurrence =>
    mapLinearEffect (fun site => site) resourceMap
      (analysis.effect (sourceOccurrence translation presentation occurrence))

@[simp] theorem transportedEffectAnalysis_transportOccurrence
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source)
    {SourceResource : Type uSourceResource}
    {TargetResource : Type uTargetResource}
    (analysis : OccurrenceEffectAnalysis presentation SourceResource)
    (resourceMap : SourceResource → TargetResource)
    (occurrence : Occurrence presentation) :
    (transportedEffectAnalysis translation presentation analysis resourceMap
      ).effect (transportOccurrence translation presentation occurrence) =
      mapLinearEffect (fun site => site) resourceMap
        (analysis.effect occurrence) := by
  rfl

/-- A separated pair of exact source occurrences remains separated in the
derived transported effect analysis. -/
def transportPairSeparation
    {sourceTheory targetTheory : GSLT}
    (translation : OperationalTranslation sourceTheory targetTheory)
    (presentation : InteractionPresentation.{uSite, uEvent} sourceTheory)
    {SourceResource : Type uSourceResource}
    {TargetResource : Type uTargetResource}
    (analysis : OccurrenceEffectAnalysis presentation SourceResource)
    (resourceMap : SourceResource → TargetResource)
    {inventory : Multiset SourceResource}
    {left right : Occurrence presentation}
    (separation : PairSeparation inventory
      (analysis.effect left) (analysis.effect right)) :
    PairSeparation (inventory.map resourceMap)
      ((transportedEffectAnalysis translation presentation analysis resourceMap
        ).effect (transportOccurrence translation presentation left))
      ((transportedEffectAnalysis translation presentation analysis resourceMap
        ).effect (transportOccurrence translation presentation right)) := by
  refine
    { frame := separation.frame.map resourceMap
      source_eq := ?_ }
  calc
    inventory.map resourceMap =
        ((analysis.effect left).consumed +
          (analysis.effect right).consumed + separation.frame).map
            resourceMap :=
      congrArg (Multiset.map resourceMap) separation.source_eq
    _ =
        ((transportedEffectAnalysis translation presentation analysis
          resourceMap).effect
            (transportOccurrence translation presentation left)).consumed +
          ((transportedEffectAnalysis translation presentation analysis
            resourceMap).effect
              (transportOccurrence translation presentation right)).consumed +
            separation.frame.map resourceMap := by
      rw [transportedEffectAnalysis_transportOccurrence,
        transportedEffectAnalysis_transportOccurrence]
      simp [mapLinearEffect]

/-! ## Agreement with an independently authored target analysis -/

/-- The weakest pointwise agreement needed to reuse a resource-separation
certificate.  Sites and produced resources may differ: `PairSeparation`
depends only on the consumed occurrence multisets.

This is intentionally not yet an operational commutation capability.  A
target language must separately prove that its complete native effects realize
a commuting diamond or schedule. -/
structure ConsumptionAgreement
    {theory : GSLT}
    {presentation : InteractionPresentation.{uSite, uEvent} theory}
    {Resource : Type uSourceResource}
    (reference target : OccurrenceEffectAnalysis presentation Resource) : Prop
    where
  consumed_eq : ∀ occurrence,
    (target.effect occurrence).consumed =
      (reference.effect occurrence).consumed

namespace ConsumptionAgreement

/-- Every exact analysis agrees with itself. -/
def refl
    {theory : GSLT}
    {presentation : InteractionPresentation.{uSite, uEvent} theory}
    {Resource : Type uSourceResource}
    (analysis : OccurrenceEffectAnalysis presentation Resource) :
    ConsumptionAgreement analysis analysis :=
  ⟨fun _ => rfl⟩

/-- One changed consumption multiset is a complete obstruction to agreement. -/
theorem not_of_consumed_ne
    {theory : GSLT}
    {presentation : InteractionPresentation.{uSite, uEvent} theory}
    {Resource : Type uSourceResource}
    {reference target : OccurrenceEffectAnalysis presentation Resource}
    (occurrence : Occurrence presentation)
    (different : (target.effect occurrence).consumed ≠
      (reference.effect occurrence).consumed) :
    ¬ ConsumptionAgreement reference target := by
  intro agreement
  exact different (agreement.consumed_eq occurrence)

/-- Pair separation is invariant under pointwise consumption agreement. -/
def transportPairSeparation
    {theory : GSLT}
    {presentation : InteractionPresentation.{uSite, uEvent} theory}
    {Resource : Type uSourceResource}
    {reference target : OccurrenceEffectAnalysis presentation Resource}
    (agreement : ConsumptionAgreement reference target)
    {inventory : Multiset Resource}
    {left right : Occurrence presentation}
    (separation : PairSeparation inventory
      (reference.effect left) (reference.effect right)) :
    PairSeparation inventory
      (target.effect left) (target.effect right) where
  frame := separation.frame
  source_eq := by
    rw [agreement.consumed_eq left, agreement.consumed_eq right]
    exact separation.source_eq

end ConsumptionAgreement

/-- Transported source separation becomes target-analysis separation exactly
at the point where the target analysis agrees on consumed occurrences. -/
def targetPairSeparationOfConsumptionAgreement
    {sourceTheory targetTheory : GSLT}
    (translation : OperationalTranslation sourceTheory targetTheory)
    (presentation : InteractionPresentation.{uSite, uEvent} sourceTheory)
    {SourceResource : Type uSourceResource}
    {TargetResource : Type uTargetResource}
    (sourceAnalysis : OccurrenceEffectAnalysis presentation SourceResource)
    (resourceMap : SourceResource → TargetResource)
    (targetAnalysis : OccurrenceEffectAnalysis
      (transportedPresentation translation presentation) TargetResource)
    (agreement : ConsumptionAgreement
      (transportedEffectAnalysis translation presentation sourceAnalysis
        resourceMap)
      targetAnalysis)
    {inventory : Multiset SourceResource}
    {left right : Occurrence presentation}
    (separation : PairSeparation inventory
      (sourceAnalysis.effect left) (sourceAnalysis.effect right)) :
    PairSeparation (inventory.map resourceMap)
      (targetAnalysis.effect
        (transportOccurrence translation presentation left))
      (targetAnalysis.effect
        (transportOccurrence translation presentation right)) :=
  agreement.transportPairSeparation
    (transportPairSeparation translation presentation sourceAnalysis
      resourceMap separation)

/-! ## Name collapse versus occurrence contraction -/

namespace Canary

inductive Site where
  | interaction
  deriving DecidableEq

inductive SourceResource where
  | first
  | second
  deriving DecidableEq

def left : LinearEffect Site SourceResource :=
  ⟨.interaction, {.first}, 0⟩

def right : LinearEffect Site SourceResource :=
  ⟨.interaction, {.second}, 0⟩

def sourceInventory : Multiset SourceResource :=
  {.first, .second}

def sourceSeparation : PairSeparation sourceInventory left right where
  frame := 0
  source_eq := by decide

/-- Deliberately identify both resource names. -/
def collapseName : SourceResource → Unit := fun _ => ()

/-- Non-injective naming still preserves two linear occurrences. -/
def collapsedNameSeparation :
    PairSeparation (sourceInventory.map collapseName)
      (mapLinearEffect id collapseName left)
      (mapLinearEffect id collapseName right) :=
  mapPairSeparation id collapseName sourceSeparation

theorem noninjective_name_map_preserves_separation :
    (¬ Function.Injective collapseName) ∧
      Nonempty
        (PairSeparation (sourceInventory.map collapseName)
          (mapLinearEffect id collapseName left)
          (mapLinearEffect id collapseName right)) := by
  constructor
  · intro injective
    have equal : SourceResource.first = SourceResource.second :=
      injective rfl
    exact SourceResource.noConfusion equal
  · exact ⟨collapsedNameSeparation⟩

/-- A contracting target inventory keeps only one occurrence after both source
names have been identified. -/
def contractedInventory : Multiset Unit :=
  {()}

/-- Contraction, unlike non-injective renaming, destroys the separation. -/
theorem contraction_destroys_separation :
    IsEmpty
      (PairSeparation contractedInventory
        (mapLinearEffect id collapseName left)
        (mapLinearEffect id collapseName right)) := by
  constructor
  intro separation
  have cards := congrArg Multiset.card separation.source_eq
  simp [contractedInventory, mapLinearEffect, left, right] at cards

/-- The positive and negative controls isolate the actual transport law:
preserve linear occurrences, not necessarily resource names. -/
theorem multiplicity_not_name_injectivity_is_the_boundary :
    Nonempty (PairSeparation sourceInventory left right) ∧
      Nonempty
        (PairSeparation (sourceInventory.map collapseName)
          (mapLinearEffect id collapseName left)
          (mapLinearEffect id collapseName right)) ∧
      IsEmpty
        (PairSeparation contractedInventory
          (mapLinearEffect id collapseName left)
          (mapLinearEffect id collapseName right)) :=
  ⟨⟨sourceSeparation⟩, ⟨collapsedNameSeparation⟩,
    contraction_destroys_separation⟩

end Canary

#print axioms mapPairSeparation
#print axioms sourceOccurrence_transportOccurrence
#print axioms transportedEffectAnalysis_transportOccurrence
#print axioms transportPairSeparation
#print axioms ConsumptionAgreement.refl
#print axioms ConsumptionAgreement.not_of_consumed_ne
#print axioms ConsumptionAgreement.transportPairSeparation
#print axioms targetPairSeparationOfConsumptionAgreement
#print axioms Canary.noninjective_name_map_preserves_separation
#print axioms Canary.contraction_destroys_separation
#print axioms Canary.multiplicity_not_name_injectivity_is_the_boundary

end Mettapedia.Languages.MeTTa.Prime.GSLTILLinearEffectTransport
