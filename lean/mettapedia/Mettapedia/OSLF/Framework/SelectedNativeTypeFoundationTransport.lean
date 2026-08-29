import Mettapedia.OSLF.Framework.CarrierObjectClosureTransport
import Mettapedia.OSLF.Framework.DisplayedContextProfileTransport
import Mettapedia.OSLF.Framework.SelectedNativeTypeFoundation

/-!
# Structural transport of selected native-type demands

A selected native-type demand is dependent data over its source language:
typed displayed rewrite occurrences plus grounding evidence for every carrier
they require.  This module proves that the entire demand, rather than only its
site list, reindexes along a structural language map.

The resulting laws are exact on ordered roots and occurrences.  Carrier
closure is exactly pointwise only under an injective sort action; without that
hypothesis the one-way membership theorem still records that mapped carriers
cannot disappear.  Keeping these two strengths separate prevents a
many-to-one source translation from masquerading as slot-preserving
compilation.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

namespace SelectedNativeTypeFoundation

/-- Required carrier roots commute with structural transport of one typed
displayed occurrence. -/
theorem requiredCarrierRoots_map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (typing : DisplayedRewriteTyping source) :
    requiredCarrierRoots (typing.map morphism) =
      (requiredCarrierRoots typing).map
        (mapTypeExpr morphism.symbols) := by
  unfold requiredCarrierRoots
  rw [DisplayedContextProfile.carrierTypes_map morphism typing]
  simp [DisplayedRewriteTyping.map, List.map_append]

/-- Grounding evidence is stable under every structural language map. -/
theorem CarrierGrounded.map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {typing : DisplayedRewriteTyping source}
    (grounded : CarrierGrounded typing) :
    CarrierGrounded (typing.map morphism) := by
  intro mappedObject mappedMembership
  rw [requiredCarrierRoots_map morphism typing] at mappedMembership
  obtain ⟨object, objectMembership, rfl⟩ :=
    List.mem_map.mp mappedMembership
  exact CarrierObjectClosure.GroundedIn.map morphism
    (grounded object objectMembership)

namespace Demand

/-- Reindex a complete ordered generation demand along a structural language
map.  Typing derivations are transported, never recomputed. -/
noncomputable def map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : Demand source) : Demand target where
  typings := demand.typings.map (DisplayedRewriteTyping.map morphism)
  grounded := by
    intro mappedTyping mappedMembership
    obtain ⟨typing, typingMembership, rfl⟩ :=
      List.mem_map.mp mappedMembership
    exact (demand.grounded typing typingMembership).map morphism

@[simp] theorem map_typings
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : Demand source) :
    (demand.map morphism).typings =
      demand.typings.map (DisplayedRewriteTyping.map morphism) :=
  rfl

@[simp] theorem map_id
    (source : ValidatedLanguageDef) (demand : Demand source) :
    demand.map (StructuralMorphism.id source) = demand := by
  apply Demand.ext
  change demand.typings.map
      (DisplayedRewriteTyping.map (StructuralMorphism.id source)) =
    demand.typings
  induction demand.typings with
  | nil => rfl
  | cons typing typings inductionHypothesis =>
      simp [DisplayedRewriteTyping.map_id, inductionHypothesis]

theorem map_comp
    {first second third : ValidatedLanguageDef}
    (earlier : StructuralMorphism first second)
    (later : StructuralMorphism second third)
    (demand : Demand first) :
    demand.map (StructuralMorphism.comp earlier later) =
      (demand.map earlier).map later := by
  apply Demand.ext
  simp only [map_typings, List.map_map]
  apply List.map_congr_left
  intro typing _
  exact DisplayedRewriteTyping.map_comp earlier later typing

/-- Reindexing preserves ordered demand composition exactly. -/
theorem map_append
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (first second : Demand source) :
    (first.append second).map morphism =
      (first.map morphism).append (second.map morphism) := by
  apply Demand.ext
  simp [Demand.append, List.map_append]

/-- The selected occurrence list of a reindexed demand is exactly the
pointwise structural image of the source list. -/
theorem selectedSites_map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : Demand source) :
    (demand.map morphism).selectedSites =
      DisplayedRewriteSite.mapSelection morphism demand.selectedSites := by
  simp [selectedSites, map, DisplayedRewriteSite.mapSelection,
    DisplayedRewriteTyping.map]

/-- Ordered carrier roots of a reindexed demand are the pointwise structural
image of the source roots. -/
theorem carrierRoots_map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : Demand source) :
    (demand.map morphism).carrierRoots =
      demand.carrierRoots.map (mapTypeExpr morphism.symbols) := by
  unfold carrierRoots
  rw [map_typings]
  induction demand.typings with
  | nil => rfl
  | cons typing typings inductionHypothesis =>
      simp only [List.map_cons, List.flatMap_cons,
        requiredCarrierRoots_map, List.map_append]
      rw [inductionHypothesis]

/-- The carrier request derived after reindexing is exactly the generic
reindexing of the carrier request derived before it. -/
theorem carrierObjects_map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : Demand source) :
    (demand.map morphism).carrierObjects =
      demand.carrierObjects.map morphism := by
  apply CarrierObjectClosure.Request.ext
  exact carrierRoots_map morphism demand

/-- Injective sort transport preserves the exact carrier inventory and its
stable order. -/
theorem carrierInventory_map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : Demand source) :
    (demand.map morphism).carrierObjects.objects =
      demand.carrierObjects.objects.map
        (mapTypeExpr morphism.symbols) := by
  rw [carrierObjects_map]
  exact CarrierObjectClosure.Request.objects_map morphism sortInjective
    demand.carrierObjects

/-- Positional carrier wire names are unchanged by exact injective
reindexing.  Their decoded carrier expressions change functorially, while
their stable slots do not. -/
theorem stableCarrierTypes_map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : Demand source) :
    stableCarrierTypes (demand.map morphism) = stableCarrierTypes demand := by
  apply stableCarrierTypes_eq_of_object_count
  rw [carrierInventory_map morphism sortInjective demand, List.length_map]

theorem stableCarrierNames_map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : Demand source) :
    stableCarrierNames (demand.map morphism) = stableCarrierNames demand := by
  unfold stableCarrierNames
  exact congrArg (fun types : List TypeDecl => types.map (·.name))
    (stableCarrierTypes_map morphism sortInjective demand)

/-- Even a non-injective sort map cannot remove the image of a generated
source carrier, though it may merge several images into one target slot. -/
theorem mappedCarrier_mem
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : Demand source) {object : TypeExpr}
    (membership : object ∈ demand.carrierObjects.objects) :
    mapTypeExpr morphism.symbols object ∈
      (demand.map morphism).carrierObjects.objects := by
  rw [carrierObjects_map]
  exact CarrierObjectClosure.mem_close_mapTypeExpr morphism.symbols membership

end Demand

/-! ## Positive and negative controls -/

namespace TransportCanary

/-- Reindexing the empty demand is exactly empty. -/
theorem empty_maps_to_empty
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) :
    (Demand.empty source).map morphism = Demand.empty target := by
  apply Demand.ext
  rfl

/-- Injectivity is genuinely needed for cardinality preservation; the
carrier-closure counterexample exhibits a two-to-one sort collapse. -/
theorem noninjective_transport_need_not_preserve_cardinality :
    ∃ (symbols : PresentationSymbols) (roots : List TypeExpr),
      (CarrierObjectClosure.close
        (roots.map (mapTypeExpr symbols))).length ≠
        (CarrierObjectClosure.close roots).length := by
  let symbols : PresentationSymbols :=
    { sort := fun _ => "selected-native-transport:merged"
      constructor := _root_.id
      relation := _root_.id
      equation := _root_.id
      rewrite := _root_.id }
  refine ⟨symbols,
    [.base "selected-native-transport:A",
      .base "selected-native-transport:B"], ?_⟩
  decide

end TransportCanary

#print axioms requiredCarrierRoots_map
#print axioms CarrierGrounded.map
#print axioms Demand.map_comp
#print axioms Demand.map_append
#print axioms Demand.selectedSites_map
#print axioms Demand.carrierRoots_map
#print axioms Demand.carrierObjects_map
#print axioms Demand.carrierInventory_map
#print axioms Demand.stableCarrierTypes_map
#print axioms Demand.stableCarrierNames_map
#print axioms Demand.mappedCarrier_mem
#print axioms TransportCanary.empty_maps_to_empty
#print axioms TransportCanary.noninjective_transport_need_not_preserve_cardinality

end SelectedNativeTypeFoundation

end Mettapedia.OSLF.Framework
