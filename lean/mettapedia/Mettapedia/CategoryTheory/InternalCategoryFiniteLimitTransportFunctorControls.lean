import Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportFunctor
import Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportControls
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Complete functor action and the limit-preserving information boundary

Actual evaluation transports a nonidentity internal functor and its
composition. A separately authored two-context diagram supplies a strict
separator: evaluation at one context preserves limits while identifying
internal functors that differ in the other context, including their
occurrence identifiers. Faithfulness is therefore substantive.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportFunctorControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open InternalCategoryFunctorCategory
open InternalCategoryControls
open InternalCategoryFiniteLimitTransportControls (evaluate original transported)

abbrev actualMap : original ⟶ original := InternalCategoryPathMaps.internalFunctor doubling
abbrev action := InternalCategoryFiniteLimitTransportFunctor.action evaluate
abbrev mapped : transported ⟶ transported := action.map actualMap

theorem complete_mapped_occurrence :
    mapped.edge (InternalCategoryPathDiagram.edge graph stage (7, 1, 2)) =
      InternalCategoryPathDiagram.edge graph stage (107, 2, 4) :=
  actual_nonidentity_edge_image

theorem mapped_is_not_identity : mapped ≠ 𝟙 transported := by
  intro same
  have read := congrArg
    (fun arrow : transported ⟶ transported =>
      readout (arrow.edge (InternalCategoryPathDiagram.edge graph stage (7, 1, 2)))) same
  have changed := congrArg readout complete_mapped_occurrence
  change readout (mapped.edge (InternalCategoryPathDiagram.edge graph stage (7, 1, 2))) = [7] at read
  change readout (mapped.edge (InternalCategoryPathDiagram.edge graph stage (7, 1, 2))) = [107] at changed
  have clash : ([107] : List Nat) = [7] := changed.symm.trans read
  cases clash

theorem whole_composite : action.map (actualMap ≫ actualMap) = mapped ≫ mapped :=
  action.map_comp actualMap actualMap

theorem actual_twice_changed_occurrence :
    (action.map (actualMap ≫ actualMap)).edge
      (InternalCategoryPathDiagram.edge graph stage (7, 1, 2)) =
        InternalCategoryPathDiagram.edge graph stage (207, 4, 8) := by
  change (actualMap.edge ≫ actualMap.edge).app stage
    (InternalCategoryPathDiagram.edge graph stage (7, 1, 2)) = _
  change actualMap.edge.app stage
    (actualMap.edge.app stage (InternalCategoryPathDiagram.edge graph stage (7, 1, 2))) = _
  rw [InternalCategoryPathMaps.edge_readout, InternalCategoryPathMaps.edge_readout]
  rfl

namespace MissingContext

abbrev Stage := Discrete Bool
def visible : Stage := Discrete.mk false
def omitted : Stage := Discrete.mk true

abbrev originalCategory : Cat := (InternalCategoryPathDiagram.diagram graph).obj stage
abbrev diagram : Stage ⥤ Cat := Discrete.functor (fun _ => originalCategory)
abbrev category := InternalCategoryDiagram.category diagram

def change : diagram ⟶ diagram := Discrete.natTrans fun world =>
  if world.as then (InternalCategoryPathMaps.diagramMap doubling).app stage else 𝟙 originalCategory

abbrev sourceMap : category ⟶ category := InternalCategoryDiagramMaps.internalFunctor change

theorem source_map_is_nonidentity : sourceMap ≠ 𝟙 category := by
  intro same
  have changed := congrArg
    (fun mapping : category ⟶ category => mapping.vertex.app omitted (1 : Nat)) same
  change (2 * 1 : Nat) = 1 at changed
  cases changed

theorem omitted_origin_is_changed :
    readout (sourceMap.edge.app omitted (InternalCategoryPathDiagram.edge graph stage (7, 1, 2))) =
      [107] := changed_edge_origin_readout

abbrev evaluate : (Stage ⥤ Type) ⥤ Type := (evaluation Stage Type).obj visible
abbrev action := InternalCategoryFiniteLimitTransportFunctor.action evaluate

theorem evaluated_maps_are_equal : action.map sourceMap = action.map (𝟙 category) := by
  apply map_ext
  · rfl
  · rfl

theorem evaluation_does_not_reflect_internal_maps :
    ¬ Function.Injective (action.map (X := category) (Y := category)) := by
  intro reflects
  exact source_map_is_nonidentity (reflects evaluated_maps_are_equal)

end MissingContext

end Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportFunctorControls
