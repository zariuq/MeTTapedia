import Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransport

/-!
# Complete internal category maps through preserved pullbacks

The canonical matching-pair comparison commutes with a supplied internal
functor. Its composition square is earned from both pullback projections,
then combined with the original composition square. Edge and vertex maps
retain the complete supplied arrows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open InternalCategoryFiniteLimitTransport

universe u v w z

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {D : Type w} [Category.{z} D] [HasPullbacks D]
variable (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F]
variable {first second : InternalCategory C} (original : InternalCategory.Hom first second)

def graphMap : InternalGraph.Hom (category F first).toInternalGraph
    (category F second).toInternalGraph where
  vertex := F.map original.vertex
  edge := F.map original.edge
  source := by
    change F.map original.edge ≫ F.map second.source = F.map first.source ≫ F.map original.vertex
    rw [← F.map_comp, original.source, F.map_comp]
  target := by
    change F.map original.edge ≫ F.map second.target = F.map first.target ≫ F.map original.vertex
    rw [← F.map_comp, original.target, F.map_comp]

theorem complete_pair_map :
    (PreservesPullback.iso F first.target first.source).inv ≫ F.map original.toHom.composableMap =
      (graphMap F original).composableMap ≫ (PreservesPullback.iso F second.target second.source).inv := by
  apply PullbackCone.IsLimit.hom_ext (endpoints F second).pairLimit
  · change ((PreservesPullback.iso F first.target first.source).inv ≫
        F.map original.toHom.composableMap) ≫ F.map (pullback.fst second.target second.source) = _
    calc
      _ = pullback.fst (F.map first.target) (F.map first.source) ≫ F.map original.edge := by
        rw [Category.assoc, ← F.map_comp, original.toHom.composableMap_first,
          F.map_comp, ← Category.assoc, PreservesPullback.iso_inv_fst]
      _ = ((graphMap F original).composableMap ≫
          (PreservesPullback.iso F second.target second.source).inv) ≫
            F.map (pullback.fst second.target second.source) := by
        rw [Category.assoc, PreservesPullback.iso_inv_fst]
        exact (graphMap F original).composableMap_first.symm
  · change ((PreservesPullback.iso F first.target first.source).inv ≫
        F.map original.toHom.composableMap) ≫ F.map (pullback.snd second.target second.source) = _
    calc
      _ = pullback.snd (F.map first.target) (F.map first.source) ≫ F.map original.edge := by
        rw [Category.assoc, ← F.map_comp, original.toHom.composableMap_second,
          F.map_comp, ← Category.assoc, PreservesPullback.iso_inv_snd]
      _ = ((graphMap F original).composableMap ≫
          (PreservesPullback.iso F second.target second.source).inv) ≫
            F.map (pullback.snd second.target second.source) := by
        rw [Category.assoc, PreservesPullback.iso_inv_snd]
        exact (graphMap F original).composableMap_second.symm

def map : InternalCategory.Hom (category F first) (category F second) where
  toHom := graphMap F original
  unit := by
    change F.map first.unit ≫ F.map original.edge = F.map original.vertex ≫ F.map second.unit
    rw [← F.map_comp, original.unit, F.map_comp]
  composition := by
    change (category F first).composition ≫ F.map original.edge =
      (graphMap F original).composableMap ≫ (category F second).composition
    rw [complete_composition, complete_composition, Category.assoc,
      ← F.map_comp, original.composition, F.map_comp, ← Category.assoc, complete_pair_map,
      Category.assoc]

theorem complete_vertex : (map F original).vertex = F.map original.vertex := rfl
theorem complete_edge : (map F original).edge = F.map original.edge := rfl

theorem whole_composition_read {stage : C} (before after : stage ⟶ first.edge)
    (matching : before ≫ first.target = after ≫ first.source) :
    (category F first).compose (F.map before) (F.map after)
        (mapped_matching F first before after matching) ≫ (map F original).edge =
      F.map (second.compose (before ≫ original.edge) (after ≫ original.edge)
        (by rw [Category.assoc, original.target, ← Category.assoc, matching,
          Category.assoc, ← original.source, ← Category.assoc])) := by
  rw [category_compose_read, complete_edge, ← F.map_comp, original.compose_readout]
  exact matching

end Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportMaps
