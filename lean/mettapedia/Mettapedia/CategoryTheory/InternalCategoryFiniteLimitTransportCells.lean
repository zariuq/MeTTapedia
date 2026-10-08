import Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportFunctor

/-!
# Complete natural cells on transported internal categories

A natural transformation of pullback-preserving base functors acts on
both the vertex and the complete edge object. Naturality at the original
matching-pair object earns the composition square through both preserved
pullback projections. The resulting internal functors themselves form a
natural transformation, with the actual vertical identity and composition
laws. An invertible base cell yields an invertible whole-category cell.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportCells

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open InternalCategoryFunctorCategory InternalCategoryFiniteLimitTransport
open InternalCategoryFiniteLimitTransportFunctor (action)

universe u v w z

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {D : Type w} [Category.{z} D] [HasPullbacks D]
variable {F G H : C ⥤ D}
variable [PreservesLimitsOfShape WalkingCospan F]
variable [PreservesLimitsOfShape WalkingCospan G]
variable [PreservesLimitsOfShape WalkingCospan H]

def graph (cell : F ⟶ G) (original : InternalCategory C) :
    InternalGraph.Hom (category F original).toInternalGraph
      (category G original).toInternalGraph where
  vertex := cell.app original.vertex
  edge := cell.app original.edge
  source := (cell.naturality original.source).symm
  target := (cell.naturality original.target).symm

theorem complete_pair (cell : F ⟶ G) (original : InternalCategory C) :
    (PreservesPullback.iso F original.target original.source).inv ≫
        cell.app original.toInternalGraph.Composable =
      (graph cell original).composableMap ≫
        (PreservesPullback.iso G original.target original.source).inv := by
  apply PullbackCone.IsLimit.hom_ext (endpoints G original).pairLimit
  · change ((PreservesPullback.iso F original.target original.source).inv ≫
        cell.app original.toInternalGraph.Composable) ≫
          G.map (pullback.fst original.target original.source) = _
    calc
      _ = pullback.fst (F.map original.target) (F.map original.source) ≫
          cell.app original.edge := by
        rw [Category.assoc, ← cell.naturality, ← Category.assoc,
          PreservesPullback.iso_inv_fst]
      _ = ((graph cell original).composableMap ≫
          (PreservesPullback.iso G original.target original.source).inv) ≫
            G.map (pullback.fst original.target original.source) := by
        rw [Category.assoc, PreservesPullback.iso_inv_fst]
        exact (graph cell original).composableMap_first.symm
  · change ((PreservesPullback.iso F original.target original.source).inv ≫
        cell.app original.toInternalGraph.Composable) ≫
          G.map (pullback.snd original.target original.source) = _
    calc
      _ = pullback.snd (F.map original.target) (F.map original.source) ≫
          cell.app original.edge := by
        rw [Category.assoc, ← cell.naturality, ← Category.assoc,
          PreservesPullback.iso_inv_snd]
      _ = ((graph cell original).composableMap ≫
          (PreservesPullback.iso G original.target original.source).inv) ≫
            G.map (pullback.snd original.target original.source) := by
        rw [Category.assoc, PreservesPullback.iso_inv_snd]
        exact (graph cell original).composableMap_second.symm

def component (cell : F ⟶ G) (original : InternalCategory C) :
    (action F).obj original ⟶ (action G).obj original where
  toHom := graph cell original
  unit := cell.naturality original.unit
  composition := by
    change (category F original).composition ≫ cell.app original.edge =
      (graph cell original).composableMap ≫ (category G original).composition
    rw [complete_composition, complete_composition, Category.assoc,
      cell.naturality, ← Category.assoc, complete_pair, Category.assoc]

def transformation (cell : F ⟶ G) : action F ⟶ action G where
  app := component cell
  naturality {first second} mapping := by
    apply map_ext
    · exact cell.naturality mapping.vertex
    · exact cell.naturality mapping.edge

theorem whole_identity : transformation (𝟙 F) = 𝟙 (action F) := by
  apply NatTrans.ext
  funext original
  apply map_ext <;> rfl

theorem whole_vertical_composition (before : F ⟶ G) (after : G ⟶ H) :
    transformation (before ≫ after) = transformation before ≫ transformation after := by
  apply NatTrans.ext
  funext original
  apply map_ext <;> rfl

def comparison (cell : F ≅ G) : action F ≅ action G where
  hom := transformation cell.hom
  inv := transformation cell.inv
  hom_inv_id := by
    rw [← whole_vertical_composition, cell.hom_inv_id, whole_identity]
  inv_hom_id := by
    rw [← whole_vertical_composition, cell.inv_hom_id, whole_identity]

theorem complete_vertex (cell : F ⟶ G) (original : InternalCategory C) :
    ((transformation cell).app original).vertex = cell.app original.vertex := rfl

theorem complete_edge (cell : F ⟶ G) (original : InternalCategory C) :
    ((transformation cell).app original).edge = cell.app original.edge := rfl

end Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportCells
