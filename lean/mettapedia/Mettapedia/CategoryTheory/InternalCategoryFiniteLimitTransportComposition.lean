import Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportCells

/-!
# Canonical composition of base functor actions

Direct transport and successive transport use independently chosen matching
pullbacks. Their complete comparison is earned from both projections of the
mapped original pullback. It identifies their composition operations and
gives a natural isomorphism of the two actual internal-category functors.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportComposition

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open InternalCategoryFunctorCategory InternalCategoryFiniteLimitTransport
open InternalCategoryFiniteLimitTransportFunctor (action)

universe u v w z a b

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {D : Type w} [Category.{z} D] [HasPullbacks D]
variable {E : Type a} [Category.{b} E] [HasPullbacks E]
variable (F : C ⥤ D) (G : D ⥤ E)
variable [PreservesLimitsOfShape WalkingCospan F]
variable [PreservesLimitsOfShape WalkingCospan G]
variable (original : InternalCategory C)

theorem complete_pair :
    (PreservesPullback.iso (F ⋙ G) original.target original.source).inv =
      (PreservesPullback.iso G (F.map original.target) (F.map original.source)).inv ≫
        G.map (PreservesPullback.iso F original.target original.source).inv := by
  apply PullbackCone.IsLimit.hom_ext (endpoints (F ⋙ G) original).pairLimit
  · change (PreservesPullback.iso (F ⋙ G) original.target original.source).inv ≫
        (F ⋙ G).map (pullback.fst original.target original.source) = _
    rw [PreservesPullback.iso_inv_fst]
    symm
    change ((PreservesPullback.iso G (F.map original.target) (F.map original.source)).inv ≫
      G.map (PreservesPullback.iso F original.target original.source).inv) ≫
        G.map (F.map (pullback.fst original.target original.source)) = _
    rw [Category.assoc, ← G.map_comp, PreservesPullback.iso_inv_fst,
      PreservesPullback.iso_inv_fst]
    rfl
  · change (PreservesPullback.iso (F ⋙ G) original.target original.source).inv ≫
        (F ⋙ G).map (pullback.snd original.target original.source) = _
    rw [PreservesPullback.iso_inv_snd]
    symm
    change ((PreservesPullback.iso G (F.map original.target) (F.map original.source)).inv ≫
      G.map (PreservesPullback.iso F original.target original.source).inv) ≫
        G.map (F.map (pullback.snd original.target original.source)) = _
    rw [Category.assoc, ← G.map_comp, PreservesPullback.iso_inv_snd,
      PreservesPullback.iso_inv_snd]
    rfl

theorem complete_composition_read :
    (category (F ⋙ G) original).composition =
      (category G (category F original)).composition := by
  rw [complete_composition, complete_composition]
  change (PreservesPullback.iso (F ⋙ G) original.target original.source).inv ≫
      G.map (F.map original.composition) =
    (PreservesPullback.iso G (F.map original.target) (F.map original.source)).inv ≫
      G.map (category F original).composition
  rw [complete_composition, G.map_comp, complete_pair, Category.assoc]

def graphComparison : InternalGraph.Hom
    (category (F ⋙ G) original).toInternalGraph
      (category G (category F original)).toInternalGraph :=
  graphIdentity (category (F ⋙ G) original).toInternalGraph

def forward : (action (F ⋙ G)).obj original ⟶ ((action F) ⋙ (action G)).obj original where
  toHom := graphComparison F G original
  unit := (Category.comp_id _).trans (Category.id_comp _).symm
  composition := by
    change (category (F ⋙ G) original).composition ≫ 𝟙 _ =
      (graphIdentity (category (F ⋙ G) original).toInternalGraph).composableMap ≫
        (category G (category F original)).composition
    rw [identity_pair_read, Category.comp_id, Category.id_comp]
    exact complete_composition_read F G original

def backward : ((action F) ⋙ (action G)).obj original ⟶ (action (F ⋙ G)).obj original where
  toHom := graphIdentity (category G (category F original)).toInternalGraph
  unit := (Category.comp_id _).trans (Category.id_comp _).symm
  composition := by
    change (category G (category F original)).composition ≫ 𝟙 _ =
      (graphIdentity (category G (category F original)).toInternalGraph).composableMap ≫
        (category (F ⋙ G) original).composition
    rw [identity_pair_read, Category.comp_id, Category.id_comp]
    exact (complete_composition_read F G original).symm

def component : (action (F ⋙ G)).obj original ≅ ((action F) ⋙ (action G)).obj original where
  hom := forward F G original
  inv := backward F G original
  hom_inv_id := map_ext (Category.id_comp _) (Category.id_comp _)
  inv_hom_id := map_ext (Category.id_comp _) (Category.id_comp _)

def comparison : action (F ⋙ G) ≅ (action F) ⋙ (action G) :=
  NatIso.ofComponents (component F G) (by
    intro first second mapping
    apply map_ext
    · change G.map (F.map mapping.vertex) ≫ 𝟙 _ = 𝟙 _ ≫ G.map (F.map mapping.vertex)
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    · change G.map (F.map mapping.edge) ≫ 𝟙 _ = 𝟙 _ ≫ G.map (F.map mapping.edge)
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

theorem complete_vertex : ((comparison F G).hom.app original).vertex =
    𝟙 (G.obj (F.obj original.vertex)) := rfl

theorem complete_edge : ((comparison F G).hom.app original).edge =
    𝟙 (G.obj (F.obj original.edge)) := rfl

end Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportComposition
