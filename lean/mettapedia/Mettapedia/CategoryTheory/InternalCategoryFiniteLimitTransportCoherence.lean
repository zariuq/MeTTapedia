import Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportComposition
import Mathlib.CategoryTheory.Whiskering

/-!
# Unit, associativity and cell coherence of the actual category action

The identity comparison is derived through the original matching pullback.
The canonical composition comparisons satisfy both unit triangles, the
three-functor associativity diagram and compatibility with actual natural
base cells. All equalities compare complete internal functors, including
their earned unit and composition squares.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportCoherence

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open InternalCategoryFunctorCategory InternalCategoryFiniteLimitTransport
open InternalCategoryFiniteLimitTransportFunctor (action)

universe u v w z a b k l

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

theorem identity_pair (original : InternalCategory C) :
    (PreservesPullback.iso (𝟭 C) original.target original.source).inv =
      𝟙 original.toInternalGraph.Composable := by
  apply pullback.hom_ext
  · exact (PreservesPullback.iso_inv_fst (𝟭 C) original.target original.source).trans
      (Category.id_comp _).symm
  · exact (PreservesPullback.iso_inv_snd (𝟭 C) original.target original.source).trans
      (Category.id_comp _).symm

theorem identity_composition (original : InternalCategory C) :
    (category (𝟭 C) original).composition = original.composition := by
  rw [complete_composition, identity_pair]
  exact Category.id_comp _

def identityForward (original : InternalCategory C) : (action (𝟭 C)).obj original ⟶ original where
  toHom := graphIdentity original.toInternalGraph
  unit := (Category.comp_id _).trans (Category.id_comp _).symm
  composition := by
    change (category (𝟭 C) original).composition ≫ 𝟙 _ =
      (graphIdentity original.toInternalGraph).composableMap ≫ original.composition
    rw [identity_pair_read, Category.comp_id, Category.id_comp]
    exact identity_composition original

def identityBackward (original : InternalCategory C) : original ⟶ (action (𝟭 C)).obj original where
  toHom := graphIdentity original.toInternalGraph
  unit := (Category.comp_id _).trans (Category.id_comp _).symm
  composition := by
    change original.composition ≫ 𝟙 _ =
      (graphIdentity original.toInternalGraph).composableMap ≫ (category (𝟭 C) original).composition
    rw [identity_pair_read, Category.comp_id, Category.id_comp]
    exact (identity_composition original).symm

def identityComponent (original : InternalCategory C) : (action (𝟭 C)).obj original ≅ original where
  hom := identityForward original
  inv := identityBackward original
  hom_inv_id := map_ext (Category.id_comp _) (Category.id_comp _)
  inv_hom_id := map_ext (Category.id_comp _) (Category.id_comp _)

def identityComparison : action (𝟭 C) ≅ 𝟭 (InternalCategory C) :=
  NatIso.ofComponents identityComponent (by
    intro first second mapping
    apply map_ext
    · change mapping.vertex ≫ 𝟙 _ = 𝟙 _ ≫ mapping.vertex
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    · change mapping.edge ≫ 𝟙 _ = 𝟙 _ ≫ mapping.edge
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

variable {D : Type w} [Category.{z} D] [HasPullbacks D]
variable {E : Type a} [Category.{b} E] [HasPullbacks E]
variable {K : Type k} [Category.{l} K] [HasPullbacks K]
variable (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ K)
variable [PreservesLimitsOfShape WalkingCospan F]
variable [PreservesLimitsOfShape WalkingCospan G]
variable [PreservesLimitsOfShape WalkingCospan H]

theorem left_unit (original : InternalCategory C) :
    (InternalCategoryFiniteLimitTransportComposition.comparison (𝟭 C) F).hom.app original ≫
        (action F).map (identityComparison.hom.app original) =
      (InternalCategoryFiniteLimitTransportCells.transformation (Functor.leftUnitor F).hom).app original := by
  apply map_ext
  · change 𝟙 _ ≫ F.map (𝟙 _) = 𝟙 _
    rw [F.map_id, Category.id_comp]
  · change 𝟙 _ ≫ F.map (𝟙 _) = 𝟙 _
    rw [F.map_id, Category.id_comp]

theorem right_unit (original : InternalCategory C) :
    (InternalCategoryFiniteLimitTransportComposition.comparison F (𝟭 D)).hom.app original ≫
        identityComparison.hom.app ((action F).obj original) =
      (InternalCategoryFiniteLimitTransportCells.transformation (Functor.rightUnitor F).hom).app original := by
  apply map_ext
  · exact Category.id_comp _
  · exact Category.id_comp _

theorem associativity (original : InternalCategory C) :
    (InternalCategoryFiniteLimitTransportComposition.comparison (F ⋙ G) H).hom.app original ≫
        (action H).map ((InternalCategoryFiniteLimitTransportComposition.comparison F G).hom.app original) =
      (InternalCategoryFiniteLimitTransportCells.transformation (Functor.associator F G H).hom).app original ≫
        ((InternalCategoryFiniteLimitTransportComposition.comparison F (G ⋙ H)).hom.app original ≫
          (InternalCategoryFiniteLimitTransportComposition.comparison G H).hom.app ((action F).obj original)) := by
  apply map_ext
  · change 𝟙 _ ≫ H.map (𝟙 _) = 𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _)
    simp only [H.map_id, Category.id_comp]
  · change 𝟙 _ ≫ H.map (𝟙 _) = 𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _)
    simp only [H.map_id, Category.id_comp]

variable {F' : C ⥤ D} {G' : D ⥤ E}
variable [PreservesLimitsOfShape WalkingCospan F']
variable [PreservesLimitsOfShape WalkingCospan G']

theorem horizontal_cells (before : F ⟶ F') (after : G ⟶ G') (original : InternalCategory C) :
    (InternalCategoryFiniteLimitTransportCells.transformation
        (Functor.whiskerRight before G ≫ Functor.whiskerLeft F' after)).app original ≫
      (InternalCategoryFiniteLimitTransportComposition.comparison F' G').hom.app original =
    (InternalCategoryFiniteLimitTransportComposition.comparison F G).hom.app original ≫
      ((action G).map ((InternalCategoryFiniteLimitTransportCells.transformation before).app original) ≫
        (InternalCategoryFiniteLimitTransportCells.transformation after).app ((action F').obj original)) := by
  apply map_ext
  · change (G.map (before.app original.vertex) ≫ after.app (F'.obj original.vertex)) ≫ 𝟙 _ =
      𝟙 _ ≫ (G.map (before.app original.vertex) ≫ after.app (F'.obj original.vertex))
    rw [Category.comp_id, Category.id_comp]
  · change (G.map (before.app original.edge) ≫ after.app (F'.obj original.edge)) ≫ 𝟙 _ =
      𝟙 _ ≫ (G.map (before.app original.edge) ≫ after.app (F'.obj original.edge))
    rw [Category.comp_id, Category.id_comp]

end Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportCoherence
