import Mettapedia.CategoryTheory.InternalCategory

/-!
# The category of internal categories and complete internal functors

Identity and composite maps retain both vertex and edge arrows. Their
matching-pair maps are determined by the actual pullback projections,
which earn preservation of the complete category composition. Equality
of functors needs only their two arrow readings; all laws are proofs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryFunctorCategory

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

theorem map_ext {first second : InternalCategory C}
    {left right : InternalCategory.Hom first second}
    (vertices : left.vertex = right.vertex) (edges : left.edge = right.edge) : left = right := by
  rcases left with ⟨⟨leftVertex, leftEdge, leftSource, leftTarget⟩, leftUnit, leftComposition⟩
  rcases right with ⟨⟨rightVertex, rightEdge, rightSource, rightTarget⟩, rightUnit, rightComposition⟩
  dsimp only at vertices edges
  cases vertices
  cases edges
  rfl

def graphIdentity (original : InternalGraph C) : InternalGraph.Hom original original where
  vertex := 𝟙 original.vertex
  edge := 𝟙 original.edge
  source := (Category.id_comp _).trans (Category.comp_id _).symm
  target := (Category.id_comp _).trans (Category.comp_id _).symm

theorem identity_pair_read (original : InternalGraph C) :
    (graphIdentity original).composableMap = 𝟙 original.Composable := by
  apply pullback.hom_ext
  · rw [InternalGraph.Hom.composableMap_first, Category.id_comp]
    exact Category.comp_id _
  · rw [InternalGraph.Hom.composableMap_second, Category.id_comp]
    exact Category.comp_id _

def identity (original : InternalCategory C) : InternalCategory.Hom original original where
  toHom := graphIdentity original.toInternalGraph
  unit := (Category.comp_id _).trans (Category.id_comp _).symm
  composition := by
    change original.composition ≫ 𝟙 original.edge =
      (graphIdentity original.toInternalGraph).composableMap ≫ original.composition
    rw [identity_pair_read, Category.comp_id, Category.id_comp]

def graphCompose {first middle last : InternalGraph C}
    (before : InternalGraph.Hom first middle) (after : InternalGraph.Hom middle last) :
    InternalGraph.Hom first last where
  vertex := before.vertex ≫ after.vertex
  edge := before.edge ≫ after.edge
  source := by
    rw [Category.assoc, after.source, ← Category.assoc, before.source, Category.assoc]
  target := by
    rw [Category.assoc, after.target, ← Category.assoc, before.target, Category.assoc]

theorem compose_pair_read {first middle last : InternalGraph C}
    (before : InternalGraph.Hom first middle) (after : InternalGraph.Hom middle last) :
    (graphCompose before after).composableMap = before.composableMap ≫ after.composableMap := by
  apply pullback.hom_ext
  · rw [InternalGraph.Hom.composableMap_first, Category.assoc,
      InternalGraph.Hom.composableMap_first, ← Category.assoc,
      InternalGraph.Hom.composableMap_first, Category.assoc]
    rfl
  · rw [InternalGraph.Hom.composableMap_second, Category.assoc,
      InternalGraph.Hom.composableMap_second, ← Category.assoc,
      InternalGraph.Hom.composableMap_second, Category.assoc]
    rfl

def compose {first middle last : InternalCategory C}
    (before : InternalCategory.Hom first middle) (after : InternalCategory.Hom middle last) :
    InternalCategory.Hom first last where
  toHom := graphCompose before.toHom after.toHom
  unit := by
    change first.unit ≫ (before.edge ≫ after.edge) = (before.vertex ≫ after.vertex) ≫ last.unit
    rw [← Category.assoc, before.unit, Category.assoc, after.unit, ← Category.assoc]
  composition := by
    change first.composition ≫ (before.edge ≫ after.edge) =
      (graphCompose before.toHom after.toHom).composableMap ≫ last.composition
    rw [compose_pair_read, ← Category.assoc, before.composition,
      Category.assoc, after.composition, ← Category.assoc]

instance internalCategory : Category.{v} (InternalCategory C) where
  Hom first second := InternalCategory.Hom first second
  id := identity
  comp := compose
  id_comp mapping := map_ext (Category.id_comp mapping.vertex) (Category.id_comp mapping.edge)
  comp_id mapping := map_ext (Category.comp_id mapping.vertex) (Category.comp_id mapping.edge)
  assoc before middle after := map_ext
    (Category.assoc before.vertex middle.vertex after.vertex)
    (Category.assoc before.edge middle.edge after.edge)

end Mettapedia.CategoryTheory.InternalCategoryFunctorCategory
