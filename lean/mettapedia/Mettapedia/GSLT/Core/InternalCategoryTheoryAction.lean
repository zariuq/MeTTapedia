import Mettapedia.GSLT.Core.LambdaTheoryBicategory
import Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportCoherence

/-!
# Actual action of closed theory maps on internal operational categories

Every independently supplied closed theory has the category of its actual
internal categories and complete internal functors. A closed theory map
transports these structures through its earned finite-limit comparisons.
Natural theory cells act on entire vertex and edge objects. Canonical unit
and composition comparisons satisfy all pseudofunctor coherence laws.

The target is Cat: no logical classifier, dependent type structure or
behavioral congruence is inferred from this operational category action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.InternalCategoryTheoryAction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory InternalCategoryFunctorCategory
open InternalCategoryFiniteLimitTransportFunctor (action)

universe u v

def modelCategory (theory : LambdaTheory.{u,v}) : Cat.{v,max u v} :=
  Cat.of (InternalCategory theory.Obj)

def operationalModels : Pseudofunctor LambdaTheory.{u,v} Cat.{v,max u v} where
  obj := modelCategory
  map route := (action route.functor).toCatHom
  map₂ cell := (InternalCategoryFiniteLimitTransportCells.transformation cell).toCatHom₂
  map₂_id route := by
    apply Cat.Hom₂.ext
    exact InternalCategoryFiniteLimitTransportCells.whole_identity
  map₂_comp before after := by
    apply Cat.Hom₂.ext
    exact InternalCategoryFiniteLimitTransportCells.whole_vertical_composition before after
  mapId _ := Cat.Hom.isoMk InternalCategoryFiniteLimitTransportCoherence.identityComparison
  mapComp before after := Cat.Hom.isoMk
    (InternalCategoryFiniteLimitTransportComposition.comparison before.functor after.functor)
  map₂_whisker_left := by
    intro source middle target before first second cell
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext original
    apply map_ext
    · change cell.app (before.functor.obj original.vertex) =
        𝟙 _ ≫ cell.app (before.functor.obj original.vertex) ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
    · change cell.app (before.functor.obj original.edge) =
        𝟙 _ ≫ cell.app (before.functor.obj original.edge) ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
  map₂_whisker_right := by
    intro source middle target first second cell after
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext original
    apply map_ext
    · change after.functor.map (cell.app original.vertex) =
        𝟙 _ ≫ after.functor.map (cell.app original.vertex) ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
    · change after.functor.map (cell.app original.edge) =
        𝟙 _ ≫ after.functor.map (cell.app original.edge) ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
  map₂_left_unitor := by
    intro source target route
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext original
    apply map_ext
    · change 𝟙 _ = 𝟙 _ ≫ route.functor.map (𝟙 _) ≫ 𝟙 _
      simp only [route.functor.map_id, Category.id_comp]
    · change 𝟙 _ = 𝟙 _ ≫ route.functor.map (𝟙 _) ≫ 𝟙 _
      simp only [route.functor.map_id, Category.id_comp]
  map₂_right_unitor := by
    intro source target route
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext original
    apply map_ext
    · change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
      simp only [Category.id_comp]
    · change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
      simp only [Category.id_comp]
  map₂_associator := by
    intro source middle next target before between after
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext original
    apply map_ext
    · change 𝟙 _ = 𝟙 _ ≫ after.functor.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
      simp only [after.functor.map_id, Category.id_comp]
    · change 𝟙 _ = 𝟙 _ ≫ after.functor.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
      simp only [after.functor.map_id, Category.id_comp]

theorem complete_vertex {source target : LambdaTheory.{u,v}} (route : source ⟶ target)
    {first second : InternalCategory source.Obj} (mapping : first ⟶ second) :
    (((operationalModels.map route).toFunctor).map mapping).vertex =
      route.functor.map mapping.vertex := rfl

theorem complete_edge {source target : LambdaTheory.{u,v}} (route : source ⟶ target)
    {first second : InternalCategory source.Obj} (mapping : first ⟶ second) :
    (((operationalModels.map route).toFunctor).map mapping).edge =
      route.functor.map mapping.edge := rfl

theorem complete_cell {source target : LambdaTheory.{u,v}} {first second : source ⟶ target}
    (cell : first ⟶ second) (original : InternalCategory source.Obj) :
    (((operationalModels.map₂ cell).toNatTrans).app original).edge = cell.app original.edge := rfl

end Mettapedia.GSLT.Core.InternalCategoryTheoryAction
