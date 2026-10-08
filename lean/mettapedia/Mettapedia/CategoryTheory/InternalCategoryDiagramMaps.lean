import Mettapedia.CategoryTheory.InternalCategoryDiagram

/-!+# Complete internal functors from category-valued diagram maps

An actual diagram transformation acts on every object and every supplied
arrow. Its ordinary naturality square earns the two presheaf actions. The
unit and composition laws concern the whole chosen composable-edge pullback,
including its matching equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryDiagramMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open InternalCategoryDiagram

universe u v w

variable {B : Type u} [Category.{v} B]
variable {first second : B ⥤ Cat.{w,w}} (map : first ⟶ second)

theorem functor_square {X Y : B} (change : X ⟶ Y) :
    (first.map change).toFunctor ⋙ (map.app Y).toFunctor =
      (map.app X).toFunctor ⋙ (second.map change).toFunctor :=
  congrArg Cat.Hom.toFunctor (map.naturality change)

def vertices : InternalCategoryDiagram.vertices first ⟶
    InternalCategoryDiagram.vertices second where
  app X := TypeCat.ofHom (map.app X).toFunctor.obj
  naturality X Y change := by
    apply ConcreteCategory.hom_ext
    intro object
    exact congrArg (fun F => F.obj object) (functor_square map change)

def arrows : InternalCategoryDiagram.arrows first ⟶
    InternalCategoryDiagram.arrows second where
  app X := TypeCat.ofHom (Arrow.map (map.app X).toFunctor)
  naturality X Y change := by
    apply ConcreteCategory.hom_ext
    intro arrow
    change Arrow.map (map.app Y).toFunctor (Arrow.map (first.map change).toFunctor arrow) =
      Arrow.map (second.map change).toFunctor (Arrow.map (map.app X).toFunctor arrow)
    exact congrArg (fun F => Arrow.map F arrow) (functor_square map change)

def graphMap : InternalGraph.Hom (graph first) (graph second) where
  vertex := vertices map
  edge := arrows map
  source := by ext X arrow; rfl
  target := by ext X arrow; rfl

theorem composable_first (X : B) (pair : (Pairs first).obj X) :
    InternalCategoryDiagram.first second X ((graphMap map).composableMap.app X pair) =
      Arrow.map (map.app X).toFunctor (InternalCategoryDiagram.first first X pair) := by
  exact congrArg (fun (arrow : Pairs first ⟶ InternalCategoryDiagram.arrows second) =>
    arrow.app X pair) (InternalGraph.Hom.composableMap_first (graphMap map))

theorem composable_second (X : B) (pair : (Pairs first).obj X) :
    InternalCategoryDiagram.second second X ((graphMap map).composableMap.app X pair) =
      Arrow.map (map.app X).toFunctor (InternalCategoryDiagram.second first X pair) := by
  exact congrArg (fun (arrow : Pairs first ⟶ InternalCategoryDiagram.arrows second) =>
    arrow.app X pair) (InternalGraph.Hom.composableMap_second (graphMap map))

/-- An actual internal functor, including the full composable-edge square. -/
def internalFunctor : InternalCategory.Hom (category first) (category second) where
  toHom := graphMap map
  unit := by
    ext X object
    exact Arrow.map_unit (map.app X).toFunctor object
  composition := by
    ext X pair
    change Arrow.map (map.app X).toFunctor
        (Arrow.compose (InternalCategoryDiagram.first first X pair)
          (InternalCategoryDiagram.second first X pair) _) =
      Arrow.compose
        (InternalCategoryDiagram.first second X ((graphMap map).composableMap.app X pair))
        (InternalCategoryDiagram.second second X ((graphMap map).composableMap.app X pair)) _
    exact (Arrow.map_compose (map.app X).toFunctor _ _ _).trans
      (Arrow.compose_congr (composable_first map X pair).symm
        (composable_second map X pair).symm _ _)

theorem vertex_readout (X : B) (object : first.obj X) :
    (internalFunctor map).vertex.app X object = (map.app X).toFunctor.obj object := rfl

theorem edge_readout (X : B) (arrow : InternalCategoryDiagram.Arrow (first.obj X)) :
    (internalFunctor map).edge.app X arrow = Arrow.map (map.app X).toFunctor arrow := rfl

theorem identity_vertex : vertices (𝟙 first) = 𝟙 (InternalCategoryDiagram.vertices first) := rfl

theorem identity_edge : arrows (𝟙 first) = 𝟙 (InternalCategoryDiagram.arrows first) := rfl

theorem composition_vertex {third : B ⥤ Cat.{w,w}} (next : second ⟶ third) :
    vertices (map ≫ next) = vertices map ≫ vertices next := rfl

theorem composition_edge {third : B ⥤ Cat.{w,w}} (next : second ⟶ third) :
    arrows (map ≫ next) = arrows map ≫ arrows next := rfl

end Mettapedia.CategoryTheory.InternalCategoryDiagramMaps
