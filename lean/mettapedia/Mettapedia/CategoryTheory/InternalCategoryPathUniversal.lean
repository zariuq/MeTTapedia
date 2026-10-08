import Mettapedia.CategoryTheory.InternalCategoryPathMaps
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Universal interpretation of retained paths

An independently supplied natural interpretation of vertices and individual
events extends to the whole path diagram. The extension composes exactly
the supplied event arrows and is unique at every context simultaneously.
Its complete internal functor acts on identities, matching composition and
all future maps. The target is an arbitrary category-valued diagram; no
behavioral equation or recovery of erased occurrences is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryPathUniversal

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open InternalCategoryPathDiagram

universe u v w
variable {B : Type u} [Category.{v} B]

abbrev freeDiagrams : (B ⥤ Quiv.{w,w}) ⥤ (B ⥤ Cat.{w,w}) :=
  (Functor.whiskeringRight B Quiv.{w,w} Cat.{w,w}).obj Cat.free

abbrev forgetDiagrams : (B ⥤ Cat.{w,w}) ⥤ (B ⥤ Quiv.{w,w}) :=
  (Functor.whiskeringRight B Cat.{w,w} Quiv.{w,w}).obj Quiv.forget

/-- The actual free/forgetful adjunction, lifted over all contexts. -/
def adjunction :
    (Functor.whiskeringRight B Quiv.{w,w} Cat.{w,w}).obj Cat.free ⊣
      (Functor.whiskeringRight B Cat.{w,w} Quiv.{w,w}).obj Quiv.forget :=
  Quiv.adj.{w,w}.whiskerRight B

variable (graph : InternalGraph (B ⥤ Type w)) (target : B ⥤ Cat.{w,w})

def interpretationEquiv : (diagram graph ⟶ target) ≃
    (quiverDiagram graph ⟶ target ⋙ Quiv.forget) :=
  (Quiv.adj.{w,w}.whiskerRight B).homEquiv (quiverDiagram graph) target

def extend (events : quiverDiagram graph ⟶ target ⋙ Quiv.forget) :
    diagram graph ⟶ target := (interpretationEquiv graph target).symm events

def restrict (paths : diagram graph ⟶ target) :
    quiverDiagram graph ⟶ target ⋙ Quiv.forget := interpretationEquiv graph target paths

theorem restrict_extend (events : quiverDiagram graph ⟶ target ⋙ Quiv.forget) :
    restrict graph target (extend graph target events) = events :=
  (interpretationEquiv graph target).apply_symm_apply events

theorem extend_restrict (paths : diagram graph ⟶ target) :
    extend graph target (restrict graph target paths) = paths :=
  (interpretationEquiv graph target).symm_apply_apply paths

theorem extension_unique (events : quiverDiagram graph ⟶ target ⋙ Quiv.forget)
    (candidate : diagram graph ⟶ target)
    (generators : restrict graph target candidate = events) :
    candidate = extend graph target events := by
  apply (interpretationEquiv graph target).injective
  exact generators.trans (restrict_extend graph target events).symm

variable (events : quiverDiagram graph ⟶ target ⋙ Quiv.forget)

/-- The full internal interpretation, including its earned composition law. -/
def internalFunctor : InternalCategory.Hom (category graph)
    (InternalCategoryDiagram.category target) :=
  InternalCategoryDiagramMaps.internalFunctor (extend graph target events)

theorem complete_vertex (X : B) (object : Vertex graph X) :
    (internalFunctor graph target events).vertex.app X object = (events.app X).obj object := rfl

theorem complete_path (X : B)
    (path : InternalCategoryDiagram.Arrow ((diagram graph).obj X)) :
    (internalFunctor graph target events).edge.app X path =
      ⟨(events.app X).obj path.1, (events.app X).obj path.2.1,
        composePath ((events.app X).mapPath path.2.2)⟩ := rfl

theorem complete_event (X : B) (supplied : graph.edge.obj X) :
    (internalFunctor graph target events).edge.app X (edge graph X supplied) =
      ⟨(events.app X).obj (graph.source.app X supplied),
        (events.app X).obj (graph.target.app X supplied),
        (events.app X).map ⟨supplied, rfl, rfl⟩⟩ := by
  rw [complete_path]
  change (⟨_, _, composePath ((events.app X).mapPath
    (@Quiver.Hom.toPath (Vertex graph X) (quiver graph X) _ _
      ⟨supplied, rfl, rfl⟩))⟩ : InternalCategoryDiagram.Arrow (target.obj X)) = _
  rw [Prefunctor.mapPath_toPath, composePath_toPath]

theorem complete_composition (X : B)
    (first second : InternalCategoryDiagram.Arrow ((diagram graph).obj X))
    (matching : InternalCategoryDiagram.Arrow.target first =
      InternalCategoryDiagram.Arrow.source second) :
    (internalFunctor graph target events).edge.app X
        (InternalCategoryDiagram.Arrow.compose first second matching) =
      InternalCategoryDiagram.Arrow.compose
        ((internalFunctor graph target events).edge.app X first)
        ((internalFunctor graph target events).edge.app X second)
        (congrArg ((extend graph target events).app X).toFunctor.obj matching) :=
  InternalCategoryDiagram.Arrow.map_compose
    ((extend graph target events).app X).toFunctor first second matching

theorem complete_future {X Y : B} (change : X ⟶ Y)
    (path : InternalCategoryDiagram.Arrow ((diagram graph).obj X)) :
    (InternalCategoryDiagram.category target).edge.map change
        ((internalFunctor graph target events).edge.app X path) =
      (internalFunctor graph target events).edge.app Y ((category graph).edge.map change path) :=
  (NatTrans.naturality_apply (internalFunctor graph target events).edge change path).symm

end Mettapedia.CategoryTheory.InternalCategoryPathUniversal
