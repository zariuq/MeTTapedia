import Mettapedia.CategoryTheory.ElementaryToposObjectUniverseLift
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor

/-!
# Object-universe lifting of geometric maps and ordinary cells

The action raises objects and retains the original morphisms and complete
natural-transformation components. Its finite-limit and left-adjoint
properties follow from the up/down equivalences and the supplied geometric
map. Identity, composition and horizontal substitution are actual laws,
so the size adapter is a strict pseudofunctor of the genuine topos
two-categories.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposObjectUniverseLift

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Bicategory

universe u v u₁ u₂

def liftFunctor {source : ElementaryTopos.{u₁,v}} {target : ElementaryTopos.{u₂,v}}
    (route : source ⥤ target) : raised source ⥤ raised target where
  obj object := ⟨route.obj object.down⟩
  map arrow := route.map arrow
  map_id object := route.map_id object.down
  map_comp first second := route.map_comp first second

theorem liftFunctor_factorization {source : ElementaryTopos.{u₁,v}}
    {target : ElementaryTopos.{u₂,v}} (route : source ⥤ target) :
    liftFunctor route = down source ⋙ route ⋙ up target := rfl

set_option backward.isDefEq.respectTransparency false in
def map {source : ElementaryTopos.{u₁,v}} {target : ElementaryTopos.{u₂,v}}
    (route : ElementaryTopos.GeometricHom source target) :
    ElementaryTopos.GeometricHom (raised source) (raised target) where
  functor := liftFunctor route.functor
  finite := by
    exact (ElementaryTopos.GeometricHom.comp (upGeometric target)
      (ElementaryTopos.GeometricHom.comp route (downGeometric source))).finite
  leftAdjoint := by
    exact (ElementaryTopos.GeometricHom.comp (upGeometric target)
      (ElementaryTopos.GeometricHom.comp route (downGeometric source))).leftAdjoint

def map₂ {source : ElementaryTopos.{u₁,v}} {target : ElementaryTopos.{u₂,v}}
    {first second : ElementaryTopos.GeometricHom source target}
    (change : first.functor ⟶ second.functor) :
    (map first).functor ⟶ (map second).functor where
  app object := change.app object.down
  naturality _ _ arrow := change.naturality arrow

@[simp] theorem map_obj_down {source : ElementaryTopos.{u₁,v}}
    {target : ElementaryTopos.{u₂,v}} (route : ElementaryTopos.GeometricHom source target)
    (object : raised source) :
    ((map route).functor.obj object).down = route.functor.obj object.down := rfl

@[simp] theorem map_arrow_readout {source : ElementaryTopos.{u₁,v}}
    {target : ElementaryTopos.{u₂,v}} (route : ElementaryTopos.GeometricHom source target)
    {first second : raised source} (arrow : first ⟶ second) :
    (down target).map ((map route).functor.map arrow) =
      route.functor.map ((down source).map arrow) := rfl

@[simp] theorem map₂_readout {source : ElementaryTopos.{u₁,v}}
    {target : ElementaryTopos.{u₂,v}} {first second : ElementaryTopos.GeometricHom source target}
    (change : first.functor ⟶ second.functor) (object : raised source) :
    (down target).map ((map₂ change).app object) = change.app ((down source).obj object) := rfl

@[simp] theorem map_identity (source : ElementaryTopos.{u,v}) :
    map (ElementaryTopos.GeometricHom.id source) =
      ElementaryTopos.GeometricHom.id (raised source) := by
  apply ElementaryTopos.GeometricHom.ext
  rfl

@[simp] theorem map_composition {source middle target : ElementaryTopos.{u,v}}
    (first : ElementaryTopos.GeometricHom source middle)
    (second : ElementaryTopos.GeometricHom middle target) :
    map (ElementaryTopos.GeometricHom.comp second first) =
      ElementaryTopos.GeometricHom.comp (map second) (map first) := by
  apply ElementaryTopos.GeometricHom.ext
  rfl

@[simp] theorem map₂_identity {source target : ElementaryTopos.{u,v}}
    (route : ElementaryTopos.GeometricHom source target) :
    map₂ (𝟙 route.functor) = 𝟙 (map route).functor := rfl

@[simp] theorem map₂_composition {source target : ElementaryTopos.{u,v}}
    {first middle last : ElementaryTopos.GeometricHom source target}
    (earlier : first.functor ⟶ middle.functor) (later : middle.functor ⟶ last.functor) :
    map₂ (earlier ≫ later) = map₂ earlier ≫ map₂ later := rfl

/-- Both objects and all cells are carried, with their original hom sizes. -/
def action : StrictPseudofunctor ElementaryTopos.{u,v} ElementaryTopos.{max u v,v} :=
  StrictPseudofunctor.mk'' {
    obj := raised
    map := map
    map₂ := map₂
    map₂_id := map₂_identity
    map₂_comp := map₂_composition
    map_id := map_identity
    map_comp := map_composition
    map₂_whisker_left := by
      intro source middle target first second third change
      apply NatTrans.ext
      funext object
      change change.app (first.functor.obj object.down) =
        𝟙 _ ≫ change.app (first.functor.obj object.down) ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
    map₂_whisker_right := by
      intro source middle target first second change last
      apply NatTrans.ext
      funext object
      change last.functor.map (change.app object.down) =
        𝟙 _ ≫ last.functor.map (change.app object.down) ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
  }

end Mettapedia.CategoryTheory.ElementaryToposObjectUniverseLift
