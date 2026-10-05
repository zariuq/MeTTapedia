import Mettapedia.TypeTheory.DisplayedPresheafComprehension
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Displayed presheaf families and the slice category

A dependent family over a presheaf is a functor on its category of
elements. Taking its total space gives an object of the slice over that
presheaf. Conversely, an arrow into the presheaf gives its actual fibres.
These constructions act on natural transformations and form an equivalence
of categories. The maps retain the elements of each fibre.

This is the family form of the standard equivalence between a presheaf
slice and presheaves on its category of elements; compare
`CategoryTheory.overEquivPresheafCostructuredArrow`. Here the total spaces
and fibres are the existing dependent-type constructions, so their
substitution and comprehension laws can be used through the equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafSlice

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafTransport DisplayedPresheafComprehension

universe u v w

variable {C : Type u} [Category.{v} C]
variable {P : Face.{u, v, w} C}

/-- A map of dependent families acts on the evidence coordinate of the
existing total presheaf and leaves its base coordinate fixed. -/
def totalHom {A B : DisplayedFamily.{u, v, w, w} P} (f : A ⟶ B) :
    totalSpace A ⟶ totalSpace B where
  app c := TypeCat.ofHom fun x => ⟨x.1, f.app ⟨c, x.1⟩ x.2⟩
  naturality := by
    intro c d g
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨P.map g x.1,
      f.app ⟨d, P.map g x.1⟩
        (A.map (CategoryOfElements.homMk _ _ g rfl) x.2)⟩ : TotalAt B d) =
      ⟨P.map g x.1,
        B.map (CategoryOfElements.homMk _ _ g rfl) (f.app ⟨c, x.1⟩ x.2)⟩
    exact congrArg (fun b => (⟨P.map g x.1, b⟩ : TotalAt B d))
      (f.naturality_apply
        (CategoryOfElements.homMk (F := P)
          ⟨c, x.1⟩ ⟨d, P.map g x.1⟩ g rfl) x.2)

@[simp] theorem totalHom_projection
    {A B : DisplayedFamily.{u, v, w, w} P} (f : A ⟶ B) :
    totalHom f ≫ totalProjection B = totalProjection A := by
  ext c x
  rfl

/-- Comprehension as a functor into the actual slice category. -/
def totalFunctor (P : Face.{u, v, w} C) :
    DisplayedFamily.{u, v, w, w} P ⥤ Over P where
  obj A := Over.mk (totalProjection A)
  map f := Over.homMk (totalHom f) (totalHom_projection f)
  map_id A := by
    ext c x
    rfl
  map_comp f g := by
    ext c x
    rfl

/-- An arrow of the slice transports the actual elements in its fibres. -/
def fibreHom {X Y : Over P} (f : X ⟶ Y) :
    observationFibreFamily X.hom ⟶ observationFibreFamily Y.hom where
  app p := TypeCat.ofHom fun x => ⟨f.left.app p.1 x.val, by
    have h := congrArg (fun k => k.app p.1 x.val) (Over.w f)
    exact h.trans x.property⟩
  naturality := by
    intro p q g
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact f.left.naturality_apply g.val x.val

/-- The inverse construction takes fibres without truncating their values. -/
def fibreFunctor (P : Face.{u, v, w} C) :
    Over P ⥤ DisplayedFamily.{u, v, w, w} P where
  obj X := observationFibreFamily X.hom
  map f := fibreHom f
  map_id X := by
    ext p x
    rfl
  map_comp f g := by
    ext p x
    rfl

/-- Recover a displayed value from the fibre of its own comprehension
projection. Only the equality of the base coordinate is used. -/
def projectionFibreEquiv (A : DisplayedFamily.{u, v, w, w} P)
    (p : P.Elements) :
    A.obj p ≃ (observationFibreFamily (totalProjection A)).obj p where
  toFun a := ⟨⟨p.2, a⟩, rfl⟩
  invFun x := by
    rcases p with ⟨c, p⟩
    rcases x with ⟨⟨q, a⟩, h⟩
    change q = p at h
    subst q
    exact a
  left_inv a := by cases p; rfl
  right_inv x := by
    rcases p with ⟨c, p⟩
    rcases x with ⟨⟨q, a⟩, h⟩
    change q = p at h
    subst q
    rfl

/-- The fibre of comprehension is naturally the original displayed family. -/
def projectionFibreIso (A : DisplayedFamily.{u, v, w, w} P) :
    A ≅ observationFibreFamily (totalProjection A) := by
  refine NatIso.ofComponents (fun p => (projectionFibreEquiv A p).toIso) ?_
  intro p q g
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  rcases p with ⟨c, p⟩
  rcases q with ⟨d, q⟩
  rcases g with ⟨g, h⟩
  change c ⟶ d at g
  change P.map g p = q at h
  subst q
  rfl

/-- The unit is natural in maps of dependent families. -/
def unitIso (P : Face.{u, v, w} C) :
    𝟭 (DisplayedFamily.{u, v, w, w} P) ≅ totalFunctor P ⋙ fibreFunctor P := by
  refine NatIso.ofComponents projectionFibreIso ?_
  intro A B f
  ext p a
  rfl

/-- The counit recovers the source of each slice object over the same base. -/
def counitIso (P : Face.{u, v, w} C) :
    fibreFunctor P ⋙ totalFunctor P ≅ 𝟭 (Over P) := by
  refine NatIso.ofComponents
    (fun X => Over.isoMk (observationTotalIso X.hom)
      (observationTotalIso_projection X.hom)) ?_
  intro X Y f
  ext c a
  rfl

/-- Dependent families and slice objects are equivalent as categories,
using the existing total-space and fibre constructions. -/
def equivalence (P : Face.{u, v, w} C) :
    DisplayedFamily.{u, v, w, w} P ≌ Over P where
  functor := totalFunctor P
  inverse := fibreFunctor P
  unitIso := unitIso P
  counitIso := counitIso P
  functor_unitIso_comp A := by
    ext c a
    rfl

/-- Natural dependent terms are exactly maps from the terminal slice
object to comprehension. The equivalence keeps the term's chosen values. -/
def termEquiv (A : DisplayedFamily.{u, v, w, w} P) :
    A.sections ≃ (Over.mk (𝟙 P) ⟶ (totalFunctor P).obj A) :=
  (sectionEquivProjectionSplittings A).trans
    { toFun := fun s => Over.homMk s.val s.property
      invFun := fun f => ⟨f.left, Over.w f⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => Over.OverMorphism.ext rfl }

end Mettapedia.TypeTheory.DisplayedPresheafSlice
