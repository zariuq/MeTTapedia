import Mathlib.CategoryTheory.Equivalence

/-!
# The image of a functor with retained arrow origins

An image arrow contains the actual target arrow, its source origin and
their comparison equation. Forgetting the origin maps into the target
category. Keeping it instead gives a category equivalent to the source,
even when the functor itself is neither full nor faithful. This does not
assert that arbitrary target arrows admit such origins.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.FunctorOriginImage

open _root_.CategoryTheory

universe u v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]

structure Object (F : C ⥤ D) where
  source : C

structure Arrow (F : C ⥤ D) (before after : Object F) where
  target : F.obj before.source ⟶ F.obj after.source
  source : before.source ⟶ after.source
  agrees : F.map source = target

@[ext] theorem Arrow.ext {F : C ⥤ D} {before after : Object F}
    {first second : Arrow F before after} (same : first.source = second.source) :
    first = second := by
  cases first with
  | mk ft fs fa =>
    cases second with
    | mk st ss sa =>
      dsimp at same
      cases same
      have targetSame : ft = st := fa.symm.trans sa
      cases targetSame
      rfl

instance (F : C ⥤ D) : Category (Object F) where
  Hom := Arrow F
  id before := ⟨𝟙 _, 𝟙 before.source, F.map_id before.source⟩
  comp first second := ⟨first.target ≫ second.target, first.source ≫ second.source,
    by rw [F.map_comp, first.agrees, second.agrees]⟩
  id_comp _ := Arrow.ext (Category.id_comp _)
  comp_id _ := Arrow.ext (Category.comp_id _)
  assoc _ _ _ := Arrow.ext (Category.assoc _ _ _)

/-- Include a source arrow together with its literal target translation. -/
def embed (F : C ⥤ D) : C ⥤ Object F where
  obj source := ⟨source⟩
  map source := ⟨F.map source, source, rfl⟩
  map_id _ := Arrow.ext rfl
  map_comp _ _ := Arrow.ext rfl

def recover (F : C ⥤ D) : Object F ⥤ C where
  obj point := point.source
  map arrow := arrow.source

/-- Execute or otherwise interpret the independently supplied target
arrow. The stored equation ensures compatibility with its source origin. -/
def forget (F : C ⥤ D) : Object F ⥤ D where
  obj point := F.obj point.source
  map arrow := arrow.target

theorem embed_forget (F : C ⥤ D) : embed F ⋙ forget F = F := rfl

/-- Retained origins cover both objects and arrows of the admitted image;
this equivalence is not an equivalence with the full target category. -/
def equivalence (F : C ⥤ D) : C ≌ Object F where
  functor := embed F
  inverse := recover F
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro before after arrow
    change arrow ≫ 𝟙 after = 𝟙 before ≫ arrow
    simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro before after arrow
    apply Arrow.ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm)
  functor_unitIso_comp _ := Arrow.ext (Category.comp_id _)

theorem translated_target (F : C ⥤ D) {before after : C} (arrow : before ⟶ after) :
    ((equivalence F).functor.map arrow).target = F.map arrow := rfl

theorem recovered_origin (F : C ⥤ D) {before after : Object F} (arrow : before ⟶ after) :
    (equivalence F).functor.map ((equivalence F).inverse.map arrow) = arrow :=
  Arrow.ext rfl

end Mettapedia.CategoryTheory.FunctorOriginImage
