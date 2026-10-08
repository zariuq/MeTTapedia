import Mettapedia.CategoryTheory.CanonicalSlicePullback
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# Unit triangles for the chosen slice comparisons

The natural comparisons are the pullback maps fixed by their projections.
Their coherence is proved on the complete slice morphisms, including the
transport induced by the base category's unit and associativity equations.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.CanonicalSlicePullback

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {first middle last : C} (f : first ⟶ middle) (g : middle ⟶ last)

theorem right_triangle :
    (composition f (𝟙 middle)).hom ≫
        (Functor.isoWhiskerRight (identity middle) (Over.pullback f)).hom ≫
        (Functor.leftUnitor (Over.pullback f)).hom =
      (transport (Category.comp_id f)).hom := by
  apply NatTrans.ext
  funext object
  change ((compositionInverse f (𝟙 middle)).inv.app object) ≫
    (Over.pullback f).map ((identity middle).hom.app object) ≫ 𝟙 _ = _
  rw [right_unit]
  simp only [Category.comp_id, Iso.inv_hom_id_app_assoc]

theorem left_triangle :
    (composition (𝟙 first) f).hom ≫
        (Functor.isoWhiskerLeft (Over.pullback f) (identity first)).hom ≫
        (Functor.rightUnitor (Over.pullback f)).hom =
      (transport (Category.id_comp f)).hom := by
  apply NatTrans.ext
  funext object
  change ((compositionInverse (𝟙 first) f).inv.app object) ≫
    (identity first).hom.app ((Over.pullback f).obj object) ≫ 𝟙 _ = _
  rw [left_unit]
  simp only [Category.comp_id, Iso.inv_hom_id_app_assoc]

theorem associative_pasting {final : C} (h : last ⟶ final) :
    (Functor.isoWhiskerRight (compositionInverse g h) (Over.pullback f)).hom ≫
        (compositionInverse f (g ≫ h)).hom =
      (Functor.associator (Over.pullback h) (Over.pullback g) (Over.pullback f)).hom ≫
        (Functor.isoWhiskerLeft (Over.pullback h) (compositionInverse f g)).hom ≫
        (compositionInverse (f ≫ g) h).hom ≫
        (transport (Category.assoc f g h)).hom := by
  apply NatTrans.ext
  funext object
  change _ = 𝟙 _ ≫ _
  rw [Category.id_comp]
  exact associativity f g h object

theorem forward_pentagon {final : C} (h : last ⟶ final) :
    (composition f (g ≫ h)).hom ≫
        (Functor.isoWhiskerRight (composition g h) (Over.pullback f)).hom ≫
        (Functor.associator (Over.pullback h) (Over.pullback g) (Over.pullback f)).hom ≫
        (Functor.isoWhiskerLeft (Over.pullback h) (compositionInverse f g)).hom ≫
        (compositionInverse (f ≫ g) h).hom =
      (transport (Category.assoc f g h)).inv := by
  apply (cancel_mono (transport (Category.assoc f g h)).hom).mp
  simp only [Category.assoc]
  rw [← associative_pasting]
  change (compositionInverse f (g ≫ h)).inv ≫
      (Functor.isoWhiskerRight (compositionInverse g h) (Over.pullback f)).inv ≫
      (Functor.isoWhiskerRight (compositionInverse g h) (Over.pullback f)).hom ≫
      (compositionInverse f (g ≫ h)).hom = _
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id]

end Mettapedia.CategoryTheory.CanonicalSlicePullback
