import Mettapedia.OSLF.Syntax.PresheafStructuredExtensionCore
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# A colimit-generated interpretation beyond one representable

The actual Yoneda extension of the coproduct of two representables is
the coproduct of their meanings. Both injections are tracked through the
comparison, and maps on this presheaf remain uniquely determined by density.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Mettapedia.CategoryTheory.PresheafStructuredExtension

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe w u v
variable {C : Type} [Category C]
variable {D : Type u} [Category.{v} D]
variable [HasColimitsOfSize.{0, max w v} D]

local instance : HasColimitsOfSize.{0, 0} D := hasColimitsOfSizeShrink.{0, 0} D

/-- The actual extension on a two-summand colimit of representables. -/
def extensionCoproductIso (F : C ⥤ D) (a b : C) :
    ((embedding.{w, 0, 0, v} (C := C)).lan.obj F).obj
      (embedding.{w, 0, 0, v}.obj a ⨿ embedding.{w, 0, 0, v}.obj b) ≅
      F.obj a ⨿ F.obj b := by
  have : PreservesColimitsOfSize.{0, max w v}
      ((embedding.{w, 0, 0, v} (C := C)).lan.obj F) := extension_cocontinuous F
  have : PreservesColimitsOfSize.{0, 0}
      ((embedding.{w, 0, 0, v} (C := C)).lan.obj F) :=
    preservesColimitsOfSize_shrink.{0, max w v, 0, 0} _
  exact (asIso (coprodComparison ((embedding.{w, 0, 0, v} (C := C)).lan.obj F)
      (embedding.{w, 0, 0, v}.obj a) (embedding.{w, 0, 0, v}.obj b))).symm ≪≫
    coprod.mapIso (((unitIso.{w, 0, 0, v, u}).app F).app a).symm
      (((unitIso.{w, 0, 0, v, u}).app F).app b).symm

/-- The first summand is interpreted through the original meaning of a. -/
theorem extensionCoproductIso_inl (F : C ⥤ D) (a b : C) :
    ((embedding.{w, 0, 0, v} (C := C)).lan.obj F).map
      (coprod.inl : embedding.{w, 0, 0, v}.obj a ⟶
        embedding.{w, 0, 0, v}.obj a ⨿ embedding.{w, 0, 0, v}.obj b) ≫
      (extensionCoproductIso.{w, u, v} F a b).hom =
      ((unitIso.{w, 0, 0, v, u}).app F).inv.app a ≫ coprod.inl := by
  have : PreservesColimitsOfSize.{0, max w v}
      ((embedding.{w, 0, 0, v} (C := C)).lan.obj F) := extension_cocontinuous F
  have : PreservesColimitsOfSize.{0, 0}
      ((embedding.{w, 0, 0, v} (C := C)).lan.obj F) :=
    preservesColimitsOfSize_shrink.{0, max w v, 0, 0} _
  dsimp [extensionCoproductIso, coprod.mapIso, unitIso, extend, restrict]
  rw [← Category.assoc, map_inl_inv_coprodComparison, coprod.inl_map]

/-- The second summand is interpreted through the original meaning of b. -/
theorem extensionCoproductIso_inr (F : C ⥤ D) (a b : C) :
    ((embedding.{w, 0, 0, v} (C := C)).lan.obj F).map
      (coprod.inr : embedding.{w, 0, 0, v}.obj b ⟶
        embedding.{w, 0, 0, v}.obj a ⨿ embedding.{w, 0, 0, v}.obj b) ≫
      (extensionCoproductIso.{w, u, v} F a b).hom =
      ((unitIso.{w, 0, 0, v, u}).app F).inv.app b ≫ coprod.inr := by
  have : PreservesColimitsOfSize.{0, max w v}
      ((embedding.{w, 0, 0, v} (C := C)).lan.obj F) := extension_cocontinuous F
  have : PreservesColimitsOfSize.{0, 0}
      ((embedding.{w, 0, 0, v} (C := C)).lan.obj F) :=
    preservesColimitsOfSize_shrink.{0, max w v, 0, 0} _
  dsimp [extensionCoproductIso, coprod.mapIso, unitIso, extend, restrict]
  rw [← Category.assoc, map_inr_inv_coprodComparison, coprod.inr_map]

/-- Density determines maps even on the two-summand colimit, not just on
individual representables. -/
theorem extension_maps_equal_on_coproduct
    {L K : CocontinuousFunctors.{w, 0, 0, v, u} (C := C) (D := D)} (α β : L ⟶ K)
    (same : (restrict.{w, 0, 0, v, u}).map α = (restrict.{w, 0, 0, v, u}).map β)
    (a b : C) :
    α.hom.app (embedding.{w, 0, 0, v}.obj a ⨿ embedding.{w, 0, 0, v}.obj b) =
      β.hom.app (embedding.{w, 0, 0, v}.obj a ⨿ embedding.{w, 0, 0, v}.obj b) := by
  have equal : α = β := (equivalence.{w, 0, 0, v, u}).inverse.map_injective same
  exact congrArg (fun f => f.hom.app
    (embedding.{w, 0, 0, v}.obj a ⨿ embedding.{w, 0, 0, v}.obj b)) equal

end Mettapedia.CategoryTheory.PresheafStructuredExtension
