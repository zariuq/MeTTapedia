import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Equivalence

/-!
# Cocomplete extensions along the lifted Yoneda embedding

Restriction along Yoneda is an equivalence between functors on the base
and functors on its presheaves preserving the colimits used by density.
The morphisms are all natural transformations, including noninvertible ones.
The universe bounds expose the size of the category-of-elements colimits.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.CategoryTheory.PresheafStructuredExtension

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe w vC uC vD uD
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

set_option linter.checkUnivs false in
/-- Presheaves large enough for both the base and target hom universes. -/
abbrev Presheaves (C : Type uC) [Category.{vC} C] := Cᵒᵖ ⥤ Type (max w vC vD)

/-- Colimits of exactly the sizes occurring in the density presentation. -/
def Cocontinuous : ObjectProperty (Presheaves.{w, vC, uC, vD} C ⥤ D) :=
  fun L => PreservesColimitsOfSize.{vC, max w uC vC vD} L

/-- The full category of density-colimit-preserving presheaf functors. -/
abbrev CocontinuousFunctors := (Cocontinuous.{w, vC, uC, vD, uD} (C := C) (D := D)).FullSubcategory

variable [HasColimitsOfSize.{vC, max w uC vC vD} D]

set_option linter.checkUnivs false in
/-- The actual lifted Yoneda functor at the declared presheaf universe. -/
abbrev embedding : C ⥤ Presheaves.{w, vC, uC, vD} C := uliftYoneda.{max w vD}

/-- Density-colimit preservation for the actual chosen left Kan extension. -/
theorem extension_cocontinuous (F : C ⥤ D) :
    Cocontinuous.{w, vC, uC, vD, uD} ((embedding.{w, vC, uC, vD} (C := C)).lan.obj F) := by
  change PreservesColimitsOfSize.{vC, max w uC vC vD}
    (uliftYoneda.{max w vD}.leftKanExtension F)
  infer_instance

/-- Left Kan extension on objects and every natural transformation. -/
def extend : (C ⥤ D) ⥤ CocontinuousFunctors.{w, vC, uC, vD, uD} (C := C) (D := D) :=
  (Cocontinuous.{w, vC, uC, vD, uD} (C := C) (D := D)).lift (embedding.{w, vC, uC, vD} (C := C)).lan
    extension_cocontinuous

/-- Restriction is precomposition with the lifted Yoneda embedding. -/
def restrict : CocontinuousFunctors.{w, vC, uC, vD, uD} (C := C) (D := D) ⥤ (C ⥤ D) :=
  (Cocontinuous.{w, vC, uC, vD, uD} (C := C) (D := D)).ι ⋙
    (Functor.whiskeringLeft C (Presheaves.{w, vC, uC, vD} C) D).obj embedding.{w, vC, uC, vD}

/-- Extending and restricting a base functor gives it back, naturally on all maps. -/
def unitIso : 𝟭 (C ⥤ D) ≅ extend.{w, vC, uC, vD, uD} (C := C) (D := D) ⋙ restrict.{w, vC, uC, vD, uD} :=
  by
    haveI (F : C ⥤ D) : IsIso ((embedding.{w, vC, uC, vD} (C := C)).lanUnit.app F) := by
      change IsIso (uliftYoneda.{max w vD}.leftKanExtensionUnit F)
      infer_instance
    have unit : IsIso ((embedding.{w, vC, uC, vD} (C := C)).lanUnit (H := D)) :=
      NatIso.isIso_of_isIso_app _
    exact @asIso _ _ _ _ ((embedding.{w, vC, uC, vD} (C := C)).lanUnit (H := D))
      unit

/-- The adjunction counit is invertible on every cocontinuous extension. -/
theorem isIso_counit (L : CocontinuousFunctors.{w, vC, uC, vD, uD} (C := C) (D := D)) :
    IsIso (((embedding.{w, vC, uC, vD} (C := C)).lanAdjunction D).counit.app L.obj) := by
  let : PreservesColimitsOfSize.{vC, max w uC vC vD} L.obj := L.property
  apply ((embedding.{w, vC, uC, vD} (C := C)).isIso_lanAdjunction_counit_app_iff L.obj).mpr
  exact Presheaf.isLeftKanExtension_of_preservesColimits L.obj (Iso.refl _)

/-- Restricting and extending a cocontinuous functor gives it back,
naturally on every natural transformation. -/
def counitIso : restrict.{w, vC, uC, vD, uD} (C := C) (D := D) ⋙ extend.{w, vC, uC, vD, uD} ≅
    𝟭 (CocontinuousFunctors.{w, vC, uC, vD, uD} (C := C) (D := D)) :=
  NatIso.ofComponents
    (fun (L : CocontinuousFunctors.{w, vC, uC, vD, uD} (C := C) (D := D)) =>
      (Cocontinuous.{w, vC, uC, vD, uD} (C := C) (D := D)).isoMk
        (@asIso _ _ _ _ (((embedding.{w, vC, uC, vD} (C := C)).lanAdjunction D).counit.app L.obj)
          (isIso_counit L)))
    (fun {L K} α => by
      apply ObjectProperty.hom_ext
      exact (((embedding.{w, vC, uC, vD} (C := C)).lanAdjunction D).counit.naturality α.hom))

/-- The free cocompletion universal property, including noninvertible maps,
its unit and counit. -/
def equivalence : (C ⥤ D) ≌ CocontinuousFunctors.{w, vC, uC, vD, uD} (C := C) (D := D) :=
  _root_.CategoryTheory.Equivalence.mk extend.{w, vC, uC, vD, uD} restrict.{w, vC, uC, vD, uD}
    unitIso.{w, vC, uC, vD, uD} counitIso.{w, vC, uC, vD, uD}

end Mettapedia.CategoryTheory.PresheafStructuredExtension
