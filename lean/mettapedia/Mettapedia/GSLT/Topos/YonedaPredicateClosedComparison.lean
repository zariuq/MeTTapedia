import Mettapedia.GSLT.Topos.PresheafPredicateCartesianClosed
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Canonical closed comparison of the Yoneda embedding

For a cartesian closed small category, the actual canonical exponential
comparison of Yoneda is invertible. The proof constructs its full generalized
element bijection from base transposition, the fully faithful Yoneda map,
the canonical product comparison and presheaf transposition. Thus the
representing isomorphism is earned from the selected base closed structure.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.YonedaClosed

open _root_.CategoryTheory
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed Opposite

universe u
variable {C : Type u} [Category.{u} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]

/-- The canonical comparison transports actual base transposition to
presheaf transposition through the inverse product comparison. -/
theorem map_curry {X Y U : C} (body : X ⊗ U ⟶ Y) :
    yoneda.map (curry body) ≫ (expComparison (yoneda (C := C)) X).natTrans.app Y =
      curry (inv (prodComparison (yoneda (C := C)) X U) ≫ yoneda.map body) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_expComparison, uncurry_curry]
  rw [← Category.assoc, ← prodComparison_inv_natural_whiskerLeft,
    Category.assoc, ← yoneda.map_comp, ← uncurry_eq, uncurry_curry]

/-- Precomposition with the actual inverse product comparison is a bijection. -/
noncomputable def productHomEquiv (X U Y : C) :
    (yoneda.obj (X ⊗ U) ⟶ yoneda.obj Y) ≃
      (yoneda.obj X ⊗ yoneda.obj U ⟶ yoneda.obj Y) where
  toFun body := inv (prodComparison (yoneda (C := C)) X U) ≫ body
  invFun body := prodComparison (yoneda (C := C)) X U ≫ body
  left_inv body := by simp
  right_inv body := by simp

/-- The complete bijection of generalized exponential elements. -/
noncomputable def sectionEquiv (X Y U : C) :
    (U ⟶ (ihom X).obj Y) ≃ ((ihom (yoneda.obj X)).obj (yoneda.obj Y)).obj (op U) :=
  ((ihom.adjunction X).homEquiv U Y).symm |>.trans
    (Yoneda.fullyFaithful.homEquiv.trans
      ((productHomEquiv X U Y).trans
        (((ihom.adjunction (yoneda.obj X)).homEquiv (yoneda.obj U) (yoneda.obj Y)).trans
          _root_.CategoryTheory.yonedaEquiv)))

/-- The independently constructed bijection is the actual canonical
comparison at every generalized element. -/
theorem sectionEquiv_readout (X Y U : C) (function : U ⟶ (ihom X).obj Y) :
    sectionEquiv X Y U function =
      ((expComparison (yoneda (C := C)) X).natTrans.app Y).app (op U) function := by
  change _root_.CategoryTheory.yonedaEquiv (curry (inv (prodComparison (yoneda (C := C)) X U) ≫
    yoneda.map (uncurry function))) = _
  rw [← map_curry, curry_uncurry, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-- Every component of the canonical exponential comparison is invertible. -/
noncomputable instance comparison_component_iso (X Y : C) :
    IsIso ((expComparison (yoneda (C := C)) X).natTrans.app Y) := by
  have (U : Cᵒᵖ) :
      IsIso (((expComparison (yoneda (C := C)) X).natTrans.app Y).app U) := by
    apply (_root_.CategoryTheory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun function : U.unop ⟶ (ihom X).obj Y =>
      ((expComparison (yoneda (C := C)) X).natTrans.app Y).app U function)
    have reading : (fun function : U.unop ⟶ (ihom X).obj Y =>
        ((expComparison (yoneda (C := C)) X).natTrans.app Y).app U function) =
        sectionEquiv X Y U.unop := by
      funext function
      exact (sectionEquiv_readout X Y U.unop function).symm
    rw [reading]
    exact (sectionEquiv X Y U.unop).bijective
  exact NatIso.isIso_of_isIso_app _

/-- Yoneda is closed through its actual canonical exponential comparison. -/
noncomputable instance closedFunctor : MonoidalClosedFunctor (yoneda (C := C)) where
  comparison_iso _X := NatIso.isIso_of_isIso_app _

/-- The earned representing isomorphism, with its canonical comparison hom. -/
noncomputable def exponentialIso (X Y : C) :
    yoneda.obj ((ihom X).obj Y) ≅ (ihom (yoneda.obj X)).obj (yoneda.obj Y) :=
  asIso ((expComparison (yoneda (C := C)) X).natTrans.app Y)

theorem exponentialIso_hom (X Y : C) :
    (exponentialIso X Y).hom = (expComparison (yoneda (C := C)) X).natTrans.app Y := rfl

/-- The representing isomorphism preserves actual evaluation. -/
theorem exponentialIso_evaluation (X Y : C) :
    yoneda.obj X ◁ (exponentialIso X Y).hom ≫
        (ihom.ev (yoneda.obj X)).app (yoneda.obj Y) =
      inv (prodComparison (yoneda (C := C)) X ((ihom X).obj Y)) ≫
        yoneda.map ((ihom.ev X).app Y) :=
  expComparison_ev (yoneda (C := C)) X Y

end Mettapedia.GSLT.Topos.YonedaClosed
