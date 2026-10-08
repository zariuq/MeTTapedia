import Mettapedia.CategoryTheory.RelativeClosedBasePreservation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxClosedReadout
import Mathlib.CategoryTheory.Monoidal.Closed.Functor

/-!
# Canonical closed base comparison from the local inverse diagrams

The complete evaluation equation determines the exponential comparison. The
generic theorem retains independent base object and hom universes. At a
common hom universe it identifies the constructed arrow with Mathlib's actual
`expComparison`, earning `MonoidalClosedFunctor` for the base inclusion.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory

universe u v w

variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]

theorem product_comparison_inv (first second : C) :
    (comparison (.product first second)).inv =
      inv (CartesianMonoidalCategory.prodComparison (base (C := C)) first second) := by
  apply IsIso.eq_inv_of_hom_inv_id
    (f := CartesianMonoidalCategory.prodComparison (base (C := C)) first second)
  exact (congrArg
    (fun incoming : (base (C := C)).obj (first ⊗ second) ⟶
        product ((base (C := C)).obj first) ((base (C := C)).obj second) =>
          incoming ≫ (comparison (.product first second)).inv)
    (product_comparison_hom first second).symm).trans
      (comparison (.product first second)).hom_inv_id

theorem product_exchange_square (first second : C) :
    CartesianMonoidalCategory.prodComparison (base (C := C)) first second ≫
      Interpretation.exchange ((base (C := C)).obj first) ((base (C := C)).obj second) =
    (base (C := C)).map (Interpretation.exchange first second) ≫
      CartesianMonoidalCategory.prodComparison (base (C := C)) second first := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, Interpretation.exchange_first,
      CartesianMonoidalCategory.prodComparison_fst, CartesianMonoidalCategory.prodComparison_snd,
      ← (base (C := C)).map_comp]
  · simp only [Category.assoc, Interpretation.exchange_second,
      CartesianMonoidalCategory.prodComparison_snd, CartesianMonoidalCategory.prodComparison_fst,
      ← (base (C := C)).map_comp]

theorem inverse_product_exchange (first second : C) :
    inv (CartesianMonoidalCategory.prodComparison (base (C := C)) first second) ≫
        (base (C := C)).map (Interpretation.exchange first second) =
      Interpretation.exchange ((base (C := C)).obj first) ((base (C := C)).obj second) ≫
        inv (CartesianMonoidalCategory.prodComparison (base (C := C)) second first) := by
  apply (cancel_mono (CartesianMonoidalCategory.prodComparison (base (C := C)) second first)).1
  rw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact (congrArg (fun outgoing =>
    inv (CartesianMonoidalCategory.prodComparison (base (C := C)) first second) ≫ outgoing)
    (product_exchange_square first second).symm).trans
      (IsIso.inv_hom_id_assoc
        (CartesianMonoidalCategory.prodComparison (base (C := C)) first second) _)

theorem canonicalExponentialComparison_uncurry (argument result : C) :
    MonoidalClosed.uncurry (canonicalExponentialComparison argument result) =
      inv (CartesianMonoidalCategory.prodComparison (base (C := C)) argument (argument ⟶[C] result)) ≫
        (base (C := C)).map ((ihom.ev argument).app result) := by
  let context := (base (C := C)).obj (argument ⟶[C] result)
  let input := (base (C := C)).obj argument
  let output := (base (C := C)).obj result
  have rightRead : unabstract (canonicalExponentialComparison argument result) =
      inv (CartesianMonoidalCategory.prodComparison (base (C := C)) (argument ⟶[C] result) argument) ≫
        (base (C := C)).map (Interpretation.evaluation argument result) :=
    (canonicalExponentialComparison_evaluation argument result).trans
      (congrArg (fun incoming : product context input ⟶
          (base (C := C)).obj ((argument ⟶[C] result) ⊗ argument) =>
            incoming ≫ (base (C := C)).map (Interpretation.evaluation argument result))
        (product_comparison_inv (argument ⟶[C] result) argument))
  have bodyRead :
      inv (CartesianMonoidalCategory.prodComparison (base (C := C)) (argument ⟶[C] result) argument) ≫
        (base (C := C)).map (Interpretation.evaluation argument result) =
      (GeneratedCategory.exchange context input).hom ≫
        (inv (CartesianMonoidalCategory.prodComparison (base (C := C)) argument (argument ⟶[C] result)) ≫
          (base (C := C)).map ((ihom.ev argument).app result)) := by
    have mapped : (base (C := C)).map (Interpretation.evaluation argument result) =
        (base (C := C)).map (Interpretation.exchange (argument ⟶[C] result) argument) ≫
          (base (C := C)).map ((ihom.ev argument).app result) :=
      (base (C := C)).map_comp _ _
    have transported := inverse_product_exchange (argument ⟶[C] result) argument
    have swapped := cartesian_exchange context input
    exact (congrArg (fun outgoing : (base (C := C)).obj ((argument ⟶[C] result) ⊗ argument) ⟶ output =>
      inv (CartesianMonoidalCategory.prodComparison (base (C := C)) (argument ⟶[C] result) argument) ≫
        outgoing) mapped).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun incoming : product context input ⟶
            (base (C := C)).obj (argument ⊗ (argument ⟶[C] result)) =>
              incoming ≫ (base (C := C)).map ((ihom.ev argument).app result)) transported).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun incoming : product context input ⟶ product input context =>
              incoming ≫
                (inv (CartesianMonoidalCategory.prodComparison (base (C := C)) argument
                    (argument ⟶[C] result)) ≫
                  (base (C := C)).map ((ihom.ev argument).app result))) swapped))))
  exact (monoidal_uncurry (canonicalExponentialComparison argument result)).trans
    ((congrArg (fun body : product context input ⟶ output =>
      (GeneratedCategory.exchange context input).inv ≫ body) (rightRead.trans bodyRead)).trans
        ((GeneratedCategory.exchange context input).inv_hom_id_assoc _))

section CommonUniverse

variable {E : Type w} [Category.{w} E]
variable [CartesianMonoidalCategory E] [MonoidalClosed E] [HasFiniteLimits E]

theorem canonicalExponentialComparison_mathlib (argument result : E) :
    canonicalExponentialComparison argument result =
      (expComparison (base (C := E)) argument).natTrans.app result := by
  apply MonoidalClosed.uncurry_injective
  exact (canonicalExponentialComparison_uncurry argument result).trans
    (uncurry_expComparison (base (C := E)) argument result).symm

instance base_expComparison_isIso (argument result : E) :
    IsIso ((expComparison (base (C := E)) argument).natTrans.app result) := by
  rw [← canonicalExponentialComparison_mathlib]
  exact canonicalExponentialComparison_isIso argument result

instance base_closed : MonoidalClosedFunctor (base (C := E)) where
  comparison_iso _argument := NatIso.isIso_of_isIso_app _

end CommonUniverse

end Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons
