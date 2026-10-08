import Mettapedia.GSLT.Topos.YonedaPredicateExponential

/-!
# Complete generalized-element readings of Yoneda predicate exponentials

The canonical representing map is tied to the base's actual evaluation.
Consequently the exponential predicate tests the supplied base function at
every future generalized element, rather than only at its present arguments.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.YonedaClosed

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite

universe u
variable {C : Type u} [Category.{u} C] [CartesianMonoidalCategory C]

/-- The inverse canonical Yoneda product comparison retains both supplied
generalized elements through the actual base pairing. -/
theorem productComparison_inv_apply (X Y U : C) (first : U ⟶ X) (second : U ⟶ Y) :
    (inv (prodComparison (yoneda (C := C)) X Y)).app (op U) (first, second) =
      lift first second := by
  apply CartesianMonoidalCategory.hom_ext
  · have reading := congrArg (fun transformation => transformation.app (op U) (first, second))
      (inv_prodComparison_map_fst (yoneda (C := C)) X Y)
    change (inv (prodComparison (yoneda (C := C)) X Y)).app (op U) (first, second) ≫
      fst X Y = first at reading
    rw [lift_fst]
    exact reading
  · have reading := congrArg (fun transformation => transformation.app (op U) (first, second))
      (inv_prodComparison_map_snd (yoneda (C := C)) X Y)
    change (inv (prodComparison (yoneda (C := C)) X Y)).app (op U) (first, second) ≫
      snd X Y = second at reading
    rw [lift_snd]
    exact reading

variable [MonoidalClosed C]

/-- The actual representing isomorphism evaluates the entire supplied
generalized function through the original base evaluation. -/
theorem exponentialIso_evaluation_apply (X Y U : C) (argument : U ⟶ X)
    (function : U ⟶ (ihom X).obj Y) :
    ((ihom.ev (yoneda.obj X)).app (yoneda.obj Y)).app (op U)
        (argument, (exponentialIso X Y).hom.app (op U) function) =
      lift argument function ≫ (ihom.ev X).app Y := by
  have reading := congrArg (fun transformation => transformation.app (op U) (argument, function))
    (exponentialIso_evaluation X Y)
  change ((ihom.ev (yoneda.obj X)).app (yoneda.obj Y)).app (op U)
      (argument, (exponentialIso X Y).hom.app (op U) function) =
    (inv (prodComparison (yoneda (C := C)) X ((ihom X).obj Y))).app (op U)
      (argument, function) ≫ (ihom.ev X).app Y at reading
  rw [productComparison_inv_apply] at reading
  exact reading

end Mettapedia.GSLT.Topos.YonedaClosed

namespace Mettapedia.GSLT.Topos.YonedaPredicate

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite

universe u
variable {C : Type u} [Category.{u} C] [CartesianMonoidalCategory C] [MonoidalClosed C]

/-- A base function satisfies the canonical exponential predicate exactly
when every future admissible argument has an admissible evaluated result. -/
theorem mem_canonicalExponential {X Y : C}
    (source : Subfunctor (yoneda.obj X)) (target : Subfunctor (yoneda.obj Y))
    (U : C) (function : U ⟶ (ihom X).obj Y) :
    function ∈ (canonicalYonedaExpPredicate source target).obj (op U) ↔
      ∀ (V : C) (future : V ⟶ U) (argument : V ⟶ X),
        argument ∈ source.obj (op V) →
          lift argument (future ≫ function) ≫ (ihom.ev X).app Y ∈ target.obj (op V) := by
  change (YonedaClosed.exponentialIso X Y).hom.app (op U) function ∈
    (expPredicate (totalOfPredicate (yoneda.obj X) source)
      (totalOfPredicate (yoneda.obj Y) target)).obj (op U) ↔ _
  rw [mem_expPredicate]
  constructor
  · intro held V future argument admissible
    have applied := held (op V) future.op argument admissible
    have naturality := NatTrans.naturality_apply
      (YonedaClosed.exponentialIso X Y).hom future.op function
    change (YonedaClosed.exponentialIso X Y).hom.app (op V) (future ≫ function) =
      ((ihom (yoneda.obj X)).obj (yoneda.obj Y)).map future.op
        ((YonedaClosed.exponentialIso X Y).hom.app (op U) function) at naturality
    change ((ihom.ev (yoneda.obj X)).app (yoneda.obj Y)).app (op V)
      (argument, _) ∈ target.obj (op V) at applied
    rw [← naturality, YonedaClosed.exponentialIso_evaluation_apply] at applied
    exact applied
  · intro held V future argument admissible
    have applied := held V.unop future.unop argument admissible
    have naturality := NatTrans.naturality_apply
      (YonedaClosed.exponentialIso X Y).hom future function
    change (YonedaClosed.exponentialIso X Y).hom.app V (future.unop ≫ function) =
      ((ihom (yoneda.obj X)).obj (yoneda.obj Y)).map future
        ((YonedaClosed.exponentialIso X Y).hom.app (op U) function) at naturality
    change ((ihom.ev (yoneda.obj X)).app (yoneda.obj Y)).app V
      (argument, _) ∈ target.obj V
    rw [← naturality, YonedaClosed.exponentialIso_evaluation_apply]
    exact applied

end Mettapedia.GSLT.Topos.YonedaPredicate
