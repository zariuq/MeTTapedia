import Mettapedia.OSLF.Syntax.CategoricalBindingClosedTargetChange
import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
# A limit-preserving target change that does not preserve function objects

The Boolean power functor is naturally isomorphic to the square functor. It
preserves all limits, including products and the pullbacks used by event
contexts. Its exponential comparison cannot represent a function that
exchanges the two Boolean coordinates.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.CategoricalBindingSquareTargetControl

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

/-- The Boolean power is the square functor in function-coordinate form. -/
def squareFunctor : Type ⥤ Type where
  obj A := Bool ⟶ A
  map f := ↾fun g => g ≫ f

/-- The square preserves all limits because it is right adjoint to the
product with the two-element type. -/
instance squareFunctor_preservesLimits : PreservesLimits squareFunctor :=
  by
    change PreservesLimits (coyoneda.obj (Opposite.op Bool))
    exact (Types.tensorProductAdjunction Bool).rightAdjoint_preservesLimits

/-- Boolean functions have precisely two coordinates. -/
def coordinates (A : Type) : squareFunctor.obj A ≃ A × A where
  toFun (f : Bool ⟶ A) := (f false, f true)
  invFun p := ↾fun b => if b then p.2 else p.1
  left_inv f := by
    let g : Bool ⟶ A := f
    change (↾fun b => if b then g true else g false) = g
    ext b
    cases b <;> rfl
  right_inv p := rfl

/-- The two-coordinate identification is natural in the type and its maps. -/
theorem coordinates_natural {A B : Type} (f : A ⟶ B) (x : squareFunctor.obj A) :
    coordinates B (squareFunctor.map f x) =
      (f (coordinates A x).1, f (coordinates A x).2) := rfl

/-- Finite products are preserved by this actual target change. -/
theorem square_preservesFiniteProducts : PreservesFiniteProducts squareFunctor :=
  inferInstance

/-- Event-domain pullbacks are also preserved. -/
theorem square_preservesPullbacks : PreservesLimitsOfShape WalkingCospan squareFunctor :=
  inferInstance

/-- The inverse product comparison as an explicit function-valued arrow. -/
def pairingComparisonInv (A B : Type) :
    ((Bool ⟶ A) × (Bool ⟶ B)) ⟶ (Bool ⟶ A × B) :=
  by
    have comparisonIso : IsIso (CartesianMonoidalCategory.prodComparison squareFunctor A B) := by infer_instance
    exact @inv (Type) _ _ _ (CartesianMonoidalCategory.prodComparison squareFunctor A B) comparisonIso

/-- Inverting the product comparison pairs the two function coordinates. -/
theorem inv_prodComparison_apply {A B : Type} (f : Bool ⟶ A) (g : Bool ⟶ B) (b : Bool) :
    pairingComparisonInv A B (f, g) b = (f b, g b) := by
  have first := congrArg (fun h => (TypeCat.Hom.hom (X := Bool) (Y := A) (h (f, g))) b)
    (inv_prodComparison_map_fst squareFunctor A B)
  have second := congrArg (fun h => (TypeCat.Hom.hom (X := Bool) (Y := B) (h (f, g))) b)
    (inv_prodComparison_map_snd squareFunctor A B)
  exact Prod.ext first second

/-- The actual exponential comparison, with its function-valued endpoints
made explicit. -/
def comparison : (Bool ⟶ (Bool ⟶ Bool)) ⟶ ((Bool ⟶ Bool) ⟶ (Bool ⟶ Bool)) :=
  (expComparison squareFunctor Bool).natTrans.app Bool

/-- The canonical exponential comparison acts on each coordinate separately. -/
theorem expComparison_apply (q : Bool ⟶ (Bool ⟶ Bool)) (f : Bool ⟶ Bool) (b : Bool) :
    comparison q f b = q b (f b) := by
  have evaluation := congrArg (fun h => (TypeCat.Hom.hom (X := Bool) (Y := Bool) (h (f, q))) b)
    (expComparison_ev squareFunctor Bool Bool)
  change comparison q f b = (pairingComparisonInv Bool (Bool ⟶ Bool) (f, q) b).2
    ((pairingComparisonInv Bool (Bool ⟶ Bool) (f, q) b).1) at evaluation
  rw [inv_prodComparison_apply] at evaluation
  exact evaluation

/-- An operation exchanging the coordinates is a valid function between
the target function objects. -/
def exchange : (squareFunctor.obj Bool) ⟶ squareFunctor.obj Bool :=
  ↾fun (f : Bool ⟶ Bool) => ↾fun b => f (!b)

/-- Coordinate exchange is outside the canonical exponential comparison's
image. The obstruction already occurs at Boolean domain and codomain. -/
theorem exchange_not_in_image :
    ¬ ∃ q, comparison q = exchange := by
  rintro ⟨q, same⟩
  have first := congrArg (fun h => ((h : (Bool ⟶ Bool) ⟶ (Bool ⟶ Bool))
    (↾fun _ : Bool => false)) false) same
  have second := congrArg (fun h => ((h : (Bool ⟶ Bool) ⟶ (Bool ⟶ Bool))
    (↾fun b : Bool => b)) false) same
  rw [expComparison_apply] at first second
  change q false false = false at first
  change q false false = true at second
  exact Bool.false_ne_true (first.symm.trans second)

/-- Preserving products and pullbacks does not make the target change a
closed functor. -/
theorem square_not_closed : ¬ MonoidalClosedFunctor squareFunctor := by
  intro closed
  have iso : IsIso (expComparison squareFunctor Bool).natTrans := closed.comparison_iso Bool
  have comparisonIso : IsIso comparison := by
    change IsIso ((expComparison squareFunctor Bool).natTrans.app Bool)
    exact NatIso.isIso_app_of_isIso (expComparison squareFunctor Bool).natTrans Bool
  apply exchange_not_in_image
  exact ⟨(@inv (Type) _ _ _ comparison comparisonIso) exchange,
    by exact congrArg (fun h :
      ((Bool ⟶ Bool) ⟶ (Bool ⟶ Bool)) ⟶ ((Bool ⟶ Bool) ⟶ (Bool ⟶ Bool)) => h exchange)
        (@IsIso.inv_hom_id (Type) _ _ _ comparison comparisonIso)⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The failed Boolean comparison also rules out the selected-function-object
preservation required by binding models, despite preservation of all limits. -/
theorem square_not_preserves_exponentials :
    ¬ Nonempty (CategoricalBindingModel.ExponentialPreservation squareFunctor) := by
  rintro ⟨preserves⟩
  let E := preserves.image (CategoricalBindingModel.Exponential.closed Bool Bool)
  let back : ((Bool ⟶ Bool) ⟶ (Bool ⟶ Bool)) ⟶ (Bool ⟶ (Bool ⟶ Bool)) :=
    E.curry ((ihom.ev (squareFunctor.obj Bool)).app (squareFunctor.obj Bool))
  have factor : E.eval =
      (squareFunctor.obj Bool ◁ comparison) ≫
        (ihom.ev (squareFunctor.obj Bool)).app (squareFunctor.obj Bool) := by
    exact (preserves.eval_image (CategoricalBindingModel.Exponential.closed Bool Bool)).trans
      (expComparison_ev squareFunctor Bool Bool).symm
  have rightInverse : back ≫ comparison = 𝟙 _ := by
    apply (CategoricalBindingModel.Exponential.closed
      (squareFunctor.obj Bool) (squareFunctor.obj Bool)).hom_ext
    change (squareFunctor.obj Bool ◁ (back ≫ comparison)) ≫
      (ihom.ev (squareFunctor.obj Bool)).app (squareFunctor.obj Bool) =
        (squareFunctor.obj Bool ◁ 𝟙 _) ≫
          (ihom.ev (squareFunctor.obj Bool)).app (squareFunctor.obj Bool)
    calc
      ((squareFunctor.obj Bool ◁ (back ≫ comparison)) ≫
          (ihom.ev (squareFunctor.obj Bool)).app (squareFunctor.obj Bool)) =
        (squareFunctor.obj Bool ◁ back) ≫ E.eval := by
        rw [whiskerLeft_comp, Category.assoc, ← factor]
      _ = (ihom.ev (squareFunctor.obj Bool)).app (squareFunctor.obj Bool) :=
        E.curry_eval _
      _ = _ := by rw [whiskerLeft_id, Category.id_comp]
  apply exchange_not_in_image
  exact ⟨back exchange, congrArg (fun h :
    ((Bool ⟶ Bool) ⟶ (Bool ⟶ Bool)) ⟶ ((Bool ⟶ Bool) ⟶ (Bool ⟶ Bool)) => h exchange)
    rightInverse⟩

end Mettapedia.OSLF.Binding.CategoricalBindingSquareTargetControl
