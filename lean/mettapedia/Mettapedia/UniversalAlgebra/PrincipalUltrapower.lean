import Mettapedia.UniversalAlgebra.ModelHom
import Mettapedia.UniversalAlgebra.Ultrapower

/-!
# Principal ultrapowers collapse to the selected coordinate

An ultrapower along the principal ultrafilter at `point` is canonically
isomorphic to its base model.  Evaluation at `point` and the diagonal map are
mutually inverse model homomorphisms.

This is the negative control for nonstandard or ultrafilter-relative semantic
constructions: a principal view selects one ordinary coordinate and creates no
new carrier elements.  The free-ultrafilter counterexample in `Ultrapower`
then supplies the paired non-collapse result.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

open Filter

universe u v w

variable {S : Signature.{u}}

namespace Model

/-- Evaluation at the selected coordinate is an equivalence from a principal
ultrapower carrier to the base carrier. -/
def principalUltrapowerEquiv {Carrier : Type v} {Index : Type w}
    (point : Index) :
    UltrapowerCarrier Carrier (pure point : Ultrafilter Index) ≃ Carrier where
  toFun := Quotient.lift (fun representative : Index → Carrier =>
    representative point) (by
      intro first second eventuallyEqual
      exact Filter.eventually_pure.mp eventuallyEqual)
  invFun := diagonal (pure point : Ultrafilter Index)
  left_inv := by
    intro value
    refine Quotient.inductionOn' value ?_
    intro representative
    apply Quotient.sound
    exact Filter.eventually_pure.mpr rfl
  right_inv := by
    intro value
    rfl

@[simp] theorem principalUltrapowerEquiv_diagonal
    {Carrier : Type v} {Index : Type w} (point : Index) (value : Carrier) :
    principalUltrapowerEquiv point
        (diagonal (pure point : Ultrafilter Index) value) = value :=
  rfl

/-- The diagonal map into a principal ultrapower is bijective. -/
theorem diagonal_bijective_principal
    {Carrier : Type v} {Index : Type w} (point : Index) :
    Function.Bijective
      (diagonal (pure point : Ultrafilter Index) :
        Carrier → UltrapowerCarrier Carrier (pure point : Ultrafilter Index)) :=
  (principalUltrapowerEquiv point).symm.bijective

/-- Evaluation at the principal coordinate preserves every operation. -/
noncomputable def principalProjectionHom
    {Carrier : Type v} {Index : Type w}
    (model : Model S Carrier) (point : Index) :
    Hom (model.ultrapower (pure point)) model where
  toFun := principalUltrapowerEquiv point
  map_operation := by
    classical
    intro operation arguments
    let representatives : Fin (S.arity operation) → Index → Carrier :=
      fun position => Quotient.out (arguments position)
    have arguments_eq :
        (fun position =>
          (representatives position :
            UltrapowerCarrier Carrier (pure point : Ultrafilter Index))) =
          arguments := by
      funext position
      exact Quotient.out_eq (arguments position)
    rw [← arguments_eq]
    rw [ultrapower_interpret]
    rfl

/-- The diagonal map preserves every operation. -/
def principalDiagonalHom
    {Carrier : Type v} {Index : Type w}
    (model : Model S Carrier) (point : Index) :
    Hom model (model.ultrapower (pure point)) where
  toFun := diagonal (pure point : Ultrafilter Index)
  map_operation := by
    intro operation arguments
    symm
    exact ultrapower_interpret model (pure point) operation
      (fun position _index => arguments position)

/-- A principal ultrapower is isomorphic to the base model, not merely
equivalent as a bare carrier. -/
noncomputable def principalUltrapowerIso
    {Carrier : Type v} {Index : Type w}
    (model : Model S Carrier) (point : Index) :
    Iso (model.ultrapower (pure point)) model where
  hom := principalProjectionHom model point
  inv := principalDiagonalHom model point
  hom_inv_id := by
    intro value
    exact (principalUltrapowerEquiv point).symm_apply_apply value
  inv_hom_id := by
    intro value
    exact (principalUltrapowerEquiv point).apply_symm_apply value

end Model

/-! ## Paired principal/free boundary -/

/-- Principal ultrapowers add no points, while the natural-number ultrapower
along the free hyperfilter has a point outside the diagonal image. -/
theorem principal_collapses_free_does_not :
    (∀ point : Nat,
      Function.Surjective
        (Model.diagonal (pure point : Ultrafilter Nat) :
          Nat → Model.UltrapowerCarrier Nat (pure point : Ultrafilter Nat))) ∧
      ¬ Function.Surjective
        (Model.diagonal (Filter.hyperfilter Nat) :
          Nat →
            Model.UltrapowerCarrier Nat (Filter.hyperfilter Nat)) := by
  constructor
  · intro point
    exact (Model.diagonal_bijective_principal point).2
  · exact UltrapowerBoundary.diagonal_not_surjective

#print axioms Model.principalUltrapowerEquiv
#print axioms Model.diagonal_bijective_principal
#print axioms Model.principalProjectionHom
#print axioms Model.principalDiagonalHom
#print axioms Model.principalUltrapowerIso
#print axioms principal_collapses_free_does_not

end Mettapedia.UniversalAlgebra
