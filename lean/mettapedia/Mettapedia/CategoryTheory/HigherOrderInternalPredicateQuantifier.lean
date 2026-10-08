import Mettapedia.CategoryTheory.HigherOrderInternalPredicateObject
import Mettapedia.CategoryTheory.InternalPredicateQuantifier
import Mettapedia.CategoryTheory.InternalPredicateExistential

/-!
# Earned higher-order instances of the finite quantifier diagrams

The actual quantified generic predicate constructs a function-object arrow.
Its complete supplied-input reading follows from classifier uniqueness and
the Cartesian parameter pullback. The independently formed ordered-pair
scope then earns the local monotonicity diagram; the original quantifier
adjunction earns the two local unit/counit diagrams. These instantiate the
finite contract without assuming a whole generated interpretation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.HigherOrderInternalPredicateQuantifier

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open HigherOrderInternalPredicateObject

universe u v p
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (doctrine : PredicateDoctrine.HigherOrder.{u,v,p} C)

abbrev power (value : C) := InternalPredicateFunctionObject.power (operations doctrine) value

variable {source target : C} (route : source ⟶ target)

def forallOperation : power doctrine source ⟶ power doctrine target :=
  InternalPredicateFunctionObject.quote (operations doctrine)
    (doctrine.generic.characteristic _
      (doctrine.forallAlong (route ▷ power doctrine source) (family doctrine (𝟙 _))))

theorem forallOperation_family :
    family doctrine (forallOperation doctrine route) =
      doctrine.forallAlong (route ▷ power doctrine source) (family doctrine (𝟙 _)) := by
  change doctrine.reindex (uncurry (curry (doctrine.generic.characteristic _ _)))
    doctrine.generic.truth = _
  rw [uncurry_curry, doctrine.generic.classifies]

theorem forall_supplied {parameter : C} (predicate : parameter ⟶ power doctrine source) :
    family doctrine (predicate ≫ forallOperation doctrine route) =
      doctrine.forallAlong (route ▷ parameter) (family doctrine predicate) := by
  rw [family_substitution, forallOperation_family]
  have comparison := doctrine.forall_baseChange (source ◁ predicate) (route ▷ parameter)
    (route ▷ power doctrine source) (target ◁ predicate)
    (CartesianTensorPullback.parameterSquare route predicate) (family doctrine (𝟙 _))
  exact comparison.trans (congrArg (doctrine.forallAlong (route ▷ parameter))
    ((family_substitution doctrine predicate (𝟙 _)).symm.trans
      (congrArg (family doctrine) (Category.comp_id predicate))))

theorem precomposition_supplied {parameter : C} (predicate : parameter ⟶ power doctrine target) :
    family doctrine (predicate ≫ InternalPredicateQuantifier.precomposition (operations doctrine) route) =
      doctrine.reindex (route ▷ parameter) (family doctrine predicate) := by
  rw [family, InternalPredicateQuantifier.precomposition_read, decode_substitution]
  rfl

theorem precomposition_generic :
    family doctrine (InternalPredicateQuantifier.precomposition (operations doctrine) route) =
      doctrine.reindex (route ▷ power doctrine target) (family doctrine (𝟙 _)) := by
  simpa only [Category.id_comp] using precomposition_supplied doctrine route (𝟙 _)

def existsOperation : power doctrine source ⟶ power doctrine target :=
  InternalPredicateFunctionObject.quote (operations doctrine)
    (doctrine.generic.characteristic _
      (doctrine.existsAlong (route ▷ power doctrine source) (family doctrine (𝟙 _))))

theorem existsOperation_family :
    family doctrine (existsOperation doctrine route) =
      doctrine.existsAlong (route ▷ power doctrine source) (family doctrine (𝟙 _)) := by
  change doctrine.reindex (uncurry (curry (doctrine.generic.characteristic _ _)))
    doctrine.generic.truth = _
  rw [uncurry_curry, doctrine.generic.classifies]

theorem exists_supplied {parameter : C} (predicate : parameter ⟶ power doctrine source) :
    family doctrine (predicate ≫ existsOperation doctrine route) =
      doctrine.existsAlong (route ▷ parameter) (family doctrine predicate) := by
  rw [family_substitution, existsOperation_family]
  have comparison := doctrine.exists_baseChange (source ◁ predicate) (route ▷ parameter)
    (route ▷ power doctrine source) (target ◁ predicate)
    (CartesianTensorPullback.parameterSquare route predicate) (family doctrine (𝟙 _))
  exact comparison.trans (congrArg (doctrine.existsAlong (route ▷ parameter))
    ((family_substitution doctrine predicate (𝟙 _)).symm.trans
      (congrArg (family doctrine) (Category.comp_id predicate))))

variable [HasEqualizers C]

private theorem ordered_inputs (value : C) :
    (InternalPredicateQuantifier.functions (operations doctrine) value).meet
      (InternalPredicateQuantifier.secondInput (operations doctrine) value)
      (InternalPredicateQuantifier.firstInput (operations doctrine) value) =
        InternalPredicateQuantifier.firstInput (operations doctrine) value := by
  have complete := equalizer.condition
    (InternalPredicateQuantifier.functions (operations doctrine) value).conjunction
    (fst (power doctrine value) (power doctrine value))
  have pointwise := InternalPredicateFunctionObject.conjunction_after (operations doctrine)
    (InternalPredicateQuantifier.orderInclusion (operations doctrine) value)
  exact ((InternalPredicateQuantifier.functions (operations doctrine) value).meet_comm
    (InternalPredicateFunctionObject.function_laws (operations doctrine) (laws doctrine) value) _ _).trans
      (pointwise.symm.trans complete)

theorem forall_monotonicity :
    InternalPredicateQuantifier.Monotonicity (operations doctrine) (forallOperation doctrine route) where
  ordered := by
    apply family_injective doctrine
    rw [family_meet]
    simp only [forall_supplied]
    apply inf_eq_right.mpr
    apply doctrine.forall_mono
    apply inf_eq_right.mp
    exact (family_meet doctrine _ _).symm.trans
      (congrArg (family doctrine) (ordered_inputs doctrine source))

def forallQualification : InternalPredicateQuantifier.Universal (operations doctrine) route where
  operation := forallOperation doctrine route
  monotonicity := forall_monotonicity doctrine route
  unit := by
    apply family_injective doctrine
    rw [family_meet]
    simp only [forall_supplied, precomposition_generic]
    exact inf_eq_right.mpr ((doctrine.forall_adj (route ▷ power doctrine target) _ _).mp le_rfl)
  counit := by
    apply family_injective doctrine
    rw [family_meet, precomposition_supplied, forallOperation_family]
    exact inf_eq_right.mpr ((doctrine.forall_adj (route ▷ power doctrine source) _ _).mpr le_rfl)

theorem exists_monotonicity :
    InternalPredicateQuantifier.Monotonicity (operations doctrine) (existsOperation doctrine route) where
  ordered := by
    apply family_injective doctrine
    rw [family_meet]
    simp only [exists_supplied]
    apply inf_eq_right.mpr
    apply doctrine.exists_mono
    apply inf_eq_right.mp
    exact (family_meet doctrine _ _).symm.trans
      (congrArg (family doctrine) (ordered_inputs doctrine source))

def existsQualification : InternalPredicateExistential.Existential (operations doctrine) route where
  operation := existsOperation doctrine route
  monotonicity := exists_monotonicity doctrine route
  unit := by
    apply family_injective doctrine
    rw [family_meet, precomposition_supplied, existsOperation_family]
    exact inf_eq_right.mpr ((doctrine.exists_adj (route ▷ power doctrine source) _ _).mp le_rfl)
  counit := by
    apply family_injective doctrine
    rw [family_meet]
    simp only [exists_supplied, precomposition_generic]
    exact inf_eq_right.mpr ((doctrine.exists_adj (route ▷ power doctrine target) _ _).mpr le_rfl)

end Mettapedia.CategoryTheory.HigherOrderInternalPredicateQuantifier
