import Mettapedia.CategoryTheory.CartesianTensorPullback
import Mettapedia.CategoryTheory.PositionedRewritePredicateLogic
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# A uniform higher-order positioned modality

Rely and postcondition predicates are independent function-object inputs.
The output function is obtained by classifying the quantified predicate
and currying its characteristic map. Its complete evaluation and arbitrary
parameter substitution are derived from classification, the exponential
adjunction, and two actual Cartesian pullback squares.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.PositionedRewritePredicatePower

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open PositionedRewritePredicateLogic

universe u v p
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (doctrine : PredicateDoctrine.HigherOrder.{u,v,p} C)

abbrev power (object : C) : C := (ihom object).obj doctrine.generic.object

/-- A supplied function object is read on the complete value/parameter context. -/
def family {object parameter : C} (name : parameter ⟶ power doctrine object) :
    doctrine.Fiber (object ⊗ parameter) :=
  doctrine.reindex (uncurry name) doctrine.generic.truth

theorem family_substitution {object first second : C} (change : first ⟶ second)
    (name : second ⟶ power doctrine object) :
    doctrine.reindex (object ◁ change) (family doctrine name) =
      family doctrine (change ≫ name) := by
  rw [family, ← doctrine.reindex_comp, ← uncurry_natural_left]
  rfl

def name {object parameter : C} (predicate : doctrine.Fiber (object ⊗ parameter)) :
    parameter ⟶ power doctrine object :=
  curry (doctrine.generic.characteristic _ predicate)

theorem family_name {object parameter : C} (predicate : doctrine.Fiber (object ⊗ parameter)) :
    family doctrine (name doctrine predicate) = predicate := by
  rw [family, name, uncurry_curry]
  exact doctrine.generic.classifies _ _

abbrev profiles (assay outgoing : C) : C := power doctrine assay ⊗ power doctrine outgoing

variable {instances assignments assay carrier outgoing : C}
variable (forget : instances ⟶ assignments) (focus : assignments ⟶ carrier)
variable (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing)

/-- Both inputs remain independent, with the whole rule instance used by each. -/
def conditionAt {parameter : C} (inputs : parameter ⟶ profiles doctrine assay outgoing) :
    doctrine.Fiber (instances ⊗ parameter) :=
  doctrine.reindex (instantiate ▷ parameter)
      (family doctrine (inputs ≫ fst _ _)) ⇨
    doctrine.reindex (reduct ▷ parameter)
      (family doctrine (inputs ≫ snd _ _))

theorem condition_substitution {first second : C} (change : first ⟶ second)
    (inputs : second ⟶ profiles doctrine assay outgoing) :
    doctrine.reindex (instances ◁ change)
        (conditionAt doctrine instantiate reduct inputs) =
      conditionAt doctrine instantiate reduct (change ≫ inputs) := by
  rw [conditionAt, doctrine.reindex_himp, ← doctrine.reindex_comp,
    ← doctrine.reindex_comp]
  have firstSquare := (CartesianTensorPullback.square instantiate change).w
  have secondSquare := (CartesianTensorPullback.square reduct change).w
  rw [← firstSquare, ← secondSquare, doctrine.reindex_comp,
    doctrine.reindex_comp, family_substitution, family_substitution]
  simp only [conditionAt, Category.assoc]

def modalAt {parameter : C} (inputs : parameter ⟶ profiles doctrine assay outgoing) :
    doctrine.Fiber (carrier ⊗ parameter) :=
  modality doctrine.toFirstOrder (forget ▷ parameter) (focus ▷ parameter)
    (conditionAt doctrine instantiate reduct inputs)

theorem modal_substitution {first second : C} (change : first ⟶ second)
    (inputs : second ⟶ profiles doctrine assay outgoing) :
    doctrine.reindex (carrier ◁ change)
        (modalAt doctrine forget focus instantiate reduct inputs) =
      modalAt doctrine forget focus instantiate reduct (change ≫ inputs) := by
  have comparison := modality_baseChange doctrine.toFirstOrder (forget ▷ second)
    (focus ▷ second) (instances ◁ change) (assignments ◁ change)
    (carrier ◁ change) (forget ▷ first) (focus ▷ first)
    (CartesianTensorPullback.parameterSquare forget change)
    (CartesianTensorPullback.parameterSquare focus change)
    (conditionAt doctrine instantiate reduct inputs)
  simpa only [modalAt, condition_substitution] using comparison

/-- The operation is an actual arrow between the independent input powers
and the output power, rather than an object-indexed external function. -/
def operation : profiles doctrine assay outgoing ⟶ power doctrine carrier :=
  curry (doctrine.generic.characteristic _
    (modalAt doctrine forget focus instantiate reduct (𝟙 _)))

theorem operation_evaluation :
    uncurry (operation doctrine forget focus instantiate reduct) =
      doctrine.generic.characteristic _
        (modalAt doctrine forget focus instantiate reduct (𝟙 _)) :=
  uncurry_curry _

theorem operation_classifies :
    family doctrine (operation doctrine forget focus instantiate reduct) =
      modalAt doctrine forget focus instantiate reduct (𝟙 _) := by
  rw [family, operation_evaluation]
  exact doctrine.generic.classifies _ _

/-- Every supplied pair of predicate functions has the exact quantified reading. -/
theorem supplied_evaluation {parameter : C}
    (inputs : parameter ⟶ profiles doctrine assay outgoing) :
    family doctrine (inputs ≫ operation doctrine forget focus instantiate reduct) =
      modalAt doctrine forget focus instantiate reduct inputs := by
  rw [← family_substitution, operation_classifies, modal_substitution, Category.comp_id]

theorem operation_unique (candidate : profiles doctrine assay outgoing ⟶ power doctrine carrier)
    (reading : family doctrine candidate =
      modalAt doctrine forget focus instantiate reduct (𝟙 _)) :
    candidate = operation doctrine forget focus instantiate reduct := by
  apply uncurry_injective
  rw [operation_evaluation]
  exact doctrine.generic.unique _ _ _ reading

end Mettapedia.CategoryTheory.PositionedRewritePredicatePower
