import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafSharedComparison

/-!
# Authored presentations through the one operational classification theorem

The actual contextual equation quotient supplies programs. Existing local
firing trees supply individual events, their substitution action, and each
ordered rule constructor. Classification and cocontinuous extension then
apply to that independently constructed model.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedAuthoredClassifiedInstance

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open IntrinsicScopedLocalPolynomial (LocalRule)
open IntrinsicScopedLocalSubstitutionModel (SubstitutionModel)
open IntrinsicScopedOperationalPresheafPrograms (target)
open IntrinsicScopedLocalActedCategoricalModels (CategoricalModel StructuredFunctor)

universe u
variable {S : Signature} {schema : List (MetaArity S)}

/-- The existing local constructor trees with their proved simultaneous substitution. -/
def treeModel (R : List (LocalRule S)) (A : BindingCloneAlgebra.Algebra.{u} S) :
    SubstitutionModel.{u,u} R A where
  carrier := IntrinsicScopedLocalPolynomial.Tree R A
  act := IntrinsicScopedLocalPolynomial.substTree R A
  act_identity := IntrinsicScopedLocalPolynomial.substTree_identity R A
  act_comp := IntrinsicScopedLocalPolynomial.substTree_comp R A
  rules := { act := fun _ _ layer => .roll layer.1 layer.2 }
  act_rules := by
    dsimp only [IntrinsicScopedLocalSubstitutionModel.RulesLaw]
    intros
    rfl

variable (R : List (LocalRule S)) (equations : List (EqAxiom S schema))

/-- The actual authored contextual equation quotient. -/
abbrev algebra := BindingEquationQuotientModel.algebra equations

/-- The real authored firing-tree categorical model in its clone presheaves. -/
def model : CategoricalModel R equations (D := target (algebra equations)) :=
  IntrinsicScopedOperationalPresheafCategoricalModel.categoricalModel R
    (treeModel R (algebra equations)) equations
    (BindingEquationQuotientModel.algebra_satisfies equations)

/-- The authored presentation's actual structure-preserving classifying functor. -/
def classified : StructuredFunctor R equations (D := target (algebra equations)) :=
  (model R equations).structured

/-- Its genuine cocontinuous interpretation is produced by the same classification theorem. -/
def interpretation :
    IntrinsicScopedLocalActedCategoricalModels.CocontinuousInterpretation.{0,1,0}
      (R := R) (equations := equations) (D := target (algebra equations)) :=
  (IntrinsicScopedLocalActedCategoricalModels.CocontinuousInterpretation.classificationEquivalence.{0}
    (R := R) (equations := equations) (D := target (algebra equations))).functor.obj
      (model R equations)

/-- Restriction of the genuine extension recovers the actual classifying carrier. -/
def restrictionIso :
    IntrinsicScopedLocalActedPresheaf.embedding.{0} R equations ⋙
      (interpretation R equations).carrier ≅ (classified R equations).carrier :=
  IntrinsicScopedLocalActedPresheaf.modelPresheafExtensionRestriction.{0} (model R equations)

/-- Classification also recovers the independently constructed operational model. -/
def recoveredModelIso :
    (IntrinsicScopedLocalActedCategoricalModels.CocontinuousInterpretation.classificationEquivalence.{0}
      (R := R) (equations := equations) (D := target (algebra equations))).inverse.obj
        (interpretation R equations) ≅ model R equations :=
  ((IntrinsicScopedLocalActedCategoricalModels.CocontinuousInterpretation.classificationEquivalence.{0}
    (R := R) (equations := equations) (D := target (algebra equations))).unitIso.app
      (model R equations)).symm

end Mettapedia.OSLF.Binding.IntrinsicScopedAuthoredClassifiedInstance
