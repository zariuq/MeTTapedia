import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafFoldComparison

/-!
# The named program-base interpretation in clone presheaves

Equation contexts are interpreted in the original clone's presheaf target.
Raw assignments use the actual binding interpretation, and the rule-local
classifier restricts to this same functor on its event-free objects. This
comparison concerns program substitutions; retained event data is supplied
separately by the actual operational model.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafBaseComparison

open _root_.CategoryTheory
open IntrinsicScopedOperationalPresheafPrograms (target model)
open IntrinsicScopedOperationalPresheafCategoricalModel (categoricalModel)
open IntrinsicScopedLocalActedClassifier (Base programSection)
open SecondOrderContext

universe u
variable {S : Signature} {schema : List (MetaArity S)}
variable (A : BindingCloneAlgebra.Algebra.{u} S)
variable (equations : List (EqAxiom S schema))
variable (satisfies : BindingEquationInterpretation.Satisfies A equations)

/-- The actual equation-context program functor into the original clone presheaves. -/
def programBaseFunctor : Base equations ⥤ target A :=
  (model A).equationClassifyingFunctor (authoredEquationPresentation S equations)
    (IntrinsicScopedOperationalPresheafEquations.model_satisfies A equations satisfies)

/-- Every equation context is interpreted by its original ordered function carriers. -/
theorem programBaseFunctor_obj (X : Base equations) :
    (programBaseFunctor A equations satisfies).obj X = (model A).family X.as.arities := rfl

/-- The raw-context quotient square commutes with the genuine binding interpretation. -/
theorem programBaseFunctor_raw :
    (authoredEquationPresentation S equations).quotientFunctor ⋙
      programBaseFunctor A equations satisfies = (model A).classifyingFunctor :=
  (model A).quotient_comp_equationClassifyingFunctor _ _

/-- Each raw assignment is sent to the actual simultaneous assignment arrow,
including every authored binder-dependent metavariable value. -/
theorem programBaseFunctor_raw_map {X Z : Object S} (σ : X ⟶ Z) :
    (programBaseFunctor A equations satisfies).map
      ((authoredEquationPresentation S equations).quotientFunctor.map σ) =
        (model A).assignHom σ := rfl

/-- The actual operational classifier's program section uses that same
named base interpretation and its proved substitution laws. -/
theorem programSection_comparison (R : List (IntrinsicScopedLocalPolynomial.LocalRule S))
    (Y : IntrinsicScopedLocalSubstitutionModel.SubstitutionModel.{u,u} R A) :
    programSection R equations ⋙ (categoricalModel R Y equations satisfies).classifyingFunctor =
      programBaseFunctor A equations satisfies :=
  (categoricalModel R Y equations satisfies).programSection_classifyingFunctor

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafBaseComparison
