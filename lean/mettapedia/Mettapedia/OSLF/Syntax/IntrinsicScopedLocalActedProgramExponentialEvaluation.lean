import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramExponentialPresheaf

/-!
# Evaluation of actual represented binder bodies

The exponential evaluation of an authored body composes the actual ordinary
parameter assignment with that body's fresh-variable abstraction. All original
metavariable assignments and local binder arguments remain in the computation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open SecondOrderContext SecondOrderVariableAbstraction
open CategoricalBindingModel
open IntrinsicScopedLocalPolynomial IntrinsicScopedLocalActedClassifier

universe w
variable {S : Signature} {K : List (MetaArity S)} (equations : List (EqAxiom S K))

/-- The quotient Hom equivalence acts on an actual authored term by its
binder-aware fresh-variable abstraction. -/
theorem abstractionHomEquiv_termArrow (X : Base equations) {Γ : Ctx S} {s : S.Srt}
    (term : Term (withMetas S X.as.arities) Γ s) :
    abstractionHomEquiv equations X Γ s
        ((authoredEquationPresentation S equations).quotientFunctor.map (termArrow term)) =
      (authoredEquationPresentation S equations).quotientFunctor.map
        (termArrow (abstractVars term)) := rfl

/-- The inverse selected-power correspondence exposes the actual parameter
order comparison followed by the authored abstracted body. -/
theorem baseSelectedBinderHomEquiv_symm_termArrow
    (X : Base equations) {Γ : Ctx S} {s : S.Srt}
    (term : Term (withMetas S X.as.arities) Γ s) :
    (baseSelectedBinderHomEquiv equations X Γ s).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map (termArrow term)) =
      (extensionProductIso equations Γ X).inv ≫
        (authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (abstractVars term)) := rfl

variable (R : List (LocalRule S))

/-- Evaluation at an arbitrary operational stage applies the actual closed
parameter assignment to the abstracted authored body. -/
theorem parameterExponential_eval_termArrow_base
    (a : Classifier R equations) {Γ : Ctx S} {s : S.Srt}
    (argument : (parameterRepresentable.{w} R equations Γ).obj (Opposite.op a))
    (term : Term (withMetas S a.base.as.arities) Γ s) :
    ((parameterExponential R equations Γ s).eval.app (Opposite.op a)
      (argument, ULift.up ((programHomEquiv R equations a _).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map (termArrow term))))).down.base =
      prod.lift (𝟙 a.base) argument.down.base ≫
        (extensionProductIso equations Γ a.base).inv ≫
          (authoredEquationPresentation S equations).quotientFunctor.map
            (termArrow (abstractVars term)) := by
  rw [parameterExponential_eval_apply]
  change (programProductLift R equations (𝟙 a) argument.down).base ≫
      (baseSelectedBinderHomEquiv equations a.base Γ s).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map (termArrow term)) = _
  rw [programProductLift_base, baseSelectedBinderHomEquiv_symm_termArrow]
  change prod.lift (𝟙 a.base) argument.down.base ≫
      (extensionProductIso equations Γ a.base).inv ≫
        (authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (abstractVars term)) = _
  rfl

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
