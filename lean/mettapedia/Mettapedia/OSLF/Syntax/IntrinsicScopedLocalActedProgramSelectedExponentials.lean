import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramExponentialEvaluation
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedYonedaParameterContext

/-!
# Selected binder exponentials for the authored operational Yoneda model

The ordered context of closed program objects has the authored scoped program
object as its exponential into the result-sort object. The structure is derived
from the actual standard internal hom and the actual parameter-product
comparison, including at operational stages carrying event variables.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open CategoricalBindingModel
open IntrinsicScopedLocalPolynomial IntrinsicScopedLocalActedClassifier

universe w
variable {S : Signature} {K : List (MetaArity S)}
variable (R : List (LocalRule S)) (equations : List (EqAxiom S K))

/-- The independently derived selected exponential of an entire ordered
ordinary binder context. -/
def programExponential (Γ : Ctx S) (s : S.Srt) :
    Exponential (contextOf (program.{w} R equations []) Γ)
      (program R equations [] s) (program R equations Γ s) :=
  (parameterExponential R equations Γ s).transport
    (parameterContextRepresentableIso R equations Γ).symm (Iso.refl _) (Iso.refl _)

/-- Selected evaluation converts the ordinary environment through the proved
parameter-product comparison and applies the actual restored body arrow. -/
theorem programExponential_eval_apply (a : Classifier R equations)
    (Γ : Ctx S) (s : S.Srt)
    (environment : (contextOf (program.{w} R equations []) Γ).obj (Opposite.op a))
    (body : (program.{w} R equations Γ s).obj (Opposite.op a)) :
    (programExponential R equations Γ s).eval.app (Opposite.op a) (environment, body) =
      ULift.up (programProductLift R equations (𝟙 a)
          (((parameterContextRepresentableIso R equations Γ).inv.app (Opposite.op a)
            environment).down) ≫
        (selectedBinderHomEquiv equations R a Γ s).symm body.down) := by
  change (parameterExponential R equations Γ s).eval.app (Opposite.op a)
      (((parameterContextRepresentableIso R equations Γ).inv.app (Opposite.op a) environment),
        body) = _
  exact parameterExponential_eval_apply R equations a Γ s _ body

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
