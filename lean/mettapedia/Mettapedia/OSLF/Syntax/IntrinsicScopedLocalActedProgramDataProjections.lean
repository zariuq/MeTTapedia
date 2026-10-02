import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramData

/-!
# Selected evaluator projections of the canonical program data

The canonical program interpretation carries precisely the independently
constructed represented powers, evaluators and currying operations.
-/

set_option autoImplicit false
noncomputable section
namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open CategoricalBindingModel IntrinsicScopedLocalPolynomial
universe w
variable {S : Signature} {K : List (MetaArity S)}
variable (R : List (LocalRule S)) (equations : List (EqAxiom S K))

theorem programData_eval (Γ : Ctx S) (s : S.Srt) :
    (programData.{w} R equations).toModel.eval Γ s =
      (programExponential R equations Γ s).eval := rfl

theorem programData_curry {Z : Presheaf.{w} R equations}
    {Γ : Ctx S} {s : S.Srt}
    (f : contextOf (program R equations []) Γ ⊗ Z ⟶ program R equations [] s) :
    (programData R equations).toModel.curry f =
      (programExponential R equations Γ s).curry f := rfl

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
end
