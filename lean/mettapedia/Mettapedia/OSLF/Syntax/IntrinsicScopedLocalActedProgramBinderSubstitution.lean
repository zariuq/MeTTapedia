import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramPartialMeaning
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramMeaningApplication

/-!
# Actual evaluation and retained-binder substitution

Selected evaluation is the existing quotient clone's ordinary substitution.
The comparison keeps both the authored parameter order and every operational
stage explicit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open CategoricalBindingModel SecondOrderContext
open IntrinsicScopedLocalPolynomial IntrinsicScopedLocalActedClassifier
universe w
variable {S : Signature} {K : List (MetaArity S)}
variable (R : List (LocalRule S)) (equations : List (EqAxiom S K))

/-- An actual represented raw term reads as its existing equation class. -/
theorem programClassEquiv_termArrow (a : Classifier R equations)
    {Γ : Ctx S} {s : S.Srt} (term : Term (withMetas S a.base.as.arities) Γ s) :
    programClassEquiv.{w} R equations a Γ s
      (ULift.up ((programHomEquiv R equations a _).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map (termArrow term)))) =
      Quotient.mk _ term := rfl

/-- The inverse class comparison is the actual represented term arrow. -/
theorem programClassEquiv_symm_mk (a : Classifier R equations)
    {Γ : Ctx S} {s : S.Srt} (term : Term (withMetas S a.base.as.arities) Γ s) :
    (programClassEquiv.{w} R equations a Γ s).symm (Quotient.mk _ term) =
      ULift.up ((programHomEquiv R equations a _).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map (termArrow term))) := rfl

/-- Every actual program section has a raw representative in its original
ordinary context. Selecting it introduces no restriction on the section. -/
theorem programSection_eq_representative (a : Classifier R equations)
    {Γ : Ctx S} {s : S.Srt} (body : (program.{w} R equations Γ s).obj (Opposite.op a)) :
    body = ULift.up ((programHomEquiv R equations a _).symm
      ((authoredEquationPresentation S equations).quotientFunctor.map
        (termArrow (Quotient.out (programClassEquiv R equations a Γ s body))))) := by
  apply (programClassEquiv R equations a Γ s).injective
  exact ((Quotient.out_eq _).symm).trans
    (programClassEquiv_termArrow.{w} R equations a _).symm

/-- Selected evaluation reads as the quotient's genuine ordinary
substitution for arbitrary bodies and arbitrary ordered parameter points. -/
theorem programExponential_eval_class (a : Classifier R equations)
    (Γ : Ctx S) (s : S.Srt)
    (environment : (contextOf (program.{w} R equations []) Γ).obj (Opposite.op a))
    (body : (program.{w} R equations Γ s).obj (Opposite.op a)) :
    programClassEquiv R equations a [] s
      ((programExponential R equations Γ s).eval.app (Opposite.op a) (environment, body)) =
      (authoredEquationModelAt S equations a.base.as).algebra.substitution.substitute
        (fun r v => programClassEquiv R equations a [] r
          ((projectVar (program R equations []) v).app (Opposite.op a) environment))
        (programClassEquiv R equations a Γ s body) := by
  let env : Sub (withMetas S a.base.as.arities) Γ [] := fun r v =>
    Quotient.out (programClassEquiv R equations a [] r
      ((projectVar (program R equations []) v).app (Opposite.op a) environment))
  let term := Quotient.out (programClassEquiv R equations a Γ s body)
  have tuple : environment = (parameterContextRepresentableIso R equations Γ).hom.app
      (Opposite.op a) (ULift.up ((programHomEquiv R equations a _).symm
        (parameterEnvironmentArrow equations a.base Γ env))) := by
    apply contextPoint_ext (program R equations []) (Opposite.op a) Γ
    intro r v
    let point : (parameterRepresentable.{w} R equations Γ).obj (Opposite.op a) :=
      ULift.up ((programHomEquiv R equations a _).symm
        (parameterEnvironmentArrow equations a.base Γ env))
    have coordinate := ConcreteCategory.congr_hom
      (NatTrans.congr_app (parameterContextRepresentableIso_variable R equations v)
        (Opposite.op a)) point
    refine (coordinate.trans ?_).symm
    apply ULift.ext
    apply (programHomEquiv R equations a _).injective
    change parameterEnvironmentArrow equations a.base Γ env ≫
      parameterVariable equations v = _
    exact (parameterEnvironmentArrow_variable equations a.base Γ env v).trans
      (congrArg (fun value => value.down.base)
        (programSection_eq_representative R equations a
          ((projectVar (program R equations []) v).app (Opposite.op a) environment))).symm
  have represented : body = ULift.up ((programHomEquiv R equations a _).symm
      ((authoredEquationPresentation S equations).quotientFunctor.map (termArrow term))) :=
    programSection_eq_representative R equations a body
  have evaluated := programExponential_eval_environment equations R a Γ env term
  have calculation :
      (programExponential R equations Γ s).eval.app (Opposite.op a) (environment, body) =
      ULift.up ((programHomEquiv R equations a _).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (bind env term)))) := by
    rw [tuple, represented]
    exact evaluated
  have interpreted := (congrArg (programClassEquiv.{w} R equations a [] s) calculation).trans
    (programClassEquiv_termArrow.{w} R equations a (bind env term))
  refine interpreted.trans ?_
  let envQ : BindingSubstitutionAlgebra.Environment (withMetas S a.base.as.arities)
      (TermQ ((authoredEquationPresentation S equations).axioms a.base.as)) Γ [] :=
    fun r v => programClassEquiv R equations a [] r
      ((projectVar (program R equations []) v).app (Opposite.op a) environment)
  change (Quotient.mk _ (bind env term) :
      TermQ ((authoredEquationPresentation S equations).axioms a.base.as) [] s) =
    BindingEquationQuotientSubstitution.substitute _ envQ
      (programClassEquiv R equations a Γ s body)
  have quotientSubstitution := BindingEquationQuotientSubstitution.substitute_eq_bindQ
    ((authoredEquationPresentation S equations).axioms a.base.as) envQ env
    (by intro r v; exact Quotient.out_eq _) (programClassEquiv R equations a Γ s body)
  exact (congrArg (bindQ env) (Quotient.out_eq _)).trans quotientSubstitution.symm

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
end
