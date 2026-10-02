import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramData
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramSelectedExponentials
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramParameterCoordinates
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedYonedaProgramProducts
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedYonedaParameterCoordinates

/-!
# Variable evaluation in the actual operational Yoneda model

The represented variable body evaluates to its supplied ordinary parameter.
This uses the independently proved selected exponential and its actual
fresh-coordinate comparison rather than assuming a variable interpretation law.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open CategoricalBindingModel SecondOrderContext SecondOrderVariableAbstraction
open IntrinsicScopedLocalPolynomial IntrinsicScopedLocalActedClassifier

universe w
variable {S : Signature} {K : List (MetaArity S)}
variable (R : List (LocalRule S)) (equations : List (EqAxiom S K))

/-- Equation-class assignment leaves every ordinary variable unchanged. -/
theorem quotient_variable_natural {X Y : Base equations} (f : X ⟶ Y)
    {Γ : Ctx S} {s : S.Srt} (v : Var Γ s) :
    f ≫ (authoredEquationPresentation S equations).quotientFunctor.map
        (termArrow (Term.var (S := withMetas S Y.as.arities) v)) =
      (authoredEquationPresentation S equations).quotientFunctor.map
        (termArrow (Term.var (S := withMetas S X.as.arities) v)) := by
  induction f using Quot.ind with
  | _ f =>
      change (authoredEquationPresentation S equations).quotientFunctor.map
          (f ≫ termArrow (Term.var (S := withMetas S Y.as.arities) v)) = _
      apply congrArg (authoredEquationPresentation S equations).quotientFunctor.map
      apply oneObj_hom_ext
      rfl

/-- The actual image of a variable arrow is independent of every supplied
metavariable valuation, including at stages containing event variables. -/
theorem programRestriction_variable_apply (X : Object S)
    (a : Classifier R equations) {Γ : Ctx S} {s : S.Srt}
    (assignment : ((programRestriction.{w} R equations).obj X).obj (Opposite.op a))
    (v : Var Γ s) :
    ((programRestriction R equations).map
        (termArrow (Term.var (S := withMetas S X.arities) v))).app (Opposite.op a)
        assignment =
      ULift.up ((programHomEquiv R equations a _).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (Term.var (S := withMetas S a.base.as.arities) v)))) := by
  apply ULift.ext
  apply (programHomEquiv R equations a _).injective
  exact quotient_variable_natural equations assignment.down.base v

/-- The actual parameter evaluation of a variable has precisely that
parameter's program assignment, retaining the arbitrary operational stage. -/
theorem parameterExponential_eval_variable_base
    (a : Classifier R equations) {Γ : Ctx S} {s : S.Srt}
    (argument : (parameterRepresentable.{w} R equations Γ).obj (Opposite.op a))
    (v : Var Γ s) :
    ((parameterExponential R equations Γ s).eval.app (Opposite.op a)
      (argument, ULift.up ((programHomEquiv R equations a _).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (Term.var (S := withMetas S a.base.as.arities) v)))))).down.base =
      argument.down.base ≫ parameterVariable equations v := by
  rw [parameterExponential_eval_termArrow_base]
  rw [← extensionProductIso_variable equations a.base v]
  simp only [Iso.inv_hom_id_assoc]
  exact prod.lift_snd_assoc (𝟙 a.base) argument.down.base (parameterVariable equations v)

/-- Parameter evaluation of a variable is the actual representable image
of the corresponding parameter coordinate. -/
theorem parameterExponential_eval_variable
    (a : Classifier R equations) {Γ : Ctx S} {s : S.Srt}
    (argument : (parameterRepresentable.{w} R equations Γ).obj (Opposite.op a))
    (v : Var Γ s) :
    (parameterExponential R equations Γ s).eval.app (Opposite.op a)
      (argument, ULift.up ((programHomEquiv R equations a _).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (Term.var (S := withMetas S a.base.as.arities) v))))) =
      ((programSection R equations ⋙ embedding.{w} R equations).map
        (parameterVariable equations v)).app (Opposite.op a) argument := by
  apply ULift.ext
  apply (programHomEquiv R equations a _).injective
  exact parameterExponential_eval_variable_base R equations a argument v

/-- Actual selected evaluation of a variable body returns the supplied
ordinary environment coordinate at every operational stage. -/
theorem programExponential_eval_variable
    (a : Classifier R equations) {Γ : Ctx S} {s : S.Srt}
    (environment : (contextOf (program.{w} R equations []) Γ).obj (Opposite.op a))
    (v : Var Γ s) :
    (programExponential R equations Γ s).eval.app (Opposite.op a)
      (environment, ULift.up ((programHomEquiv R equations a _).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (Term.var (S := withMetas S a.base.as.arities) v))))) =
      (projectVar (program R equations []) v).app (Opposite.op a) environment := by
  change (parameterExponential R equations Γ s).eval.app (Opposite.op a)
      ((parameterContextRepresentableIso R equations Γ).inv.app (Opposite.op a)
        environment, ULift.up ((programHomEquiv R equations a _).symm
          ((authoredEquationPresentation S equations).quotientFunctor.map
            (termArrow (Term.var (S := withMetas S a.base.as.arities) v))))) = _
  rw [parameterExponential_eval_variable]
  have projection :
      (parameterContextRepresentableIso.{w} R equations Γ).inv ≫
        (programSection R equations ⋙ embedding R equations).map
          (parameterVariable equations v) =
      projectVar (program R equations []) v := by
    rw [← parameterContextRepresentableIso_variable R equations v,
      Iso.inv_hom_id_assoc]
  change ((parameterContextRepresentableIso R equations Γ).inv ≫
      (programSection R equations ⋙ embedding R equations).map
        (parameterVariable equations v)).app (Opposite.op a) environment = _
  rw [projection]
  rfl

/-- Evaluation of an actual variable arrow is projection after the ordinary
environment, for every presheaf stage and every metavariable valuation. -/
theorem programExponential_variableArrow_eval
    {Z : Presheaf.{w} R equations} (X : Object S)
    {Γ : Ctx S} {s : S.Srt} (v : Var Γ s)
    (environment : Z ⟶ contextOf (program R equations []) Γ)
    (assignment : Z ⟶ (programRestriction R equations).obj X) :
    _root_.CategoryTheory.CartesianMonoidalCategory.lift environment
        (assignment ≫ (programRestriction R equations).map (termArrow (Term.var v))) ≫
      (programExponential R equations Γ s).eval =
      environment ≫ projectVar (program R equations []) v := by
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.hom_ext
  intro z
  change (programExponential R equations Γ s).eval.app a
      (environment.app a z,
        ((programRestriction R equations).map (termArrow (Term.var v))).app a
          (assignment.app a z)) = _
  rw [programRestriction_variable_apply]
  exact programExponential_eval_variable R equations a.unop (environment.app a z) v

section GenericVariableMeaning

universe u v
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {F : Object S ⥤ D} (data : PreservingData F)

/-- Projection evaluation implies the variable constructor law. The
evaluation premise is a statement about the actual generic variable arrow,
independently of the natural-family definition of term meaning. -/
theorem meaning_var_of_variableArrow_eval
    (evaluation : ∀ {Z : D} (X : Object S) {Γ : Ctx S} {s : S.Srt} (v : Var Γ s)
      (environment : Z ⟶ data.toModel.ctx Γ) (assignment : Z ⟶ F.obj X),
      _root_.CategoryTheory.CartesianMonoidalCategory.lift environment
          (assignment ≫ F.map (termArrow (Term.var v))) ≫ data.toModel.eval Γ s =
        environment ≫ projectVar data.toModel.sort v)
    (X : Object S) {Γ : Ctx S} {s : S.Srt} (v : Var Γ s) :
    data.meaning (X := X) (Term.var v) =
      ⟨fun _ _ ρ => ρ _ v, fun _ _ _ => rfl⟩ := by
  apply Model.ElemOver.ext
  funext Z m ρ
  change _root_.CategoryTheory.CartesianMonoidalCategory.lift
      (data.toModel.tupleEnv ρ)
      (m ≫ (data.famIso X.arities).inv ≫ F.map (termArrow (Term.var v))) ≫
      data.toModel.eval Γ s = ρ s v
  rw [← Category.assoc m (data.famIso X.arities).inv, evaluation]
  exact data.toModel.tupleEnv_projectVar ρ v

end GenericVariableMeaning

private theorem variableProgramData_evaluation
    {Z : Presheaf.{w} R equations} (X : Object S)
    {Γ : Ctx S} {s : S.Srt} (v : Var Γ s)
    (environment : Z ⟶ (programData R equations).toModel.ctx Γ)
    (assignment : Z ⟶ (programRestriction R equations).obj X) :
    _root_.CategoryTheory.CartesianMonoidalCategory.lift environment
        (assignment ≫ (programRestriction R equations).map (termArrow (Term.var v))) ≫
      (programData R equations).toModel.eval Γ s =
      environment ≫ projectVar (programData R equations).toModel.sort v :=
  programExponential_variableArrow_eval R equations X v environment assignment

private theorem variableProgramData_variable (X : Object S)
    {Γ : Ctx S} {s : S.Srt} (v : Var Γ s) :
    (programData.{w} R equations).meaning (X := X) (Term.var v) =
      ⟨fun _ _ ρ => ρ _ v, fun _ _ _ => rfl⟩ :=
  meaning_var_of_variableArrow_eval (programData R equations)
    (variableProgramData_evaluation R equations) X v

/-- The actual program restriction's independently constructed data obeys
the variable constructor law, at all metavariable and operational stages. -/
theorem programRestrictionData_meaning_var (X : Object S)
    {Γ : Ctx S} {s : S.Srt} (v : Var Γ s) :
    (programData.{w} R equations).meaning
        (X := X) (Term.var v) =
      ⟨fun _ _ ρ => ρ _ v, fun _ _ _ => rfl⟩ :=
  variableProgramData_variable R equations X v

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
