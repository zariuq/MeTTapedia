import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramData
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramParameterApplication
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedYonedaVariableMeaning

/-!
# Actual Yoneda term application and independent representatives

An ordinary environment is read through the ordered parameter product.
The actual program evaluator then applies its independent metavariable
assignment and ordinary substitution. The calculation holds at arbitrary
presheaf stages, including stages containing operational event variables.
-/

set_option autoImplicit false

noncomputable section
namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open CategoricalBindingModel SecondOrderContext IntrinsicScopedLocalActedClassifier
open IntrinsicScopedLocalPolynomial
universe w
variable {S : Signature}

section Points
variable {C : Type*} [Category C] (sort : S.Srt → Cᵒᵖ ⥤ Type w)

/-- Ordered context sections are determined by all their variable coordinates. -/
theorem contextPoint_ext (a : Cᵒᵖ) :
    ∀ (Γ : Ctx S) (first second : (contextOf sort Γ).obj a),
      (∀ {s : S.Srt} (v : Var Γ s),
        (projectVar sort v).app a first = (projectVar sort v).app a second) → first = second
  | [], first, second, _ => by
      change PUnit at first second
      exact Subsingleton.elim first second
  | _ :: Γ, first, second, same => by
      apply Prod.ext
      · exact same Var.zero
      · apply contextPoint_ext a Γ first.2 second.2
        intro s v
        exact same (Var.succ v)
end Points

variable (R : List (LocalRule S)) {K : List (MetaArity S)}
variable (equations : List (EqAxiom S K))
/-- Read an ordinary environment tuple using independent raw representatives
of its individual equation-class coordinates. -/
theorem programRestrictionData_tupleEnv_apply
    {Z : Presheaf.{w} R equations} {Γ : Ctx S}
    (environment : (programData R equations).toModel.Env Z Γ)
    (a : Classifier R equations) (z : Z.obj (Opposite.op a))
    (env : Sub (withMetas S a.base.as.arities) Γ [])
    (read : ∀ s (v : Var Γ s),
      ((environment s v).app (Opposite.op a) z).down.base =
        (authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (env s v))) :
    ((programData R equations).toModel.tupleEnv environment).app (Opposite.op a) z =
      (parameterContextRepresentableIso R equations Γ).hom.app (Opposite.op a)
        (ULift.up ((programHomEquiv R equations a _).symm
          (parameterEnvironmentArrow equations a.base Γ env))) := by
  apply contextPoint_ext (program R equations []) (Opposite.op a) Γ
  intro s v
  let point : (parameterRepresentable.{w} R equations Γ).obj (Opposite.op a) :=
    ULift.up ((programHomEquiv R equations a _).symm
      (parameterEnvironmentArrow equations a.base Γ env))
  have tuple := ConcreteCategory.congr_hom
    (NatTrans.congr_app ((programData R equations).toModel.tupleEnv_projectVar environment v)
      (Opposite.op a)) z
  have coordinate := ConcreteCategory.congr_hom
    (NatTrans.congr_app (parameterContextRepresentableIso_variable R equations v)
      (Opposite.op a)) point
  refine tuple.trans (coordinate.trans ?_).symm
  apply ULift.ext
  apply (programHomEquiv R equations a _).injective
  change parameterEnvironmentArrow equations a.base Γ env ≫
      parameterVariable equations v = ((environment s v).app (Opposite.op a) z).down.base
  exact (parameterEnvironmentArrow_variable equations a.base Γ env v).trans (read s v).symm

/-- The actual meaning evaluator applies the represented program assignment
and ordinary environment independently. The read equations select arbitrary
raw representatives; they do not constrain which valuations can be used. -/
theorem programRestrictionData_meaning_apply
    (X : Object S) {Z : Presheaf.{w} R equations} {Γ : Ctx S} {s : S.Srt}
    (term : Term (withMetas S X.arities) Γ s)
    (assignmentPoint : Z ⟶ (programData R equations).toModel.family X.arities)
    (environment : (programData R equations).toModel.Env Z Γ)
    (a : Classifier R equations) (z : Z.obj (Opposite.op a))
    (assignment : a.base.as ⟶ X)
    (env : Sub (withMetas S a.base.as.arities) Γ [])
    (readAssignment :
      (((programData R equations).famIso X.arities).inv.app (Opposite.op a)
        (assignmentPoint.app (Opposite.op a) z)).down.base =
          (authoredEquationPresentation S equations).quotientFunctor.map assignment)
    (readEnvironment : ∀ r (v : Var Γ r),
      ((environment r v).app (Opposite.op a) z).down.base =
        (authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (env r v))) :
    (((programData R equations).meaning term).value Z assignmentPoint environment).app
        (Opposite.op a) z =
      ULift.up ((programHomEquiv R equations a _).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (bind env (instInto assignment term))))) := by
  have tuple := programRestrictionData_tupleEnv_apply R equations environment a z env
    readEnvironment
  have body :
      (assignmentPoint ≫ ((programData R equations).famIso X.arities).inv ≫
        (programRestriction R equations).map (termArrow term)).app (Opposite.op a) z =
      ULift.up ((programHomEquiv R equations a _).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (instInto assignment term)))) := by
    apply ULift.ext
    apply (programHomEquiv R equations a _).injective
    change (((programData R equations).famIso X.arities).inv.app (Opposite.op a)
      (assignmentPoint.app (Opposite.op a) z)).down.base ≫
        (authoredEquationPresentation S equations).quotientFunctor.map (termArrow term) = _
    rw [readAssignment]
    let Q := (authoredEquationPresentation S equations).quotientFunctor
    have raw := assignment_comp_termArrow assignment term
    have mapped : Q.map assignment ≫ Q.map (termArrow term) =
        Q.map (termArrow (instInto assignment term)) :=
      (Q.map_comp assignment (termArrow term)).symm.trans (congrArg Q.map raw)
    exact mapped
  change (programExponential R equations Γ s).eval.app (Opposite.op a)
    (((programData R equations).toModel.tupleEnv environment).app (Opposite.op a) z,
      (assignmentPoint ≫ ((programData R equations).famIso X.arities).inv ≫
        (programRestriction R equations).map (termArrow term)).app (Opposite.op a) z) = _
  rw [tuple, body]
  exact programExponential_eval_environment equations R a Γ env (instInto assignment term)

/-- The meaning computation read as its actual equation-context arrow. -/
theorem programRestrictionData_meaning_apply_base
    (X : Object S) {Z : Presheaf.{w} R equations} {Γ : Ctx S} {s : S.Srt}
    (term : Term (withMetas S X.arities) Γ s)
    (assignmentPoint : Z ⟶ (programData R equations).toModel.family X.arities)
    (environment : (programData R equations).toModel.Env Z Γ)
    (a : Classifier R equations) (z : Z.obj (Opposite.op a))
    (assignment : a.base.as ⟶ X)
    (env : Sub (withMetas S a.base.as.arities) Γ [])
    (readAssignment :
      (((programData R equations).famIso
        X.arities).inv.app (Opposite.op a) (assignmentPoint.app (Opposite.op a) z)).down.base =
          (authoredEquationPresentation S equations).quotientFunctor.map assignment)
    (readEnvironment : ∀ r (v : Var Γ r),
      ((environment r v).app (Opposite.op a) z).down.base =
        (authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (env r v))) :
    ((((programData R equations).meaning term).value
        Z assignmentPoint environment).app (Opposite.op a) z).down.base =
      (authoredEquationPresentation S equations).quotientFunctor.map
        (termArrow (bind env (instInto assignment term))) :=
  congrArg (fun value => value.down.base)
    (programRestrictionData_meaning_apply R equations X term assignmentPoint environment a z
      assignment env readAssignment readEnvironment)

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
end
