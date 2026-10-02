import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramParameterCoordinates
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramExponentialHom
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramSelectedExponentials
import Mettapedia.OSLF.Syntax.CategoricalBindingUniversal

/-!
# Parameter application is ordinary substitution

The true product assignment fills the fresh parameters of a represented
body and retains its old metavariables. Applying that assignment to the
abstracted body is ordinary capture-avoiding substitution. The comparison
uses the actual equation-context products and their projection laws.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open SecondOrderContext SecondOrderVariableAbstraction
open CategoricalBindingModel IntrinsicScopedLocalActedClassifier

variable {S : Signature} {K : List (MetaArity S)} (equations : List (EqAxiom S K))
universe w

/-- Filling fresh parameters retains every original assignment, including
its own declared binder context. -/
theorem dischargeAssignment_oldParameterProjection (Γ : Ctx S) (X : Object S)
    {N : List (MetaArity S)}
    (body : (i : Fin X.arities.length) →
      Term (withMetas S N) (X.arities.get i).1 (X.arities.get i).2)
    (env : Sub (withMetas S N) Γ [])
    {Δ : Ctx S} {s : S.Srt} (term : Term (withMetas S X.arities) Δ s) :
    instInto (dischargeAssignment Γ body env)
      (instInto (oldParameterProjection Γ X) term) = instInto body term := by
  induction Γ generalizing X with
  | nil =>
      change instInto body (instInto (fun i => metaVar i) term) = instInto body term
      rw [instInto_metaVar_id]
  | cons a Γ ih =>
      change instInto (dischargeAssignment Γ
          (dischargeHeadAssignment (env _ .zero) body) (fun r v => env r (.succ v)))
        (instInto (oldParameterProjection Γ ⟨headMetas a X.arities⟩ ≫
          secondProjection S (single S [] a) X) term) = _
      have composite : instInto
          (oldParameterProjection Γ ⟨headMetas a X.arities⟩ ≫
            secondProjection S (single S [] a) X) term =
          instInto (oldParameterProjection Γ ⟨headMetas a X.arities⟩) (shift a term) :=
        (instInto_instInto (shiftAssignment a)
          (oldParameterProjection Γ ⟨headMetas a X.arities⟩) term).symm
      have retained := ih ⟨headMetas a X.arities⟩
        (dischargeHeadAssignment (env _ .zero) body) (fun r v => env r (.succ v)) (shift a term)
      exact (congrArg
        (instInto (dischargeAssignment Γ (dischargeHeadAssignment (env _ .zero) body)
          (fun r v => env r (.succ v)))) composite).trans
            (retained.trans (dischargeHeadAssignment_shift (env _ .zero) body term))

/-- Tuple the actual closed parameter values in the product's declaration order. -/
def parameterEnvironmentArrow (X : Base equations) : ∀ Γ : Ctx S,
    Sub (withMetas S X.as.arities) Γ [] → (X ⟶ parameterContext equations Γ)
  | [], _ => terminal.from X
  | _ :: Γ, env => prod.lift
      (parameterEnvironmentArrow X Γ (fun r v => env r (.succ v)))
      ((authoredEquationPresentation S equations).quotientFunctor.map (termArrow (env _ .zero)))

/-- Every tuple coordinate is the actual term assigned to that variable. -/
theorem parameterEnvironmentArrow_variable (X : Base equations) :
    ∀ (Γ : Ctx S) (env : Sub (withMetas S X.as.arities) Γ [])
      {s : S.Srt} (v : Var Γ s),
      parameterEnvironmentArrow equations X Γ env ≫ parameterVariable equations v =
        (authoredEquationPresentation S equations).quotientFunctor.map (termArrow (env s v))
  | _ :: _, env, _, .zero => prod.lift_snd _ _
  | a :: Γ, env, _, .succ v => by
      have coordinate := prod.lift_fst
        (parameterEnvironmentArrow equations X Γ (fun r w => env r (.succ w)))
        ((authoredEquationPresentation S equations).quotientFunctor.map (termArrow (env a .zero)))
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun h => h ≫ parameterVariable equations v) coordinate).trans
          (parameterEnvironmentArrow_variable X Γ (fun r w => env r (.succ w)) v))

/-- The actual ordered parameter projections jointly determine every arrow. -/
theorem parameterContext_hom_ext {Z : Base equations} :
    ∀ (Γ : Ctx S) (f g : Z ⟶ parameterContext equations Γ),
      (∀ {s : S.Srt} (v : Var Γ s),
        f ≫ parameterVariable equations v = g ≫ parameterVariable equations v) → f = g
  | [], f, g, _ => terminal.hom_ext f g
  | _ :: Γ, f, g, same => by
      apply prod.hom_ext
      · apply parameterContext_hom_ext Γ (f ≫ prod.fst) (g ≫ prod.fst)
        intro s v
        exact (Category.assoc _ _ _).trans
          ((same (.succ v)).trans (Category.assoc _ _ _).symm)
      · exact same .zero

/-- The raw assignment filling all fresh nullaries while retaining old declarations. -/
def parameterApplicationAssignment (X : Object S) (Γ : Ctx S)
    (env : Sub (withMetas S X.arities) Γ []) :
    X ⟶ (⟨extendedMetas Γ X.arities⟩ : Object S) :=
  dischargeAssignment Γ (fun i => metaVar i) env

/-- The old projection of the filled assignment is the identity assignment. -/
theorem parameterApplicationAssignment_old (X : Object S) (Γ : Ctx S)
    (env : Sub (withMetas S X.arities) Γ []) :
    parameterApplicationAssignment X Γ env ≫ oldParameterProjection Γ X = 𝟙 X := by
  funext i
  change instInto (parameterApplicationAssignment X Γ env)
      (oldParameterProjection Γ X i) = metaVar i
  have retaining := dischargeAssignment_oldParameterProjection Γ X (fun i => metaVar i) env
    (metaVar i)
  rw [instInto_metaVar, instInto_metaVar_id] at retaining
  exact retaining

/-- Filling an abstracted body is ordinary substitution in that body. -/
theorem parameterApplicationAssignment_abstractVars (X : Object S) (Γ : Ctx S)
    (env : Sub (withMetas S X.arities) Γ []) {s : S.Srt}
    (term : Term (withMetas S X.arities) Γ s) :
    instInto (parameterApplicationAssignment X Γ env) (abstractVars term) = bind env term := by
  change instInto (dischargeAssignment Γ (fun i => metaVar i) env) (abstractVars term) = _
  rw [dischargeAssignment_abstractVars, instInto_metaVar_id]

/-- Composition with a represented term instantiates its actual metavariables. -/
theorem assignment_comp_termArrow {X Y : Object S} (assignment : X ⟶ Y)
    {Γ : Ctx S} {s : S.Srt} (term : Term (withMetas S Y.arities) Γ s) :
    assignment ≫ termArrow term = termArrow (instInto assignment term) := by
  apply oneObj_hom_ext
  rfl

/-- The filling assignment is exactly the actual product pairing transported
back through the independently proved parameter-product isomorphism. -/
theorem parameterApplicationAssignment_product (X : Base equations) (Γ : Ctx S)
    (env : Sub (withMetas S X.as.arities) Γ []) :
    (authoredEquationPresentation S equations).quotientFunctor.map
        (parameterApplicationAssignment X.as Γ env) ≫
          (extensionProductIso equations Γ X).hom =
      prod.lift (𝟙 X) (parameterEnvironmentArrow equations X Γ env) := by
  let Q := (authoredEquationPresentation S equations).quotientFunctor
  let assignment := parameterApplicationAssignment X.as Γ env
  apply prod.hom_ext
  · have stage := extensionProductIso_stage equations Γ X
    have mapped : Q.map assignment ≫ Q.map (oldParameterProjection Γ X.as) = 𝟙 X :=
      (Q.map_comp assignment (oldParameterProjection Γ X.as)).symm.trans
        ((congrArg Q.map (parameterApplicationAssignment_old X.as Γ env)).trans (Q.map_id X.as))
    have stageAfter := congrArg (fun h => Q.map assignment ≫ h) stage
    exact (Category.assoc _ _ _).trans
      (stageAfter.trans (mapped.trans (prod.lift_fst _ _).symm))
  · apply parameterContext_hom_ext equations Γ
    intro s v
    have coordinate := extensionProductIso_variable equations X v
    have raw : assignment ≫ termArrow
          (abstractVars (Term.var (S := withMetas S X.as.arities) v)) =
        termArrow (env s v) :=
      (assignment_comp_termArrow assignment _).trans
        (congrArg (fun t : Term (withMetas S X.as.arities) [] s => termArrow t)
          (parameterApplicationAssignment_abstractVars X.as Γ env (.var v)))
    have mapped : Q.map assignment ≫
        Q.map (termArrow (abstractVars (Term.var (S := withMetas S X.as.arities) v))) =
        Q.map (termArrow (env s v)) :=
      (Q.map_comp assignment _).symm.trans (congrArg Q.map raw)
    have after := congrArg (fun h => Q.map assignment ≫ h) coordinate
    have actual : (Q.map assignment ≫ (extensionProductIso equations Γ X).hom) ≫
        prod.snd ≫ parameterVariable equations v = Q.map (termArrow (env s v)) :=
      (Category.assoc _ _ _).trans (after.trans mapped)
    have expected : prod.lift (𝟙 X) (parameterEnvironmentArrow equations X Γ env) ≫
        prod.snd ≫ parameterVariable equations v = Q.map (termArrow (env s v)) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun h => h ≫ parameterVariable equations v) (prod.lift_snd _ _)).trans
          (parameterEnvironmentArrow_variable equations X Γ env v))
    exact (Category.assoc _ _ _).trans
      ((actual.trans expected.symm).trans (Category.assoc _ _ _).symm)

/-- Read the actual pairing as its explicit filling assignment. -/
theorem parameterApplicationAssignment_product_inv (X : Base equations) (Γ : Ctx S)
    (env : Sub (withMetas S X.as.arities) Γ []) :
    prod.lift (𝟙 X) (parameterEnvironmentArrow equations X Γ env) ≫
        (extensionProductIso equations Γ X).inv =
      (authoredEquationPresentation S equations).quotientFunctor.map
        (parameterApplicationAssignment X.as Γ env) := by
  let assignment := (authoredEquationPresentation S equations).quotientFunctor.map
    (parameterApplicationAssignment X.as Γ env)
  have back : (assignment ≫ (extensionProductIso equations Γ X).hom) ≫
      (extensionProductIso equations Γ X).inv = assignment :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun h => assignment ≫ h) (extensionProductIso equations Γ X).hom_inv_id).trans
        (Category.comp_id assignment))
  exact (congrArg (fun h => h ≫ (extensionProductIso equations Γ X).inv)
    (parameterApplicationAssignment_product equations X Γ env).symm).trans
      back

/-- Applying the actual selected binder arrow to a parameter environment
is the equation class of ordinary capture-avoiding substitution. -/
theorem baseSelectedBinderHomEquiv_apply_environment
    (X : Base equations) (Γ : Ctx S)
    (env : Sub (withMetas S X.as.arities) Γ []) {s : S.Srt}
    (term : Term (withMetas S X.as.arities) Γ s) :
    prod.lift (𝟙 X) (parameterEnvironmentArrow equations X Γ env) ≫
        (baseSelectedBinderHomEquiv equations X Γ s).symm
          ((authoredEquationPresentation S equations).quotientFunctor.map (termArrow term)) =
      (authoredEquationPresentation S equations).quotientFunctor.map
        (termArrow (bind env term)) := by
  let Q := (authoredEquationPresentation S equations).quotientFunctor
  change prod.lift (𝟙 X) (parameterEnvironmentArrow equations X Γ env) ≫
      (extensionProductIso equations Γ X).inv ≫ Q.map (termArrow (abstractVars term)) = _
  have reassociated := (Category.assoc
    (prod.lift (𝟙 X) (parameterEnvironmentArrow equations X Γ env))
    (extensionProductIso equations Γ X).inv (Q.map (termArrow (abstractVars term)))).symm
  have paired := congrArg (fun h => h ≫ Q.map (termArrow (abstractVars term)))
    (parameterApplicationAssignment_product_inv equations X Γ env)
  have raw := (assignment_comp_termArrow (parameterApplicationAssignment X.as Γ env)
      (abstractVars term)).trans
    (congrArg (fun t : Term (withMetas S X.as.arities) [] s => termArrow t)
      (parameterApplicationAssignment_abstractVars X.as Γ env term))
  exact reassociated.trans (paired.trans
    ((Q.map_comp _ _).symm.trans (congrArg Q.map raw)))

/-- The same application law keeps an independent authored metavariable
assignment and ordinary variable environment. -/
theorem baseSelectedBinderHomEquiv_apply_assignment
    (X Y : Base equations) (assignment : X.as ⟶ Y.as) (Γ : Ctx S)
    (env : Sub (withMetas S X.as.arities) Γ []) {s : S.Srt}
    (term : Term (withMetas S Y.as.arities) Γ s) :
    prod.lift (𝟙 X) (parameterEnvironmentArrow equations X Γ env) ≫
        (baseSelectedBinderHomEquiv equations X Γ s).symm
          ((authoredEquationPresentation S equations).quotientFunctor.map assignment ≫
            (authoredEquationPresentation S equations).quotientFunctor.map (termArrow term)) =
      (authoredEquationPresentation S equations).quotientFunctor.map
        (termArrow (bind env (instInto assignment term))) := by
  let Q := (authoredEquationPresentation S equations).quotientFunctor
  have body : Q.map assignment ≫ Q.map (termArrow term) =
      Q.map (termArrow (instInto assignment term)) :=
    (Q.map_comp assignment (termArrow term)).symm.trans
      (congrArg Q.map (assignment_comp_termArrow assignment term))
  exact (congrArg (fun f => prod.lift (𝟙 X) (parameterEnvironmentArrow equations X Γ env) ≫
      (baseSelectedBinderHomEquiv equations X Γ s).symm f) body).trans
    (baseSelectedBinderHomEquiv_apply_environment equations X Γ env (instInto assignment term))

/-- The genuine presheaf exponential applies an authored environment as
ordinary substitution at every operational stage, including stages with events. -/
theorem programExponential_eval_environment
    (R : List (IntrinsicScopedLocalPolynomial.LocalRule S)) (a : Classifier R equations)
    (Γ : Ctx S) (env : Sub (withMetas S a.base.as.arities) Γ []) {s : S.Srt}
    (term : Term (withMetas S a.base.as.arities) Γ s) :
    (programExponential.{w} R equations Γ s).eval.app (Opposite.op a)
        ((parameterContextRepresentableIso R equations Γ).hom.app (Opposite.op a)
            (ULift.up ((programHomEquiv R equations a _).symm
              (parameterEnvironmentArrow equations a.base Γ env))),
          ULift.up ((programHomEquiv R equations a _).symm
            ((authoredEquationPresentation S equations).quotientFunctor.map (termArrow term)))) =
      ULift.up ((programHomEquiv R equations a _).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (bind env term)))) := by
  let point : (parameterRepresentable.{w} R equations Γ).obj (Opposite.op a) :=
    ULift.up ((programHomEquiv R equations a _).symm
      (parameterEnvironmentArrow equations a.base Γ env))
  have cancel : (parameterContextRepresentableIso.{w} R equations Γ).inv.app (Opposite.op a)
      ((parameterContextRepresentableIso R equations Γ).hom.app (Opposite.op a) point) = point :=
    ConcreteCategory.congr_hom
      ((parameterContextRepresentableIso R equations Γ).hom_inv_id_app (Opposite.op a)) point
  change (parameterExponential R equations Γ s).eval.app (Opposite.op a)
      ((parameterContextRepresentableIso R equations Γ).inv.app (Opposite.op a)
        ((parameterContextRepresentableIso R equations Γ).hom.app (Opposite.op a) point), _) = _
  rw [cancel]
  apply ULift.ext
  apply (programHomEquiv R equations a _).injective
  have actual := parameterExponential_eval_termArrow_base equations R a point term
  change ((parameterExponential R equations Γ s).eval.app (Opposite.op a)
      (point, ULift.up ((programHomEquiv R equations a _).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map (termArrow term))))).down.base = _
  exact actual.trans (baseSelectedBinderHomEquiv_apply_environment equations a.base Γ env term)

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

end
