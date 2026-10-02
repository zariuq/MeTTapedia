import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramData
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramMeaningRepresentatives
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramBinderSubstitution

/-!
# Metavariable application in the actual operational Yoneda model

An independent metavariable assignment supplies its scoped body. Evaluating
the ordered ordinary arguments uses the actual selected exponential and the
established capture-avoiding substitution. The comparison applies at every
generalized presheaf stage.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open CategoricalBindingModel SecondOrderContext
open IntrinsicScopedLocalPolynomial IntrinsicScopedLocalActedClassifier
open FreeBindingTerms (FamilyArgs)
universe w
variable {S : Signature} {K : List (MetaArity S)}
variable (R : List (LocalRule S)) (equations : List (EqAxiom S K))

section GenericCoordinates
variable {D : Type*} [Category D] [CartesianMonoidalCategory D]
variable (M : Model S D) {X : Object S}

/-- Tupled ordinary arguments are the ordinary environment of their
individual meanings, without currying or changing their order. -/
theorem tupleCtx_meaning_tupleEnv
    {Γ : Ctx S}
    (meaning : ∀ {Ξ : Ctx S} {r : S.Srt}, Term (withMetas S X.arities) Ξ r → M.Elem X.arities Ξ r)
    {Z : D} (assignment : Z ⟶ M.family X.arities) (environment : M.Env Z Γ) :
    ∀ (bs : Ctx S) (args : Args (withMetas S X.arities) (bs.map fun r => ([], r)) Γ),
      M.tupleCtx bs (FamilyArgs.map (fun term => meaning term)
        (FreeBindingTerms.syntaxToFamily args)) Z assignment environment =
      M.tupleEnv (fun r v => (meaning (argsToSub args r v)).value Z assignment environment)
  | [], .nil => rfl
  | _ :: bs, .cons head tail => by
      change lift ((meaning head).value Z assignment environment)
        (M.tupleCtx bs _ Z assignment environment) =
        lift ((meaning head).value Z assignment environment) _
      exact congrArg (lift ((meaning head).value Z assignment environment))
        (tupleCtx_meaning_tupleEnv meaning assignment environment bs tail)

/-- A family coordinate read through the functor's product comparison is
the actual generic metavariable slot. -/
theorem famIso_inv_familyProj {F : Object S ⥤ D} (data : PreservingData F)
    (L : List (MetaArity S)) (j : Fin L.length) :
    (data.famIso L).inv ≫ F.map (slot L j) = data.toModel.familyProj L j := by
  rw [← data.famIso_proj L j, Iso.inv_hom_id_assoc]
end GenericCoordinates

/-- Metavariable application after independent instantiation and ordinary
substitution is ordinary application of the assigned body. -/
theorem meta_application_substitution {M N : List (MetaArity S)}
    (assignment : (⟨N⟩ : Object S) ⟶ ⟨M⟩) {Γ : Ctx S}
    (environment : Sub (withMetas S N) Γ []) (j : Fin M.length)
    (args : Args (withMetas S M) ((M.get j).1.map fun r => ([], r)) Γ) :
    bind environment (instInto assignment (Term.op (Sum.inr (MetaOp.mk j)) args)) =
      bind (fun r v => bind environment (instInto assignment (argsToSub args r v)))
        (assignment j) := by
  change bind environment (bind (argsToSub (instIntoArgs assignment args)) (assignment j)) = _
  rw [bind_comp]
  congr 1
  funext r v
  exact congrArg (bind environment) (argsToSub_instIntoArgs assignment _ args r v)

/-- Read any assigned scoped metavariable body through its actual generic
slot, for arbitrary noninjective quotient assignments. -/
theorem programRestrictionData_assignment_slot_apply
    (X : Object S) (j : Fin X.arities.length)
    {Z : Presheaf.{w} R equations}
    (assignmentPoint : Z ⟶ (programData R equations).toModel.family X.arities)
    (a : Classifier R equations) (z : Z.obj (Opposite.op a))
    (assignment : a.base.as ⟶ X)
    (readAssignment :
      (((programData R equations).famIso X.arities).inv.app (Opposite.op a)
        (assignmentPoint.app (Opposite.op a) z)).down.base =
        (authoredEquationPresentation S equations).quotientFunctor.map assignment) :
    (assignmentPoint ≫ (programData R equations).toModel.familyProj X.arities j).app
        (Opposite.op a) z =
      ULift.up ((programHomEquiv R equations a _).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (assignment j)))) := by
  have coordinate := congrArg (assignmentPoint ≫ ·)
    (famIso_inv_familyProj (programData R equations) X.arities j).symm
  have read := ConcreteCategory.congr_hom (NatTrans.congr_app coordinate (Opposite.op a)) z
  refine read.trans ?_
  apply ULift.ext
  apply (programHomEquiv R equations a _).injective
  change (((programData R equations).famIso X.arities).inv.app (Opposite.op a)
      (assignmentPoint.app (Opposite.op a) z)).down.base ≫
      (authoredEquationPresentation S equations).quotientFunctor.map (slot X.arities j) = _
  rw [readAssignment]
  let Q := (authoredEquationPresentation S equations).quotientFunctor
  have raw : assignment ≫ slot X.arities j = termArrow (assignment j) :=
    (assignment_comp_termArrow assignment (metaVar j)).trans
      (congrArg termArrow (instInto_metaVar assignment j))
  exact (Q.map_comp assignment (slot X.arities j)).symm.trans (congrArg Q.map raw)

/-- Actual metavariable argument meanings form precisely the represented
ordered ordinary argument tuple. -/
theorem programRestrictionData_tupleCtx_apply
    (X : Object S) {Γ : Ctx S} (bs : Ctx S)
    (args : Args (withMetas S X.arities) (bs.map fun r => ([], r)) Γ)
    {Z : Presheaf.{w} R equations}
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
        (authoredEquationPresentation S equations).quotientFunctor.map (termArrow (env r v))) :
    ((programData R equations).toModel.tupleCtx bs
      (FamilyArgs.map (fun term => (programData R equations).meaning term)
        (FreeBindingTerms.syntaxToFamily args)) Z assignmentPoint environment).app
        (Opposite.op a) z =
      (parameterContextRepresentableIso R equations bs).hom.app (Opposite.op a)
        (ULift.up ((programHomEquiv R equations a _).symm
          (parameterEnvironmentArrow equations a.base bs
            (fun r v => bind env (instInto assignment (argsToSub args r v)))))) := by
  have tuple := tupleCtx_meaning_tupleEnv (programData R equations).toModel
    (fun term => (programData R equations).meaning term) assignmentPoint environment bs args
  have calculated := programRestrictionData_tupleEnv_apply R equations
    (fun r v => ((programData R equations).meaning (argsToSub args r v)).value
      Z assignmentPoint environment) a z
      (fun r v => bind env (instInto assignment (argsToSub args r v)))
      (fun r v => programRestrictionData_meaning_apply_base R equations X
        (argsToSub args r v) assignmentPoint environment a z assignment env
        readAssignment readEnvironment)
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app tuple (Opposite.op a)) z).trans calculated

/-- Metavariable application obeys the actual constructor law on every
point of every generalized operational stage. -/
theorem programRestrictionData_meaning_meta_value
    (X : Object S) {Γ : Ctx S} (j : Fin X.arities.length)
    (args : Args (withMetas S X.arities) ((X.arities.get j).1.map fun r => ([], r)) Γ)
    (Z : Presheaf.{w} R equations)
    (assignmentPoint : Z ⟶ (programData R equations).toModel.family X.arities)
    (environment : (programData R equations).toModel.Env Z Γ) :
    ((programData R equations).meaning (Term.op (Sum.inr (MetaOp.mk j)) args)).value
      Z assignmentPoint environment =
    ((programData R equations).toModel.metaElem j
      (FamilyArgs.map (fun term => (programData R equations).meaning term)
        (FreeBindingTerms.syntaxToFamily args))).value Z assignmentPoint environment := by
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.hom_ext
  intro z
  obtain ⟨assignment, env, readAssignment, readEnvironment⟩ :=
    programRestrictionData_meaning_representatives R equations X assignmentPoint environment a.unop z
  have meaning := programRestrictionData_meaning_apply R equations X
    (Term.op (Sum.inr (MetaOp.mk j)) args) assignmentPoint environment a.unop z
      assignment env readAssignment readEnvironment
  have arguments := programRestrictionData_tupleCtx_apply R equations X (X.arities.get j).1
    args assignmentPoint environment a.unop z assignment env readAssignment readEnvironment
  have body := programRestrictionData_assignment_slot_apply R equations X j assignmentPoint
    a.unop z assignment readAssignment
  have evaluated := programExponential_eval_environment equations R a.unop (X.arities.get j).1
    (fun r v => bind env (instInto assignment (argsToSub args r v))) (assignment j)
  have right :
      (((programData R equations).toModel.metaElem j
        (FamilyArgs.map (fun term => (programData R equations).meaning term)
          (FreeBindingTerms.syntaxToFamily args))).value Z assignmentPoint environment).app a z =
      ULift.up ((programHomEquiv R equations a.unop _).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (bind (fun r v => bind env (instInto assignment (argsToSub args r v)))
            (assignment j))))) := by
    change (programExponential R equations (X.arities.get j).1 (X.arities.get j).2).eval.app a
      (((programData R equations).toModel.tupleCtx _ _ Z assignmentPoint environment).app a z,
        (assignmentPoint ≫ (programData R equations).toModel.familyProj X.arities j).app a z) = _
    rw [arguments, body]
    exact evaluated
  have raw := meta_application_substitution assignment env j args
  exact meaning.trans ((congrArg (fun term => ULift.up ((programHomEquiv R equations a.unop _).symm
    ((authoredEquationPresentation S equations).quotientFunctor.map (termArrow term)))) raw).trans
      right.symm)

private theorem metaData_metavariable (X : Object S) {Γ : Ctx S} (j : Fin X.arities.length)
    (args : Args (withMetas S X.arities) ((X.arities.get j).1.map fun r => ([], r)) Γ) :
    (programData.{w} R equations).meaning (Term.op (Sum.inr (MetaOp.mk j)) args) =
      (programData R equations).toModel.metaElem j
        (FamilyArgs.map (fun term => (programData R equations).meaning term)
          (FreeBindingTerms.syntaxToFamily args)) := by
  apply Model.ElemOver.ext
  funext Z assignment environment
  exact programRestrictionData_meaning_meta_value R equations X j args Z assignment environment

/-- The actual program restriction satisfies the metavariable constructor
law, including arbitrary scoped assignments and ordinary argument values. -/
theorem programRestrictionData_meaning_meta (X : Object S) {Γ : Ctx S}
    (j : Fin X.arities.length)
    (args : Args (withMetas S X.arities) ((X.arities.get j).1.map fun r => ([], r)) Γ) :
    (programRestrictionData.{w} R equations (programExponential R equations)).meaning
      (Term.op (Sum.inr (MetaOp.mk j)) args) =
      (programRestrictionData R equations (programExponential R equations)).toModel.metaElem j
        (FamilyArgs.map (fun term =>
          (programRestrictionData R equations (programExponential R equations)).meaning term)
          (FreeBindingTerms.syntaxToFamily args)) :=
  metaData_metavariable R equations X j args

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
end
