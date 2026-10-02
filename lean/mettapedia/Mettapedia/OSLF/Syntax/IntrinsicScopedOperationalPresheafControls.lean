import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafActions
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalModelPresheafControls
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalCarrierTransport

/-!
# Retained LamCong evidence in the operational presheaf interpretation

The existing Boolean function model's actual ordered binder-local firing is
retained by the new contextual event powers. Its source and target remain
distinct; representing and substituting generalized evidence does not identify
them or discard its witness.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafControls

open _root_.CategoryTheory
open IntrinsicScopedLocalActedTypeComparisonControls
open IntrinsicScopedOperationalPresheafEvents
open IntrinsicScopedOperationalPresheafEventPowers
open IntrinsicScopedOperationalPresheafActions
open AuthoredPositionedRulePolynomial (Judgment)

abbrev originalModel := IntrinsicScopedLocalModelPresheafControls.localModel
abbrev algebra := boolPrograms.stage PUnit
abbrev stage := IntrinsicScopedLocalModelPresheafControls.closedStage

/-- The genuine original operational model with only its evidence universe raised. -/
def liftedModel : IntrinsicScopedLocalSubstitutionModel.SubstitutionModel.{1,1} lambdaRules algebra :=
  originalModel.transportCarrier
    (carrier := fun j => ULift.{1,0} (originalModel.carrier j)) (fun _ => Equiv.ulift.symm)

/-- The actual retained LamCong witness, preserving its ordered bound premise. -/
def lamEvidence : liftedModel.carrier IntrinsicScopedLocalModelPresheafControls.lamJudgment :=
  (liftedModel.rules).act () _ ⟨⟨lamOccurrence, rfl⟩, fun position => ULift.up (lamChildren position)⟩

/-- The contextual event object retains the real firing and its endpoint pair. -/
def lamEvent : (events liftedModel.toAction [] .term).obj stage :=
  (eventAtEquiv liftedModel.toAction [] .term stage).symm
    ⟨IntrinsicScopedLocalModelPresheafControls.lamJudgment.2.2, lamEvidence⟩

/-- The source power reads the original LamCong source, rather than a closed approximation. -/
theorem lam_source_body :
    MultiBinderPresheaf.scopedBodyEquiv algebra stage.unop [] .term
        ((sourcePower liftedModel.toAction [] .term).app stage lamEvent) =
      IntrinsicScopedLocalModelPresheafControls.lamJudgment.2.2.1 :=
  sourcePower_body liftedModel.toAction [] .term stage lamEvent

/-- The target power reads the original result of the actual rule action. -/
theorem lam_target_body :
    MultiBinderPresheaf.scopedBodyEquiv algebra stage.unop [] .term
        ((targetPower liftedModel.toAction [] .term).app stage lamEvent) =
      IntrinsicScopedLocalModelPresheafControls.lamJudgment.2.2.2 :=
  targetPower_body liftedModel.toAction [] .term stage lamEvent

/-- Passing to actual event function objects preserves the two distinct program endpoints. -/
theorem lam_powers_not_diagonal :
    (sourcePower liftedModel.toAction [] .term).app stage lamEvent ≠
      (targetPower liftedModel.toAction [] .term).app stage lamEvent := by
  intro same
  have bodies := congrArg (MultiBinderPresheaf.scopedBodyEquiv algebra stage.unop [] .term) same
  rw [lam_source_body, lam_target_body] at bodies
  have values := congrArg
    (IntrinsicScopedLocalActedTypeComparison.TypeModel.carrierEquiv boolModel [] .term) bodies
  change (fun _ => false) = (fun _ => true) at values
  have impossible : false = true := congrFun values PUnit.unit
  cases impossible

/-- A generalized stage carrying the actual retained LamCong section. -/
abbrev generalizedStage := yoneda.obj stage.unop

/-- The real LamCong event determines a natural arrow at every clone stage. -/
def generalizedLamArrow : generalizedStage ⟶ events liftedModel.toAction [] .term :=
  yonedaEquiv.symm lamEvent

/-- Generalized source and target name the actual previously compared event powers. -/
def generalizedLamJudgment : Judgment ((IntrinsicScopedOperationalPresheafPrograms.model algebra).stage generalizedStage) :=
  ⟨[], .term,
    (IntrinsicScopedOperationalPresheafPrograms.model algebra).elemEquiv.symm
      (generalizedLamArrow ≫ sourcePower liftedModel.toAction [] .term),
    (IntrinsicScopedOperationalPresheafPrograms.model algebra).elemEquiv.symm
      (generalizedLamArrow ≫ targetPower liftedModel.toAction [] .term)⟩

/-- The actual contextual event object has this genuine generalized retained witness. -/
def generalizedLamEvent : (objects liftedModel.toAction).StageEvent generalizedStage generalizedLamJudgment :=
  ⟨generalizedLamArrow,
    ((IntrinsicScopedOperationalPresheafPrograms.model algebra).elemEquiv.apply_symm_apply _).symm,
    ((IntrinsicScopedOperationalPresheafPrograms.model algebra).elemEquiv.apply_symm_apply _).symm⟩

/-- Recovering the generalized arrow at its representing stage gives the real retained event. -/
theorem generalizedLamArrow_recovers :
    generalizedLamArrow.app stage (𝟙 stage.unop) = lamEvent :=
  yonedaEquiv.apply_symm_apply lamEvent

/-- The implemented categorical substitution fixes this nontrivial LamCong witness under identity. -/
theorem generalizedLam_identity :
    act liftedModel.toAction generalizedStage generalizedLamJudgment generalizedLamEvent
      (fun _ var => ((IntrinsicScopedOperationalPresheafPrograms.model algebra).stage generalizedStage).substitution.injectVar var)
      generalizedLamJudgment
      (IntrinsicScopedConditionalSubstitution.substJudgment_identity generalizedLamJudgment) =
        generalizedLamEvent :=
  act_identity liftedModel.toAction generalizedStage generalizedLamJudgment generalizedLamEvent _

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafControls
