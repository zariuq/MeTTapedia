import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafFoldComparison
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafCategoricalControls

/-!
# The actual extension of the categorical LamCong firing

The genuine Kan extension is evaluated at the adapted original Boolean
occurrence and its retained binder-local child. The result is the implemented
categorical firing, with the same original evidence and distinct endpoints.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafExtensionControls

open _root_.CategoryTheory
open IntrinsicScopedLocalActedTypeComparisonControls
open IntrinsicScopedOperationalPresheafControls (algebra liftedModel stage generalizedStage)
open IntrinsicScopedOperationalPresheafPrograms (model power)
open IntrinsicScopedOperationalPresheafEvents (events)
open IntrinsicScopedOperationalPresheafEventPowers (objects sourcePower targetPower)
open IntrinsicScopedOperationalPresheafEventFunctions (stageEventEquiv)
open IntrinsicScopedOperationalPresheafCategoricalControls
open IntrinsicScopedOperationalPresheafFoldComparison
open IntrinsicScopedLocalPolynomial (childJudgment conclusionJudgment)

/-- The actual occurrence and original ordered child value the classifier's generic rule object. -/
def extensionLamValuation :=
  ruleValuation categoricalBoolModel categoricalLamOccurrence categoricalLamChildren

/-- The generic rule input retains the represented individual child under its authored binder. -/
theorem extension_lam_ordered_child
    (position : Fin (lambdaRules.get categoricalLamOccurrence.index).2.premises.length) :
    HEq ((ruleValuation categoricalBoolModel categoricalLamOccurrence categoricalLamChildren).event
      position) (categoricalLamChildren position) :=
  ruleValuation_event categoricalBoolModel categoricalLamOccurrence categoricalLamChildren position

/-- The real left Kan extension of the generic rule representative at this full valuation. -/
def extensionLamEvent : generalizedStage ⟶ events liftedModel.toAction [] .term :=
  extensionRuleEvent.{0} categoricalBoolModel categoricalLamOccurrence categoricalLamChildren

/-- The actual extension returns the implemented categorical rule action. -/
theorem extension_lam_rule_action : extensionLamEvent = categoricalLamFiring.1 :=
  extension_rule_action.{0} categoricalBoolModel categoricalLamOccurrence categoricalLamChildren

/-- The independently constructed extension arrow has the actual firing's two endpoint clauses. -/
def extensionLamStageEvent : (objects liftedModel.toAction).StageEvent generalizedStage
    (conclusionJudgment lambdaRules ((model algebra).stage generalizedStage) categoricalLamOccurrence) :=
  ⟨extensionLamEvent,
    (congrArg (· ≫ sourcePower liftedModel.toAction [] .term) extension_lam_rule_action).trans
      categoricalLamFiring.2.1,
    (congrArg (· ≫ targetPower liftedModel.toAction [] .term) extension_lam_rule_action).trans
      categoricalLamFiring.2.2⟩

/-- Its retained event fiber is exactly the actual categorical rule firing. -/
theorem extension_lam_stage_event : extensionLamStageEvent = categoricalLamFiring :=
  Subtype.ext extension_lam_rule_action

/-- Reading the genuine extension at its representing point recovers the original retained event. -/
theorem extension_lam_recovers :
    (stageEventEquiv liftedModel.toAction generalizedStage _ extensionLamStageEvent).1.app stage
      (PUnit.unit, 𝟙 stage.unop) = IntrinsicScopedOperationalPresheafControls.lamEvent :=
  (congrArg (fun event : (objects liftedModel.toAction).StageEvent generalizedStage
      (conclusionJudgment lambdaRules ((model algebra).stage generalizedStage) categoricalLamOccurrence) =>
    (stageEventEquiv liftedModel.toAction generalizedStage _ event).1.app stage
      (PUnit.unit, 𝟙 stage.unop)) extension_lam_stage_event).trans categoricalLamFiring_recovers

/-- The actual extended event still reads the original false source function. -/
theorem extension_lam_source :
    IntrinsicScopedLocalActedTypeComparison.TypeModel.carrierEquiv boolModel [] .term
      (MultiBinderPresheaf.scopedBodyEquiv algebra stage.unop [] .term
        ((extensionLamEvent ≫ sourcePower liftedModel.toAction [] .term).app stage
          (𝟙 stage.unop))) = (fun _ => false) :=
  (congrArg (fun arrow : generalizedStage ⟶ events liftedModel.toAction [] .term =>
    IntrinsicScopedLocalActedTypeComparison.TypeModel.carrierEquiv boolModel [] .term
      (MultiBinderPresheaf.scopedBodyEquiv algebra stage.unop [] .term
        ((arrow ≫ sourcePower liftedModel.toAction [] .term).app stage (𝟙 stage.unop))))
    extension_lam_rule_action).trans categoricalLamFiring_source

/-- The same extension retains the distinct true target function. -/
theorem extension_lam_target :
    IntrinsicScopedLocalActedTypeComparison.TypeModel.carrierEquiv boolModel [] .term
      (MultiBinderPresheaf.scopedBodyEquiv algebra stage.unop [] .term
        ((extensionLamEvent ≫ targetPower liftedModel.toAction [] .term).app stage
          (𝟙 stage.unop))) = (fun _ => true) :=
  (congrArg (fun arrow : generalizedStage ⟶ events liftedModel.toAction [] .term =>
    IntrinsicScopedLocalActedTypeComparison.TypeModel.carrierEquiv boolModel [] .term
      (MultiBinderPresheaf.scopedBodyEquiv algebra stage.unop [] .term
        ((arrow ≫ targetPower liftedModel.toAction [] .term).app stage (𝟙 stage.unop))))
    extension_lam_rule_action).trans categoricalLamFiring_target

/-- A real binder-local firing remains non-diagonal after the actual presheaf extension. -/
theorem extension_lam_not_diagonal :
    extensionLamEvent ≫ sourcePower liftedModel.toAction [] .term ≠
      extensionLamEvent ≫ targetPower liftedModel.toAction [] .term := by
  intro same
  apply categoricalLamFiring_not_diagonal
  exact (congrArg (· ≫ sourcePower liftedModel.toAction [] .term) extension_lam_rule_action).symm.trans
    (same.trans (congrArg (· ≫ targetPower liftedModel.toAction [] .term) extension_lam_rule_action))

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafExtensionControls
