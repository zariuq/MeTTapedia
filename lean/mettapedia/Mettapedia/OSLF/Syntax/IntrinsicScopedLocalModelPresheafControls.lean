import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalModelPresheaf
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTypeComparisonControls

/-!
# A retained LamCong section in the local model presheaf

The existing Boolean function model interprets the unchanged Lambda rule.
Its ordered premise is under one term binder. The actual rule action supplies
a section of the new endpoint image, and its two states remain distinct.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalModelPresheafControls

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone (ContextObject)
open IntrinsicScopedLocalActedTypeComparisonControls
open IntrinsicScopedLocalPolynomial (conclusionJudgment)
open AuthoredPositionedRulePolynomial (Judgment)

abbrev localModel := boolModel.stageModel PUnit

abbrev lamJudgment : Judgment (boolPrograms.stage PUnit) :=
  conclusionJudgment lambdaRules _ lamOccurrence

abbrev closedStage : IntrinsicScopedConditionalPresheaf.Base (boolPrograms.stage PUnit) :=
  Opposite.op (ContextObject.ofList (boolPrograms.stage PUnit).substitution.toClone [])

/-- The new event object retains the actual existing LamCong rule action. -/
def retainedLamEvent : IntrinsicScopedLocalModelPresheaf.ModelEvent lambdaRules localModel [] :=
  IntrinsicScopedLocalModelPresheaf.ruleEvent lambdaRules localModel
    ⟨lamOccurrence, rfl⟩ lamChildren

/-- The local image contains the endpoint pair of this actual binder-local firing. -/
theorem lam_reduction_section :
    ((ULift.up ⟨lamJudgment.2.1, lamJudgment.2.2.1⟩,
        ULift.up ⟨lamJudgment.2.1, lamJudgment.2.2.2⟩) :
      (IntrinsicScopedLocalModelPresheaf.modelStates (boolPrograms.stage PUnit)).obj closedStage ×
      (IntrinsicScopedLocalModelPresheaf.modelStates (boolPrograms.stage PUnit)).obj closedStage) ∈
      (IntrinsicScopedLocalModelPresheaf.modelReduction lambdaRules localModel).obj closedStage :=
  IntrinsicScopedLocalModelPresheaf.ruleEvent_mem_reduction lambdaRules localModel
    ⟨lamOccurrence, rfl⟩ lamChildren

/-- Its retained evidence is the same ordered-premise LamCong operation
whose endpoints compute to the two distinct Boolean constant functions. -/
theorem retainedLamEvent_value :
    retainedLamEvent.2.2.1 PUnit.unit = ((fun _ => false), (fun _ => true)) :=
  lam_firing_endpoint_pair

/-- Membership in the reduction image does not identify its two states. -/
theorem lam_section_not_diagonal :
    (IntrinsicScopedJudgmentActionPresheaf.endpointPair localModel.toAction retainedLamEvent).1 ≠
      (IntrinsicScopedJudgmentActionPresheaf.endpointPair localModel.toAction retainedLamEvent).2 := by
  intro same
  have termsEqual := eq_of_heq (Sigma.mk.inj_iff.mp same).2
  have valuesEqual := congrArg
    (IntrinsicScopedLocalActedTypeComparison.TypeModel.carrierEquiv boolModel []
      .term) termsEqual
  change (fun _ => false) = (fun _ => true) at valuesEqual
  have impossible : false = true := congrFun valuesEqual PUnit.unit
  cases impossible

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalModelPresheafControls
