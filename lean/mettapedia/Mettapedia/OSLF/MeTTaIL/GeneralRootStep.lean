import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics
import Mettapedia.OSLF.MeTTaIL.GeneralRootReceipt

/-! A licensed root firing is a step of the existing occurrence GSLT.
The receipt retains the actual selected row, captures and premise history.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem root_firing_step {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {bound : List TypeExpr} {type : TypeExpr}
    {source target : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row) (enabled : plan.permissions.sites.enabled = true)
    (sourceTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      plan.snapshot.free bound type source)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) bound type source ordinal
      trace captured completed history target) :
    (gslt plan bound type).Step source target := by
  have targetTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      plan.snapshot.free bound type target := by
    cases firing with
    | fire _ _ _ _ _ _ _ _ typed => exact typed
  let receipt : GeneralRuleJobs.Receipt := {
    job := ⟨ordinal, row, .here bound type source⟩
    matcherTrace := trace
    captured := captured
    completed := completed
    premiseHistory := history
    localTarget := target
    target := target }
  have valid : receipt.Valid plan bound type source :=
    ⟨⟨List.mk_mem_zipIdx_iff_getElem?.mpr position, .here enabled sourceTyped.2.2.1 sourceTyped.1⟩,
      firing, rfl, rfl, targetTyped⟩
  exact ⟨source, receipt, .refl source, valid, .refl target⟩

theorem root_firing_semantic_step {plan : GeneralExecutionAdmission.Plan}
    {ordinal : Nat} {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} (enabled : plan.permissions.sites.enabled = true)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) bound type source ordinal
      trace captured completed history target) :
    (gslt plan bound type).Step source target := by
  obtain ⟨receipt, valid, same, _⟩ := GeneralRuleJobs.root_receipt plan enabled bound type source target ordinal
    trace captured completed history firing
  rw [← same]
  exact ⟨source, receipt, .refl source, valid, .refl receipt.target⟩

#print axioms root_firing_semantic_step

#print axioms root_firing_step

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics
