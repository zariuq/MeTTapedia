import Mettapedia.Languages.Metamath.MM2SourceActionRuleInventory
import Mettapedia.Languages.ProcessCalculi.MORK.MM2RuleScopedExecution

/-!
# Rule-scoped execution of the normal DV recovery loader

The recovery loader emits the normal DV verifier rules as authored literals.
Variables inside those literals are local to each emitted rule; they are not
matcher variables of the loader.  This module connects that real verifier
joint to the rule-scoped MM2 execution GSLT.
-/

namespace Mettapedia.Languages.Metamath.MM2NormalDVRuleScopedReload

open Mettapedia.GSLT
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2SourceActionExecution
open Mettapedia.Languages.Metamath.MM2SourceActionRuleInventory
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

private abbrev inventory : NormalProofRuleInventory :=
  normalProofMachineRuleInventory

private def reloadTrigger : Atom :=
  .expression [.symbol "mm-reload-dv", .symbol "proof-canary",
    .symbol "pc-canary"]

private def reloadRule : Atom :=
  normalDVFailureReloadRule inventory

private def expectedReloadedRules : List Atom :=
  [reloadRule,
   inventory.dvPairBegin,
   inventory.dvLeftConst,
   inventory.dvLeftVariable,
   inventory.dvRightConst,
   inventory.dvRightVariable,
   normalDVSameVariableFaultRule,
   inventory.dvRightNil,
   inventory.dvLeftNil,
   inventory.dvComplete]

/-- The real recovery loader remains accepted by the strict syntax decoder. -/
theorem recoveryLoader_decodes_exactly :
    extractSupportedSourceExecFact reloadRule =
      some (normalDVFailureReloadDirective inventory) := by
  exact extract_normalDVFailureReloadRule_exact inventory

/-- Rule-scoped execution consumes the request and installs all nine authored
normal-DV directives, including the same-variable fault case. -/
theorem recoveryLoader_fires_exactly :
    cFireRuleScopedSourceExecFact [reloadRule, reloadTrigger]
      (normalDVFailureReloadDirective inventory) = expectedReloadedRules := by
  decide +kernel

/-- The recovery load is one actual scheduled step of the reusable MM2 GSLT. -/
theorem recoveryLoader_scheduled_step :
    (ruleScopedNativeListExecGSLT .leaveInert).Step
      [reloadRule, reloadTrigger] expectedReloadedRules := by
  rw [ruleScopedNativeListExecGSLT_step_iff]
  decide +kernel

/-- The bounded evaluator records exactly this one transition and reaches the
same normal-DV inventory state. -/
theorem recoveryLoader_bounded_run :
    cRuleScopedSourceWorkQueueRunN .leaveInert 1
      [reloadRule, reloadTrigger] = (expectedReloadedRules, 1) := by
  decide +kernel

/-- The shared rule-scoped trace exposes the load as one transition rather
than hiding it in a closed evaluator result. -/
theorem recoveryLoader_rewritePath_length :
    (cRuleScopedSourceWorkQueueRunN_rewritePath .leaveInert 1
      [reloadRule, reloadTrigger]).length = 1 := by
  rw [cRuleScopedSourceWorkQueueRunN_rewritePath_length,
    recoveryLoader_bounded_run]

/-- The earlier fully-bound output policy republishes the loader but loses
every authored rule literal.  This is the exact semantic gap repaired by the
rule-scoped execution layer. -/
theorem strictReflectiveExecution_loses_reloadedRules :
    cFireReflectiveSourceExecFact [reloadRule, reloadTrigger]
      (normalDVFailureReloadDirective inventory) = [reloadRule] := by
  decide +kernel

/-- The installed result has one representative per physical compact key. -/
theorem recoveryLoader_result_keys_are_distinct :
    (expectedReloadedRules.map morkSupportKey).Nodup := by
  decide +kernel

#print axioms recoveryLoader_decodes_exactly
#print axioms recoveryLoader_fires_exactly
#print axioms recoveryLoader_scheduled_step
#print axioms recoveryLoader_bounded_run
#print axioms recoveryLoader_rewritePath_length
#print axioms strictReflectiveExecution_loses_reloadedRules
#print axioms recoveryLoader_result_keys_are_distinct

end Mettapedia.Languages.Metamath.MM2NormalDVRuleScopedReload
