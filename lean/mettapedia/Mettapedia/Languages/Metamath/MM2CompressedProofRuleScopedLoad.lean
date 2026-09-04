import Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
import Mettapedia.Languages.ProcessCalculi.MORK.MM2RuleScopedExecution

/-!
# Rule-scoped execution of compressed-verifier inventory loading

The compressed loader transports an opaque executable rule obtained from its
ordered input row.  This is the complementary case to literal rule emission:
the captured value is fully bound at the outer level, so the rule-scoped and
earlier reflective executions must agree exactly.
-/

namespace Mettapedia.Languages.Metamath.MM2CompressedProofRuleScopedLoad

open Mettapedia.GSLT
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

private def source : Atom := .symbol "compressed-rule-load-source"

private def position : Nat := 3

private def proofOwner : Atom :=
  .expression [.symbol "mm-source-proof-owner", source, natAtom position]

private def headerControl : Atom :=
  .expression
    [.symbol "mm-compressed-header-control", source, proofOwner, natAtom 0]

private def loading (rulePosition : Nat) : Atom :=
  .expression
    [.symbol "mm-source-compressed-rule-loading", source, natAtom position,
      proofOwner, headerControl, natAtom rulePosition]

/-- An opaque captured directive whose internal variable is local to that
directive rather than to the inventory loader. -/
private def loadedRule : Atom :=
  .expression
    [.symbol "exec",
      .expression [.symbol "98", .symbol "compressed-inventory-probe"],
      .expression
        [.symbol ",",
          .expression [.symbol "compressed-probe", .var "payload"]],
      .expression
        [.symbol "O",
          .expression
            [.symbol "+",
              .expression [.symbol "compressed-seen", .var "payload"]]]]

private def ruleRow : Atom :=
  linkedRow "compressed-verifier-rule" compressedVerifierRuleOwner 0 1
    loadedRule

private def loadInput : List Atom :=
  [sourceCompressedRuleLoadRule, loading 0, ruleRow]

private def loadedDispatchRow : Atom :=
  .expression [.symbol "mm-internal-compressed-dispatch-rule", loadedRule]

private def loadOutput : List Atom :=
  [ruleRow, sourceCompressedRuleLoadRule, loadedDispatchRow, loading 1]

/-- The rule-scoped execution transports the opaque compressed rule and
advances the exact occurrence-indexed loading cursor. -/
theorem compressedRuleLoader_fires_exactly :
    cFireRuleScopedSourceExecFact loadInput
      sourceCompressedRuleLoadDirective = loadOutput := by
  decide +kernel

/-- The compressed loader is one scheduled step of the rule-scoped MM2 GSLT. -/
theorem compressedRuleLoader_scheduled_step :
    (ruleScopedNativeListExecGSLT .leaveInert).Step loadInput loadOutput := by
  rw [ruleScopedNativeListExecGSLT_step_iff]
  decide +kernel

/-- The bounded evaluator records exactly the ordered rule-load transition. -/
theorem compressedRuleLoader_bounded_run :
    cRuleScopedSourceWorkQueueRunN .leaveInert 1 loadInput =
      (loadOutput, 1) := by
  decide +kernel

/-- The same generic trace boundary used by normal verification exposes this
compressed loader as exactly one transition. -/
theorem compressedRuleLoader_rewritePath_length :
    (cRuleScopedSourceWorkQueueRunN_rewritePath .leaveInert 1
      loadInput).length = 1 := by
  rw [cRuleScopedSourceWorkQueueRunN_rewritePath_length,
    compressedRuleLoader_bounded_run]

/-- Captured-rule loading lies in the conservative overlap: the corrected
rule-scoped semantics and the earlier reflective semantics agree exactly. -/
theorem compressedRuleLoader_agrees_with_reflective :
    cFireRuleScopedSourceExecFact loadInput
        sourceCompressedRuleLoadDirective =
      cFireReflectiveSourceExecFact loadInput
        sourceCompressedRuleLoadDirective := by
  rw [compressedRuleLoader_fires_exactly]
  decide +kernel

/-- The output keeps one representative for each physical compact key. -/
theorem compressedRuleLoader_result_keys_are_distinct :
    (loadOutput.map morkSupportKey).Nodup := by
  decide +kernel

#print axioms compressedRuleLoader_fires_exactly
#print axioms compressedRuleLoader_scheduled_step
#print axioms compressedRuleLoader_bounded_run
#print axioms compressedRuleLoader_rewritePath_length
#print axioms compressedRuleLoader_agrees_with_reflective
#print axioms compressedRuleLoader_result_keys_are_distinct

end Mettapedia.Languages.Metamath.MM2CompressedProofRuleScopedLoad
