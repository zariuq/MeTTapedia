import Mettapedia.Languages.Metamath.CompressedByteClassifierCore
import Mettapedia.Languages.Metamath.MM2CompressedProofExecution

/-!
# Compact compressed-proof finalizer to MM2 static inventory

The compact-byte semantic core gives end-of-input its own classifier GSLT:
the finalizer either accepts a completed phase or reports an unfinished
numeric prefix.  This adapter makes its target observation load-bearing for
the existing MM2 verifier by selecting the exact verifier-owned static row
needed for each possible finalizer result.

It deliberately does not manufacture a proof-end datum, run the scheduler,
or derive a verdict.  The proof-end datum remains dynamic source data and the
MM2 verifier consumes it together with the selected static inventory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2FinalizerAdapter

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution

/-- The two completed scanner phases that are licensed to finish a compact
proof have distinct public MM2 final-phase rows. -/
def finalPhaseRow : Phase -> Option Atom
  | .between =>
      some (.expression
        [.symbol "mm-compressed-final-phase",
          .symbol "mm-compressed-between-steps"])
  | .completed =>
      some (.expression
        [.symbol "mm-compressed-final-phase",
          .symbol "mm-compressed-just-completed-step"])
  | .open _ => none

/-- The incomplete-prefix branch selects the verifier's installed incomplete
rule.  It is verifier-owned static inventory, never a source-provided rule. -/
def incompletePrefixRuleRow : Atom :=
  compressedOwnedRuntimeRuleRow "incomplete" compressedIncompleteRule

/-- Reify only semantically possible finalizer observations as existing MM2
static inventory.  Impossible phase/row pairings remain absent rather than
being coerced into a target row. -/
def finalizerStaticRow : Phase -> EndRow -> Option Atom
  | .between, .completeInput => finalPhaseRow .between
  | .completed, .completeInput => finalPhaseRow .completed
  | .open _, .incompleteOpenIndex _ => some incompletePrefixRuleRow
  | _, _ => none

/-- The static MM2 observation determined by the authored finalizer stage. -/
def classifiedFinalizerStaticRow (phase : Phase) : Option Atom :=
  finalizerStaticRow phase (EndClass.row (classifyEnd phase))

@[simp] theorem classified_between_row_exact :
    classifiedFinalizerStaticRow .between = finalPhaseRow .between := by
  rfl

@[simp] theorem classified_completed_row_exact :
    classifiedFinalizerStaticRow .completed = finalPhaseRow .completed := by
  rfl

@[simp] theorem classified_open_row_exact (reversePrefix : List Nat) :
    classifiedFinalizerStaticRow (.open reversePrefix) =
      some incompletePrefixRuleRow := by
  rfl

/-- An unfinished prefix cannot be misclassified as a completed-input row. -/
@[simp] theorem open_complete_row_is_absent (reversePrefix : List Nat) :
    finalizerStaticRow (.open reversePrefix) .completeInput = none := by
  rfl

/-- A completed scanner phase cannot select the incomplete-prefix rule. -/
@[simp] theorem completed_incomplete_row_is_absent
    (reversePrefix : List Nat) :
    finalizerStaticRow .completed (.incompleteOpenIndex reversePrefix) = none := by
  rfl

/-- Each completed finalizer observation names a static row from the actual
MM2 verifier inventory. -/
theorem between_final_phase_row_is_static :
    (finalPhaseRow .between).getD (.symbol "mm-missing-final-phase") ∈
      compressedVerifierStaticRows := by
  change
    (.expression
      [.symbol "mm-compressed-final-phase",
        .symbol "mm-compressed-between-steps"] : Atom) ∈
      compressedTerminalByteRows ++ compressedPrefixByteRows ++
        compressedInvalidByteRows ++ compressedQuestionAllowedPhaseRows ++
          compressedSaveDisallowedPhaseRows ++
            [.expression
                [.symbol "mm-compressed-final-phase",
                  .symbol "mm-compressed-between-steps"],
             .expression
                [.symbol "mm-compressed-final-phase",
                  .symbol "mm-compressed-just-completed-step"]] ++
              compressedHeapLookupReloadRows ++ compressedScannerRuleCaptureRows ++
                compressedAssertionContinuationCaptureRows
  simp only [List.mem_append, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

theorem completed_final_phase_row_is_static :
    (finalPhaseRow .completed).getD (.symbol "mm-missing-final-phase") ∈
      compressedVerifierStaticRows := by
  change
    (.expression
      [.symbol "mm-compressed-final-phase",
        .symbol "mm-compressed-just-completed-step"] : Atom) ∈
      compressedTerminalByteRows ++ compressedPrefixByteRows ++
        compressedInvalidByteRows ++ compressedQuestionAllowedPhaseRows ++
          compressedSaveDisallowedPhaseRows ++
            [.expression
                [.symbol "mm-compressed-final-phase",
                  .symbol "mm-compressed-between-steps"],
             .expression
                [.symbol "mm-compressed-final-phase",
                  .symbol "mm-compressed-just-completed-step"]] ++
              compressedHeapLookupReloadRows ++ compressedScannerRuleCaptureRows ++
                compressedAssertionContinuationCaptureRows
  simp only [List.mem_append, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))

/-- The open-prefix finalizer selects the verifier's installed incomplete
rule, which is retained as static inventory rather than emitted by the source
transform. -/
theorem incomplete_prefix_rule_row_is_static :
    incompletePrefixRuleRow ∈ compressedVerifierStaticRows := by
  change incompletePrefixRuleRow ∈
    compressedTerminalByteRows ++ compressedPrefixByteRows ++
      compressedInvalidByteRows ++ compressedQuestionAllowedPhaseRows ++
        compressedSaveDisallowedPhaseRows ++
          [.expression
              [.symbol "mm-compressed-final-phase",
                .symbol "mm-compressed-between-steps"],
           .expression
              [.symbol "mm-compressed-final-phase",
                .symbol "mm-compressed-just-completed-step"]] ++
            compressedHeapLookupReloadRows ++
              [compressedOwnedRuntimeRuleRow "prefix" compressedPrefixRule,
               compressedOwnedRuntimeRuleRow "terminal" compressedTerminalRule,
               compressedOwnedRuntimeRuleRow "proof" compressedProofStepRule,
               compressedOwnedRuntimeRuleRow "assertion-launch"
                 compressedAssertionLaunchRule,
               compressedOwnedRuntimeRuleRow "lookup-fault"
                 compressedHeapLookupFaultRule,
               compressedOwnedRuntimeRuleRow "lookup-advance"
                 compressedHeapLookupAdvanceRule,
               compressedOwnedRuntimeRuleRow "save" compressedSaveRule,
               compressedOwnedRuntimeRuleRow "word-advance"
                 compressedWordAdvanceRule,
               compressedOwnedRuntimeRuleRow "accept" compressedAcceptRule,
               incompletePrefixRuleRow,
               compressedOwnedRuntimeRuleRow "invalid-byte"
                 compressedInvalidByteRule,
               compressedOwnedRuntimeRuleRow "question" compressedQuestionRule,
               compressedOwnedRuntimeRuleRow "question-open-fault"
                 compressedQuestionOpenFaultRule,
               compressedOwnedRuntimeRuleRow "save-fault" compressedSaveFaultRule] ++
                compressedAssertionContinuationCaptureRows
  simp only [List.mem_append, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl rfl))))))))))))))))))

/-- The semantic finalizer determines a static MM2 inventory observation for
every actual phase.  This is a selection theorem only: firing still requires
the dynamic proof-end and scanner-state data. -/
theorem classified_finalizer_row_is_static (phase : Phase) :
    ∃ row, classifiedFinalizerStaticRow phase = some row ∧
      row ∈ compressedVerifierStaticRows := by
  cases phase with
  | between =>
      refine ⟨(finalPhaseRow .between).getD (.symbol "mm-missing-final-phase"), ?_,
        between_final_phase_row_is_static⟩
      rfl
  | completed =>
      refine ⟨(finalPhaseRow .completed).getD (.symbol "mm-missing-final-phase"), ?_,
        completed_final_phase_row_is_static⟩
      rfl
  | open reversePrefix =>
      exact ⟨incompletePrefixRuleRow, classified_open_row_exact reversePrefix,
        incomplete_prefix_rule_row_is_static⟩

/-- The existing path-valued GSLT realization remains the semantic arrow;
this adapter only makes its intermediate row observable in the MM2 inventory.
-/
theorem finalizer_realization_has_two_target_steps (phase : Phase) :
    (finalizerRealization.mapStep
      (Mettapedia.GSLT.ClassifierLowering.SourceStep.run
        (stage := finalizerStage) phase)).length = 2 :=
  finalizerRealization_step_length phase

#print axioms classified_between_row_exact
#print axioms classified_completed_row_exact
#print axioms classified_open_row_exact
#print axioms open_complete_row_is_absent
#print axioms completed_incomplete_row_is_absent
#print axioms between_final_phase_row_is_static
#print axioms completed_final_phase_row_is_static
#print axioms incomplete_prefix_rule_row_is_static
#print axioms classified_finalizer_row_is_static
#print axioms finalizer_realization_has_two_target_steps

end Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2FinalizerAdapter
