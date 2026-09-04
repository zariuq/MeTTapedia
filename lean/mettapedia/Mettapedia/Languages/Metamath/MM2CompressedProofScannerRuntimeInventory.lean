import Mettapedia.Languages.Metamath.MM2CompressedProofSaveContinuous
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookup

/-!
# Compressed scanner runtime inventory

The incremental scanner is reinstalled from an authenticated inventory rather
than from fixed global rule constants.  The inventory extends the shared save
runtime bundle with the scanner continuations not used by `Z`.  Consequently a
verifier transformation may replace one continuation, such as the terminal
lookup rule, without changing the assertion-resume protocol.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofScannerRuntimeInventory

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSaveContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookup

/-- Complete executable payload inventory restored when an assertion returns
to the incremental compressed-proof scanner. -/
structure ScannerRuntimeRuleBundle where
  saveCore : SaveRuntimeRuleBundle
  assertionLaunchRule : Atom
  saveRule : Atom
  wordAdvanceRule : Atom
  acceptRule : Atom
  incompleteRule : Atom
  saveFaultRule : Atom
deriving DecidableEq

namespace ScannerRuntimeRuleBundle

/-- Inert role-indexed carriers consumed by the assertion-resume matcher. -/
def captureRows (rules : ScannerRuntimeRuleBundle) : List Atom :=
  [compressedOwnedRuntimeRuleRow "prefix" rules.saveCore.prefixRule,
   compressedOwnedRuntimeRuleRow "terminal" rules.saveCore.terminalRule,
   compressedOwnedRuntimeRuleRow "proof" rules.saveCore.proofRule,
   compressedOwnedRuntimeRuleRow "assertion-launch"
     rules.assertionLaunchRule,
   compressedOwnedRuntimeRuleRow "save" rules.saveRule,
   compressedOwnedRuntimeRuleRow "word-advance" rules.wordAdvanceRule,
   compressedOwnedRuntimeRuleRow "accept" rules.acceptRule,
   compressedOwnedRuntimeRuleRow "incomplete" rules.incompleteRule,
   compressedOwnedRuntimeRuleRow "invalid-byte"
     rules.saveCore.invalidByteRule,
   compressedOwnedRuntimeRuleRow "question" rules.saveCore.questionRule,
   compressedOwnedRuntimeRuleRow "question-open-fault"
     rules.saveCore.questionOpenFaultRule,
   compressedOwnedRuntimeRuleRow "save-fault" rules.saveFaultRule]

/-- Executable rules restored by the assertion-resume sink batch, in authored
sink order. -/
def payloadRows (rules : ScannerRuntimeRuleBundle) : List Atom :=
  [rules.saveCore.prefixRule, rules.saveCore.terminalRule,
   rules.saveCore.proofRule, rules.assertionLaunchRule, rules.saveRule,
   rules.wordAdvanceRule, rules.acceptRule, rules.incompleteRule,
   rules.saveCore.invalidByteRule, rules.saveCore.questionRule,
   rules.saveCore.questionOpenFaultRule, rules.saveFaultRule]

end ScannerRuntimeRuleBundle

/-- Inventory of the untransformed compressed verifier. -/
def baseScannerRuntimeRuleBundle : ScannerRuntimeRuleBundle where
  saveCore := baseSaveRuntimeRuleBundle
  assertionLaunchRule := compressedAssertionLaunchRule
  saveRule := compressedSaveRule
  wordAdvanceRule := compressedWordAdvanceRule
  acceptRule := compressedAcceptRule
  incompleteRule := compressedIncompleteRule
  saveFaultRule := compressedSaveFaultRule

/-- Inventory selected by the maintained speculative verifier
transformation.  Its terminal rule is the compiler product; all other scanner
continuations remain source-identical. -/
def speculativeScannerRuntimeRuleBundle : ScannerRuntimeRuleBundle where
  saveCore :=
    { baseSaveRuntimeRuleBundle with
      terminalRule := compressedSpeculativeTerminalRule }
  assertionLaunchRule := compressedAssertionLaunchRule
  saveRule := compressedSaveRule
  wordAdvanceRule := compressedWordAdvanceRule
  acceptRule := compressedAcceptRule
  incompleteRule := compressedIncompleteRule
  saveFaultRule := compressedSaveFaultRule

@[simp] theorem base_captureRows_exact :
    baseScannerRuntimeRuleBundle.captureRows =
      [compressedOwnedRuntimeRuleRow "prefix" compressedPrefixRule,
       compressedOwnedRuntimeRuleRow "terminal" compressedTerminalRule,
       compressedOwnedRuntimeRuleRow "proof" compressedProofStepRule,
       compressedOwnedRuntimeRuleRow "assertion-launch"
         compressedAssertionLaunchRule,
       compressedOwnedRuntimeRuleRow "save" compressedSaveRule,
       compressedOwnedRuntimeRuleRow "word-advance"
         compressedWordAdvanceRule,
       compressedOwnedRuntimeRuleRow "accept" compressedAcceptRule,
       compressedOwnedRuntimeRuleRow "incomplete" compressedIncompleteRule,
       compressedOwnedRuntimeRuleRow "invalid-byte"
         compressedInvalidByteRule,
       compressedOwnedRuntimeRuleRow "question" compressedQuestionRule,
       compressedOwnedRuntimeRuleRow "question-open-fault"
         compressedQuestionOpenFaultRule,
       compressedOwnedRuntimeRuleRow "save-fault"
         compressedSaveFaultRule] := by
  rfl

@[simp] theorem base_payloadRows_eq_existing :
    baseScannerRuntimeRuleBundle.payloadRows =
      [compressedPrefixRule, compressedTerminalRule,
       compressedProofStepRule, compressedAssertionLaunchRule,
       compressedSaveRule, compressedWordAdvanceRule, compressedAcceptRule,
       compressedIncompleteRule, compressedInvalidByteRule,
       compressedQuestionRule, compressedQuestionOpenFaultRule,
       compressedSaveFaultRule] := by
  rfl

/-- Negative control: the maintained transformation changes the terminal
continuation instead of silently falling back to the base scanner. -/
theorem speculative_terminal_differs_from_base :
    speculativeScannerRuntimeRuleBundle.saveCore.terminalRule ≠
      baseScannerRuntimeRuleBundle.saveCore.terminalRule := by
  decide +kernel

/-- Negative control: replacing the terminal continuation does not leave the
retired base terminal elsewhere in the scanner payload inventory. -/
theorem base_terminal_not_mem_speculative_payload :
    compressedTerminalRule ∉
      speculativeScannerRuntimeRuleBundle.payloadRows := by
  decide +kernel

#print axioms base_captureRows_exact
#print axioms base_payloadRows_eq_existing
#print axioms speculative_terminal_differs_from_base
#print axioms base_terminal_not_mem_speculative_payload

end Mettapedia.Languages.Metamath.MM2CompressedProofScannerRuntimeInventory
