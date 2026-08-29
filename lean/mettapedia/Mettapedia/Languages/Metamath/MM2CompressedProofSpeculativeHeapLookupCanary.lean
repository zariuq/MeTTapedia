import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookup

/-!
# Bounded execution controls for generated speculative heap lookup

These controls execute the rules produced by the strict finite-presentation
transformation.  A matching proof cell resolves directly.  A cell belonging
to another proof owner cannot resolve the request; after both direct probes
are consumed, the retained cursor machine reaches its ordinary live-frontier
fault.

The controls exercise one tiny compact index.  They do not replace the
symbolic scheduler-exhaustion and preservation/reflection theorems.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookup
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- Finite runtime slice needed by the direct-lookup controls.  Every row is
drawn from the complete transformed persistent inventory; unrelated scanner
handlers stay outside this bounded execution fixture. -/
def speculativeLookupRuntimeRows : List Atom :=
  [compressedOwnedRuntimeRuleRow "terminal" compressedSpeculativeTerminalRule,
   compressedOwnedRuntimeRuleRow "proof" compressedProofStepRule,
   compressedOwnedRuntimeRuleRow "assertion-launch"
     compressedAssertionLaunchRule,
   compressedOwnedRuntimeRuleRow "lookup-fault"
     compressedHeapLookupFaultRule,
   compressedOwnedRuntimeRuleRow "lookup-advance"
     compressedHeapLookupAdvanceRule,
   compressedDirectProofHandlerRow, compressedDirectAssertionHandlerRow] ++
    compressedHeapLookupReloadRows ++
    [compressedOwnedRuntimeRuleRow "prefix" compressedPrefixRule,
     compressedOwnedRuntimeRuleRow "invalid-byte" compressedInvalidByteRule,
     compressedOwnedRuntimeRuleRow "question" compressedQuestionRule,
     compressedOwnedRuntimeRuleRow "question-open-fault"
       compressedQuestionOpenFaultRule]

theorem speculativeLookupRuntimeRows_from_transformed_inventory :
    ∀ row ∈ speculativeLookupRuntimeRows,
      row ∈ compressedVerifierStaticRowsWithSpeculativeLookup := by
  decide +kernel

def speculativeTerminalDirective : SourceExecFact :=
  (extractSupportedSourceExecFact compressedSpeculativeTerminalRule).get
    (by decide +kernel)

def speculativeDirectProofDirective : SourceExecFact :=
  (extractSupportedSourceExecFact compressedDirectProofRule).get
    (by decide +kernel)

def speculativeDirectAssertionDirective : SourceExecFact :=
  (extractSupportedSourceExecFact compressedDirectAssertionRule).get
    (by decide +kernel)

theorem extract_speculativeDirectProofDirective_exact :
    extractSupportedSourceExecFact compressedDirectProofRule =
      some speculativeDirectProofDirective := by
  decide +kernel

theorem extract_speculativeDirectAssertionDirective_exact :
    extractSupportedSourceExecFact compressedDirectAssertionRule =
      some speculativeDirectAssertionDirective := by
  decide +kernel

/-! ## Direct proof-cell hit -/

def speculativeHitProgram : List Atom :=
  [compressedSpeculativeTerminalRule,
   compressedTerminalByteRow 66 1, byteBScan, machineWithTwoHeapEntries,
   heapSuccessorZero, heapOne, nodeOneRow, stackSuccessorZero] ++
    speculativeLookupRuntimeRows

def speculativeHitAfterTerminal : List Atom :=
  cFireReflectiveSourceExecFact speculativeHitProgram
    speculativeTerminalDirective

/-- The second state is computed from the transformed terminal's actual
successor, rather than reconstructed from a rule-local interface. -/
def speculativeHitAfterDirect : List Atom :=
  cFireReflectiveSourceExecFact speculativeHitAfterTerminal
    speculativeDirectProofDirective

def directStepPending : Atom :=
  .expression
    [.symbol "mm-compressed-step-pending", scopeOwner, proofOwner,
      MM2DataEncoding.natAtom 0,
      MM2DataEncoding.listAtom MM2DataEncoding.natAtom [], code 1]

def directLookupOne : Atom :=
  .expression
    [.symbol "mm-compressed-heap-lookup", scopeOwner, proofOwner,
      MM2DataEncoding.natAtom 0,
      MM2DataEncoding.listAtom MM2DataEncoding.natAtom [], code 1, code 0]

def directProofContinuationRows : List Atom :=
  [compressedOwnedRuntimeRuleRow "prefix" compressedPrefixRule,
   compressedOwnedRuntimeRuleRow "terminal" compressedSpeculativeTerminalRule,
   compressedOwnedRuntimeRuleRow "invalid-byte" compressedInvalidByteRule,
   compressedOwnedRuntimeRuleRow "question" compressedQuestionRule,
   compressedOwnedRuntimeRuleRow "question-open-fault"
     compressedQuestionOpenFaultRule]

/-- Exact local input interface retained as a diagnostic control for the
generated direct proof handler. -/
def directHitProgram : List Atom :=
  [compressedDirectProofRule, directStepPending, directLookupOne, heapOne,
   nodeOneRow, machineWithTwoHeapEntries, stackSuccessorZero] ++
    directProofContinuationRows

def directHitAfter : List Atom :=
  cFireReflectiveSourceExecFact directHitProgram
    speculativeDirectProofDirective

/-! ## Negative direct probes -/

def foreignProofOwner : Atom := .symbol "compressed-foreign-proof"

def foreignHeapOne : Atom :=
  .expression
    [.symbol "mm-compressed-heap-proof", foreignProofOwner, code 1, nodeOne]

def directWrongOwnerProofProgram : List Atom :=
  [compressedDirectProofRule, directStepPending, directLookupOne,
   foreignHeapOne, nodeOneRow, machineWithOneHeapEntry, stackSuccessorZero] ++
    directProofContinuationRows

def directWrongOwnerProofAfter : List Atom :=
  cFireReflectiveSourceExecFact directWrongOwnerProofProgram
    speculativeDirectProofDirective

/-! ## Continuous wrong-owner miss and cursor fallback -/

/-- A foreign-owner heap cell cannot satisfy either generated direct handler.
The ordinary cursor verifier remains present and must diagnose index one at
the local heap frontier after the two inert speculative probes are consumed. -/
def speculativeMissProgram : List Atom :=
  [compressedSpeculativeTerminalRule,
   compressedTerminalByteRow 66 1, byteBScan, machineWithOneHeapEntry,
   heapSuccessorZero, foreignHeapOne, nodeOneRow, stackSuccessorZero] ++
    speculativeLookupRuntimeRows

def speculativeMissAfterTerminal : List Atom :=
  cFireReflectiveSourceExecFact speculativeMissProgram
    speculativeTerminalDirective

def speculativeMissAfterDirectProof : List Atom :=
  cFireReflectiveSourceExecFact speculativeMissAfterTerminal
    speculativeDirectProofDirective

def speculativeMissAfterDirectAssertion : List Atom :=
  cFireReflectiveSourceExecFact speculativeMissAfterDirectProof
    speculativeDirectAssertionDirective

def speculativeMissAfterCursorProofProbe : List Atom :=
  cFireReflectiveSourceExecFact speculativeMissAfterDirectAssertion
    compressedProofStepDirective

def speculativeMissAfterCursorFaultProbe : List Atom :=
  cFireReflectiveSourceExecFact speculativeMissAfterCursorProofProbe
    compressedHeapLookupFaultDirective

def speculativeMissAfterCursorAssertionProbe : List Atom :=
  cFireReflectiveSourceExecFact speculativeMissAfterCursorFaultProbe
    compressedAssertionLaunchDirective

def speculativeMissAfterAdvance : List Atom :=
  cFireReflectiveSourceExecFact speculativeMissAfterCursorAssertionProbe
    compressedHeapLookupAdvanceDirective

def speculativeMissAfterFrontierProofProbe : List Atom :=
  cFireReflectiveSourceExecFact speculativeMissAfterAdvance
    compressedProofStepDirective

def speculativeMissAfterFrontierFault : List Atom :=
  cFireReflectiveSourceExecFact speculativeMissAfterFrontierProofProbe
    compressedHeapLookupFaultDirective

def directMissingAssertionProgram : List Atom :=
  [compressedDirectAssertionRule, directStepPending, directLookupOne,
   machineWithOneHeapEntry]

def directMissingAssertionAfter : List Atom :=
  cFireReflectiveSourceExecFact directMissingAssertionProgram
    speculativeDirectAssertionDirective

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
