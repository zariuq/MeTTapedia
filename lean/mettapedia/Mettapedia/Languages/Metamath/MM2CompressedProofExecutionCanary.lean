import Mettapedia.Languages.Metamath.MM2CompressedProofExecution

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-! # Bounded continuous controls for incremental compressed MM2 execution -/

def canaryScope : Atom := .symbol "compressed-canary-scope"
def canaryProof : Atom := .symbol "compressed-canary-proof"
def canaryFormula : Atom := .symbol "compressed-canary-formula"
def canaryLabel : Atom := .symbol "compressed-canary-theorem"
def canaryNode : Atom := .symbol "compressed-canary-node-0"
def canaryOccurrence : Atom := .symbol "compressed-canary-occurrence-0"

def canaryDescriptor : Atom :=
  .expression
    [.symbol "mm-proof", canaryScope, canaryProof, .symbol "compressed",
      canaryLabel, canaryFormula]

def canaryMachine : Atom :=
  .expression
    [.symbol "mm-compressed-machine", canaryScope, canaryProof,
      compressedIndexCodeAtom [] 1, compressedIndexCodeAtom [] 1,
      compressedIndexCodeAtom [] 0]

def canaryHeapZero : Atom :=
  .expression
    [.symbol "mm-compressed-heap-proof", canaryProof,
      compressedIndexCodeAtom [] 0, canaryNode]

def canaryNodeZero : Atom :=
  .expression
    [.symbol "mm-compressed-node", canaryProof, canaryNode,
      canaryFormula, canaryOccurrence]

def canaryStackSuccessor : Atom :=
  compressedIndexSuccessorRow (compressedStackOwner canaryProof)
    (compressedIndexCodeAtom [] 0) (compressedIndexCodeAtom [] 1)

def canaryHeapSuccessor : Atom :=
  compressedIndexSuccessorRow (compressedHeapOwner canaryProof)
    (compressedIndexCodeAtom [] 1) (compressedIndexCodeAtom [] 2)

def canaryAccepted : Atom :=
  .expression
    [.symbol "mm-accepted", canaryScope, canaryProof, canaryLabel,
      canaryFormula, canaryOccurrence]

def canarySavedHeapOne : Atom :=
  .expression
    [.symbol "mm-compressed-heap-proof", canaryProof,
      compressedIndexCodeAtom [] 1, canaryNode]

def canaryUnexpectedNodeOne : Atom :=
  .expression
    [.symbol "mm-compressed-node", canaryProof,
      .symbol "compressed-canary-node-1", canaryFormula,
      canaryOccurrence]

/-- Only the opaque continuations exercised by the `A`/`Z` path. Keeping
this fixture exact avoids normalizing unrelated assertion and terminal code. -/
def compressedAZCaptureRows : List Atom :=
  [compressedOwnedRuntimeRuleRow "prefix" compressedPrefixRule,
   compressedOwnedRuntimeRuleRow "terminal" compressedTerminalRule,
   compressedOwnedRuntimeRuleRow "proof" compressedProofStepRule,
   compressedOwnedRuntimeRuleRow "assertion-launch" compressedAssertionLaunchRule,
   compressedOwnedRuntimeRuleRow "lookup-fault" compressedHeapLookupFaultRule,
   compressedOwnedRuntimeRuleRow "lookup-advance" compressedHeapLookupAdvanceRule,
   compressedOwnedRuntimeRuleRow "invalid-byte" compressedInvalidByteRule,
   compressedOwnedRuntimeRuleRow "question" compressedQuestionRule,
   compressedOwnedRuntimeRuleRow "question-open-fault"
     compressedQuestionOpenFaultRule]

def compressedAZProgram : List Atom :=
  [compressedStartRule, compressedTerminalRule, compressedProofStepRule,
    compressedSaveRule, compressedAcceptRule,
    compressedTerminalByteRow 65 0,
    .expression
      [.symbol "mm-compressed-final-phase",
        .symbol "mm-compressed-between-steps"]] ++
    [canaryDescriptor,
     .expression
       [.symbol "mm-compressed-control", canaryScope, canaryProof,
         natAtom 0, compressedIndexCodeAtom [] 0],
     indexedRow "compressed-body-word" canaryProof 0
       (compressedWordAtom [65, 90]),
     .expression
       [.symbol "mm-index-successor", canaryProof, natAtom 0, natAtom 1],
     .expression [.symbol "mm-proof-end", canaryProof, natAtom 1],
     canaryMachine, canaryHeapZero, canaryNodeZero,
     canaryStackSuccessor, canaryHeapSuccessor] ++
    compressedAZCaptureRows

def compressedSingleIndexProgram : List Atom :=
  [compressedStartRule, compressedTerminalRule, compressedProofStepRule,
    compressedAcceptRule, compressedTerminalByteRow 65 0,
    .expression
      [.symbol "mm-compressed-final-phase",
        .symbol "mm-compressed-just-completed-step"],
    canaryDescriptor,
    .expression
      [.symbol "mm-compressed-control", canaryScope, canaryProof,
        natAtom 0, compressedIndexCodeAtom [] 0],
    indexedRow "compressed-body-word" canaryProof 0
      (compressedWordAtom [65]),
    .expression
      [.symbol "mm-index-successor", canaryProof, natAtom 0, natAtom 1],
    .expression [.symbol "mm-proof-end", canaryProof, natAtom 1],
    canaryMachine, canaryHeapZero, canaryNodeZero,
    canaryStackSuccessor] ++ compressedAZCaptureRows

def canaryCodeTwentyPending : Atom :=
  .expression
    [.symbol "mm-compressed-step-pending", canaryScope, canaryProof,
      natAtom 1, listAtom natAtom [], compressedIndexCodeAtom [1] 0]

def compressedCrossWordTwentyProgram : List Atom :=
  [compressedWordAdvanceRule, compressedTerminalByteRow 65 0,
    .expression
      [.symbol "mm-compressed-scan", canaryScope, canaryProof, natAtom 0,
        listAtom natAtom [], .symbol "mm-compressed-open-index",
        listAtom natAtom [1]],
     indexedRow "compressed-body-word" canaryProof 1
       (compressedWordAtom [65]),
     .expression
       [.symbol "mm-index-successor", canaryProof, natAtom 0, natAtom 1],
     .expression [.symbol "mm-proof-end", canaryProof, natAtom 2]] ++
    (compressedAZCaptureRows ++
      [compressedOwnedRuntimeRuleRow "save" compressedSaveRule,
       compressedOwnedRuntimeRuleRow "save-fault" compressedSaveFaultRule])

def compressedCrossWordAfterAdvance : List Atom :=
  cFireReflectiveSourceExecFact compressedCrossWordTwentyProgram
    compressedWordAdvanceDirective

def compressedCrossWordAfterPrefixProbe : List Atom :=
  cFireReflectiveSourceExecFact compressedCrossWordAfterAdvance
    compressedPrefixDirective

def compressedCrossWordAfterTerminal : List Atom :=
  cFireReflectiveSourceExecFact compressedCrossWordAfterPrefixProbe
    compressedTerminalDirective

def compressedIncompletePrefixProgram : List Atom :=
  [compressedStartRule, compressedPrefixRule, compressedIncompleteRule,
    compressedPrefixByteRow 85 1] ++
    [.expression
       [.symbol "mm-compressed-control", canaryScope, canaryProof,
         natAtom 0, compressedIndexCodeAtom [] 0],
     indexedRow "compressed-body-word" canaryProof 0
       (compressedWordAtom [85]),
     .expression
       [.symbol "mm-index-successor", canaryProof, natAtom 0, natAtom 1],
     .expression [.symbol "mm-proof-end", canaryProof, natAtom 1],
     canaryMachine]

def canaryIncompletePrefixFault : Atom :=
  .expression
    [.symbol "mm-proof-fault", canaryScope, canaryProof, natAtom 0,
      .symbol "compressed-incomplete-index", .symbol "compressed-proof",
      listAtom natAtom [1], .symbol "end-of-proof"]

end Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary
