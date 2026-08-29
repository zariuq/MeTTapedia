import Mettapedia.Languages.Metamath.MM2CompressedProofExecution

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeCanary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

def scopeOwner : Atom := .symbol "compressed-assertion-scope"
def proofOwner : Atom := .symbol "compressed-assertion-proof"
def assertionLabel : Atom := stringAtom "ax"
def resultFormula : Atom := .symbol "compressed-assertion-result"
def remainingBytes : Atom := listAtom natAtom []

def code (value : Nat) : Atom := (CompressedIndexCode.ofNat value).atom

def assertionPC : Atom :=
  .expression
    [.symbol "mm-compressed-assertion-pc", natAtom 0, remainingBytes, code 0]

def assertionNextPC : Atom :=
  .expression [.symbol "mm-compressed-assertion-done", assertionPC]

def assertionOccurrence : Atom :=
  .expression [.symbol "mm-assertion-occurrence", assertionPC, assertionLabel]

def pending : Atom :=
  .expression
    [.symbol "mm-compressed-step-pending", scopeOwner, proofOwner,
      natAtom 0, remainingBytes, code 0]

def exactHeapLookup : Atom :=
  .expression
    [.symbol "mm-compressed-heap-lookup", scopeOwner, proofOwner,
      natAtom 0, remainingBytes, code 0, code 0]

def assertionHeap : Atom :=
  .expression
    [.symbol "mm-compressed-heap-assertion", proofOwner, code 0, natAtom 7,
      assertionLabel]

def assertionHeader : Atom :=
  .expression
    [.symbol "mm-assertion-header", scopeOwner, natAtom 7, assertionLabel,
      natAtom 0]

def initialMachine : Atom :=
  .expression
    [.symbol "mm-compressed-machine", scopeOwner, proofOwner,
      code 1, code 0, code 0]

def normalControl : Atom :=
  .expression
    [.symbol "mm-normal-control", scopeOwner, proofOwner, assertionPC, code 0]

def normalLabelRow : Atom :=
  .expression
    [.symbol "mm-linked-row", stringAtom "normal-proof-label", proofOwner,
      assertionPC, assertionNextPC, assertionLabel]

def assertionContext : Atom :=
  .expression
    [.symbol "mm-compressed-assertion-context", scopeOwner, proofOwner,
      natAtom 0, remainingBytes, assertionPC, assertionNextPC,
      assertionLabel, code 1, code 0]

def launchProgram : List Atom :=
  [compressedAssertionLaunchRule, pending, exactHeapLookup, assertionHeap,
    initialMachine, assertionHeader,
    compressedOwnedRuntimeRuleRow "assertion-rejoin"
      compressedAssertionRejoinRule]

def launchFinal : List Atom :=
  cFireReflectiveSourceExecFact launchProgram
    compressedAssertionLaunchDirective

def returnedControl : Atom :=
  .expression
    [.symbol "mm-normal-control", scopeOwner, proofOwner, assertionNextPC,
      code 1]

def returnedStack : Atom :=
  .expression
    [.symbol "mm-stack-cell", proofOwner, code 0, resultFormula,
      assertionOccurrence]

def normalStackSuccessor : Atom :=
  .expression
    [.symbol "mm-index-successor", proofOwner, code 0, code 1]

def nodeSuccessor : Atom :=
  compressedIndexSuccessorRow (compressedNodeOwner proofOwner) (code 0)
    (code 1)

def rejoinProgram : List Atom :=
  [compressedAssertionRejoinRule, assertionContext, returnedControl,
    returnedStack, normalStackSuccessor, nodeSuccessor, normalLabelRow,
    compressedOwnedRuntimeRuleRow "assertion-resume"
      compressedAssertionResumeRule]

def rejoinFinal : List Atom :=
  cFireReflectiveSourceExecFact rejoinProgram
    compressedAssertionRejoinDirective

def resultNode : Atom :=
  .expression
    [.symbol "mm-compressed-node", proofOwner, code 0, resultFormula,
      assertionOccurrence]

def resultStack : Atom :=
  .expression
    [.symbol "mm-compressed-stack-cell", proofOwner, code 0, code 0]

def resumedMachine : Atom :=
  .expression
    [.symbol "mm-compressed-machine", scopeOwner, proofOwner,
      code 1, code 1, code 1]

def resumeRequest : Atom :=
  .expression
    [.symbol "mm-compressed-assertion-resume", scopeOwner, proofOwner,
      natAtom 0, remainingBytes]

def resumedScan : Atom :=
  .expression
    [.symbol "mm-compressed-scan", scopeOwner, proofOwner, natAtom 0,
      remainingBytes, .symbol "mm-compressed-just-completed-step",
      listAtom natAtom []]

def resumeProgram : List Atom :=
  [compressedAssertionResumeRule, resumeRequest] ++
    compressedScannerRuleCaptureRows

def resumeFinal : List Atom :=
  cFireReflectiveSourceExecFact resumeProgram compressedAssertionResumeDirective

def acceptRuleCapture : Atom :=
  compressedOwnedRuntimeRuleRow "accept" compressedAcceptRule

def wrongOccurrenceStack : Atom :=
  .expression
    [.symbol "mm-stack-cell", proofOwner, code 0, resultFormula,
      .expression
        [.symbol "mm-assertion-occurrence", assertionPC,
          stringAtom "other"]]

def wrongOccurrenceRejoinProgram : List Atom :=
  [compressedAssertionRejoinRule, assertionContext, returnedControl,
    wrongOccurrenceStack, normalStackSuccessor, nodeSuccessor, normalLabelRow,
    compressedOwnedRuntimeRuleRow "assertion-resume"
      compressedAssertionResumeRule]

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeCanary
