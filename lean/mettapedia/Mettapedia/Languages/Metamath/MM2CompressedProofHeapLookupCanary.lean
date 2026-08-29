import Mettapedia.Languages.Metamath.MM2CompressedProofExecution

/-!
# Bounded controls for compact heap lookup

The programs in this module begin at one decoded terminal byte.  They exercise
the same scheduled lookup rules used by the incremental compressed verifier,
without constructing an expanded normal-label trace.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

def scopeOwner : Atom := .symbol "compressed-lookup-scope"
def proofOwner : Atom := .symbol "compressed-lookup-proof"
def nodeOne : Atom := .symbol "compressed-lookup-node-1"
def formula : Atom := .symbol "compressed-lookup-formula"
def occurrence : Atom := .symbol "compressed-lookup-occurrence"

def code (value : Nat) : Atom := (CompressedIndexCode.ofNat value).atom

def byteBScan : Atom :=
  .expression
    [.symbol "mm-compressed-scan", scopeOwner, proofOwner, natAtom 0,
      compressedWordAtom [66], .symbol "mm-compressed-between-steps",
      listAtom natAtom []]

def heapSuccessorZero : Atom :=
  compressedIndexSuccessorRow (compressedHeapOwner proofOwner) (code 0)
    (code 1)

def stackSuccessorZero : Atom :=
  compressedIndexSuccessorRow (compressedStackOwner proofOwner) (code 0)
    (code 1)

def heapOne : Atom :=
  .expression
    [.symbol "mm-compressed-heap-proof", proofOwner, code 1, nodeOne]

def nodeOneRow : Atom :=
  .expression
    [.symbol "mm-compressed-node", proofOwner, nodeOne, formula, occurrence]

def machineWithTwoHeapEntries : Atom :=
  .expression
    [.symbol "mm-compressed-machine", scopeOwner, proofOwner,
      code 2, code 2, code 0]

def machineWithOneHeapEntry : Atom :=
  .expression
    [.symbol "mm-compressed-machine", scopeOwner, proofOwner,
      code 1, code 1, code 0]

def resolvedStackCell : Atom :=
  .expression
    [.symbol "mm-compressed-stack-cell", proofOwner, code 0, nodeOne]

def missingOneFault : Atom :=
  .expression
    [.symbol "mm-proof-fault", scopeOwner, proofOwner, natAtom 0,
      .symbol "compressed-missing-heap-reference", .symbol "compressed-heap",
      code 1, code 1]

def lookupHitProgram : List Atom :=
  [compressedTerminalRule, compressedProofStepRule,
   compressedHeapLookupAdvanceRule,
   compressedTerminalByteRow 66 1, byteBScan, machineWithTwoHeapEntries,
   heapSuccessorZero, heapOne, nodeOneRow, stackSuccessorZero] ++
    compressedHeapLookupReloadRows ++ compressedScannerRuleCaptureRows

def lookupFaultProgram : List Atom :=
  [compressedTerminalRule, compressedHeapLookupAdvanceRule,
   compressedHeapLookupFaultRule,
   compressedTerminalByteRow 66 1, byteBScan, machineWithOneHeapEntry,
   heapSuccessorZero, stackSuccessorZero] ++ compressedHeapLookupReloadRows ++
    compressedScannerRuleCaptureRows

def lookupHitAfterTerminal : List Atom :=
  cFireReflectiveSourceExecFact lookupHitProgram compressedTerminalDirective

def lookupHitAfterProofProbe : List Atom :=
  cFireReflectiveSourceExecFact lookupHitAfterTerminal
    compressedProofStepDirective

def lookupHitAfterAdvance : List Atom :=
  cFireReflectiveSourceExecFact lookupHitAfterProofProbe
    compressedHeapLookupAdvanceDirective

def lookupHitAfterResolve : List Atom :=
  cFireReflectiveSourceExecFact lookupHitAfterAdvance
    compressedProofStepDirective

def lookupFaultAfterTerminal : List Atom :=
  cFireReflectiveSourceExecFact lookupFaultProgram compressedTerminalDirective

def lookupFaultAfterProbe : List Atom :=
  cFireReflectiveSourceExecFact lookupFaultAfterTerminal
    compressedHeapLookupFaultDirective

def lookupFaultAfterAdvance : List Atom :=
  cFireReflectiveSourceExecFact lookupFaultAfterProbe
    compressedHeapLookupAdvanceDirective

def lookupFaultAfterProofProbe : List Atom :=
  cFireReflectiveSourceExecFact lookupFaultAfterAdvance
    compressedProofStepDirective

def lookupFaultAfterFault : List Atom :=
  cFireReflectiveSourceExecFact lookupFaultAfterProofProbe
    compressedHeapLookupFaultDirective

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
