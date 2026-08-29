import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitDirectCanary

/-!
# Direct speculative proof-hit interface

This module states the independently inspectable MM2 input, output, and sink
vocabulary for one generated direct proof-cell handler.  Matching and firing
proofs live in downstream modules so elaboration remains modular.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInputData

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK

def directHitInputSlice : List Atom :=
  [speculativeDirectProofDirective.atom, directStepPending, directLookupOne,
   heapOne, nodeOneRow, machineWithTwoHeapEntries, stackSuccessorZero] ++
    directProofContinuationRows

def directPendingTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-step-pending", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      .expression
        [.symbol "mm-compressed-index-code", .var "reverse-prefix",
          .var "terminal-digit"]]

def directLookupTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-heap-lookup", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      .var "compressed-index", .var "speculative-cursor"]

def directMachineTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-machine", .var "scope-owner",
      .var "proof-owner", .var "heap-next", .var "node-next",
      .var "stack-position"]

def directNextMachineTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-machine", .var "scope-owner",
      .var "proof-owner", .var "heap-next", .var "node-next",
      .var "next-stack-position"]

def directStackCellTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-stack-cell", .var "proof-owner",
      .var "stack-position", .var "node-id"]

def directNormalStackCellTemplate : Atom :=
  .expression
    [.symbol "mm-stack-cell", .var "proof-owner",
      .var "stack-position", .var "node-formula", .var "node-occurrence"]

def directResumedScanTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-scan", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      .symbol "mm-compressed-just-completed-step",
      MM2DataEncoding.listAtom MM2DataEncoding.natAtom []]

def directNextMachine : Atom :=
  .expression
    [.symbol "mm-compressed-machine", scopeOwner, proofOwner, code 2, code 2,
      code 1]

def directNormalStackCell : Atom :=
  .expression
    [.symbol "mm-stack-cell", proofOwner, code 0, formula, occurrence]

def directResumedScan : Atom :=
  .expression
    [.symbol "mm-compressed-scan", scopeOwner, proofOwner,
      MM2DataEncoding.natAtom 0,
      MM2DataEncoding.listAtom MM2DataEncoding.natAtom [],
      .symbol "mm-compressed-just-completed-step",
      MM2DataEncoding.listAtom MM2DataEncoding.natAtom []]

def directProofSelfTemplate : Atom :=
  .expression
    [.symbol "exec",
      .expression [.symbol "08", .symbol "mm-compressed-proof-step"],
      .var "proof-step-input", .var "proof-step-output"]

def directProofSinks : List Sink :=
  [.add directProofSelfTemplate,
   .add (.var "compressed-prefix-rule"),
   .add (.var "compressed-terminal-rule"),
   .add (.var "compressed-invalid-byte-rule"),
   .add (.var "compressed-question-rule"),
   .add (.var "compressed-question-open-fault-rule"),
   .remove directPendingTemplate,
   .remove directLookupTemplate,
   .remove directMachineTemplate,
   .add directNextMachineTemplate,
   .add directStackCellTemplate,
   .add directNormalStackCellTemplate,
   .add directResumedScanTemplate]

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInputData
