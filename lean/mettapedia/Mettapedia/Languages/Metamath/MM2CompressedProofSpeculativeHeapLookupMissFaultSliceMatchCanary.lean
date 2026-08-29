import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultInputData

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultSliceMatchCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultInputData
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

def missingStepPendingTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-step-pending", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      .expression
        [.symbol "mm-compressed-index-code", .var "reverse-prefix",
          .var "terminal-digit"]]

def missingHeapLookupTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-heap-lookup", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      .var "compressed-index", .var "heap-next"]

def missingMachineTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-machine", .var "scope-owner",
      .var "proof-owner", .var "heap-next", .var "node-next",
      .var "stack-position"]

def missingHeapReferenceFaultTemplate : Atom :=
  .expression
    [.symbol "mm-proof-fault", .var "scope-owner", .var "proof-owner",
      .var "word-position", .symbol "compressed-missing-heap-reference",
      .symbol "compressed-heap", .var "compressed-index", .var "heap-next"]

def speculativeMissFaultSliceRows : List Subst :=
  (Conformance.Computable.cmatchInputSpec [] speculativeMissFaultInputSlice
      compressedHeapLookupFaultDirective.rule.input).map Prod.fst

/-- The four-atom positive interface produces a substitution that instantiates
the exact missing-reference observation. -/
theorem speculative_miss_fault_slice_instantiates :
    ∃ substitution ∈ speculativeMissFaultSliceRows,
      instantiateTemplateAtom? substitution
          missingHeapReferenceFaultTemplate =
        some missingOneFault := by
  decide +kernel

/-- One matcher row instantiates the complete consume/consume/consume/emit
interface of the missing-reference transition. -/
theorem speculative_miss_fault_slice_instantiates_all :
    ∃ substitution ∈ speculativeMissFaultSliceRows,
      instantiateTemplateAtom? substitution missingStepPendingTemplate =
          some directStepPending ∧
        instantiateTemplateAtom? substitution missingHeapLookupTemplate =
          some frontierLookupOne ∧
        instantiateTemplateAtom? substitution missingMachineTemplate =
          some machineWithOneHeapEntry ∧
        instantiateTemplateAtom? substitution
            missingHeapReferenceFaultTemplate =
          some missingOneFault := by
  decide +kernel

#print axioms speculative_miss_fault_slice_instantiates
#print axioms speculative_miss_fault_slice_instantiates_all

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultSliceMatchCanary
