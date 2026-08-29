import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFrontierFaultStepCanary

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultInputData

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary

/-- The unresolved request after the cursor has advanced to compact index one,
which is also the first-free heap frontier in the miss fixture. -/
def frontierLookupOne : Atom :=
  .expression
    [.symbol "mm-compressed-heap-lookup", scopeOwner, proofOwner,
      MM2DataEncoding.natAtom 0,
      MM2DataEncoding.listAtom MM2DataEncoding.natAtom [], code 1, code 1]

/-- Minimal positive interface consumed by the frontier fault rule. -/
def speculativeMissFaultInputSlice : List Atom :=
  [compressedHeapLookupFaultDirective.atom, directStepPending,
   frontierLookupOne, machineWithOneHeapEntry]

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultInputData
