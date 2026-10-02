import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary

/-!
# Reserved-successor heap-walker safety controls

This bounded program deliberately retains a successor row beyond the live
heap frontier.  The proof, fault, and assertion probes at cursor zero precede
the cursor advance.  At the live frontier the proof probe is inert, and the
scheduled fault handler consumes the lookup before the reserved successor
edge can advance it beyond that frontier.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultCanary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding (natAtom compressedWordAtom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

def reservedHeapSuccessorOne : Atom :=
  compressedIndexSuccessorRow (compressedHeapOwner proofOwner) (code 1)
    (code 2)

/-- The ordinary fault fixture, extended by one deliberately unused reserved
cursor edge beginning exactly at the live frontier. -/
def lookupReservedFaultProgram : List Atom :=
  lookupFaultProgram ++ [reservedHeapSuccessorOne]

def lookupReservedFaultAfterTerminal : List Atom :=
  cFireReflectiveSourceExecFact lookupReservedFaultProgram
    compressedTerminalDirective

def lookupReservedFaultAfterInitialProofProbe : List Atom :=
  cFireReflectiveSourceExecFact lookupReservedFaultAfterTerminal
    compressedProofStepDirective

def lookupReservedFaultAfterProbe : List Atom :=
  cFireReflectiveSourceExecFact lookupReservedFaultAfterInitialProofProbe
    compressedHeapLookupFaultDirective

def lookupReservedFaultAfterAssertionProbe : List Atom :=
  cFireReflectiveSourceExecFact lookupReservedFaultAfterProbe
    compressedAssertionLaunchDirective

def lookupReservedFaultAfterAdvance : List Atom :=
  cFireReflectiveSourceExecFact lookupReservedFaultAfterAssertionProbe
    compressedHeapLookupAdvanceDirective

def lookupReservedFaultAfterProofProbe : List Atom :=
  cFireReflectiveSourceExecFact lookupReservedFaultAfterAdvance
    compressedProofStepDirective

def lookupReservedFaultAfterFault : List Atom :=
  cFireReflectiveSourceExecFact lookupReservedFaultAfterProofProbe
    compressedHeapLookupFaultDirective

def reservedOutOfFrontierLookup : Atom :=
  .expression
    [.symbol "mm-compressed-heap-lookup", scopeOwner, proofOwner,
      natAtom 0, compressedWordAtom [], code 1, code 2]

theorem reserved_fault_after_terminal_supported_exact :
    cSupportedSourceExecFacts lookupReservedFaultAfterTerminal =
      [compressedHeapLookupAdvanceDirective, compressedHeapLookupFaultDirective,
       compressedProofStepDirective, compressedAssertionLaunchDirective] := by
  rfl

/-- Exact handlers, including the explicit frontier fault, are scheduled
before the generic cursor advance. -/
theorem frontier_fault_has_priority_over_reserved_advance :
    compressedHeapLookupFaultDirective.rule.priority <
      compressedHeapLookupAdvanceDirective.rule.priority := by
  decide

#print axioms frontier_fault_has_priority_over_reserved_advance

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultCanary
