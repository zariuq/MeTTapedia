import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary

/-!
# Reserved-successor heap-walker adequacy counterexample

This bounded program deliberately retains a successor row beyond the live
heap frontier.  The current computable Lean list realization consumes three
scheduler directives and then stalls without producing either a proof value
or the explicit frontier fault.  The counterexample identifies an unclosed
agreement seam between the reflective runner and the MM2 behavior qualified
by the separate command-line fixtures; it is not a counterexample to the
abstract reserved-cursor GSLT.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultCanary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
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

def lookupReservedFaultAfterProbe : List Atom :=
  cFireReflectiveSourceExecFact lookupReservedFaultAfterTerminal
    compressedHeapLookupFaultDirective

def lookupReservedFaultAfterAdvance : List Atom :=
  cFireReflectiveSourceExecFact lookupReservedFaultAfterProbe
    compressedHeapLookupAdvanceDirective

/-- Exact handlers, including the explicit frontier fault, are scheduled
before the generic cursor advance. -/
theorem frontier_fault_has_priority_over_reserved_advance :
    compressedHeapLookupFaultDirective.rule.priority <
      compressedHeapLookupAdvanceDirective.rule.priority := by
  decide

#print axioms frontier_fault_has_priority_over_reserved_advance

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultCanary
