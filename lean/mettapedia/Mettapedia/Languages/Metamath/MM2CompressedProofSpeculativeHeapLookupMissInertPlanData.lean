import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissCursorAssertionCanary
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveInertScheduling

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissInertPlanData

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK

/-- Exact scheduler interface after the generated proof-valued direct probe
has missed for the foreign-owner fixture. -/
def missFallbackCandidates : List SourceExecFact :=
  [compressedProofStepDirective, compressedAssertionLaunchDirective,
   compressedHeapLookupFaultDirective, compressedHeapLookupAdvanceDirective,
   speculativeDirectAssertionDirective]

/-- The four unsuccessful probes consumed before the retained cursor advance
can move from heap cursor zero to the requested compact index one. -/
def missFallbackInertProbes : List SourceExecFact :=
  [speculativeDirectAssertionDirective, compressedProofStepDirective,
   compressedHeapLookupFaultDirective, compressedAssertionLaunchDirective]

def missAfterDirectAssertionCandidates : List SourceExecFact :=
  missFallbackCandidates.erase speculativeDirectAssertionDirective

def missAfterCursorProofCandidates : List SourceExecFact :=
  missAfterDirectAssertionCandidates.erase compressedProofStepDirective

def missAfterCursorFaultCandidates : List SourceExecFact :=
  missAfterCursorProofCandidates.erase compressedHeapLookupFaultDirective

def missAfterCursorAssertionCandidates : List SourceExecFact :=
  missAfterCursorFaultCandidates.erase compressedAssertionLaunchDirective

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissInertPlanData
