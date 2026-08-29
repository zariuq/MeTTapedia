import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitTerminalCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

theorem lookup_hit_terminal_selected :
    cReflectiveSourceWorkQueueStep .leaveInert lookupHitProgram =
      some lookupHitAfterTerminal := by
  decide +kernel

#print axioms lookup_hit_terminal_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitTerminalCanary
