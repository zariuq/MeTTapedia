import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultTerminalCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

theorem reserved_fault_terminal_selected :
    cReflectiveSourceWorkQueueStep .leaveInert lookupReservedFaultProgram =
      some lookupReservedFaultAfterTerminal := by
  decide +kernel

#print axioms reserved_fault_terminal_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultTerminalCanary
