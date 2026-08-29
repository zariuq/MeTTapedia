import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterAssertionScheduling

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK

theorem select_cursor_advance_after_assertion_probe :
    selectNextScheduled [compressedHeapLookupAdvanceDirective] =
      some compressedHeapLookupAdvanceDirective := by
  rfl

#print axioms select_cursor_advance_after_assertion_probe

end Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterAssertionScheduling
