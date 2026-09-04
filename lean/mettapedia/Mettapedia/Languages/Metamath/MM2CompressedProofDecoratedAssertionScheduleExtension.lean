import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveInertFrame

/-!
# Scheduler extension for decorated assertion source frames

Rows that decode to no supported executable leave the exact decorated
assertion scheduler inventory unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionScheduleExtension

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

theorem canonicalDecoratedDirectAssertionSpace_append_supported
    (context : DirectAssertionContext) (extra : List Atom)
    (inert : cSupportedSourceExecFacts extra = []) :
    cSupportedSourceExecFacts
        (canonicalDecoratedDirectAssertionSpace context ++ extra) =
      [decoratedDirectAssertionDirective, compressedProofStepDirective,
       decoratedCursorAssertionDirective,
       compressedHeapLookupFaultDirective,
       compressedHeapLookupAdvanceDirective] := by
  exact (cSupportedSourceExecFacts_append_inert
    (canonicalDecoratedDirectAssertionSpace context) extra inert).trans
      (canonicalDecoratedDirectAssertionSpace_supported context)

theorem canonicalDecoratedDirectAssertionSpace_append_selects
    (context : DirectAssertionContext) (extra : List Atom)
    (inert : cSupportedSourceExecFacts extra = []) :
    selectNextScheduled
        (cSupportedSourceExecFacts
          (canonicalDecoratedDirectAssertionSpace context ++ extra)) =
      some decoratedDirectAssertionDirective := by
  exact (selectNextScheduled_supported_append_inert
    (canonicalDecoratedDirectAssertionSpace context) extra inert).trans
      (canonicalDecoratedDirectAssertionSpace_selects context)

theorem canonicalDecoratedDirectAssertionSpace_append_steps
    (context : DirectAssertionContext) (extra : List Atom)
    (inert : cSupportedSourceExecFacts extra = []) :
    cReflectiveSourceWorkQueueStep .leaveInert
        (canonicalDecoratedDirectAssertionSpace context ++ extra) =
      some (cFireReflectiveSourceExecFact
        (canonicalDecoratedDirectAssertionSpace context ++ extra)
        decoratedDirectAssertionDirective) := by
  exact cReflectiveSourceWorkQueueStep_append_inert_of_selected
    (canonicalDecoratedDirectAssertionSpace context) extra
    decoratedDirectAssertionDirective inert
    (canonicalDecoratedDirectAssertionSpace_selects context)

#print axioms canonicalDecoratedDirectAssertionSpace_append_supported
#print axioms canonicalDecoratedDirectAssertionSpace_append_steps

end Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionScheduleExtension
