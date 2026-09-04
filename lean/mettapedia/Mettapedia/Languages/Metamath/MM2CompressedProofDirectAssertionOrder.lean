import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderPeerCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderProofCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderAssertionCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderAdvanceCanary
import Mettapedia.Languages.ProcessCalculi.MORK.PhysicalExecPrefixOrder

/-!
# Physical order of the direct assertion probe

The direct assertion probe has physical priority `00`; the retained cursor
proof handler has priority `08`.  The comparison is made from their compact
location prefixes, leaving both executable bodies opaque.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofDirectAssertionOrder

open Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderAdvanceCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderAssertionCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderProofCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderPeerCanary
open Mettapedia.Languages.ProcessCalculi.MORK

theorem cursor_proof_representable :
    MorkCompactRepresentable compressedProofStepDirective.atom :=
  morkCompactRepresentable_of_isSome (by decide +kernel)

theorem cursor_proof_scheduler_prefix :
    ∃ rest,
      SchedulerKey.key compressedProofStepDirective =
        [4, 196, 101, 120, 101, 99, 2] ++
          compactSymbolBytes "08" ++
          compactSymbolBytes "mm-compressed-proof-step" ++ rest := by
  change ∃ rest,
    totalMorkCompactKey compressedProofStepDirective.atom =
      [4, 196, 101, 120, 101, 99, 2] ++
        compactSymbolBytes "08" ++
        compactSymbolBytes "mm-compressed-proof-step" ++ rest
  obtain ⟨input, output, surface⟩ :
      ExecSurfaceAt compressedProofStepDirective.atom
        compressedProofStepDirective.loc := by
    exact ⟨_, _, rfl⟩
  exact totalMorkCompactExec_location_prefix
    "08" "mm-compressed-proof-step" input output surface (by rfl)
    (by decide) (by decide) (by decide) (by decide)
    cursor_proof_representable

theorem direct_assertion_preempts_cursor_proof :
    lexLt (SchedulerKey.key speculativeDirectAssertionDirective)
      (SchedulerKey.key compressedProofStepDirective) = true := by
  obtain ⟨directRest, directPrefix⟩ :=
    speculative_direct_assertion_scheduler_prefix
  obtain ⟨cursorRest, cursorPrefix⟩ := cursor_proof_scheduler_prefix
  rw [directPrefix, cursorPrefix]
  rfl

theorem direct_assertion_preempts_cursor_assertion :
    lexLt (SchedulerKey.key speculativeDirectAssertionDirective)
      (SchedulerKey.key compressedAssertionLaunchDirective) = true :=
  lexLt_trans _ _ _ direct_assertion_preempts_cursor_proof
    cursor_proof_preempts_cursor_assertion

theorem direct_assertion_preempts_cursor_fault :
    lexLt (SchedulerKey.key speculativeDirectAssertionDirective)
      (SchedulerKey.key compressedHeapLookupFaultDirective) = true :=
  lexLt_trans _ _ _ direct_assertion_preempts_cursor_proof
    cursor_proof_preempts_cursor_fault

theorem direct_assertion_preempts_cursor_advance :
    lexLt (SchedulerKey.key speculativeDirectAssertionDirective)
      (SchedulerKey.key compressedHeapLookupAdvanceDirective) = true :=
  lexLt_trans _ _ _ direct_assertion_preempts_cursor_proof
    cursor_proof_preempts_cursor_advance

end Mettapedia.Languages.Metamath.MM2CompressedProofDirectAssertionOrder
