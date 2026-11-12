import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedFixtures
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckedReplay
import Mettapedia.Tools.CbvDestinationSupport

set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 16000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedRootRuns.Good

attribute [local cbv_simproc ↓] Mettapedia.Tools.CbvDestinationSupport.encodedSupport
open PettaInheritedFixtures
open PettaCheckpointFixtures (num text)

kernel_petta_run entryTrace using (PettaOccurrenceOverlay.machine services .eagerValue (program false))
  for 6 from (initial false false)

theorem source_ready : ready false false = some entryTrace.residual := by
  unfold ready
  change (match ((PettaOccurrenceOverlay.machine services .eagerValue (program false)).run 6
    (initial false false)).2 with
    | .exhausted reached => some reached
    | _ => none) = some entryTrace.residual
  rw [entryTrace.run]
  rfl

kernel_petta_run remainingTrace using (PettaOccurrenceOverlay.machine services .eagerValue (program false))
  for 120 from entryTrace.residual

theorem execution : observed false false = some ([num 4, text "outside"], [text "before", text "body"]) := by
  unfold observed
  rw [source_ready]
  change observe (PettaInheritedContext.execute services (program false) 120
    (PettaInheritedContext.nest entryTrace.residual)) = _
  rw [PettaInheritedContext.execute_in_host]
  unfold observe
  rw [remainingTrace.run]
  try dsimp only
  all_goals cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedRootRuns.Good
