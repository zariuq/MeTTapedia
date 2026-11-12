import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRuns.Missing

set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 16000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRuns.Replayed

attribute [local cbv_simproc ↓] Mettapedia.Tools.CbvDestinationSupport.encodedSupport
open PettaCallerReturnRunFixtures

def restarted : PettaOccurrenceOverlay.State Unit :=
  let start := initial services ordinary
  (start.1, {start.2 with world := {start.2.world with output := Missing.saved.2.world.output}})

kernel_petta_run executionTrace using (PettaOccurrenceOverlay.machine services .eagerValue ordinary)
  for 1000 from restarted

theorem execution : replayed = some ([num 4, num 4, num 4], [num 7, num 7, num 7, num 9]) := by
  unfold replayed
  rw [Missing.saved_exact]
  change observe services ordinary restarted = _
  unfold observe
  rw [executionTrace.run]
  try dsimp only
  all_goals cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRuns.Replayed
