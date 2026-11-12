import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRuns.Missing

set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 16000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRuns.Resumed

attribute [local cbv_simproc ↓] Mettapedia.Tools.CbvDestinationSupport.encodedSupport
open PettaCallerReturnRunFixtures

kernel_petta_run executionTrace using (PettaOccurrenceOverlay.machine services .eagerValue ordinary)
  for 1000 from Missing.saved

theorem execution : resumed = some ([num 4, num 4, num 4], [num 7, num 7, num 9]) := by
  unfold resumed
  rw [Missing.saved_exact]
  change observe services ordinary Missing.saved = _
  unfold observe
  rw [executionTrace.run]
  try dsimp only
  all_goals cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRuns.Resumed
