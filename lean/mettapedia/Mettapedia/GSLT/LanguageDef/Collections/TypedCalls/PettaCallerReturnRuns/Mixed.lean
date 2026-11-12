import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckedReplay
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRunFixtures
import Mettapedia.Tools.CbvDestinationSupport

set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 16000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRuns.Mixed

attribute [local cbv_simproc ↓] Mettapedia.Tools.CbvDestinationSupport.encodedSupport
open PettaCallerReturnRunFixtures

kernel_petta_run executionTrace using (PettaOccurrenceOverlay.machine services .eagerValue mixed)
  for 1000 from (initial services mixed)

theorem execution : observed services mixed = some ([num 4, num 4], [num 7, num 9]) := by
  unfold observed observe
  rw [executionTrace.run]
  try dsimp only
  all_goals cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRuns.Mixed
