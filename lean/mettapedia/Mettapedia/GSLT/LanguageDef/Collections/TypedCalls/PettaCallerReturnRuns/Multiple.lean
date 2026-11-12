import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckedReplay
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRunFixtures
import Mettapedia.Tools.CbvDestinationSupport

set_option autoImplicit false
set_option maxHeartbeats 128000000
set_option maxRecDepth 16000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRuns.Multiple

attribute [local cbv_simproc ↓] Mettapedia.Tools.CbvDestinationSupport.encodedSupport
open PettaCallerReturnRunFixtures

kernel_petta_run executionTrace using (PettaOccurrenceOverlay.machine services .eagerValue multiple)
  for 1000 from (initial services multiple)

theorem execution :
    observed services multiple = some (List.replicate 4 (num 4), List.replicate 4 (sym "dual")) := by
  unfold observed observe
  rw [executionTrace.run]
  try dsimp only
  all_goals cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRuns.Multiple
