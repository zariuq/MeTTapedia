import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckedReplay
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRunFixtures
import Mettapedia.Tools.CbvDestinationSupport

set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 16000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRuns.Missing

attribute [local cbv_simproc ↓] Mettapedia.Tools.CbvDestinationSupport.encodedSupport
open PettaCallerReturnRunFixtures

kernel_petta_run executionTrace using (PettaOccurrenceOverlay.machine missingResult .eagerValue ordinary)
  for 1000 from (initial missingResult ordinary)

def saved : PettaOccurrenceOverlay.State Unit := executionTrace.retained

theorem saved_exact : stopped = some saved := by
  unfold stopped
  rw [executionTrace.run]
  rfl

theorem execution :
    stopped.map (fun kept => (kept.2.world.output, kept.2.scopes.length,
      kept.2.scopes.head?.map (fun scope => scope.frontier.length))) = some ([num 7], 1, some 3) := by
  rw [saved_exact]
  try dsimp only
  all_goals cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRuns.Missing
