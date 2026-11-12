import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckedReplay
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRunFixtures
import Mettapedia.Machines.ReplaySlices
import Mettapedia.Tools.CbvDestinationSupport

/-!
# Checked source prefix before the first typed argument guard

These are actual initial-machine transitions, not a reconstructed entry
state. The prefix does not include the guard transition or claim completion
of the enclosing caller-return fixture.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnReplayPrefix

attribute [local cbv_simproc ↓] Mettapedia.Tools.CbvDestinationSupport.encodedSupport

open Mettapedia.GSLT.Distinction.ProductiveBlocks
open PettaCallerReturnRunFixtures

def runner := PettaOccurrenceOverlay.machine services .eagerValue ordinary

kernel_petta_run firstFive using runner for 5 from (initial services ordinary)
kernel_petta_run nextFour using runner for 4 from firstFive.residual

theorem nine_steps_reach_the_guard :
    runner.run 9 (initial services ordinary) = ([], .exhausted nextFour.residual) := by
  exact Mettapedia.Machines.ReplaySlices.compose runner 5 4
    (initial services ordinary) firstFive.residual [] [] (.exhausted nextFour.residual)
    firstFive.run nextFour.run

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnReplayPrefix
