import Mettapedia.Logic.MarkovDeFinettiHardBEST
import Mettapedia.Logic.MarkovDeFinettiHardPatternCollisionCounterexample

/-!
Counterexamples for the Markov de Finetti hard-direction bridge statements.

This file reexports the counterexample placed in `MarkovDeFinettiHardBEST`
so it is built with the main development.
-/

namespace Mettapedia.Logic

namespace MarkovDeFinettiHardCounterexamples

abbrev wr_bridge_counts_counterexample :=
  MarkovDeFinettiHardBEST.WRBridgeCounterexample.wr_bridge_counts_counterexample

abbrev not_hasPatternCollisionPosAll_k6 :=
  MarkovDeFinettiHard.PatternCollisionCounterexample.not_HasPatternCollisionPosAll_k6

end MarkovDeFinettiHardCounterexamples

end Mettapedia.Logic
