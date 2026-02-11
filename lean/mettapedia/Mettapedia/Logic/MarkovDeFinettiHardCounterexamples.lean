import Mettapedia.Logic.MarkovDeFinettiHardBEST

/-!
Counterexamples for the Markov de Finetti hard-direction bridge statements.

This file reexports the counterexample placed in `MarkovDeFinettiHardBEST`
so it is built with the main development.
-/

namespace Mettapedia.Logic

namespace MarkovDeFinettiHardCounterexamples

theorem wr_bridge_counts_counterexample :=
  MarkovDeFinettiHardBEST.WRBridgeCounterexample.wr_bridge_counts_counterexample

end MarkovDeFinettiHardCounterexamples

end Mettapedia.Logic
