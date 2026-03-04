import Mettapedia.Logic.MarkovDeFinettiFortiniBridgeCrux

/-!
# Markov de Finetti Fortini Bridge: Internal Staging Surface

This module is for internal proof-plumbing only.
It intentionally re-exports internal interfaces from `...BridgeCrux` so they
can be developed without polluting the canonical entry surface.
-/

noncomputable section

namespace Mettapedia.Logic
namespace MarkovDeFinettiHard

abbrev FortiniInternalBuiltKernelBridge (k : ℕ) : Prop :=
  ExistsBuiltRowKernel_of_successorMatrixPE k

abbrev FortiniInternalRecurrentCoherenceBridge (k : ℕ) : Prop :=
  RecurrentLatentCoherenceBridgeTheorem k

abbrev FortiniInternalBuildOnRecurrentExtension (k : ℕ) : Prop :=
  BuildRowKernelOnRecurrentExtension k

end MarkovDeFinettiHard
end Mettapedia.Logic

