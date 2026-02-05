import Mettapedia.Logic.MarkovDeFinettiRecurrence
import Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge

/-!
# Markov de Finetti (Recurrence is an extra hypothesis)

Diaconis–Freedman’s recurrence condition (4) is **not** implied by Markov exchangeability.
We provide a concrete counterexample (a deterministic chain that leaves its initial state once
and never returns).
-/

noncomputable section

namespace Mettapedia.Logic

open Mettapedia.Logic.MarkovDeFinettiRecurrence

variable {k : ℕ}

/-! ## Counterexample summary -/

theorem markov_exchangeable_not_implies_recurrent :
    ∃ μ : FiniteAlphabet.PrefixMeasure (Fin 2),
      MarkovExchangeabilityBridge.MarkovExchangeablePrefixMeasure (k := 2) μ ∧
      ¬ MarkovRecurrentPrefixMeasure (k := 2) μ := by
  classical
  refine ⟨MarkovDeFinettiRecurrence.Counterexample.μ, ?_⟩
  simpa using MarkovDeFinettiRecurrence.Counterexample.markov_exchangeable_not_recurrent

end Mettapedia.Logic
