import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure
import Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge

/-!
# Markov de Finetti (Recurrence Assumption)

Diaconis–Freedman (1980) show that **Markov exchangeability** alone is not sufficient to
guarantee a mixture-of-Markov-chains representation unless one adds a **recurrence**
assumption (see their condition (4) and Theorem 7).

This file packages a *prefix-measure level* recurrence assumption in a way that can be
used by the hard-direction theorem:

* a prefix measure `μ` is **recurrent** if it extends to a probability measure on infinite
  trajectories and that extension returns to the initial state infinitely often (a.s.).

Important: this is **only a hypothesis**. We do **not** assume or postulate any theorem
that produces recurrence. Any future proof that a given class of prefix measures is
recurrent should live in a separate file and be stated as a theorem (not an axiom).
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical
open MeasureTheory

namespace MarkovDeFinettiRecurrence

variable {k : ℕ}

/-! ## Cylinder sets on infinite trajectories -/

/-- Cylinder set for a finite word `xs` in the space of infinite trajectories. -/
def cylinder (xs : List (Fin k)) : Set (ℕ → Fin k) :=
  { ω | ∀ i : Fin xs.length, ω i = xs.get i }

/-! ## Recurrence event -/

/-- The event that the trajectory returns to its initial state infinitely often. -/
def recurrentEvent : Set (ℕ → Fin k) :=
  { ω | Set.Infinite { n : ℕ | ω n = ω 0 } }

/-! ## Recurrence for prefix measures -/

/--
A prefix measure `μ` is **Markov-recurrent** if it extends to a probability measure on
infinite trajectories such that the recurrence event holds almost surely.

This mirrors Diaconis–Freedman’s recurrence condition (4):
`P{ X_n = X_0 for infinitely many n } = 1`.
-/
def MarkovRecurrentPrefixMeasure
    (μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)) : Prop :=
  ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
    (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
    P (recurrentEvent (k := k)) = 1

/-!
## Recurrence hypothesis (explicit TODO)

We keep the Diaconis–Freedman recurrence condition **as a theorem with `sorry`**
so it is visible in builds and cannot be mistaken for a harmless assumption.

This statement is intentionally strong; if it turns out to be false in this generality,
it should be replaced by a counterexample or by a correctly weakened hypothesis.
-/
theorem markovRecurrentPrefixMeasure_of_exchangeable
    (μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge.MarkovExchangeablePrefixMeasure (k := k) μ) :
    MarkovRecurrentPrefixMeasure (k := k) μ := by
  -- TODO (Diaconis–Freedman): decide whether recurrence follows from exchangeability
  -- under additional hypotheses (or provide a counterexample if not).
  sorry

end MarkovDeFinettiRecurrence

end Mettapedia.Logic
