import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mettapedia.Logic.MarkovDeFinettiHardMomentFunctional

/-!
# Minimal measure-theory curriculum for the Markov de Finetti hard direction

This file ties the four measure-theory steps explicitly to concrete lemmas used in the proof.
It is intentionally small and proof-checked (no sorries).
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators
open MeasureTheory

namespace MarkovDeFinettiHard

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet

variable {k : ℕ}

/-- Step 1 (finite measures & PMFs): the empirical `lintegral` is a finite sum. -/
lemma curriculum_step1_finite_sum
    (hk : 0 < k) (μ : PrefixMeasure (Fin k)) (N n : ℕ) (e : MarkovState k) :
    lintegral (empiricalMeasure (k := k) hk μ N) (fun θ => Wnn (k := k) n e θ) =
      (stateFinset k N).sum (fun s =>
        (Wnn (k := k) n e (empiricalParam (k := k) hk s) : ENNReal) * wμ (k := k) μ N s) := by
  -- The lemma in the main file uses integral notation; rewrite via `lintegral`.
  simpa using
    (lintegral_Wnn_empiricalMeasure_eq_sum (k := k) hk (μ := μ) (N := N) (n := n) (e := e))

/-- Step 2 (Tonelli/Fubini for nonnegative integrals): finite sums commute with `lintegral`. -/
lemma curriculum_step2_fubini
    {α : Type*} [MeasurableSpace α] (s : Finset ℕ)
    (f : ℕ → α → ENNReal) (hf : ∀ i, i ∈ s → Measurable (f i)) (μ : Measure α) :
    lintegral μ (fun x => Finset.sum s (fun i => f i x)) =
      Finset.sum s (fun i => lintegral μ (f i)) := by
  simpa using (lintegral_finset_sum (s := s) (f := f) (hf := hf) (μ := μ))

/-- Step 3 (continuity of π ↦ ∫ f dπ): used in `evalVec` continuity. -/
lemma curriculum_step3_continuity
    (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k)) :
    Continuous (evalVec (k := k) μ u) :=
  continuous_evalVec (k := k) μ u

/-- Step 4 (compactness of ProbabilityMeasure K): used in moment-polytope closure. -/
lemma curriculum_step4_compact (k : ℕ) :
    IsCompact (Set.univ : Set (ProbabilityMeasure (MarkovParam k))) :=
  isCompact_univ

end MarkovDeFinettiHard

end Mettapedia.Logic
