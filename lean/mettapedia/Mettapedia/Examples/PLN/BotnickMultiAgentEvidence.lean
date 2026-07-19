import Mathlib.Tactic
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathDependency

/-!
# Botnick multi-agent evidence example

The Botnick-style lesson is source accounting.  Independent agents combine by
noisy-OR; agents sharing a source combine by measured overlap; duplicate
reports do not create new evidence.
-/

namespace Mettapedia.Examples.PLN.BotnickMultiAgentEvidence

open scoped BigOperators ENNReal NNReal
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathDependency
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathFrechet

noncomputable section

/-! ## Positive case: independent agents -/

/-- Two independent half-probability sources combine to the noisy-OR value
`3/4`. -/
theorem independent_agents_union_three_quarters :
    let p : ℕ → ℝ≥0 := fun _ => (1 / 2 : ℝ≥0)
    let hp : ∀ s, p s ≤ 1 := by intro _; norm_num
    (infiniteFactMeasure p hp).real
        (sourceEvent ({0} : Finset ℕ) ∪ sourceEvent ({1} : Finset ℕ)) =
      (3 / 4 : ℝ) := by
  intro p hp
  rw [sourcePair_disjoint_union_eq_noisyOr p hp (by decide)]
  rw [sourceEvent_measureReal, sourceEvent_measureReal]
  norm_num [noisyOrFrequency]

/-! ## Negative case: duplicate reports are not independent paths -/

/-- Reusing the same source gives the max/redundancy value, not noisy-OR. -/
theorem duplicate_agent_source_union_half :
    let p : ℕ → ℝ≥0 := fun _ => (1 / 2 : ℝ≥0)
    let hp : ∀ s, p s ≤ 1 := by intro _; norm_num
    (infiniteFactMeasure p hp).real
        (sourceEvent ({0} : Finset ℕ) ∪ sourceEvent ({0} : Finset ℕ)) =
      (1 / 2 : ℝ) := by
  intro p hp
  rw [sourcePair_equal_union_eq_max p hp (hEq := rfl)]
  rw [sourceEvent_measureReal]
  norm_num

/-- The rule-family canary records the incorrect noisy-OR value for the same
duplicate frequency, separating independent support from repeated support. -/
theorem duplicate_source_not_noisy_or :
    noisyOrFrequency (fun _ : Fin 2 => (1 / 2 : ℝ)) = (3 / 4 : ℝ) :=
  (sourcePair_same_source_not_noisyOr_canary).2

/-! ## Shared sublemma: partial overlap -/

/-- If two agents each require a private source and one shared sublemma, the
union subtracts the shared overlap exactly. -/
theorem shared_sublemma_union_three_eighths :
    let p : ℕ → ℝ≥0 := fun _ => (1 / 2 : ℝ≥0)
    let hp : ∀ s, p s ≤ 1 := by intro _; norm_num
    (infiniteFactMeasure p hp).real
        (sourceEvent ({0, 2} : Finset ℕ) ∪
          sourceEvent ({1, 2} : Finset ℕ)) =
      (3 / 8 : ℝ) := by
  intro p hp
  rw [sourcePair_union_eq_add_sub_overlap p hp]
  rw [sourceEvent_measureReal, sourceEvent_measureReal]
  norm_num

/-! ## Revision-below-floor warning -/

/-- Negative example: equal-weight revision can fall below the redundancy
floor, so multipath evidence cannot be modeled as a blind average. -/
theorem revision_below_redundancy_floor :
    revisionFrequency₂ (9 / 10 : ℝ) (1 / 10 : ℝ) <
      max (9 / 10 : ℝ) (1 / 10 : ℝ) :=
  (revisionFrequency₂_canary).2

end

end Mettapedia.Examples.PLN.BotnickMultiAgentEvidence
