import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration

/-!
# Prefix Measures for Trajectory Laws

For Leike-style arguments (Thompson sampling, merging, value continuity), it is convenient to
work with the *finite-dimensional marginals* of the trajectory measure `μ^π`.

This file defines the pushforward measure on `Fin t → Step` given by truncating a trajectory to its
first `t` interaction steps, and provides basic projection combinators for splitting a prefix of
length `t+m` into a head of length `t` and a tail of length `m`.
-/

namespace Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PrefixMeasure

open ProbabilityTheory
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration
open Mettapedia.UniversalAI.BayesianAgents

/-! ## Prefix measure `μ^π ∘ truncate t` -/

noncomputable def prefixMeasureWithPolicy (μ : Environment) (π : Agent) (h_stoch : isStochastic μ) (t : ℕ) :
    MeasureTheory.Measure (Fin t → Step) :=
  (environmentMeasureWithPolicy μ π h_stoch).map (truncate t)

instance prefixMeasureWithPolicy_isProbability (μ : Environment) (π : Agent) (h_stoch : isStochastic μ) (t : ℕ) :
    MeasureTheory.IsProbabilityMeasure (prefixMeasureWithPolicy μ π h_stoch t) := by
  classical
  have : MeasureTheory.IsProbabilityMeasure (environmentMeasureWithPolicy μ π h_stoch) :=
    environmentMeasureWithPolicy_isProbability μ π h_stoch
  constructor
  simp [prefixMeasureWithPolicy, MeasureTheory.Measure.map_apply, truncate_measurable]

/-! ## Basic head/tail projections on prefix spaces -/

noncomputable def headPrefix {t m : ℕ} (p : Fin (t + m) → Step) : Fin t → Step :=
  fun i => p ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right t m)⟩

noncomputable def tailPrefix {t m : ℕ} (p : Fin (t + m) → Step) : Fin m → Step :=
  fun j => p ⟨t + j.val, Nat.add_lt_add_left j.isLt t⟩

theorem headPrefix_truncate {t m : ℕ} (traj : Trajectory) :
    headPrefix (t := t) (m := m) (truncate (t + m) traj) = truncate t traj := by
  funext i
  simp [headPrefix, truncate]

theorem tailPrefix_truncate {t m : ℕ} (traj : Trajectory) :
    tailPrefix (t := t) (m := m) (truncate (t + m) traj) =
      fun j : Fin m => traj (t + j.val) := by
  funext j
  simp [tailPrefix, truncate]

theorem headPrefix_measurable {t m : ℕ} : Measurable (headPrefix (t := t) (m := m)) := by
  classical
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply (⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right t m)⟩ : Fin (t + m))

theorem tailPrefix_measurable {t m : ℕ} : Measurable (tailPrefix (t := t) (m := m)) := by
  classical
  apply measurable_pi_lambda
  intro j
  exact measurable_pi_apply (⟨t + j.val, Nat.add_lt_add_left j.isLt t⟩ : Fin (t + m))

end Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PrefixMeasure
