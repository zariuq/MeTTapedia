import Mettapedia.Logic.PLNHigherOrderVarianceUpdate
import Mathlib.Data.Real.Basic

/-!
# Higher-Order Value-of-Information Theorems

This module gives a finite theorem-facing VOI layer for reveal scheduling.
It deliberately stays one-step and finite.
-/

namespace Mettapedia.Logic

open scoped BigOperators

variable {C : Type*}

def candidateVOI
    (varianceReduction : C → ℝ)
    (cost : C → ℝ)
    (c : C) : ℝ :=
  varianceReduction c - cost c

theorem voi_nonneg_if_cost_le_varianceReduction
    (varianceReduction : C → ℝ)
    (cost : C → ℝ)
    {c : C}
    (hcost : cost c ≤ varianceReduction c) :
    0 ≤ candidateVOI varianceReduction cost c := by
  unfold candidateVOI
  linarith

theorem exists_best_revealCandidate
    (candidates : Finset C)
    (varianceReduction : C → ℝ)
    (cost : C → ℝ)
    (hnonempty : candidates.Nonempty) :
    ∃ c ∈ candidates,
      ∀ d ∈ candidates,
        candidateVOI varianceReduction cost d ≤
          candidateVOI varianceReduction cost c := by
  classical
  let f := candidateVOI varianceReduction cost
  let vals := candidates.image f
  have hvals_nonempty : vals.Nonempty := by
    rcases hnonempty with ⟨c, hc⟩
    refine ⟨f c, ?_⟩
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  have hmax_mem : vals.max' hvals_nonempty ∈ vals := Finset.max'_mem vals hvals_nonempty
  rcases Finset.mem_image.mp hmax_mem with ⟨c, hc_mem, hc_max⟩
  refine ⟨c, hc_mem, ?_⟩
  intro d hd_mem
  have hd_val_mem : f d ∈ vals := Finset.mem_image.mpr ⟨d, hd_mem, rfl⟩
  have hle : f d ≤ vals.max' hvals_nonempty := Finset.le_max' vals (f d) hd_val_mem
  have hle' : f d ≤ f c := by
    rw [hc_max]
    exact hle
  simpa [f] using hle'

theorem greedyReveal_beats_neverReveal_singleStep
    (candidates : Finset C)
    (varianceReduction : C → ℝ)
    (cost : C → ℝ)
    (hnonempty : candidates.Nonempty)
    (hgood :
      ∃ c ∈ candidates,
        0 ≤ candidateVOI varianceReduction cost c) :
    ∃ c ∈ candidates,
      (∀ d ∈ candidates,
        candidateVOI varianceReduction cost d ≤
          candidateVOI varianceReduction cost c) ∧
      0 ≤ candidateVOI varianceReduction cost c := by
  rcases exists_best_revealCandidate candidates varianceReduction cost hnonempty with
    ⟨c, hc_mem, hbest⟩
  rcases hgood with ⟨c₀, hc₀_mem, hc₀_nonneg⟩
  refine ⟨c, hc_mem, hbest, ?_⟩
  have hdom := hbest c₀ hc₀_mem
  linarith

end Mettapedia.Logic
