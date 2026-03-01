/-
# Structural Decomposition Lemmas (Init-only)

These lemmas allow splitting a large `hasIndepSetAux` computation into smaller
sub-problems that the kernel can check independently, avoiding OOM on
large graphs (e.g., Fin 17).

No imports beyond IndepSetFunc — these are purely about unfolding the Bool computation.

## What lives elsewhere
- `hasIndepSetAux_complete` (completeness theorem): requires Finset (Mathlib), lives in the
  consumer (e.g. ramsey36/IndepSetBridge.lean)
- SimpleGraph bridge theorems: similarly Mathlib-dependent, live in the consumer
-/

import Algorithms.Graph.IndepSetFunc

/-- When pigeonhole prunes (not enough vertices remain), returns false. -/
theorem hasIndepSetAux_false_of_pig
    {n : Nat} {adj : Fin n → Fin n → Bool}
    {remaining start : Nat} {chosen : List (Fin n)} {fuel : Nat}
    (h_rem : remaining ≠ 0) (h_start : start < n) (h_pig : n - start < remaining) :
    hasIndepSetAux n adj remaining start chosen (fuel + 1) = false := by
  unfold hasIndepSetAux
  simp [h_rem, dif_pos h_start, h_pig]

/-- Decomposition: if vertex `start` is compatible with `chosen` and both the
    include and skip branches return false, then the whole call returns false. -/
theorem hasIndepSetAux_false_of_compat
    {n : Nat} {adj : Fin n → Fin n → Bool}
    {remaining start : Nat} {chosen : List (Fin n)} {fuel : Nat}
    (h_rem : remaining ≠ 0) (h_start : start < n) (h_pig : ¬(n - start < remaining))
    (h_compat : (chosen.all fun w => !adj ⟨start, h_start⟩ w) = true)
    (h_inc : hasIndepSetAux n adj (remaining - 1) (start + 1)
      (⟨start, h_start⟩ :: chosen) fuel = false)
    (h_skip : hasIndepSetAux n adj remaining (start + 1) chosen fuel = false) :
    hasIndepSetAux n adj remaining start chosen (fuel + 1) = false := by
  unfold hasIndepSetAux
  simp only [h_rem, ↓reduceIte, dif_pos h_start, h_pig,
    show (chosen.all fun w => !adj ⟨start, h_start⟩ w) = true from h_compat,
    h_inc, h_skip, Bool.false_or]
