import Mathlib

/-!
# Marginal invariants for reservoir replay

Buzzega et al., *Dark Experience for General Continual Learning: a Strong,
Simple Baseline* (NeurIPS 2020, arXiv:2004.07211), use reservoir sampling to
populate the replay buffer in Dark Experience Replay.  Their Section 3 states
that a buffer of capacity `m`, after seeing a stream of length `n`, retains
each item with the same marginal probability `m / n` without knowing the final
stream length.

This file isolates the exact induction behind that statement.  When item
`n + 1` is admitted with probability `m / (n + 1)` and, conditional on
admission, a uniformly chosen one of the `m` occupied slots is evicted, every
old marginal `m / n` and the new marginal both become `m / (n + 1)`.  The
invariant propagates for an arbitrary number of later arrivals and preserves
expected occupancy exactly.

The marginal theorem does not identify the joint distribution over buffer
subsets, independence between inclusion events, the quality of stored logits,
or the empirical continual-learning results.  Uniform conditional eviction is
load bearing: a concrete two-slot counterexample shows that biased eviction
breaks equal marginals while preserving the same incoming-item probability.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace ReservoirReplaySampling

noncomputable section

/-! ## Source-shaped probabilities -/

/-- The target marginal inclusion probability for a capacity-`capacity`
reservoir after `seen` stream items. -/
def uniformMarginal (capacity seen : ℕ) : ℝ :=
  (capacity : ℝ) / (seen : ℝ)

/-- The incoming item is admitted with probability `capacity / (seen + 1)`. -/
def incomingSelectionProbability (capacity seen : ℕ) : ℝ :=
  (capacity : ℝ) / ((seen + 1 : ℕ) : ℝ)

/-- Conditional on admitting the incoming item, reservoir sampling evicts a
uniformly chosen occupied slot. -/
def uniformEvictionProbability (capacity : ℕ) : ℝ :=
  1 / (capacity : ℝ)

/-- Marginal inclusion of one old item after the admission-and-eviction step. -/
def oldMarginalAfterStep
    (oldMarginal incomingProbability conditionalEvictionProbability : ℝ) : ℝ :=
  oldMarginal *
    (1 - incomingProbability * conditionalEvictionProbability)

/-- One old item with marginal `capacity / seen` retains exactly the new
uniform marginal after a valid reservoir step. -/
theorem oldMarginalAfterStep_eq_uniformMarginal_succ
    {capacity seen : ℕ}
    (capacity_pos : 0 < capacity)
    (seen_pos : 0 < seen) :
    oldMarginalAfterStep
        (uniformMarginal capacity seen)
        (incomingSelectionProbability capacity seen)
        (uniformEvictionProbability capacity) =
      uniformMarginal capacity (seen + 1) := by
  have capacity_ne : (capacity : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt capacity_pos
  have seen_ne : (seen : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt seen_pos
  have seen_succ_ne : ((seen + 1 : ℕ) : ℝ) ≠ 0 := by
    positivity
  simp only [oldMarginalAfterStep, uniformMarginal,
    incomingSelectionProbability, uniformEvictionProbability]
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- The newly arriving item has the same marginal as every retained old item. -/
theorem incomingSelectionProbability_eq_uniformMarginal_succ
    (capacity seen : ℕ) :
    incomingSelectionProbability capacity seen =
      uniformMarginal capacity (seen + 1) := by
  rfl

/-- Therefore a single valid step preserves equality between an old item's
marginal and the incoming item's marginal. -/
theorem oldMarginalAfterStep_eq_incomingSelectionProbability
    {capacity seen : ℕ}
    (capacity_pos : 0 < capacity)
    (seen_pos : 0 < seen) :
    oldMarginalAfterStep
        (uniformMarginal capacity seen)
        (incomingSelectionProbability capacity seen)
        (uniformEvictionProbability capacity) =
      incomingSelectionProbability capacity seen := by
  rw [oldMarginalAfterStep_eq_uniformMarginal_succ capacity_pos seen_pos]
  rfl

/-! ## Arbitrarily long streams -/

/-- Propagate the marginal of an already-seen item through `laterArrivals`
reservoir updates.  The initial value is the uniform marginal at
`initialSeen`; each recurrence uses only the current stream length. -/
def propagatedOldMarginal
    (capacity initialSeen : ℕ) : ℕ → ℝ
  | 0 => uniformMarginal capacity initialSeen
  | laterArrivals + 1 =>
      oldMarginalAfterStep
        (propagatedOldMarginal capacity initialSeen laterArrivals)
        (incomingSelectionProbability capacity
          (initialSeen + laterArrivals))
        (uniformEvictionProbability capacity)

/-- Equal marginal inclusion is invariant for every finite continuation of
the stream.  No final horizon occurs in the update rule. -/
theorem propagatedOldMarginal_eq_uniformMarginal
    {capacity initialSeen : ℕ}
    (capacity_pos : 0 < capacity)
    (initialSeen_pos : 0 < initialSeen)
    (laterArrivals : ℕ) :
    propagatedOldMarginal capacity initialSeen laterArrivals =
      uniformMarginal capacity (initialSeen + laterArrivals) := by
  induction laterArrivals with
  | zero =>
      simp [propagatedOldMarginal]
  | succ laterArrivals ih =>
      rw [propagatedOldMarginal, ih]
      simpa [Nat.add_assoc] using
        oldMarginalAfterStep_eq_uniformMarginal_succ
          capacity_pos (Nat.add_pos_left initialSeen_pos laterArrivals)

/-- An item admitted after `seen` previous arrivals has marginal
`capacity / (seen + 1 + laterArrivals)` after any later continuation. -/
theorem incomingItemMarginal_after_laterArrivals
    {capacity seen : ℕ}
    (capacity_pos : 0 < capacity)
    (laterArrivals : ℕ) :
    propagatedOldMarginal capacity (seen + 1) laterArrivals =
      uniformMarginal capacity (seen + 1 + laterArrivals) := by
  exact propagatedOldMarginal_eq_uniformMarginal
    capacity_pos (Nat.succ_pos seen) laterArrivals

/-! ## Probability and occupancy boundaries -/

/-- With positive capacity no larger than the number of seen items, the
uniform marginal is a valid probability. -/
theorem uniformMarginal_mem_Icc
    {capacity seen : ℕ}
    (capacity_pos : 0 < capacity)
    (capacity_le_seen : capacity ≤ seen) :
    uniformMarginal capacity seen ∈ Set.Icc (0 : ℝ) 1 := by
  have seen_pos : 0 < seen :=
    capacity_pos.trans_le capacity_le_seen
  constructor
  · exact div_nonneg (by positivity) (by positivity)
  · exact (div_le_one (by positivity)).2 (by exact_mod_cast capacity_le_seen)

/-- Summing the equal marginals over all seen items recovers the fixed
expected occupancy `capacity`. -/
theorem sum_uniformMarginals_eq_capacity
    {capacity seen : ℕ}
    (seen_pos : 0 < seen) :
    ∑ _ : Fin seen, uniformMarginal capacity seen = (capacity : ℝ) := by
  have seen_ne : (seen : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt seen_pos
  simp only [uniformMarginal, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-! ## Negative boundaries -/

/-- Zero capacity cannot supply a normalized conditional eviction
distribution over an occupied slot.  This is why the invariance theorem
requires positive capacity. -/
theorem uniformEvictionProbability_zero :
    uniformEvictionProbability 0 = 0 := by
  norm_num [uniformEvictionProbability]

/-- With capacity two after two items, admitting the third item with the
correct probability `2/3` but evicting the first old slot with conditional
probability `3/4` and the second with `1/4` yields old marginals `1/2` and
`5/6`, while the new marginal is `2/3`.  Uniform admission alone therefore
does not imply uniform retention. -/
theorem biasedEviction_breaks_equalMarginals :
    oldMarginalAfterStep 1 ((2 : ℝ) / 3) ((3 : ℝ) / 4) = (1 : ℝ) / 2 ∧
      oldMarginalAfterStep 1 ((2 : ℝ) / 3) ((1 : ℝ) / 4) = (5 : ℝ) / 6 ∧
      incomingSelectionProbability 2 2 = (2 : ℝ) / 3 ∧
      oldMarginalAfterStep 1 ((2 : ℝ) / 3) ((3 : ℝ) / 4) ≠
        oldMarginalAfterStep 1 ((2 : ℝ) / 3) ((1 : ℝ) / 4) := by
  norm_num [oldMarginalAfterStep, incomingSelectionProbability]

end

end ReservoirReplaySampling

end Mettapedia.MachineLearning.ContinualLearning
