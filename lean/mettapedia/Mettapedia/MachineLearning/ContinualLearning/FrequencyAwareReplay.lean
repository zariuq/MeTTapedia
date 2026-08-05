import Mathlib.Tactic

/-!
# Frequency-aware replay quotas and their rounding boundary

Hemati et al., *Class-Incremental Learning with Repetition*
(CoLLAs 2023, arXiv:2301.11396), Section 3 and Algorithm 3, allocate replay
memory inversely to the number of experiences in which each class has
appeared. The inverse counts are normalized and each resulting real-valued
quota is multiplied by the buffer capacity and rounded upward.

This file isolates the finite allocation arithmetic. Under the source
invariant that every tracked class has a positive observation count:

* normalized inverse-frequency quotas are positive and sum to one;
* a less frequently observed class receives a strictly larger quota;
* independently rounding every class upward allocates at least the requested
  capacity, but fewer than one extra slot per tracked class.

The final point is a real implementation boundary. With two classes observed
once and twice and a one-slot buffer, the normalized quotas are `2/3` and
`1/3`; rounding both upward requests two slots. Thus an implementation needs
an explicit capacity-reconciliation rule after the displayed source formula.
A zero-count fixture also shows why the source's positive-count initialization
is load-bearing: totalized rational division assigns zero inverse weight to
an unseen class.

These theorems concern quota arithmetic only. They do not establish replay
accuracy, forgetting reduction, class-frequency estimation, buffer-update
semantics, or the source's empirical comparisons.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace FrequencyAwareReplay

variable {Class : Type*} [Fintype Class]

/-- Unnormalized replay weight: the reciprocal of a class's positive
experience-observation count. -/
def inverseObservationWeight
    (observations : Class → ℕ) (cls : Class) : ℚ :=
  1 / observations cls

/-- Sum of all unnormalized inverse-frequency weights. -/
def inverseWeightTotal (observations : Class → ℕ) : ℚ :=
  ∑ cls, inverseObservationWeight observations cls

/-- Source-shaped normalized inverse-frequency quota. -/
def normalizedInverseQuota
    (observations : Class → ℕ) (cls : Class) : ℚ :=
  inverseObservationWeight observations cls /
    inverseWeightTotal observations

/-- Real-valued number of slots requested before rounding. -/
def scaledSlotQuota
    (observations : Class → ℕ) (capacity : ℕ) (cls : Class) : ℚ :=
  capacity * normalizedInverseQuota observations cls

/-- Per-class slot request obtained by independently rounding upward. -/
def roundedSlotQuota
    (observations : Class → ℕ) (capacity : ℕ) (cls : Class) : ℕ :=
  ⌈scaledSlotQuota observations capacity cls⌉₊

/-- Total number of slots requested after independent upward rounding. -/
def totalRoundedSlots
    (observations : Class → ℕ) (capacity : ℕ) : ℕ :=
  ∑ cls, roundedSlotQuota observations capacity cls

omit [Fintype Class] in
theorem inverseObservationWeight_pos
    (observations : Class → ℕ)
    (observations_pos : ∀ cls, 0 < observations cls)
    (cls : Class) :
    0 < inverseObservationWeight observations cls := by
  have cls_pos : (0 : ℚ) < observations cls := by
    exact_mod_cast observations_pos cls
  exact one_div_pos.mpr cls_pos

theorem inverseWeightTotal_pos [Nonempty Class]
    (observations : Class → ℕ)
    (observations_pos : ∀ cls, 0 < observations cls) :
    0 < inverseWeightTotal observations := by
  apply Finset.sum_pos
  · intro cls _
    exact inverseObservationWeight_pos observations observations_pos cls
  · exact Finset.univ_nonempty

theorem normalizedInverseQuota_pos [Nonempty Class]
    (observations : Class → ℕ)
    (observations_pos : ∀ cls, 0 < observations cls)
    (cls : Class) :
    0 < normalizedInverseQuota observations cls := by
  exact div_pos
    (inverseObservationWeight_pos observations observations_pos cls)
    (inverseWeightTotal_pos observations observations_pos)

theorem sum_normalizedInverseQuota_eq_one [Nonempty Class]
    (observations : Class → ℕ)
    (observations_pos : ∀ cls, 0 < observations cls) :
    ∑ cls, normalizedInverseQuota observations cls = 1 := by
  simp only [normalizedInverseQuota]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt
    (inverseWeightTotal_pos observations observations_pos))

/-- The source's intended monotonicity: fewer observations imply a larger
normalized replay quota. -/
theorem normalizedInverseQuota_gt_of_observations_lt [Nonempty Class]
    (observations : Class → ℕ)
    (observations_pos : ∀ cls, 0 < observations cls)
    {rarer frequent : Class}
    (rarer_lt : observations rarer < observations frequent) :
    normalizedInverseQuota observations frequent <
      normalizedInverseQuota observations rarer := by
  have rarer_pos : (0 : ℚ) < observations rarer := by
    exact_mod_cast observations_pos rarer
  have count_lt :
      (observations rarer : ℚ) < observations frequent := by
    exact_mod_cast rarer_lt
  have weight_lt :
      inverseObservationWeight observations frequent <
        inverseObservationWeight observations rarer := by
    exact one_div_lt_one_div_of_lt rarer_pos count_lt
  exact (div_lt_div_iff_of_pos_right
    (inverseWeightTotal_pos observations observations_pos)).2 weight_lt

theorem scaledSlotQuota_nonneg [Nonempty Class]
    (observations : Class → ℕ)
    (observations_pos : ∀ cls, 0 < observations cls)
    (capacity : ℕ) (cls : Class) :
    0 ≤ scaledSlotQuota observations capacity cls := by
  exact mul_nonneg (by positivity)
    (le_of_lt
      (normalizedInverseQuota_pos observations observations_pos cls))

/-- Independent upward rounding never requests fewer than the declared
capacity. -/
theorem capacity_le_totalRoundedSlots [Nonempty Class]
    (observations : Class → ℕ)
    (observations_pos : ∀ cls, 0 < observations cls)
    (capacity : ℕ) :
    capacity ≤ totalRoundedSlots observations capacity := by
  have each_le :
      ∀ cls ∈ (Finset.univ : Finset Class),
        scaledSlotQuota observations capacity cls ≤
          (roundedSlotQuota observations capacity cls : ℚ) := by
    intro cls _
    exact Nat.le_ceil _
  have summed := Finset.sum_le_sum each_le
  have scaled_sum :
      ∑ cls, scaledSlotQuota observations capacity cls =
        (capacity : ℚ) := by
    simp only [scaledSlotQuota, ← Finset.mul_sum]
    rw [sum_normalizedInverseQuota_eq_one observations observations_pos]
    simp
  have rounded_cast :
      ∑ cls, (roundedSlotQuota observations capacity cls : ℚ) =
        (totalRoundedSlots observations capacity : ℚ) := by
    simp [totalRoundedSlots]
  rw [scaled_sum, rounded_cast] at summed
  exact_mod_cast summed

/-- The independent-ceiling slack is strictly below one slot per tracked
class. -/
theorem totalRoundedSlots_lt_capacity_add_card [Nonempty Class]
    (observations : Class → ℕ)
    (observations_pos : ∀ cls, 0 < observations cls)
    (capacity : ℕ) :
    totalRoundedSlots observations capacity <
      capacity + Fintype.card Class := by
  have each_lt :
      ∀ cls ∈ (Finset.univ : Finset Class),
        (roundedSlotQuota observations capacity cls : ℚ) <
          scaledSlotQuota observations capacity cls + 1 := by
    intro cls _
    exact Nat.ceil_lt_add_one
      (scaledSlotQuota_nonneg observations observations_pos capacity cls)
  have each_le :
      ∀ cls ∈ (Finset.univ : Finset Class),
        (roundedSlotQuota observations capacity cls : ℚ) ≤
          scaledSlotQuota observations capacity cls + 1 := by
    intro cls cls_mem
    exact le_of_lt (each_lt cls cls_mem)
  obtain ⟨witness⟩ := ‹Nonempty Class›
  have summed :
      ∑ candidate : Class,
          (roundedSlotQuota observations capacity candidate : ℚ) <
        ∑ candidate : Class,
          (scaledSlotQuota observations capacity candidate + 1) := by
    apply Finset.sum_lt_sum each_le
    exact ⟨witness, Finset.mem_univ witness,
      each_lt witness (Finset.mem_univ witness)⟩
  have scaled_sum :
      ∑ candidate : Class,
          scaledSlotQuota observations capacity candidate =
        (capacity : ℚ) := by
    simp only [scaledSlotQuota, ← Finset.mul_sum]
    rw [sum_normalizedInverseQuota_eq_one observations observations_pos]
    simp
  have rounded_cast :
      ∑ candidate : Class,
          (roundedSlotQuota observations capacity candidate : ℚ) =
        (totalRoundedSlots observations capacity : ℚ) := by
    simp [totalRoundedSlots]
  rw [rounded_cast] at summed
  simp only [Finset.sum_add_distrib, scaled_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at summed
  exact_mod_cast summed

/-! ## Executable source boundary -/

def twoClassObservations : Bool → ℕ
  | false => 1
  | true => 2

theorem twoClassObservations_pos :
    ∀ cls, 0 < twoClassObservations cls := by
  decide

theorem two_class_normalized_quotas :
    normalizedInverseQuota twoClassObservations false = 2 / 3 ∧
      normalizedInverseQuota twoClassObservations true = 1 / 3 := by
  norm_num [normalizedInverseQuota, inverseWeightTotal,
    inverseObservationWeight, twoClassObservations]

/-- The displayed independent-ceiling formula can request more memory than
the declared capacity: `ceil(2/3) + ceil(1/3) = 2 > 1`. -/
theorem two_class_ceil_oversubscribes_one_slot :
    totalRoundedSlots twoClassObservations 1 = 2 ∧
      1 < totalRoundedSlots twoClassObservations 1 := by
  norm_num [totalRoundedSlots, roundedSlotQuota, scaledSlotQuota,
    normalizedInverseQuota, inverseWeightTotal,
    inverseObservationWeight, twoClassObservations]
  have one_third_ceil : ⌈(1 / 3 : ℚ)⌉₊ = 1 := by
    rw [Nat.ceil_eq_iff (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num
  have two_thirds_ceil : ⌈(2 / 3 : ℚ)⌉₊ = 1 := by
    rw [Nat.ceil_eq_iff (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num
  rw [one_third_ceil, two_thirds_ceil]
  norm_num

def zeroCountObservations : Bool → ℕ
  | false => 0
  | true => 1

/-- Totalized rational division makes a zero observation count receive zero
inverse weight, so the source's initialization-at-one invariant is essential. -/
theorem zero_observation_is_not_prioritized :
    inverseObservationWeight zeroCountObservations false = 0 ∧
      inverseObservationWeight zeroCountObservations true = 1 ∧
      normalizedInverseQuota zeroCountObservations false = 0 := by
  norm_num [inverseObservationWeight, normalizedInverseQuota,
    inverseWeightTotal, zeroCountObservations]

#print axioms inverseObservationWeight_pos
#print axioms sum_normalizedInverseQuota_eq_one
#print axioms normalizedInverseQuota_gt_of_observations_lt
#print axioms capacity_le_totalRoundedSlots
#print axioms totalRoundedSlots_lt_capacity_add_card
#print axioms two_class_ceil_oversubscribes_one_slot
#print axioms zero_observation_is_not_prioritized

end FrequencyAwareReplay

end Mettapedia.MachineLearning.ContinualLearning
