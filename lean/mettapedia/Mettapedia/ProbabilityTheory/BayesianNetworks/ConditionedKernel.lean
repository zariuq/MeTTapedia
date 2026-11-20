import Mettapedia.ProbabilityTheory.FiniteWeightedExtension
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring

/-!
# Conditioning the rows of an edge kernel

An incoming child likelihood multiplies each entry of the transition
kernel. Its row sum is the message to the parent. The downward pass uses
the normalized scored row and the updated parent mass. These recover the
scored joint even when a parent branch has zero evidence.

For a binary child, the error from using the old rows has a pointwise
variance formula. The sign is determined by the relative likelihoods of
the two child states.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.ConditionedKernel

open FiniteFunctionalExtension FiniteWeightedExtension
open scoped NNReal ENNReal BigOperators

section FiniteEdge

variable {Parent Child : Type*} [Fintype Child]

/-- Multiply an edge kernel by the child-side likelihood. -/
def score (kernel : Parent → Child → ℝ≥0) (likelihood : Child → ℝ≥0) :
    Parent → Child → ℝ≥0 :=
  fun a b => kernel a b * likelihood b

/-- Normalize each supported row. The value on an empty row is zero. -/
noncomputable def normalizeRows (kernel : Parent → Child → ℝ≥0) : Parent → Child → ℝ≥0 :=
  fun a b => kernel a b / rowMass kernel a

theorem normalizeRows_rowMass (kernel : Parent → Child → ℝ≥0) (a : Parent)
    (possible : rowMass kernel a ≠ 0) :
    rowMass (normalizeRows kernel) a = 1 := by
  simp only [rowMass, normalizeRows, ← Finset.sum_div]
  exact div_self possible

theorem rowMass_mul_normalizeRows (kernel : Parent → Child → ℝ≥0) (a : Parent) (b : Child) :
    rowMass kernel a * normalizeRows kernel a b = kernel a b := by
  by_cases possible : rowMass kernel a = 0
  · have bound : kernel a b ≤ rowMass kernel a :=
      Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ b)
    rw [possible, zero_mul]
    exact le_antisymm zero_le (possible ▸ bound)
  · rw [normalizeRows, mul_comm, div_mul_cancel₀ _ possible]

/-- Eliminate the child to obtain the parent message, then attach the
normalized rows. This restores the original weighted joint pointwise. -/
theorem factorize (kernel : Parent → Child → ℝ≥0) (weight : Parent → ℝ≥0) :
    weightedExtend (normalizeRows kernel) (marginalize (weightedExtend kernel weight)) =
      weightedExtend kernel weight := by
  rw [marginalize_weightedExtend]
  funext world
  simp only [weightedExtend, mul_assoc, rowMass_mul_normalizeRows]

/-- Retain the observed parent marginal and attach the unscored rows. -/
noncomputable def reuseUnscoredRows (kernel : Parent → Child → ℝ≥0)
    (likelihood : Child → ℝ≥0) (weight : Parent → ℝ≥0) : Parent × Child → ℝ≥0 :=
  weightedExtend kernel (marginalize (weightedExtend (score kernel likelihood) weight))

theorem reuseUnscoredRows_parentMarginal (kernel : Parent → Child → ℝ≥0)
    (likelihood : Child → ℝ≥0) (weight : Parent → ℝ≥0)
    (normalized : ∀ a, rowMass kernel a = 1) :
    marginalize (reuseUnscoredRows kernel likelihood weight) =
      marginalize (weightedExtend (score kernel likelihood) weight) := by
  rw [reuseUnscoredRows, marginalize_weightedExtend]
  funext a
  simp [normalized]

theorem reuseUnscoredRows_total [Fintype Parent] (kernel : Parent → Child → ℝ≥0)
    (likelihood : Child → ℝ≥0) (weight : Parent → ℝ≥0)
    (normalized : ∀ a, rowMass kernel a = 1) :
    (∑ w, reuseUnscoredRows kernel likelihood weight w) =
      ∑ w, weightedExtend (score kernel likelihood) weight w := by
  simpa only [Fintype.sum_prod_type, marginalize] using
    congrArg (fun marginal : Parent → ℝ≥0 => ∑ a, marginal a)
      (reuseUnscoredRows_parentMarginal kernel likelihood weight normalized)

end FiniteEdge

section BinaryChild

variable {Parent : Type*} [Fintype Parent]

def bernoulli (rate : Parent → ℝ≥0) (a : Parent) (b : Bool) : ℝ≥0 :=
  if b then rate a else 1 - rate a

omit [Fintype Parent] in
theorem bernoulli_rowMass (rate : Parent → ℝ≥0) (a : Parent) (bounded : rate a ≤ 1) :
    rowMass (bernoulli rate) a = 1 := by
  simpa [rowMass, bernoulli, Fintype.sum_bool, add_comm] using tsub_add_cancel_of_le bounded

def trueMass (joint : Parent × Bool → ℝ≥0) : ℝ≥0 :=
  ∑ a, joint (a, true)

/-- A signed numerator defect for reusing the old conditional after an
observation below the child. The common denominator is the evidence mass. -/
theorem trueMass_sub_reuse (rate : Parent → ℝ≥0) (bounded : ∀ a, rate a ≤ 1)
    (likelihood : Bool → ℝ≥0) (weight : Parent → ℝ≥0) :
    (trueMass (weightedExtend (score (bernoulli rate) likelihood) weight) : ℝ) -
      (trueMass (reuseUnscoredRows (bernoulli rate) likelihood weight) : ℝ) =
    ((likelihood true : ℝ) - likelihood false) *
      ∑ a, (weight a : ℝ) * rate a * (1 - rate a) := by
  simp only [trueMass, NNReal.coe_sum, reuseUnscoredRows, marginalize_weightedExtend,
    weightedExtend, NNReal.coe_mul]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [score, bernoulli, rowMass, Fintype.sum_bool, if_true, Bool.false_eq_true,
    if_false, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_sub (bounded a), NNReal.coe_one]
  ring

private theorem weighted_variance_eq_zero_iff (rate : Parent → ℝ≥0) (bounded : ∀ a, rate a ≤ 1)
    (weight : Parent → ℝ≥0) :
    (∑ a, (weight a : ℝ) * rate a * (1 - rate a)) = 0 ↔
      ∀ a, weight a ≠ 0 → rate a = 0 ∨ rate a = 1 := by
  have nonneg : ∀ a, 0 ≤ (weight a : ℝ) * rate a * (1 - rate a) :=
    fun a => mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))
      (sub_nonneg.mpr (by exact_mod_cast bounded a))
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun a _ => nonneg a)]
  constructor
  · intro zero a positive
    have zeroAt := zero a (Finset.mem_univ a)
    rcases mul_eq_zero.mp zeroAt with first | second
    · have realPositive : (weight a : ℝ) ≠ 0 := by exact_mod_cast positive
      have realZero : (rate a : ℝ) = 0 := (mul_eq_zero.mp first).resolve_left realPositive
      exact Or.inl (by exact_mod_cast realZero)
    · have realOne : (rate a : ℝ) = 1 := (sub_eq_zero.mp second).symm
      exact Or.inr (by exact_mod_cast realOne)
  · intro deterministic a _
    by_cases zero : weight a = 0
    · simp [zero]
    · rcases deterministic a zero with h | h <;> simp [h]

/-- With positive evidence mass, the old rows give the exact child
probability precisely for a flat likelihood or deterministic active rows.
The compared joints have the same total mass by parent marginal agreement. -/
theorem trueMass_reuse_eq_iff (rate : Parent → ℝ≥0) (bounded : ∀ a, rate a ≤ 1)
    (likelihood : Bool → ℝ≥0) (weight : Parent → ℝ≥0) :
    trueMass (weightedExtend (score (bernoulli rate) likelihood) weight) =
      trueMass (reuseUnscoredRows (bernoulli rate) likelihood weight) ↔
    likelihood true = likelihood false ∨
      ∀ a, weight a ≠ 0 → rate a = 0 ∨ rate a = 1 := by
  rw [← NNReal.coe_inj, ← sub_eq_zero, trueMass_sub_reuse rate bounded,
    mul_eq_zero, sub_eq_zero, NNReal.coe_inj, weighted_variance_eq_zero_iff rate bounded]

private theorem query_true (joint : Parent × Bool → ℝ≥0)
    (possible : (∑ w, joint w) ≠ 0) :
    (observationMass joint Prod.snd).query id =
      some ((trueMass joint / ∑ w, joint w : ℝ≥0) : ℝ≥0∞) := by
  have numerator :
      (∑ w : Parent × Bool, if w.2 then joint w else 0) = trueMass joint := by
    simp [trueMass, Fintype.sum_prod_type]
  simp only [MassSemantics.query, MassSemantics.queryProb, observationMass, id_eq,
    ENNReal.coe_eq_zero, possible, if_false, numerator, ENNReal.coe_div possible]

/-- The exactness criterion for the normalized WM readout. A globally
impossible observation has no posterior, so the criterion requires support. -/
theorem posterior_reuse_eq_iff (rate : Parent → ℝ≥0) (bounded : ∀ a, rate a ≤ 1)
    (likelihood : Bool → ℝ≥0) (weight : Parent → ℝ≥0)
    (possible : (∑ w, weightedExtend (score (bernoulli rate) likelihood) weight w) ≠ 0) :
    (observationMass (weightedExtend (score (bernoulli rate) likelihood) weight) Prod.snd).query id =
      (observationMass (reuseUnscoredRows (bernoulli rate) likelihood weight) Prod.snd).query id ↔
    likelihood true = likelihood false ∨
      ∀ a, weight a ≠ 0 → rate a = 0 ∨ rate a = 1 := by
  have same := reuseUnscoredRows_total (bernoulli rate) likelihood weight
    (fun a => bernoulli_rowMass rate a (bounded a))
  rw [query_true _ possible, query_true _ (same ▸ possible), same,
    Option.some.injEq, ENNReal.coe_inj]
  rw [← trueMass_reuse_eq_iff rate bounded likelihood weight]
  exact div_left_inj' possible

/-- Positive child-side evidence makes the old-row estimate a lower bound
on the child-true mass. Normalizing uses the same evidence mass. -/
theorem trueMass_reuse_le (rate : Parent → ℝ≥0) (bounded : ∀ a, rate a ≤ 1)
    (likelihood : Bool → ℝ≥0) (favorable : likelihood false ≤ likelihood true)
    (weight : Parent → ℝ≥0) :
    trueMass (reuseUnscoredRows (bernoulli rate) likelihood weight) ≤
      trueMass (weightedExtend (score (bernoulli rate) likelihood) weight) := by
  apply NNReal.coe_le_coe.mp
  apply sub_nonneg.mp
  rw [trueMass_sub_reuse rate bounded]
  exact mul_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr favorable))
    (Finset.sum_nonneg fun a _ =>
      mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))
        (sub_nonneg.mpr (by exact_mod_cast bounded a)))

end BinaryChild

end Mettapedia.ProbabilityTheory.BayesianNetworks.ConditionedKernel
