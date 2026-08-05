import Mettapedia.MachineLearning.NeuralNetworks.Architecture.ScaledDotProductAttention

/-!
# Modern Hopfield retrieval from a finite score margin

Ramsauer et al., *Hopfield Networks is All You Need*
(arXiv:2008.02217), equations (3), (5), and (8), use the update

`X softmax (β Xᵀ ξ)`

and bound one-step retrieval error exponentially in the separation of the
target pattern.  This file isolates a finite deterministic core that applies
to any score function and therefore also to routed associative memories.

A score margin `Δ` makes every off-target softmax weight at most
`exp (-β Δ)`.  Summing this pointwise estimate gives a finite-cardinality
off-target-mass bound and, from it, a coordinatewise retrieval-error bound.
The result is weaker than the source's Euclidean fixed-point theorem but more
general in its scoring rule: it assumes neither spherical random patterns nor
that the target is already near a fixed point.

The boundary fixtures are essential.  Colliding scores return an average
rather than either stored value, and zero inverse temperature erases even a
strict raw-score margin.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace ModernHopfieldRetrieval

open Mettapedia.MachineLearning.NeuralNetworks.Architecture

noncomputable section

variable {Key : Type*}

/-- The scalar-coordinate form of the modern Hopfield update.  Vector-valued
updates are obtained by applying this definition coordinatewise. -/
def modernHopfieldRead [Fintype Key]
    (β : ℝ) (score value : Key → ℝ) : ℝ :=
  ∑ key, attentionWeight (fun item => β * score item) key * value key

/-- Total softmax mass assigned away from a designated target pattern. -/
def offTargetMass [Fintype Key] [DecidableEq Key]
    (β : ℝ) (score : Key → ℝ) (target : Key) : ℝ :=
  ∑ key ∈ (Finset.univ.erase target),
    attentionWeight (fun item => β * score item) key

/-- A score margin gives an exponential pointwise bound on every off-target
softmax weight. -/
theorem attentionWeight_le_exp_neg_margin
    [Fintype Key] [Nonempty Key]
    (β Δ : ℝ) (score : Key → ℝ) (target key : Key)
    (β_nonneg : 0 ≤ β)
    (margin : score key + Δ ≤ score target) :
    attentionWeight (fun item => β * score item) key ≤
      Real.exp (-β * Δ) := by
  have scaledMargin :
      β * score key ≤ β * score target - β * Δ := by
    nlinarith [mul_le_mul_of_nonneg_left margin β_nonneg]
  have expBound :
      Real.exp (β * score key) ≤
        Real.exp (β * score target - β * Δ) :=
    Real.exp_le_exp.mpr scaledMargin
  have targetTerm_le_mass :
      Real.exp (β * score target) ≤
        attentionMass (fun item => β * score item) := by
    unfold attentionMass
    exact Finset.single_le_sum
      (fun item _ => (Real.exp_pos (β * score item)).le)
      (Finset.mem_univ target)
  rw [attentionWeight, div_le_iff₀ (attentionMass_pos _)]
  calc
    Real.exp (β * score key) ≤
        Real.exp (β * score target - β * Δ) := expBound
    _ = Real.exp (-β * Δ) * Real.exp (β * score target) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-β * Δ) *
        attentionMass (fun item => β * score item) :=
      mul_le_mul_of_nonneg_left targetTerm_le_mass
        (Real.exp_pos _).le

/-- The total off-target mass is at most the number of competing patterns
times the exponential margin factor. -/
theorem offTargetMass_le
    [Fintype Key] [Nonempty Key] [DecidableEq Key]
    (β Δ : ℝ) (score : Key → ℝ) (target : Key)
    (β_nonneg : 0 ≤ β)
    (margin :
      ∀ key, key ≠ target → score key + Δ ≤ score target) :
    offTargetMass β score target ≤
      ((Fintype.card Key - 1 : ℕ) : ℝ) * Real.exp (-β * Δ) := by
  unfold offTargetMass
  calc
    ∑ key ∈ Finset.univ.erase target,
        attentionWeight (fun item => β * score item) key
        ≤ ∑ _key ∈ Finset.univ.erase target, Real.exp (-β * Δ) := by
          apply Finset.sum_le_sum
          intro key key_mem
          exact attentionWeight_le_exp_neg_margin β Δ score target key
            β_nonneg (margin key (Finset.ne_of_mem_erase key_mem))
    _ = ((Fintype.card Key - 1 : ℕ) : ℝ) * Real.exp (-β * Δ) := by
      simp

/-- Subtracting the target value from a Hopfield read leaves exactly the
off-target weighted differences. -/
theorem modernHopfieldRead_sub_target
    [Fintype Key] [Nonempty Key] [DecidableEq Key]
    (β : ℝ) (score value : Key → ℝ) (target : Key) :
    modernHopfieldRead β score value - value target =
      ∑ key ∈ Finset.univ.erase target,
        attentionWeight (fun item => β * score item) key *
          (value key - value target) := by
  have weightsSum :
      ∑ key, attentionWeight (fun item => β * score item) key = 1 :=
    sum_attentionWeight_eq_one _
  calc
    modernHopfieldRead β score value - value target =
        (∑ key, attentionWeight (fun item => β * score item) key *
          value key) -
        (∑ key, attentionWeight (fun item => β * score item) key) *
          value target := by
            rw [weightsSum]
            simp [modernHopfieldRead]
    _ = ∑ key,
        attentionWeight (fun item => β * score item) key *
          (value key - value target) := by
            rw [Finset.sum_mul]
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro key _
            ring
    _ = ∑ key ∈ Finset.univ.erase target,
        attentionWeight (fun item => β * score item) key *
          (value key - value target) := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ target)]
            simp

/-- One-step coordinatewise retrieval error is exponentially small in the
score margin. -/
theorem abs_modernHopfieldRead_sub_target_le
    [Fintype Key] [Nonempty Key] [DecidableEq Key]
    (β Δ diameter : ℝ) (score value : Key → ℝ) (target : Key)
    (β_nonneg : 0 ≤ β)
    (diameter_nonneg : 0 ≤ diameter)
    (margin :
      ∀ key, key ≠ target → score key + Δ ≤ score target)
    (valueDiameter :
      ∀ key, |value key - value target| ≤ diameter) :
    |modernHopfieldRead β score value - value target| ≤
      diameter * (((Fintype.card Key - 1 : ℕ) : ℝ) *
        Real.exp (-β * Δ)) := by
  rw [modernHopfieldRead_sub_target]
  calc
    |∑ key ∈ Finset.univ.erase target,
        attentionWeight (fun item => β * score item) key *
          (value key - value target)| ≤
        ∑ key ∈ Finset.univ.erase target,
          |attentionWeight (fun item => β * score item) key *
            (value key - value target)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ key ∈ Finset.univ.erase target,
        attentionWeight (fun item => β * score item) key * diameter := by
          apply Finset.sum_le_sum
          intro key _
          rw [abs_mul, abs_of_pos (attentionWeight_pos _ key)]
          exact mul_le_mul_of_nonneg_left (valueDiameter key)
            (le_of_lt (attentionWeight_pos _ key))
    _ = diameter * offTargetMass β score target := by
      unfold offTargetMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro key _
      ring
    _ ≤ diameter *
        (((Fintype.card Key - 1 : ℕ) : ℝ) * Real.exp (-β * Δ)) :=
      mul_le_mul_of_nonneg_left
        (offTargetMass_le β Δ score target β_nonneg margin)
        diameter_nonneg

/-! ## Executable boundaries -/

def collisionScores : Fin 2 → ℝ := ![0, 0]

def collisionValues : Fin 2 → ℝ := ![0, 2]

/-- Equal scores retrieve the arithmetic mean, not either stored value. -/
theorem equal_score_collision_returns_average :
    modernHopfieldRead 1 collisionScores collisionValues = 1 ∧
      modernHopfieldRead 1 collisionScores collisionValues ≠
        collisionValues 0 ∧
      modernHopfieldRead 1 collisionScores collisionValues ≠
        collisionValues 1 := by
  simp [modernHopfieldRead, collisionScores, collisionValues,
    attentionWeight, attentionMass, Fin.sum_univ_succ]
  norm_num

def strictMarginScores : Fin 2 → ℝ := ![1, 0]

/-- At zero inverse temperature, a strict raw-score margin is erased and the
read is again uniform. -/
theorem zero_temperature_erases_strict_margin :
    strictMarginScores 1 + 1 ≤ strictMarginScores 0 ∧
      modernHopfieldRead 0 strictMarginScores collisionValues = 1 := by
  constructor
  · norm_num [strictMarginScores]
  · simp [modernHopfieldRead, strictMarginScores, collisionValues,
      attentionWeight, attentionMass, Fin.sum_univ_succ]

#print axioms attentionWeight_le_exp_neg_margin
#print axioms offTargetMass_le
#print axioms modernHopfieldRead_sub_target
#print axioms abs_modernHopfieldRead_sub_target_le
#print axioms equal_score_collision_returns_average
#print axioms zero_temperature_erases_strict_margin

end

end ModernHopfieldRetrieval

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
