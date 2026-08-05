import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.RankReachability
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Low-rank adaptation of a frozen linear map

For a frozen weight `base : Output × Input`, low-rank adaptation represents
the trainable update as

`delta = (scale • up) * down`

through an `r`-dimensional bottleneck.  This file connects the operational
forward pass to the already sealed rank-budget reachability theory, proves
exact merge/unmerge and task-switching semantics, and isolates the asymmetric
initialization boundary: with `up = 0` and nonzero `down`, the initial update
is zero and `down` is temporarily invisible, while `up` can still affect the
output on its first update.

The construction recovers Equation (3) and the deployment/initialization
claims of Hu et al., *LoRA: Low-Rank Adaptation of Large Language Models*
(2021).  It does not assert that a task's optimal update is low rank or that a
particular optimizer will discover a useful factorization.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

open Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation

noncomputable section

universe uInput uOutput

variable {Input : Type uInput} {Output : Type uOutput}

/-- Trainable update matrix factored through `Fin rankBudget`.  The scalar
`scale` includes the source's `alpha / rankBudget` factor when desired. -/
def lowRankDelta [Fintype (Fin rankBudget)]
    (scale : ℝ)
    (up : Matrix Output (Fin rankBudget) ℝ)
    (down : Matrix (Fin rankBudget) Input ℝ) :
    Matrix Output Input ℝ :=
  (scale • up) * down

/-- Frozen linear weight with its low-rank update merged for deployment. -/
def mergedLowRankWeight [Fintype (Fin rankBudget)]
    (base : Matrix Output Input ℝ)
    (scale : ℝ)
    (up : Matrix Output (Fin rankBudget) ℝ)
    (down : Matrix (Fin rankBudget) Input ℝ) :
    Matrix Output Input ℝ :=
  base + lowRankDelta scale up down

/-- Training-time parallel forward pass: frozen output plus bottleneck output. -/
def lowRankApply [Fintype Input] [Fintype (Fin rankBudget)]
    (base : Matrix Output Input ℝ)
    (scale : ℝ)
    (up : Matrix Output (Fin rankBudget) ℝ)
    (down : Matrix (Fin rankBudget) Input ℝ)
    (input : Input → ℝ) : Output → ℝ :=
  base.mulVec input + (scale • up).mulVec (down.mulVec input)

/-- Source Equation (3): the parallel training path is exactly multiplication
by the merged deployment weight. -/
theorem lowRankApply_eq_merged_mulVec
    [Fintype Input] [Fintype (Fin rankBudget)]
    (base : Matrix Output Input ℝ)
    (scale : ℝ)
    (up : Matrix Output (Fin rankBudget) ℝ)
    (down : Matrix (Fin rankBudget) Input ℝ)
    (input : Input → ℝ) :
    lowRankApply base scale up down input =
      (mergedLowRankWeight base scale up down).mulVec input := by
  unfold lowRankApply mergedLowRankWeight lowRankDelta
  rw [Matrix.add_mulVec, Matrix.mulVec_mulVec]

/-- Merging and then subtracting the same task update recovers the frozen
weight exactly. -/
theorem mergedLowRankWeight_sub_delta
    [Fintype (Fin rankBudget)]
    (base : Matrix Output Input ℝ)
    (scale : ℝ)
    (up : Matrix Output (Fin rankBudget) ℝ)
    (down : Matrix (Fin rankBudget) Input ℝ) :
    mergedLowRankWeight base scale up down -
        lowRankDelta scale up down =
      base := by
  simp [mergedLowRankWeight]

/-- Deployment task switching can unmerge one adapter and merge another
without changing the shared frozen weight. -/
theorem switchMergedLowRankTask
    [Fintype (Fin firstRank)] [Fintype (Fin secondRank)]
    (base : Matrix Output Input ℝ)
    (firstScale secondScale : ℝ)
    (firstUp : Matrix Output (Fin firstRank) ℝ)
    (firstDown : Matrix (Fin firstRank) Input ℝ)
    (secondUp : Matrix Output (Fin secondRank) ℝ)
    (secondDown : Matrix (Fin secondRank) Input ℝ) :
    mergedLowRankWeight base firstScale firstUp firstDown -
          lowRankDelta firstScale firstUp firstDown +
        lowRankDelta secondScale secondUp secondDown =
      mergedLowRankWeight base secondScale secondUp secondDown := by
  simp [mergedLowRankWeight]

/-! ## Rank budget -/

/-- Every operational low-rank update is reachable through its declared
bottleneck. -/
theorem lowRankDelta_rankBudgetReachable
    [Fintype Input]
    (scale : ℝ)
    (up : Matrix Output (Fin rankBudget) ℝ)
    (down : Matrix (Fin rankBudget) Input ℝ) :
    RankBudgetReachable rankBudget (lowRankDelta scale up down) := by
  exact ⟨scale • up, down, rfl⟩

/-- Consequently, every operational update has matrix rank at most its
bottleneck width. -/
theorem lowRankDelta_rank_le
    [Fintype Output] [Fintype Input] [DecidableEq Input]
    (scale : ℝ)
    (up : Matrix Output (Fin rankBudget) ℝ)
    (down : Matrix (Fin rankBudget) Input ℝ) :
    (lowRankDelta scale up down).rank ≤ rankBudget := by
  exact (rankBudgetReachable_iff_rank_le rankBudget
    (lowRankDelta scale up down)).mp
      (lowRankDelta_rankBudgetReachable scale up down)

/-- Exact expressivity criterion at unit scale: a required update has a
rank-`r` LoRA factorization exactly when its matrix rank is at most `r`. -/
theorem exists_lowRankDelta_one_iff_rank_le
    [Fintype Output] [Fintype Input] [DecidableEq Input]
    (rankBudget : ℕ) (required : Matrix Output Input ℝ) :
    (∃ up : Matrix Output (Fin rankBudget) ℝ,
        ∃ down : Matrix (Fin rankBudget) Input ℝ,
          lowRankDelta 1 up down = required) ↔
      required.rank ≤ rankBudget := by
  simpa [RankBudgetReachable, lowRankDelta] using
    rankBudgetReachable_iff_rank_le rankBudget required

/-- Full input-width budget can represent every update matrix. -/
theorem fullInputWidth_exists_lowRankDelta
    [Fintype Output] [Fintype Input] [DecidableEq Input]
    (required : Matrix Output Input ℝ) :
    ∃ up : Matrix Output (Fin (Fintype.card Input)) ℝ,
      ∃ down : Matrix (Fin (Fintype.card Input)) Input ℝ,
        lowRankDelta 1 up down = required := by
  exact (exists_lowRankDelta_one_iff_rank_le
    (Fintype.card Input) required).mpr required.rank_le_card_width

/-- Rank one cannot represent the two-dimensional identity update. -/
theorem rankOne_lowRankDelta_cannot_equal_identityTwo :
    ¬ ∃ (scale : ℝ)
        (up : Matrix (Fin 2) (Fin 1) ℝ)
        (down : Matrix (Fin 1) (Fin 2) ℝ),
      lowRankDelta scale up down = 1 := by
  rintro ⟨scale, up, down, heq⟩
  have hle := lowRankDelta_rank_le scale up down
  rw [heq, identityMatrixTwo_rank] at hle
  omega

/-! ## Update-zero initialization boundary -/

/-- Zeroing the output factor makes the initial low-rank update exactly zero,
independently of the input factor. -/
@[simp] theorem lowRankDelta_zero_up
    [Fintype (Fin rankBudget)]
    (scale : ℝ)
    (down : Matrix (Fin rankBudget) Input ℝ) :
    lowRankDelta (Output := Output) scale
        (0 : Matrix Output (Fin rankBudget) ℝ) down =
      (0 : Matrix Output Input ℝ) := by
  simp [lowRankDelta]

/-- Zeroing the input factor also makes the update zero. -/
@[simp] theorem lowRankDelta_zero_down
    [Fintype (Fin rankBudget)]
    (scale : ℝ)
    (up : Matrix Output (Fin rankBudget) ℝ) :
    lowRankDelta (Input := Input) scale up
        (0 : Matrix (Fin rankBudget) Input ℝ) =
      (0 : Matrix Output Input ℝ) := by
  simp [lowRankDelta]

/-- At the paper's initialization `up = 0`, the forward result is the frozen
base output and changing `down` is initially unobservable. -/
theorem zeroUp_down_parameter_invisible
    [Fintype Input] [Fintype (Fin rankBudget)]
    (base : Matrix Output Input ℝ)
    (scale : ℝ)
    (firstDown secondDown : Matrix (Fin rankBudget) Input ℝ)
    (input : Input → ℝ) :
    lowRankApply base scale 0 firstDown input =
      lowRankApply base scale 0 secondDown input := by
  simp [lowRankApply]

/-- Symmetric dead boundary: if `down = 0`, changing `up` is unobservable. -/
theorem zeroDown_up_parameter_invisible
    [Fintype Input] [Fintype (Fin rankBudget)]
    (base : Matrix Output Input ℝ)
    (scale : ℝ)
    (firstUp secondUp : Matrix Output (Fin rankBudget) ℝ)
    (input : Input → ℝ) :
    lowRankApply base scale firstUp 0 input =
      lowRankApply base scale secondUp 0 input := by
  simp [lowRankApply]

/-- Positive first-update fixture: a nonzero input factor leaves the zeroed
output factor trainable even though the initial update itself is zero. -/
theorem zeroUp_but_up_direction_live_scalar :
    let base : Matrix Unit Unit ℝ := fun _ _ => 0
    let down : Matrix (Fin 1) Unit ℝ := fun _ _ => 1
    let input : Unit → ℝ := fun _ => 1
    lowRankApply base 1 (fun _ _ => 0) down input = 0 ∧
      lowRankApply base 1 (fun _ _ => 1) down input = 1 := by
  dsimp
  constructor <;>
    funext output <;>
    cases output <;>
    simp [lowRankApply, Matrix.mulVec, dotProduct, Matrix.mul_apply]

/-- At the asymmetric initialization, the scalar output-factor derivative is
exactly one in the live fixture. -/
theorem zeroUp_up_hasDerivAt_scalar :
    let base : Matrix Unit Unit ℝ := fun _ _ => 0
    let down : Matrix (Fin 1) Unit ℝ := fun _ _ => 1
    let input : Unit → ℝ := fun _ => 1
    HasDerivAt
      (fun upValue : ℝ =>
        lowRankApply base 1 (fun _ _ => upValue) down input ())
      1 0 := by
  dsimp
  have hfunction :
      (fun upValue : ℝ =>
        lowRankApply (rankBudget := 1)
          (fun _ : Unit => fun _ : Unit => (0 : ℝ)) 1
          (fun _ : Unit => fun _ : Fin 1 => upValue)
          (fun _ : Fin 1 => fun _ : Unit => 1)
          (fun _ : Unit => 1) ()) =
        id := by
    funext upValue
    simp [lowRankApply, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [hfunction]
  exact hasDerivAt_id (0 : ℝ)

/-- In the same fixture, the scalar input-factor derivative is exactly zero
while the output factor remains zero. -/
theorem zeroUp_down_hasDerivAt_zero_scalar :
    let base : Matrix Unit Unit ℝ := fun _ _ => 0
    let up : Matrix Unit (Fin 1) ℝ := fun _ _ => 0
    let input : Unit → ℝ := fun _ => 1
    HasDerivAt
      (fun downValue : ℝ =>
        lowRankApply base 1 up (fun _ _ => downValue) input ())
      0 0 := by
  simpa [lowRankApply, Matrix.mulVec, dotProduct, Matrix.mul_apply] using
    hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ))

/-- If both factors are zero, neither factor family has a first-order
functional path; this separates the paper's asymmetric initialization from an
all-zero factorization. -/
theorem bothZero_factors_dead_scalar :
    let base : Matrix Unit Unit ℝ := fun _ _ => 0
    let input : Unit → ℝ := fun _ => 1
    (∀ up : Matrix Unit (Fin 1) ℝ,
        lowRankApply base 1 up 0 input = 0) ∧
      (∀ down : Matrix (Fin 1) Unit ℝ,
        lowRankApply base 1 0 down input = 0) := by
  dsimp
  constructor
  · intro up
    funext output
    cases output
    simp [lowRankApply, Matrix.mulVec, dotProduct]
  · intro down
    funext output
    cases output
    simp [lowRankApply, Matrix.mulVec, dotProduct]

/-! ## Trainable parameter count -/

/-- Number of scalar trainable parameters in a dense update matrix. -/
def denseUpdateParameterCount (outputWidth inputWidth : ℕ) : ℕ :=
  outputWidth * inputWidth

/-- Number of scalar trainable parameters in the two low-rank factors. -/
def lowRankParameterCount
    (outputWidth inputWidth rankBudget : ℕ) : ℕ :=
  rankBudget * (outputWidth + inputWidth)

/-- For a square weight, rank below half the width uses strictly fewer
trainable parameters than a dense update. -/
theorem square_lowRankParameterCount_lt_dense
    (width rankBudget : ℕ)
    (hwidth : 0 < width) (hrank : 2 * rankBudget < width) :
    lowRankParameterCount width width rankBudget <
      denseUpdateParameterCount width width := by
  unfold lowRankParameterCount denseUpdateParameterCount
  calc
    rankBudget * (width + width) = (2 * rankBudget) * width := by ring
    _ < width * width := (Nat.mul_lt_mul_right hwidth).mpr hrank

/-- Positive parameter-count fixture from a square width-12,288 layer at
rank eight. -/
theorem width12288_rank8_parameter :
    lowRankParameterCount 12288 12288 8 = 196608 ∧
      denseUpdateParameterCount 12288 12288 = 150994944 := by
  decide

/-- Negative boundary: rank equal to the square width uses twice as many
factor parameters as one dense update. -/
theorem fullWidth_square_parameter_negative :
    lowRankParameterCount 8 8 8 = 128 ∧
      denseUpdateParameterCount 8 8 = 64 := by
  decide

#print axioms lowRankApply_eq_merged_mulVec
#print axioms switchMergedLowRankTask
#print axioms lowRankDelta_rank_le
#print axioms exists_lowRankDelta_one_iff_rank_le
#print axioms fullInputWidth_exists_lowRankDelta
#print axioms rankOne_lowRankDelta_cannot_equal_identityTwo
#print axioms zeroUp_down_parameter_invisible
#print axioms zeroUp_but_up_direction_live_scalar
#print axioms zeroUp_up_hasDerivAt_scalar
#print axioms zeroUp_down_hasDerivAt_zero_scalar
#print axioms bothZero_factors_dead_scalar
#print axioms square_lowRankParameterCount_lt_dense
#print axioms width12288_rank8_parameter
#print axioms fullWidth_square_parameter_negative

end

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
