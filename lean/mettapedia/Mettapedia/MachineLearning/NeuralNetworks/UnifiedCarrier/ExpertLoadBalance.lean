import Mathlib.Tactic

/-!
# Expert-load balance objectives

Sparse mixture-of-experts systems commonly penalize the squared coefficient of
variation of either expert importance or a smooth expert-load estimate.  This
file gives that quantity an exact finite-dimensional semantics and proves the
resource bound it supplies.

For a nonzero mean, zero squared coefficient of variation is equivalent to
perfect balance.  More quantitatively, every expert's squared deviation from
the mean is bounded by expert count times mean squared times the objective.
The hypotheses are necessary: at zero mean the field convention for division
can make an unequal signed vector have zero objective.

Importance balance and token-count balance are separate properties.  A finite
fixture has equal total gate weight for two experts but routes one token to the
first and two tokens to the second, matching the boundary that motivates a
separate load objective.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace ExpertLoadBalance

open scoped BigOperators

noncomputable section

/-! ## Squared coefficient of variation -/

/-- Arithmetic mean over a nonempty finite expert family. -/
def mean {n : ℕ} (load : Fin (n + 1) → ℝ) : ℝ :=
  (∑ expert, load expert) / ((n + 1 : ℕ) : ℝ)

/-- Sum of squared deviations from the expert mean. -/
def squaredDeviationSum {n : ℕ} (load : Fin (n + 1) → ℝ) : ℝ :=
  ∑ expert, (load expert - mean load) ^ 2

/-- Population coefficient of variation squared:
`sum (load - mean)^2 / (expertCount * mean^2)`. -/
def coefficientVariationSq {n : ℕ} (load : Fin (n + 1) → ℝ) : ℝ :=
  squaredDeviationSum load /
    (((n + 1 : ℕ) : ℝ) * (mean load) ^ 2)

/-- The load-balancing penalty used by importance and smooth-load objectives. -/
def balancePenalty {n : ℕ}
    (weight : ℝ) (load : Fin (n + 1) → ℝ) : ℝ :=
  weight * coefficientVariationSq load

theorem mean_const {n : ℕ} (value : ℝ) :
    mean (fun _expert : Fin (n + 1) => value) = value := by
  simp only [
    mean, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul
  ]
  have expertCountNonzero : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  exact mul_div_cancel_left₀ value expertCountNonzero

theorem squaredDeviationSum_nonneg {n : ℕ}
    (load : Fin (n + 1) → ℝ) :
    0 ≤ squaredDeviationSum load := by
  exact Finset.sum_nonneg fun _expert _member => sq_nonneg _

theorem coefficientVariationSq_nonneg {n : ℕ}
    (load : Fin (n + 1) → ℝ) :
    0 ≤ coefficientVariationSq load := by
  apply div_nonneg
  · exact squaredDeviationSum_nonneg load
  · positivity

theorem balancePenalty_nonneg {n : ℕ}
    {weight : ℝ} (load : Fin (n + 1) → ℝ)
    (weightNonnegative : 0 ≤ weight) :
    0 ≤ balancePenalty weight load :=
  mul_nonneg weightNonnegative (coefficientVariationSq_nonneg load)

/-- At nonzero mean, zero coefficient of variation is exactly equal load. -/
theorem coefficientVariationSq_eq_zero_iff {n : ℕ}
    (load : Fin (n + 1) → ℝ)
    (meanNonzero : mean load ≠ 0) :
    coefficientVariationSq load = 0 ↔
      ∀ expert, load expert = mean load := by
  have denominatorNonzero :
      (((n + 1 : ℕ) : ℝ) * (mean load) ^ 2) ≠ 0 := by
    apply mul_ne_zero
    · positivity
    · exact pow_ne_zero 2 meanNonzero
  constructor
  · intro zeroVariation
    have zeroSum : squaredDeviationSum load = 0 :=
      (div_eq_zero_iff.mp zeroVariation).resolve_right denominatorNonzero
    have everySquareZero :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun expert (_member : expert ∈ Finset.univ) =>
          sq_nonneg (load expert - mean load))).mp zeroSum
    intro expert
    have squareZero := everySquareZero expert (Finset.mem_univ expert)
    have differenceZero :
        load expert - mean load = 0 :=
      sq_eq_zero_iff.mp squareZero
    linarith
  · intro balanced
    simp [coefficientVariationSq, squaredDeviationSum, balanced]

/-- With a positive penalty coefficient and nonzero mean, zero penalty still
characterizes perfect expert balance. -/
theorem balancePenalty_eq_zero_iff {n : ℕ}
    {weight : ℝ} (load : Fin (n + 1) → ℝ)
    (weightPositive : 0 < weight)
    (meanNonzero : mean load ≠ 0) :
    balancePenalty weight load = 0 ↔
      ∀ expert, load expert = mean load := by
  rw [balancePenalty, mul_eq_zero]
  simp [ne_of_gt weightPositive, coefficientVariationSq_eq_zero_iff load meanNonzero]

/-- One coordinate's squared deviation is at most the total squared
deviation. -/
theorem coordinate_sq_deviation_le_sum {n : ℕ}
    (load : Fin (n + 1) → ℝ) (expert : Fin (n + 1)) :
    (load expert - mean load) ^ 2 ≤ squaredDeviationSum load := by
  exact Finset.single_le_sum
    (fun candidate _member => sq_nonneg (load candidate - mean load))
    (Finset.mem_univ expert)

theorem squaredDeviationSum_eq_count_mul_mean_sq_mul_cv {n : ℕ}
    (load : Fin (n + 1) → ℝ)
    (meanNonzero : mean load ≠ 0) :
    squaredDeviationSum load =
      (((n + 1 : ℕ) : ℝ) * (mean load) ^ 2) *
        coefficientVariationSq load := by
  rw [coefficientVariationSq]
  field_simp

/-- A small coefficient-of-variation objective supplies an explicit
per-expert overload certificate. -/
theorem coordinate_sq_deviation_le_count_mul_mean_sq_mul_cv {n : ℕ}
    (load : Fin (n + 1) → ℝ) (expert : Fin (n + 1))
    (meanNonzero : mean load ≠ 0) :
    (load expert - mean load) ^ 2 ≤
      (((n + 1 : ℕ) : ℝ) * (mean load) ^ 2) *
        coefficientVariationSq load := by
  rw [← squaredDeviationSum_eq_count_mul_mean_sq_mul_cv load meanNonzero]
  exact coordinate_sq_deviation_le_sum load expert

/-! ## Required boundaries and routing fixtures -/

def zeroMeanUnequal : Fin 2 → ℝ := ![1, -1]

/-- The nonzero-mean premise is real over signed vectors: Lean's field
division convention gives this unequal zero-mean vector a zero objective. -/
theorem zeroMeanUnequal_boundary :
    mean zeroMeanUnequal = 0 ∧
      coefficientVariationSq zeroMeanUnequal = 0 ∧
      zeroMeanUnequal 0 ≠ zeroMeanUnequal 1 := by
  have zeroMean : mean zeroMeanUnequal = 0 := by
    rw [mean, Fin.sum_univ_two]
    norm_num [zeroMeanUnequal]
  constructor
  · exact zeroMean
  constructor
  · simp [coefficientVariationSq, zeroMean]
  · norm_num [zeroMeanUnequal]

/-- Batchwise total gate weight assigned to an expert. -/
def importance
    {Token Expert : Type*} [Fintype Token]
    (gate : Token → Expert → ℝ) (expert : Expert) : ℝ :=
  ∑ token, gate token expert

/-- Number of tokens with a strictly positive gate for an expert. -/
def hardLoad
    {Token Expert : Type*} [Fintype Token] [DecidableEq Token]
    (gate : Token → Expert → ℝ) (expert : Expert) : ℕ :=
  (Finset.univ.filter fun token => 0 < gate token expert).card

/-- Expert zero receives one unit-weight token.  Expert one receives two
half-weight tokens. -/
def equalImportanceUnequalLoadGate
    (token : Fin 3) (expert : Fin 2) : ℝ :=
  if expert = 0 then
    if token = 0 then 1 else 0
  else
    if token = 0 then 0 else (1 : ℝ) / 2

theorem equalImportanceUnequalLoad :
    importance equalImportanceUnequalLoadGate 0 = 1 ∧
      importance equalImportanceUnequalLoadGate 1 = 1 ∧
      hardLoad equalImportanceUnequalLoadGate 0 = 1 ∧
      hardLoad equalImportanceUnequalLoadGate 1 = 2 := by
  have two_ne_zero : (2 : Fin 3) ≠ 0 := by decide
  have loadZero :
      (Finset.univ.filter fun token : Fin 3 =>
        0 < equalImportanceUnequalLoadGate token 0) = {0} := by
    ext token
    fin_cases token <;> norm_num [equalImportanceUnequalLoadGate]
  have loadOne :
      (Finset.univ.filter fun token : Fin 3 =>
        0 < equalImportanceUnequalLoadGate token 1) =
          Finset.univ.erase 0 := by
    ext token
    fin_cases token <;> norm_num [equalImportanceUnequalLoadGate]
  rw [show importance equalImportanceUnequalLoadGate 0 = 1 by
    norm_num [
      importance, equalImportanceUnequalLoadGate,
      Fin.sum_univ_three, two_ne_zero
    ]]
  rw [show importance equalImportanceUnequalLoadGate 1 = 1 by
    norm_num [
      importance, equalImportanceUnequalLoadGate,
      Fin.sum_univ_three, two_ne_zero
    ]]
  simp [hardLoad, loadZero, loadOne]

/-- Equal importance therefore does not imply equal token count. -/
theorem equal_importance_does_not_imply_equal_hardLoad :
    importance equalImportanceUnequalLoadGate 0 =
        importance equalImportanceUnequalLoadGate 1 ∧
      hardLoad equalImportanceUnequalLoadGate 0 ≠
        hardLoad equalImportanceUnequalLoadGate 1 := by
  obtain ⟨importanceZero, importanceOne, loadZero, loadOne⟩ :=
    equalImportanceUnequalLoad
  constructor
  · rw [importanceZero, importanceOne]
  · rw [loadZero, loadOne]
    norm_num

#print axioms coefficientVariationSq_eq_zero_iff
#print axioms balancePenalty_eq_zero_iff
#print axioms coordinate_sq_deviation_le_count_mul_mean_sq_mul_cv
#print axioms zeroMeanUnequal_boundary
#print axioms equalImportanceUnequalLoad
#print axioms equal_importance_does_not_imply_equal_hardLoad

end

end ExpertLoadBalance

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
