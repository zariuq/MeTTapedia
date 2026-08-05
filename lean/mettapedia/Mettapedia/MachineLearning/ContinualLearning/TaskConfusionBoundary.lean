import Mathlib

/-!
# Task-confusion loss decompositions

Nori, Kim, Kim, and Yun,
*Task Confusion and Catastrophic Forgetting in Class-Incremental Learning:
A Mathematical Framework for Discriminative and Generative Modelings*
(2024, arXiv:2410.20768), Lemmas 1--3 and Theorems 1--2, decompose
class-incremental objectives into within-task and between-task losses.

This file isolates three exact boundaries in that framework.

First, Equation (2) as printed sums ordered pairs `k ≠ l` but uses the
normalization for unordered pairs.  When a pair loss is the sum of its two
disjoint class contributions, the printed expression is exactly twice the
original loss.  Dividing by `2 * (N - 1)` repairs the ordered-pair formula.

Second, the source's derivative incompatibility premise really does exclude
either individual minimizer from minimizing the summed objective.

Third, a block-diagonal generative objective is equal to its diagonal
objective, so a parameter that simultaneously minimizes every diagonal block
is globally optimal.  Block diagonality alone does not establish that such a
shared parameter exists: two scalar blocks can have incompatible minimizers.

No theorem below claims that empirical class losses are differentiable, that
their minimizers exist, that class supports are disjoint, or that a
generative model prevents forgetting in practice.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace TaskConfusionBoundary

noncomputable section

open scoped BigOperators

variable {Class Parameter : Type*}

/-! ## Ordered pair normalization -/

variable [Fintype Class] [DecidableEq Class]

/-- Sum of the two class contributions over every ordered distinct pair. -/
def orderedPairLoss (classLoss : Class → ℝ) : ℝ :=
  ∑ first : Class, ∑ second ∈ Finset.univ.erase first,
    (classLoss first + classLoss second)

/-- Each row of the ordered-pair loss contains its fixed class contribution
once for every other class, plus every other class contribution once. -/
theorem orderedPairLoss_row
    (classLoss : Class → ℝ) (first : Class) :
    (∑ second ∈ Finset.univ.erase first,
        (classLoss first + classLoss second)) =
      (Fintype.card Class - 1 : ℕ) * classLoss first +
        ((∑ second : Class, classLoss second) - classLoss first) := by
  rw [Finset.sum_add_distrib]
  simp

/-- The ordered-pair expression counts every class contribution twice for
each of the other classes. -/
theorem orderedPairLoss_eq
    (classLoss : Class → ℝ) :
    orderedPairLoss classLoss =
      2 * ((Fintype.card Class - 1 : ℕ) : ℝ) *
        ∑ label : Class, classLoss label := by
  by_cases inhabited : Nonempty Class
  · letI := inhabited
    unfold orderedPairLoss
    simp_rw [orderedPairLoss_row]
    rw [Finset.sum_add_distrib]
    rw [← Finset.mul_sum]
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_const]
    simp only [nsmul_eq_mul]
    rw [Finset.card_univ]
    have card_decomposition_nat :
        Fintype.card Class - 1 + 1 = Fintype.card Class :=
      Nat.sub_add_cancel Fintype.card_pos
    have card_decomposition :
        ((Fintype.card Class - 1 : ℕ) : ℝ) + 1 =
          (Fintype.card Class : ℝ) := by
      exact_mod_cast card_decomposition_nat
    rw [← card_decomposition]
    ring
  · letI : IsEmpty Class := ⟨fun label => inhabited ⟨label⟩⟩
    simp [orderedPairLoss]

/-- The normalization printed for the ordered-pair sum is a factor of two
too large. -/
theorem printed_ordered_normalization_eq_twice
    (classLoss : Class → ℝ)
    (at_least_two : 2 ≤ Fintype.card Class) :
    (1 / ((Fintype.card Class - 1 : ℕ) : ℝ)) *
        orderedPairLoss classLoss =
      2 * ∑ label : Class, classLoss label := by
  rw [orderedPairLoss_eq]
  have denominator_pos :
      0 < ((Fintype.card Class - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt
      (lt_of_lt_of_le Nat.one_lt_two at_least_two)
  field_simp

/-- Repair for an ordered-pair presentation: divide by twice the number of
other classes. -/
theorem corrected_ordered_normalization
    (classLoss : Class → ℝ)
    (at_least_two : 2 ≤ Fintype.card Class) :
    (1 / (2 * ((Fintype.card Class - 1 : ℕ) : ℝ))) *
        orderedPairLoss classLoss =
      ∑ label : Class, classLoss label := by
  rw [orderedPairLoss_eq]
  have denominator_pos :
      0 < ((Fintype.card Class - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt
      (lt_of_lt_of_le Nat.one_lt_two at_least_two)
  field_simp

/-- Two classes already expose the factor-of-two error. -/
theorem printed_two_class :
    let classLoss : Bool → ℝ := fun
      | false => 3
      | true => 5
    (1 / ((Fintype.card Bool - 1 : ℕ) : ℝ)) *
        orderedPairLoss classLoss = 16 ∧
      (∑ label : Bool, classLoss label) = 8 := by
  norm_num [orderedPairLoss]

/-! ## Incompatible differentiable objectives -/

/-- A global minimizer, stated without choosing an `argmin`. -/
def IsGlobalMin (objective : Parameter → ℝ) (point : Parameter) : Prop :=
  ∀ candidate, objective point ≤ objective candidate

theorem IsGlobalMin.isLocalMin
    {Point : Type*} [TopologicalSpace Point]
    {objective : Point → ℝ} {point : Point}
    (minimum : IsGlobalMin objective point) :
    IsLocalMin objective point :=
  Filter.Eventually.of_forall minimum

/-- A nonzero cross derivative at an individual minimizer excludes that
point from minimizing the sum.  This is the exact differentiable core of
the source's incompatibility lemma. -/
theorem crossDerivative_excludes_sum_minimizer
    {first second : ℝ → ℝ}
    {point firstDerivative secondDerivative : ℝ}
    (first_minimum : IsGlobalMin first point)
    (first_derivative :
      HasDerivAt first firstDerivative point)
    (second_derivative :
      HasDerivAt second secondDerivative point)
    (cross_nonzero : secondDerivative ≠ 0) :
    ¬ IsGlobalMin (fun x => first x + second x) point := by
  intro sum_minimum
  have first_zero :
      firstDerivative = 0 :=
    first_minimum.isLocalMin.hasDerivAt_eq_zero first_derivative
  have sum_zero :
      firstDerivative + secondDerivative = 0 :=
    sum_minimum.isLocalMin.hasDerivAt_eq_zero
      (first_derivative.add second_derivative)
  apply cross_nonzero
  linarith

/-- With the source's symmetric nonzero-cross-gradient premises, neither
individual minimizer minimizes the sum. -/
theorem incompatible_minimizers_excluded_from_sum
    {first second : ℝ → ℝ}
    {firstPoint secondPoint
      firstAtFirst secondAtFirst
      firstAtSecond secondAtSecond : ℝ}
    (first_minimum : IsGlobalMin first firstPoint)
    (second_minimum : IsGlobalMin second secondPoint)
    (first_derivative_at_first :
      HasDerivAt first firstAtFirst firstPoint)
    (second_derivative_at_first :
      HasDerivAt second secondAtFirst firstPoint)
    (first_derivative_at_second :
      HasDerivAt first firstAtSecond secondPoint)
    (second_derivative_at_second :
      HasDerivAt second secondAtSecond secondPoint)
    (second_cross_nonzero : secondAtFirst ≠ 0)
    (first_cross_nonzero : firstAtSecond ≠ 0) :
    ¬ IsGlobalMin (fun x => first x + second x) firstPoint ∧
      ¬ IsGlobalMin (fun x => first x + second x) secondPoint := by
  constructor
  · exact crossDerivative_excludes_sum_minimizer
      first_minimum first_derivative_at_first
      second_derivative_at_first second_cross_nonzero
  · simpa [add_comm] using
      crossDerivative_excludes_sum_minimizer
        second_minimum second_derivative_at_second
        first_derivative_at_second first_cross_nonzero

/-! ## Conditional feasibility of block-diagonal objectives -/

variable {Task : Type*} [Fintype Task]

/-- Sum of the within-task loss blocks. -/
def diagonalObjective
    (withinTask : Task → Parameter → ℝ)
    (parameter : Parameter) : ℝ :=
  ∑ task : Task, withinTask task parameter

/-- Total class-incremental loss split into within-task loss and inter-task
confusion loss. -/
def totalObjective
    (withinTask : Task → Parameter → ℝ)
    (confusion : Parameter → ℝ)
    (parameter : Parameter) : ℝ :=
  diagonalObjective withinTask parameter + confusion parameter

/-- A common minimizer of every diagonal block minimizes their sum. -/
theorem simultaneous_block_minimum_minimizes_diagonal
    (withinTask : Task → Parameter → ℝ)
    (point : Parameter)
    (each_minimum :
      ∀ task, IsGlobalMin (withinTask task) point) :
    IsGlobalMin (diagonalObjective withinTask) point := by
  intro candidate
  unfold diagonalObjective
  exact Finset.sum_le_sum fun task _ => each_minimum task candidate

/-- Conditional form of the source's feasibility theorem: if confusion is
identically zero and one parameter simultaneously minimizes every diagonal
block, that parameter minimizes the total objective. -/
theorem zero_confusion_and_simultaneous_minima_are_globally_optimal
    (withinTask : Task → Parameter → ℝ)
    (confusion : Parameter → ℝ)
    (point : Parameter)
    (confusion_zero : ∀ parameter, confusion parameter = 0)
    (each_minimum :
      ∀ task, IsGlobalMin (withinTask task) point) :
    IsGlobalMin (totalObjective withinTask confusion) point := by
  intro candidate
  simp only [totalObjective, confusion_zero, add_zero]
  exact simultaneous_block_minimum_minimizes_diagonal
    withinTask point each_minimum candidate

/-- Two block-diagonal scalar losses with incompatible minimizers. -/
def incompatibleGenerativeBlocks : Bool → ℝ → ℝ
  | false, x => x ^ 2
  | true, x => (x - 1) ^ 2

theorem first_generating_block_minimum :
    IsGlobalMin (incompatibleGenerativeBlocks false) 0 := by
  intro candidate
  simp [incompatibleGenerativeBlocks, sq_nonneg]

theorem second_generating_block_minimum :
    IsGlobalMin (incompatibleGenerativeBlocks true) 1 := by
  intro candidate
  simp [incompatibleGenerativeBlocks, sq_nonneg]

theorem first_generating_block_unique_minimum
    {point : ℝ}
    (minimum :
      IsGlobalMin (incompatibleGenerativeBlocks false) point) :
    point = 0 := by
  have bound := minimum 0
  simp only [incompatibleGenerativeBlocks] at bound
  nlinarith [sq_nonneg point]

theorem second_generating_block_unique_minimum
    {point : ℝ}
    (minimum :
      IsGlobalMin (incompatibleGenerativeBlocks true) point) :
    point = 1 := by
  have bound := minimum 1
  simp only [incompatibleGenerativeBlocks] at bound
  nlinarith [sq_nonneg (point - 1)]

/-- Block diagonality alone does not produce a parameter that minimizes all
generative blocks simultaneously. -/
theorem block_diagonal_does_not_imply_simultaneous_minimizer :
    ¬ ∃ point : ℝ,
      ∀ task : Bool,
        IsGlobalMin (incompatibleGenerativeBlocks task) point := by
  rintro ⟨point, minimum⟩
  have first_zero :=
    first_generating_block_unique_minimum (minimum false)
  have second_one :=
    second_generating_block_unique_minimum (minimum true)
  linarith

/-! ## Concrete discriminative task-confusion boundary -/

def diagonalFixture (x : ℝ) : ℝ := x ^ 2

def confusionFixture (x : ℝ) : ℝ := (x - 1) ^ 2

theorem diagonalFixture_minimum :
    IsGlobalMin diagonalFixture 0 := by
  intro candidate
  simp [diagonalFixture, sq_nonneg]

/-- A diagonal-loss optimum need not minimize the total objective once an
off-diagonal confusion term is present. -/
theorem diagonal_optimum_not_total_optimum :
    ¬ IsGlobalMin
      (fun x => diagonalFixture x + confusionFixture x) 0 := by
  intro minimum
  have bound := minimum (1 / 2)
  norm_num [diagonalFixture, confusionFixture] at bound

#print axioms orderedPairLoss_eq
#print axioms printed_ordered_normalization_eq_twice
#print axioms corrected_ordered_normalization
#print axioms crossDerivative_excludes_sum_minimizer
#print axioms incompatible_minimizers_excluded_from_sum
#print axioms zero_confusion_and_simultaneous_minima_are_globally_optimal
#print axioms block_diagonal_does_not_imply_simultaneous_minimizer
#print axioms diagonal_optimum_not_total_optimum

end

end TaskConfusionBoundary

end Mettapedia.MachineLearning.ContinualLearning
