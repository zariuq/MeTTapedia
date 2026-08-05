import Mathlib.Tactic

/-!
# Operation-weighted continual-learning budgets

Prabhu et al., *Computationally Budgeted Continual Learning: What Does
Matter?* (CVPR 2023, arXiv:2303.11165), Section 2.2 and Appendix C, compare
continual-learning methods under a fixed computation budget. Their accounting
reduces the iteration count for methods with auxiliary forward work:
distillation receives approximately two thirds as many training iterations,
and costly sample selection receives one half.

This file separates the exact finite arithmetic from the paper's empirical
accuracy conclusions. A method iteration has declared primary and auxiliary
work in one common integer unit. Division gives the greatest affordable
iteration count when total per-iteration work is positive. In the source's
half-baseline unit, a baseline iteration costs two, distillation costs three,
and costly sampling costs four. Thus the displayed ratios are exact on
divisible budgets. On a baseline budget of one hundred iterations, however,
rounding two thirds to sixty-seven slightly exceeds the exact declared budget;
sixty-six is the greatest affordable integer count.

The same arithmetic exposes a second boundary when a fixed total budget is
split across stream steps: the allocated work is exact precisely when the
step count divides the total. These results do not prove that iteration
counts equal wall-clock time or hardware work, nor do they imply any ordering
of classifier accuracy. Runtime comparisons must measure the declared work
units or independently validate their cost model.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace ComputeBudgetNormalization

/-- Declared work for one method iteration, expressed in a common integer
unit. `primaryWork` covers the ordinary training action; `auxiliaryWork`
covers method-specific operations such as teacher or selection forwards. -/
structure IterationCost where
  primaryWork : ℕ
  auxiliaryWork : ℕ
  deriving DecidableEq, Repr

/-- Total declared work of one iteration. -/
def workPerIteration (profile : IterationCost) : ℕ :=
  profile.primaryWork + profile.auxiliaryWork

/-- Total declared work of a finite number of method iterations. -/
def methodWork (profile : IterationCost) (iterations : ℕ) : ℕ :=
  iterations * workPerIteration profile

/-- Greatest iteration count affordable by integer division. The maximality
theorem below requires positive per-iteration work. -/
def affordableIterations (budget : ℕ) (profile : IterationCost) : ℕ :=
  budget / workPerIteration profile

/-- The integer-division allocation never exceeds its budget. -/
theorem affordableIterations_work_le
    (budget : ℕ) (profile : IterationCost) :
    methodWork profile (affordableIterations budget profile) ≤ budget := by
  simpa [methodWork, affordableIterations, mul_comm] using
    Nat.div_mul_le_self budget (workPerIteration profile)

/-- With positive work per iteration, integer division gives the greatest
affordable iteration count. -/
theorem affordableIterations_maximal
    (budget iterations : ℕ) (profile : IterationCost)
    (work_pos : 0 < workPerIteration profile)
    (affordable : methodWork profile iterations ≤ budget) :
    iterations ≤ affordableIterations budget profile := by
  rw [affordableIterations, Nat.le_div_iff_mul_le work_pos]
  simpa [methodWork] using affordable

/-- Equal iteration counts need not mean equal compute when one method has
auxiliary work. -/
theorem equal_iterations_not_equal_work
    (iterations : ℕ) (iterations_pos : 0 < iterations)
    (left right : IterationCost)
    (work_lt : workPerIteration left < workPerIteration right) :
    methodWork left iterations < methodWork right iterations := by
  unfold methodWork
  exact Nat.mul_lt_mul_of_pos_left work_lt iterations_pos

/-! ## The source's declared operation ratios -/

/-- One baseline iteration costs two half-baseline units. -/
def baselineCost : IterationCost where
  primaryWork := 2
  auxiliaryWork := 0

/-- One distillation iteration adds one half-baseline unit for the teacher
forward, for a total cost of three. -/
def distillationCost : IterationCost where
  primaryWork := 2
  auxiliaryWork := 1

/-- The source's aggregate accounting for costly selection assigns two
additional half-baseline units per selected training iteration. -/
def costlySamplingCost : IterationCost where
  primaryWork := 2
  auxiliaryWork := 2

/-- The two-thirds distillation ratio is exactly equal-work when the baseline
iteration count is a multiple of three. -/
theorem distillation_two_thirds_exact (blocks : ℕ) :
    methodWork baselineCost (3 * blocks) =
      methodWork distillationCost (2 * blocks) := by
  simp [methodWork, workPerIteration, baselineCost, distillationCost]
  omega

/-- The one-half costly-sampling ratio is exactly equal-work on every even
baseline iteration count. -/
theorem costlySampling_one_half_exact (blocks : ℕ) :
    methodWork baselineCost (2 * blocks) =
      methodWork costlySamplingCost blocks := by
  simp [methodWork, workPerIteration, baselineCost, costlySamplingCost]
  ring

/-- At the paper's one-hundred-iteration baseline scale, sixty-six is the
greatest distillation count within the exact integer budget. Rounding to
sixty-seven spends one additional half-baseline unit. -/
theorem distillation_rounding_boundary_at_one_hundred :
    affordableIterations
        (methodWork baselineCost 100) distillationCost = 66 ∧
      methodWork distillationCost 66 = 198 ∧
      methodWork baselineCost 100 = 200 ∧
      methodWork distillationCost 67 = 201 ∧
      methodWork baselineCost 100 <
        methodWork distillationCost 67 := by
  norm_num [affordableIterations, methodWork, workPerIteration,
    baselineCost, distillationCost]

/-- The source's costly-sampling half ratio is exact at the same scale. -/
theorem costlySampling_half_exact_at_one_hundred :
    affordableIterations
        (methodWork baselineCost 100) costlySamplingCost = 50 ∧
      methodWork costlySamplingCost 50 =
        methodWork baselineCost 100 := by
  norm_num [affordableIterations, methodWork, workPerIteration,
    baselineCost, costlySamplingCost]

/-- A zero-work profile defeats the interpretation of integer division as an
affordability maximum: division returns zero although every iteration count
has zero declared cost. Hence positive work is load-bearing. -/
def zeroIterationCost : IterationCost where
  primaryWork := 0
  auxiliaryWork := 0

theorem zero_work_profile_has_no_finite_affordability_maximum
    (budget : ℕ) :
    affordableIterations budget zeroIterationCost = 0 ∧
      ∀ iterations, methodWork zeroIterationCost iterations ≤ budget := by
  simp [affordableIterations, methodWork, workPerIteration,
    zeroIterationCost]

/-! ## Splitting a total budget across stream steps -/

/-- Integer per-step budget obtained from a fixed total budget. -/
def perStepBudget (totalBudget streamSteps : ℕ) : ℕ :=
  totalBudget / streamSteps

/-- Total work actually allocated after integer division across all steps. -/
def allocatedAcrossSteps (totalBudget streamSteps : ℕ) : ℕ :=
  streamSteps * perStepBudget totalBudget streamSteps

/-- Integer allocation across steps never spends more than the total budget. -/
theorem allocatedAcrossSteps_le
    (totalBudget streamSteps : ℕ) :
    allocatedAcrossSteps totalBudget streamSteps ≤ totalBudget := by
  simpa [allocatedAcrossSteps, perStepBudget, mul_comm] using
    Nat.div_mul_le_self totalBudget streamSteps

/-- For a positive number of stream steps, the complete total is allocated
exactly iff the step count divides the total budget. -/
theorem allocatedAcrossSteps_eq_iff_dvd
    (totalBudget streamSteps : ℕ) (steps_pos : 0 < streamSteps) :
    allocatedAcrossSteps totalBudget streamSteps = totalBudget ↔
      streamSteps ∣ totalBudget := by
  constructor
  · intro allocated_eq
    rw [Nat.dvd_iff_mod_eq_zero]
    have division := Nat.mod_add_div totalBudget streamSteps
    unfold allocatedAcrossSteps perStepBudget at allocated_eq
    omega
  · rintro ⟨blocks, rfl⟩
    simp [allocatedAcrossSteps, perStepBudget, steps_pos.ne']

/-- The 8,000-iteration horizon in the source divides exactly across each of
its 20-, 50-, and 200-step schedules. -/
theorem source_horizon_allocations_exact :
    perStepBudget 8000 20 = 400 ∧
      perStepBudget 8000 50 = 160 ∧
      perStepBudget 8000 200 = 40 ∧
      allocatedAcrossSteps 8000 20 = 8000 ∧
      allocatedAcrossSteps 8000 50 = 8000 ∧
      allocatedAcrossSteps 8000 200 = 8000 := by
  norm_num [perStepBudget, allocatedAcrossSteps]

/-- Nondivisible horizons leave a remainder; matching the nominal total
requires recording that remainder rather than silently assigning it. -/
theorem nondivisible_horizon_leaves_unallocated_work :
    perStepBudget 10 3 = 3 ∧
      allocatedAcrossSteps 10 3 = 9 ∧
      allocatedAcrossSteps 10 3 < 10 := by
  norm_num [perStepBudget, allocatedAcrossSteps]

#print axioms affordableIterations_work_le
#print axioms affordableIterations_maximal
#print axioms equal_iterations_not_equal_work
#print axioms distillation_two_thirds_exact
#print axioms costlySampling_one_half_exact
#print axioms distillation_rounding_boundary_at_one_hundred
#print axioms costlySampling_half_exact_at_one_hundred
#print axioms zero_work_profile_has_no_finite_affordability_maximum
#print axioms allocatedAcrossSteps_eq_iff_dvd
#print axioms source_horizon_allocations_exact
#print axioms nondivisible_horizon_leaves_unallocated_work

end ComputeBudgetNormalization

end Mettapedia.MachineLearning.ContinualLearning
