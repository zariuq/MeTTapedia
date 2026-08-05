import Mathlib

/-!
# Linear mode-connectivity objectives and their boundaries

Mirzadeh et al., *Linear Mode Connectivity in Multitask and Continual
Learning* (ICLR 2021, arXiv:2010.04495), measure losses along straight
parameter-space segments and optimize a finite-grid approximation to a
two-task path objective in Equations 3--5.

This file separates three facts.

* Convexity of a loss on parameter space is sufficient for endpoint loss
  bounds to control the complete linear segment.
* Low endpoint losses alone are not sufficient without such a shape
  hypothesis: a scalar polynomial has zero endpoint loss and unit midpoint
  loss.
* A finite path objective is an aggregate.  Even when it has a unique
  minimizer, that point need not minimize either task loss separately.  A
  symmetric two-task quadratic gives an executable counterexample to the
  source's informal sentence after Equation 4 that the aggregate minimizer
  "should minimize both" task losses.

The finite-grid algebra is exact and reusable for arbitrary real vector
spaces.  It does not establish that neural-network loss is convex, that two
trained minima are linearly connected, that sampled quadrature approximates
the source integral to a declared tolerance, or that MC-SGD improves
continual-learning performance.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace ModeConnectivityObjective

noncomputable section

/-! ## Linear paths -/

/-- Point at interpolation coordinate `t` on the straight segment from `a`
to `b`. -/
def segmentPoint
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (a b : E) (t : ℝ) : E :=
  (1 - t) • a + t • b

@[simp] theorem segmentPoint_zero
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (a b : E) :
    segmentPoint a b 0 = a := by
  simp [segmentPoint]

@[simp] theorem segmentPoint_one
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (a b : E) :
    segmentPoint a b 1 = b := by
  simp [segmentPoint]

/-- A convex loss lies below the affine interpolation of its endpoint
losses. -/
theorem convexOn_univ_segmentPoint_le
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (loss : E → ℝ) (a b : E) (t : ℝ)
    (loss_convex : ConvexOn ℝ Set.univ loss)
    (t_nonnegative : 0 ≤ t)
    (t_at_most_one : t ≤ 1) :
    loss (segmentPoint a b t) ≤
      (1 - t) * loss a + t * loss b := by
  have weights_sum : (1 - t) + t = (1 : ℝ) := by
    ring
  simpa [segmentPoint, smul_eq_mul] using
    loss_convex.2 (Set.mem_univ a) (Set.mem_univ b)
      (sub_nonneg.mpr t_at_most_one) t_nonnegative weights_sum

/-- Under convexity, a common endpoint budget controls every point of the
complete segment. -/
theorem convexOn_univ_segmentPoint_le_endpointBudget
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (loss : E → ℝ) (a b : E) (t budget : ℝ)
    (loss_convex : ConvexOn ℝ Set.univ loss)
    (t_nonnegative : 0 ≤ t)
    (t_at_most_one : t ≤ 1)
    (loss_a_le : loss a ≤ budget)
    (loss_b_le : loss b ≤ budget) :
    loss (segmentPoint a b t) ≤ budget := by
  calc
    loss (segmentPoint a b t) ≤
        (1 - t) * loss a + t * loss b :=
      convexOn_univ_segmentPoint_le loss a b t loss_convex
        t_nonnegative t_at_most_one
    _ ≤ budget := by
      nlinarith

/-! ## Finite-grid objective -/

/-- Sum a loss over a declared finite interpolation grid. -/
def discretePathLoss
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (loss : E → ℝ) (anchor candidate : E) (grid : List ℝ) : ℝ :=
  (grid.map fun t => loss (segmentPoint anchor candidate t)).sum

/-- A grid written explicitly as zero, interior coordinates, and one
decomposes into the two endpoint losses plus the interior penalty. -/
theorem discretePathLoss_zero_cons_append_one
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (loss : E → ℝ) (anchor candidate : E) (interior : List ℝ) :
    discretePathLoss loss anchor candidate (0 :: interior ++ [1]) =
      loss anchor +
        discretePathLoss loss anchor candidate interior +
        loss candidate := by
  simp [discretePathLoss, segmentPoint, add_assoc]

/-! ## A complete scalar audit of the aggregate objective -/

/-- First scalar task, minimized at zero. -/
def firstQuadraticTaskLoss (w : ℝ) : ℝ :=
  w ^ 2

/-- Second scalar task, minimized at two. -/
def secondQuadraticTaskLoss (w : ℝ) : ℝ :=
  (w - 2) ^ 2

/-- Sum of squared interpolation coordinates in a finite grid. -/
def squaredGridWeight (grid : List ℝ) : ℝ :=
  (grid.map fun t => t ^ 2).sum

/-- Two-task finite path loss from each task's own minimizer to the common
candidate. -/
def twoTaskDiscretePathObjective (grid : List ℝ) (w : ℝ) : ℝ :=
  discretePathLoss firstQuadraticTaskLoss 0 w grid +
    discretePathLoss secondQuadraticTaskLoss 2 w grid

/-- Closed form of the symmetric two-task path objective. -/
def quadraticTwoTaskPathObjective (weight w : ℝ) : ℝ :=
  weight * (firstQuadraticTaskLoss w + secondQuadraticTaskLoss w)

/-- Every finite grid reduces the scalar two-task path objective to its
squared-coordinate weight times the endpoint aggregate. -/
theorem twoTaskDiscretePathObjective_eq_weighted
    (grid : List ℝ) (w : ℝ) :
    twoTaskDiscretePathObjective grid w =
      quadraticTwoTaskPathObjective (squaredGridWeight grid) w := by
  induction grid with
  | nil =>
      simp [twoTaskDiscretePathObjective, discretePathLoss,
        squaredGridWeight, quadraticTwoTaskPathObjective]
  | cons t ts ih =>
      simp only [twoTaskDiscretePathObjective, discretePathLoss,
        List.map_cons, List.sum_cons, squaredGridWeight,
        quadraticTwoTaskPathObjective] at ih ⊢
      dsimp [firstQuadraticTaskLoss, secondQuadraticTaskLoss,
        segmentPoint] at ih ⊢
      nlinarith

/-- Completion of the square exposes the unique aggregate optimum. -/
theorem quadraticTwoTaskPathObjective_eq
    (weight w : ℝ) :
    quadraticTwoTaskPathObjective weight w =
      2 * weight * (w - 1) ^ 2 + 2 * weight := by
  simp only [quadraticTwoTaskPathObjective, firstQuadraticTaskLoss,
    secondQuadraticTaskLoss]
  ring

/-- At every positive grid weight, the aggregate path objective is minimized
at the midpoint. -/
theorem quadraticTwoTaskPathObjective_one_le
    {weight : ℝ}
    (weight_pos : 0 < weight)
    (w : ℝ) :
    quadraticTwoTaskPathObjective weight 1 ≤
      quadraticTwoTaskPathObjective weight w := by
  rw [quadraticTwoTaskPathObjective_eq,
    quadraticTwoTaskPathObjective_eq]
  nlinarith [sq_nonneg (w - 1)]

/-- The aggregate midpoint is the unique minimizer when the grid has positive
squared-coordinate weight. -/
theorem quadraticTwoTaskPathObjective_eq_one_iff
    {weight w : ℝ}
    (weight_pos : 0 < weight) :
    quadraticTwoTaskPathObjective weight w =
        quadraticTwoTaskPathObjective weight 1 ↔
      w = 1 := by
  rw [quadraticTwoTaskPathObjective_eq,
    quadraticTwoTaskPathObjective_eq]
  constructor
  · intro equal_value
    have square_zero : (w - 1) ^ 2 = 0 := by
      nlinarith
    nlinarith [sq_nonneg (w - 1)]
  · intro w_eq
    subst w
    rfl

/-- The grid `[0,1]` has positive weight, so its aggregate optimum is one;
nevertheless zero is strictly better for task one and two is strictly better
for task two.  Minimizing the aggregate therefore does not imply minimizing
either component. -/
theorem aggregate_minimizer_not_component_minimizer :
    squaredGridWeight [0, 1] = 1 ∧
      (∀ w : ℝ,
        twoTaskDiscretePathObjective [0, 1] 1 ≤
          twoTaskDiscretePathObjective [0, 1] w) ∧
      firstQuadraticTaskLoss 0 < firstQuadraticTaskLoss 1 ∧
      secondQuadraticTaskLoss 2 < secondQuadraticTaskLoss 1 := by
  constructor
  · norm_num [squaredGridWeight]
  constructor
  · intro w
    rw [twoTaskDiscretePathObjective_eq_weighted,
      twoTaskDiscretePathObjective_eq_weighted]
    norm_num [squaredGridWeight]
    exact quadraticTwoTaskPathObjective_one_le (by norm_num) w
  · norm_num [firstQuadraticTaskLoss, secondQuadraticTaskLoss]

/-! ## Nonconvex endpoint boundary -/

/-- A scalar barrier with zero endpoint loss and unit midpoint loss. -/
def nonconvexBarrierLoss (w : ℝ) : ℝ :=
  4 * w * (1 - w)

/-- Endpoint quality alone does not certify the intervening linear path. -/
theorem lowEndpoints_highMidpoint :
    nonconvexBarrierLoss 0 = 0 ∧
      nonconvexBarrierLoss 1 = 0 ∧
      nonconvexBarrierLoss ((1 : ℝ) / 2) = 1 ∧
      nonconvexBarrierLoss ((1 : ℝ) / 2) >
        max (nonconvexBarrierLoss 0) (nonconvexBarrierLoss 1) := by
  norm_num [nonconvexBarrierLoss]

/-- The barrier fixture fails the convexity premise used by the positive
segment theorem. -/
theorem nonconvexBarrierLoss_not_convexOn_univ :
    ¬ ConvexOn ℝ Set.univ nonconvexBarrierLoss := by
  intro barrier_convex
  have midpoint_le :
      nonconvexBarrierLoss
          (segmentPoint (0 : ℝ) 1 ((1 : ℝ) / 2)) ≤ 0 :=
    convexOn_univ_segmentPoint_le_endpointBudget
      nonconvexBarrierLoss (0 : ℝ) 1 ((1 : ℝ) / 2) 0
      barrier_convex (by norm_num) (by norm_num)
      (by norm_num [nonconvexBarrierLoss])
      (by norm_num [nonconvexBarrierLoss])
  norm_num [segmentPoint, nonconvexBarrierLoss] at midpoint_le

end

end ModeConnectivityObjective

end Mettapedia.MachineLearning.ContinualLearning
