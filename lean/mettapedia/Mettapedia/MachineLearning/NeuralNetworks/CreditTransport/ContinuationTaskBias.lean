import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PrimalDualContinuation

/-!
# Task-loss bounds for released constraints

This file turns penalized optimality into a task-relevant statement without
calling the raw task value of an infeasible state an optimality gap.  The
comparison is instead made after an explicit feasibility repair.  A task
lower bound controls the residual, repair regularity converts residual into
state displacement, and task regularity converts displacement into a feasible
task-loss bound.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace ContinuationTaskBias

variable {State Residual : Type*} [NormedAddCommGroup Residual]

/-- Task loss plus a quadratic residual penalty. -/
noncomputable def penalizedValue
    (task : State → ℝ) (residual : State → Residual)
    (penalty : ℝ) (state : State) : ℝ :=
  task state + penalty / 2 * ‖residual state‖ ^ 2

/-- Comparing a penalized minimizer with any feasible point removes the
feasible point's penalty exactly. -/
theorem penalizedValue_le_feasibleTask
    (task : State → ℝ) (residual : State → Residual)
    (penalty : ℝ) (released feasible : State)
    (hcomparison :
      penalizedValue task residual penalty released ≤
        penalizedValue task residual penalty feasible)
    (hfeasible : residual feasible = 0) :
    penalizedValue task residual penalty released ≤ task feasible := by
  simpa [penalizedValue, hfeasible] using hcomparison

/-- A positive quadratic penalty and a lower bound on the task value control
the squared residual of the released minimizer. -/
theorem residual_norm_sq_le_of_task_lowerBound
    (task : State → ℝ) (residual : State → Residual)
    (penalty lowerBound : ℝ) (released feasible : State)
    (hpenalty : 0 < penalty)
    (hlower : lowerBound ≤ task released)
    (hcomparison :
      penalizedValue task residual penalty released ≤
        penalizedValue task residual penalty feasible)
    (hfeasible : residual feasible = 0) :
    ‖residual released‖ ^ 2 ≤
      2 * (task feasible - lowerBound) / penalty := by
  have hvalue := penalizedValue_le_feasibleTask task residual penalty
    released feasible hcomparison hfeasible
  rw [penalizedValue] at hvalue
  apply (le_div_iff₀ hpenalty).2
  nlinarith

/-- The repaired point has a nonnegative constrained-optimality gap and an
upper bound proportional to the actual residual of the released point. -/
theorem feasibleRepair_taskGap_le_actualResidual
    [PseudoMetricSpace State]
    (task : State → ℝ) (residual : State → Residual)
    (repair : State → State) (penalty repairFactor taskFactor : ℝ)
    (released feasible : State)
    (hpenalty : 0 ≤ penalty)
    (htaskFactor : 0 ≤ taskFactor)
    (hcomparison :
      penalizedValue task residual penalty released ≤
        penalizedValue task residual penalty feasible)
    (hfeasible : residual feasible = 0)
    (hfeasibleMin : ∀ state, residual state = 0 → task feasible ≤ task state)
    (hrepairFeasible : residual (repair released) = 0)
    (hrepairDistance :
      dist (repair released) released ≤ repairFactor * ‖residual released‖)
    (htaskRepair :
      task (repair released) ≤
        task released + taskFactor * dist (repair released) released) :
    0 ≤ task (repair released) - task feasible ∧
      task (repair released) - task feasible ≤
        taskFactor * repairFactor * ‖residual released‖ := by
  have hvalue := penalizedValue_le_feasibleTask task residual penalty
    released feasible hcomparison hfeasible
  rw [penalizedValue] at hvalue
  have hpenaltyTerm :
      0 ≤ penalty / 2 * ‖residual released‖ ^ 2 := by positivity
  have hreleasedTask : task released ≤ task feasible := by linarith
  have hdistanceScaled :
      taskFactor * dist (repair released) released ≤
        taskFactor * (repairFactor * ‖residual released‖) :=
    mul_le_mul_of_nonneg_left hrepairDistance htaskFactor
  constructor
  · linarith [hfeasibleMin (repair released) hrepairFeasible]
  · calc
      task (repair released) - task feasible ≤
          taskFactor * dist (repair released) released := by linarith
      _ ≤ taskFactor * (repairFactor * ‖residual released‖) :=
        hdistanceScaled
      _ = taskFactor * repairFactor * ‖residual released‖ := by ring

/-- Square-root version of the feasible-repair task bound.  All four
ingredients remain visible: penalized comparison, task lower boundedness,
repair regularity, and task regularity. -/
theorem feasibleRepair_taskGap_le_sqrt
    [PseudoMetricSpace State]
    (task : State → ℝ) (residual : State → Residual)
    (repair : State → State)
    (penalty lowerBound repairFactor taskFactor : ℝ)
    (released feasible : State)
    (hpenalty : 0 < penalty)
    (hrepairFactor : 0 ≤ repairFactor)
    (htaskFactor : 0 ≤ taskFactor)
    (hlower : lowerBound ≤ task released)
    (hcomparison :
      penalizedValue task residual penalty released ≤
        penalizedValue task residual penalty feasible)
    (hfeasible : residual feasible = 0)
    (hfeasibleMin : ∀ state, residual state = 0 → task feasible ≤ task state)
    (hrepairFeasible : residual (repair released) = 0)
    (hrepairDistance :
      dist (repair released) released ≤ repairFactor * ‖residual released‖)
    (htaskRepair :
      task (repair released) ≤
        task released + taskFactor * dist (repair released) released) :
    0 ≤ task (repair released) - task feasible ∧
      task (repair released) - task feasible ≤
        taskFactor * repairFactor *
          Real.sqrt (2 * (task feasible - lowerBound) / penalty) := by
  have hgap := feasibleRepair_taskGap_le_actualResidual task residual repair
    penalty repairFactor taskFactor released feasible (le_of_lt hpenalty)
    htaskFactor hcomparison hfeasible hfeasibleMin hrepairFeasible
    hrepairDistance htaskRepair
  have hresidualSq := residual_norm_sq_le_of_task_lowerBound task residual
    penalty lowerBound released feasible hpenalty hlower hcomparison hfeasible
  have hboundNonneg :
      0 ≤ 2 * (task feasible - lowerBound) / penalty :=
    le_trans (sq_nonneg ‖residual released‖) hresidualSq
  have hresidualLe :
      ‖residual released‖ ≤
        Real.sqrt (2 * (task feasible - lowerBound) / penalty) := by
    have hsqrtSq := Real.sq_sqrt hboundNonneg
    have hsqrtNonneg := Real.sqrt_nonneg
      (2 * (task feasible - lowerBound) / penalty)
    nlinarith [norm_nonneg (residual released)]
  refine ⟨hgap.1, le_trans hgap.2 ?_⟩
  exact mul_le_mul_of_nonneg_left hresidualLe
    (mul_nonneg htaskFactor hrepairFactor)

/-! ## Analytic two-state positive fixture -/

noncomputable def twoStateTask (state : ℝ × ℝ) : ℝ :=
  ((state.1 + state.2 - 1) ^ 2 + state.1 ^ 2) / 2

noncomputable def twoStateResidual (state : ℝ × ℝ) : ℝ := state.2

noncomputable def twoStateRepair (state : ℝ × ℝ) : ℝ × ℝ :=
  (state.1, 0)

noncomputable def twoStateFeasible : ℝ × ℝ := (1 / 2, 0)

noncomputable def twoStateReleased : ℝ × ℝ := (2 / 5, 1 / 5)

/-- The released state is the global minimizer of the penalty-two objective. -/
theorem twoStateReleased_globalMinimizer (state : ℝ × ℝ) :
    penalizedValue twoStateTask twoStateResidual 2 twoStateReleased ≤
      penalizedValue twoStateTask twoStateResidual 2 state := by
  have hfirst := sq_nonneg
    ((state.1 - 2 / 5) + (state.2 - 1 / 5) / 2)
  have hsecond := sq_nonneg (state.2 - 1 / 5)
  simp [penalizedValue, twoStateTask, twoStateResidual, twoStateReleased]
  nlinarith

/-- The declared feasible state minimizes the task over the exact constraint. -/
theorem twoStateFeasible_taskMinimizer
    (state : ℝ × ℝ) (hfeasible : twoStateResidual state = 0) :
    twoStateTask twoStateFeasible ≤ twoStateTask state := by
  rcases state with ⟨x, y⟩
  simp [twoStateResidual] at hfeasible
  subst y
  have hsquare := sq_nonneg (x - 1 / 2)
  simp [twoStateTask, twoStateFeasible]
  nlinarith

theorem twoStateReleased_values :
    twoStateTask twoStateReleased = 4 / 25 ∧
      twoStateTask (twoStateRepair twoStateReleased) = 13 / 50 ∧
      twoStateTask twoStateFeasible = 1 / 4 ∧
      ‖twoStateResidual twoStateReleased‖ = 1 / 5 := by
  norm_num [twoStateTask, twoStateReleased, twoStateRepair,
    twoStateFeasible, twoStateResidual, Real.norm_eq_abs]

/-- The raw infeasible task value is below the constrained optimum, while the
repaired feasible point has the positive task gap `1/100`. -/
theorem twoState_rawLower_repairedPositiveGap :
    twoStateTask twoStateReleased < twoStateTask twoStateFeasible ∧
      twoStateTask (twoStateRepair twoStateReleased) -
        twoStateTask twoStateFeasible = 1 / 100 := by
  norm_num [twoStateTask, twoStateReleased, twoStateRepair, twoStateFeasible]

theorem twoState_feasibleRepair_sqrt_certificate :
    0 ≤ twoStateTask (twoStateRepair twoStateReleased) -
        twoStateTask twoStateFeasible ∧
      twoStateTask (twoStateRepair twoStateReleased) -
          twoStateTask twoStateFeasible ≤
        (1 / 2 : ℝ) * 1 *
          Real.sqrt
            (2 * (twoStateTask twoStateFeasible - 0) / 2) := by
  apply feasibleRepair_taskGap_le_sqrt twoStateTask twoStateResidual
    twoStateRepair 2 0 1 (1 / 2) twoStateReleased twoStateFeasible
  · norm_num
  · norm_num
  · norm_num
  · norm_num [twoStateTask, twoStateReleased]
  · exact twoStateReleased_globalMinimizer twoStateFeasible
  · norm_num [twoStateResidual, twoStateFeasible]
  · exact twoStateFeasible_taskMinimizer
  · norm_num [twoStateResidual, twoStateRepair, twoStateReleased]
  · norm_num [twoStateRepair, twoStateReleased, twoStateResidual,
      Prod.dist_eq, Real.dist_eq, Prod.norm_def, Real.norm_eq_abs]
  · norm_num [twoStateTask, twoStateRepair, twoStateReleased,
      Prod.dist_eq, Real.dist_eq, Prod.norm_def, Real.norm_eq_abs]

/-! ## Necessity fixtures -/

noncomputable def softTask (state : ℝ) : ℝ := (state - 1) ^ 2 / 2

noncomputable def softEnergy (state : ℝ) : ℝ := softTask state + state ^ 2

noncomputable def softEnergyGradient (state : ℝ) : ℝ := 3 * state - 1

noncomputable def softEnergyQuarterStep (state : ℝ) : ℝ :=
  state - (1 / 4) * softEnergyGradient state

/-- A finite step decreases the soft energy while strictly increasing the
task loss, so soft-energy descent is not a task-descent certificate. -/
theorem softEnergy_descent_task_ascent :
    softEnergy (softEnergyQuarterStep (1 / 2)) < softEnergy (1 / 2) ∧
      softTask (1 / 2) < softTask (softEnergyQuarterStep (1 / 2)) := by
  norm_num [softEnergy, softTask, softEnergyQuarterStep, softEnergyGradient]

noncomputable def cancellationTask (state : ℝ) : ℝ := -(state ^ 2)

noncomputable def cancellationResidual (state : ℝ) : ℝ := state

/-- Without a task lower bound, the negative task can cancel the entire
quadratic penalty, leaving minimizers with arbitrary residual. -/
theorem cancellation_penalizedValue_constant (state : ℝ) :
    penalizedValue cancellationTask cancellationResidual 2 state = 0 := by
  simp [penalizedValue, cancellationTask, cancellationResidual,
    Real.norm_eq_abs, sq_abs]

theorem penalty_optimality_without_lowerBound_no_residual_control :
    penalizedValue cancellationTask cancellationResidual 2 100 =
        penalizedValue cancellationTask cancellationResidual 2 0 ∧
      ‖cancellationResidual 0‖ < ‖cancellationResidual 100‖ := by
  norm_num [cancellation_penalizedValue_constant, cancellationResidual,
    Real.norm_eq_abs]

noncomputable def scaledResidual (scale state : ℝ) : ℝ := state / scale

theorem scaledResidual_eq_zero_iff
    (scale state : ℝ) (hscale : scale ≠ 0) :
    scaledResidual scale state = 0 ↔ state = 0 := by
  simp [scaledResidual, hscale]

/-- Residual magnitude alone cannot control distance to feasibility uniformly:
for every positive scale, the state `scale` has unit residual but lies
`scale` units from the unique feasible point. -/
theorem scaledResidual_unit_with_unbounded_repairDistance
    (scale : ℝ) (hscale : 0 < scale) :
    ‖scaledResidual scale scale‖ = 1 ∧
      dist scale 0 = scale := by
  rw [show scaledResidual scale scale = 1 by
    simp [scaledResidual, ne_of_gt hscale]]
  simp [abs_of_pos hscale]

#print axioms penalizedValue_le_feasibleTask
#print axioms residual_norm_sq_le_of_task_lowerBound
#print axioms feasibleRepair_taskGap_le_actualResidual
#print axioms feasibleRepair_taskGap_le_sqrt
#print axioms twoStateReleased_globalMinimizer
#print axioms twoState_feasibleRepair_sqrt_certificate
#print axioms twoState_rawLower_repairedPositiveGap
#print axioms softEnergy_descent_task_ascent
#print axioms penalty_optimality_without_lowerBound_no_residual_control
#print axioms scaledResidual_unit_with_unbounded_repairDistance

end ContinuationTaskBias

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
