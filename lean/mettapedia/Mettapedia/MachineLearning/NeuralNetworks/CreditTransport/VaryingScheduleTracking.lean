import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FixedPointSensitivity

/-!
# Tracking under a varying settling schedule

Continuation solvers need not use one contraction factor or one settling
budget at every parameter change.  This file records each transition
explicitly and proves the resulting finite-time tracking convolution.  A
drift incurred early is attenuated by its own settling stage and every later
stage; consequently, equal total work and equal total drift do not make two
schedules interchangeable.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace VaryingScheduleTracking

open AmortizedInitialization
open LocalAmortizedInitialization
open ParameterTracking
open FixedPointSensitivity

variable {Parameter State : Type*} [NormedAddCommGroup State]

/-- One continuation transition: the next solver parameter, its declared
number of settling steps, and an upper bound on fixed-point drift. -/
structure TrackingStage (Parameter : Type*) where
  next : Parameter
  steps : ℕ
  driftBound : ℝ

/-- The finite-time attenuation contributed by one stage. -/
noncomputable def stageAttenuation
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (family : LocalSolverFamily solver target radius)
    (stage : TrackingStage Parameter) : ℝ :=
  (family.certificate stage.next).factor ^ stage.steps

/-- The scalar error budget after one admitted stage. -/
noncomputable def advanceBudget
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (family : LocalSolverFamily solver target radius)
    (error : ℝ) (stage : TrackingStage Parameter) : ℝ :=
  stageAttenuation family stage * (error + stage.driftBound)

/-- Execute every declared settling stage in order. -/
def runSchedule
    (solver : Parameter → State → State) :
    State → List (TrackingStage Parameter) → State
  | state, [] => state
  | state, stage :: stages =>
      runSchedule solver ((solver stage.next)^[stage.steps] state) stages

/-- Parameter whose fixed point is tracked after the whole schedule. -/
def finalParameter :
    Parameter → List (TrackingStage Parameter) → Parameter
  | previous, [] => previous
  | _, stage :: stages => finalParameter stage.next stages

/-- Recursively propagate the certified scalar tracking budget. -/
noncomputable def scheduleBudget
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (family : LocalSolverFamily solver target radius) :
    ℝ → List (TrackingStage Parameter) → ℝ
  | error, [] => error
  | error, stage :: stages =>
      scheduleBudget family (advanceBudget family error stage) stages

/-- Product of all stage attenuations. -/
noncomputable def scheduleAttenuation
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (family : LocalSolverFamily solver target radius) :
    List (TrackingStage Parameter) → ℝ
  | [] => 1
  | stage :: stages =>
      stageAttenuation family stage * scheduleAttenuation family stages

/-- Exact drift convolution.  The drift at the head is attenuated by the
head stage and by every stage that follows it. -/
noncomputable def scheduleDriftConvolution
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (family : LocalSolverFamily solver target radius) :
    List (TrackingStage Parameter) → ℝ
  | [] => 0
  | stage :: stages =>
      stageAttenuation family stage *
          scheduleAttenuation family stages * stage.driftBound +
        scheduleDriftConvolution family stages

/-- Total declared drift, retained only to state the order-sensitivity
boundary below.  It is not a valid replacement for the convolution. -/
def scheduleDriftTotal (stages : List (TrackingStage Parameter)) : ℝ :=
  (stages.map TrackingStage.driftBound).sum

/-- Exact algebraic decomposition of a varying schedule into attenuated
initial error and the time-ordered drift convolution. -/
theorem scheduleBudget_eq_attenuation_mul_add_convolution
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (family : LocalSolverFamily solver target radius)
    (error : ℝ) (stages : List (TrackingStage Parameter)) :
    scheduleBudget family error stages =
      scheduleAttenuation family stages * error +
        scheduleDriftConvolution family stages := by
  induction stages generalizing error with
  | nil =>
      simp [scheduleBudget, scheduleAttenuation, scheduleDriftConvolution]
  | cons stage stages ih =>
      rw [scheduleBudget, ih]
      simp only [advanceBudget, scheduleAttenuation,
        scheduleDriftConvolution]
      ring

/-- Attenuations compose multiplicatively when schedules are concatenated. -/
theorem scheduleAttenuation_append
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (family : LocalSolverFamily solver target radius)
    (first second : List (TrackingStage Parameter)) :
    scheduleAttenuation family (first ++ second) =
      scheduleAttenuation family first * scheduleAttenuation family second := by
  induction first with
  | nil => simp [scheduleAttenuation]
  | cons stage stages ih =>
      simp [scheduleAttenuation, ih]
      ring

/-- Earlier drift is attenuated by the complete later schedule. -/
theorem scheduleDriftConvolution_append
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (family : LocalSolverFamily solver target radius)
    (first second : List (TrackingStage Parameter)) :
    scheduleDriftConvolution family (first ++ second) =
      scheduleAttenuation family second *
          scheduleDriftConvolution family first +
        scheduleDriftConvolution family second := by
  induction first with
  | nil => simp [scheduleDriftConvolution]
  | cons stage stages ih =>
      simp only [List.cons_append, scheduleDriftConvolution,
        scheduleAttenuation_append, ih]
      ring

/-- Every transition must bound its target drift and fit the inherited
error plus that drift to the next solver's certified neighborhood. -/
noncomputable def ScheduleAdmissible
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (family : LocalSolverFamily solver target radius) :
    Parameter → ℝ → List (TrackingStage Parameter) → Prop
  | _, _, [] => True
  | previous, error, stage :: stages =>
      ‖target previous - target stage.next‖ ≤ stage.driftBound ∧
      error + stage.driftBound ≤ radius ∧
      ScheduleAdmissible family stage.next
        (advanceBudget family error stage) stages

/-- The executable solver run stays within the recursively computed varying-
schedule budget. -/
theorem runSchedule_tracking_le
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (family : LocalSolverFamily solver target radius)
    (previous : Parameter) (state : State) (error : ℝ)
    (stages : List (TrackingStage Parameter))
    (herror : ‖state - target previous‖ ≤ error)
    (hadmissible : ScheduleAdmissible family previous error stages) :
    ‖runSchedule solver state stages -
        target (finalParameter previous stages)‖ ≤
      scheduleBudget family error stages := by
  induction stages generalizing previous state error with
  | nil => simpa [runSchedule, finalParameter, scheduleBudget] using herror
  | cons stage stages ih =>
      rcases hadmissible with ⟨hdrift, hadmission, htail⟩
      have hhead :
          ‖(solver stage.next)^[stage.steps] state - target stage.next‖ ≤
            advanceBudget family error stage := by
        simpa [advanceBudget, stageAttenuation] using
          parameterized_iterate_tracking_le family previous stage.next state
            error stage.driftBound herror hdrift hadmission stage.steps
      exact ih stage.next ((solver stage.next)^[stage.steps] state)
        (advanceBudget family error stage) hhead htail

/-! ## Sensitivity-derived stages -/

/-- Package a raw solver-change bound as the fixed-point drift budget supplied
by the inverse contraction margin. -/
noncomputable def solverChangeStage
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (family : LocalSolverFamily solver target radius)
    (next : Parameter) (steps : ℕ) (solverChange : ℝ) :
    TrackingStage Parameter where
  next := next
  steps := steps
  driftBound :=
    solverChange / (1 - (family.certificate next).factor)

/-- Local fixed-point sensitivity constructs an admissible schedule head from
a bound on the solver-map change. -/
theorem scheduleAdmissible_cons_of_solverChange
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (family : LocalSolverFamily solver target radius)
    (previous next : Parameter) (error solverChange : ℝ) (steps : ℕ)
    (stages : List (TrackingStage Parameter))
    (hpreviousMem :
      InClosedBall (target next) radius (target previous))
    (hsolverChange :
      ‖solver previous (target previous) -
          solver next (target previous)‖ ≤ solverChange)
    (hadmission :
      error + solverChange / (1 - (family.certificate next).factor) ≤
        radius)
    (htail :
      ScheduleAdmissible family next
        (advanceBudget family error
          (solverChangeStage family next steps solverChange)) stages) :
    ScheduleAdmissible family previous error
      (solverChangeStage family next steps solverChange :: stages) := by
  have hdenominator :
      0 ≤ 1 - (family.certificate next).factor := by
    linarith [(family.certificate next).factor_lt_one]
  have hdrift :
      ‖target previous - target next‖ ≤
        solverChange / (1 - (family.certificate next).factor) :=
    le_trans
      (local_target_drift_le_solver_change_div family previous next
        hpreviousMem)
      (div_le_div_of_nonneg_right hsolverChange hdenominator)
  exact ⟨hdrift, hadmission, htail⟩

/-! ## Executable positive and negative fixtures -/

noncomputable def shiftedHalfTwoStageSchedule :
    List (TrackingStage ℝ) :=
  [ { next := 1 / 4, steps := 1, driftBound := 1 / 4 },
    { next := 1 / 2, steps := 2, driftBound := 1 / 4 } ]

theorem shiftedHalfTwoStageSchedule_admissible :
    ScheduleAdmissible shiftedHalfFamily 0 0
      shiftedHalfTwoStageSchedule := by
  norm_num [ScheduleAdmissible, shiftedHalfTwoStageSchedule,
    advanceBudget, stageAttenuation, shiftedHalfFamily, Real.norm_eq_abs]

theorem shiftedHalfTwoStageSchedule_run_exact :
    runSchedule shiftedHalfSolver 0 shiftedHalfTwoStageSchedule = 13 / 32 := by
  norm_num [runSchedule, shiftedHalfTwoStageSchedule, shiftedHalfSolver,
    Function.iterate_succ_apply]

theorem shiftedHalfTwoStageSchedule_budget_exact :
    scheduleBudget shiftedHalfFamily 0 shiftedHalfTwoStageSchedule = 3 / 32 := by
  norm_num [scheduleBudget, shiftedHalfTwoStageSchedule, advanceBudget,
    stageAttenuation, shiftedHalfFamily]

/-- The bound is attained by the two-stage affine fixture. -/
theorem shiftedHalfTwoStageSchedule_error_exact :
    ‖runSchedule shiftedHalfSolver 0 shiftedHalfTwoStageSchedule -
        (fun target : ℝ => target)
          (finalParameter 0 shiftedHalfTwoStageSchedule)‖ =
      scheduleBudget shiftedHalfFamily 0 shiftedHalfTwoStageSchedule := by
  norm_num [runSchedule, finalParameter, scheduleBudget,
    shiftedHalfTwoStageSchedule, shiftedHalfSolver, advanceBudget,
    stageAttenuation, shiftedHalfFamily, Function.iterate_succ_apply,
    Real.norm_eq_abs]

noncomputable def earlyDriftSchedule : List (TrackingStage ℝ) :=
  [ { next := 0, steps := 1, driftBound := 1 },
    { next := 0, steps := 2, driftBound := 0 } ]

noncomputable def lateDriftSchedule : List (TrackingStage ℝ) :=
  [ { next := 0, steps := 2, driftBound := 0 },
    { next := 0, steps := 1, driftBound := 1 } ]

/-- Equal total drift and equal total attenuation do not determine the final
tracking budget: placing the drift earlier gives later stages time to remove
more of it. -/
theorem drift_convolution_is_order_sensitive :
    scheduleDriftTotal earlyDriftSchedule =
        scheduleDriftTotal lateDriftSchedule ∧
      scheduleAttenuation shiftedHalfFamily earlyDriftSchedule =
        scheduleAttenuation shiftedHalfFamily lateDriftSchedule ∧
      scheduleDriftConvolution shiftedHalfFamily earlyDriftSchedule = 1 / 8 ∧
      scheduleDriftConvolution shiftedHalfFamily lateDriftSchedule = 1 / 2 := by
  norm_num [scheduleDriftTotal, earlyDriftSchedule, lateDriftSchedule,
    scheduleAttenuation, scheduleDriftConvolution, stageAttenuation,
    shiftedHalfFamily]

noncomputable def shiftedHalfTooFastSchedule : List (TrackingStage ℝ) :=
  [ { next := -1 / 2, steps := 1, driftBound := 1 / 2 } ]

/-- A schedule whose inherited error plus target drift exceeds the certified
radius is rejected before its local contraction theorem can be applied. -/
theorem shiftedHalfTooFastSchedule_not_admissible :
    ¬ ScheduleAdmissible shiftedHalfFamily 0 (3 / 4)
      shiftedHalfTooFastSchedule := by
  norm_num [ScheduleAdmissible, shiftedHalfTooFastSchedule,
    shiftedHalfFamily, Real.norm_eq_abs]

#print axioms scheduleBudget_eq_attenuation_mul_add_convolution
#print axioms scheduleAttenuation_append
#print axioms scheduleDriftConvolution_append
#print axioms runSchedule_tracking_le
#print axioms scheduleAdmissible_cons_of_solverChange
#print axioms shiftedHalfTwoStageSchedule_error_exact
#print axioms drift_convolution_is_order_sensitive
#print axioms shiftedHalfTooFastSchedule_not_admissible

end VaryingScheduleTracking

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
