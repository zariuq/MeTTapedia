import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.InexactForwardBackward

/-!
# Time-varying inexact contraction schedules

Schmidt, Le Roux, and Bach, *Convergence Rates of Inexact
Proximal-Gradient Methods for Convex Optimization* (2011), Proposition 3,
exhibits the central error-transport law for a strongly convex inexact
proximal-gradient iteration: errors injected at different iterations carry
different geometric weights.  Consequently, a decreasing error schedule can
retain a linear rate, while a persistent error generally cannot converge to
the exact solution.

This file isolates and generalizes that transport law from proximal-gradient
coordinates to an arbitrary contractive credit solver.  Each scheduled stage
has its own approximate map and certified uniform error.  The resulting
finite theorem separates initializer error from a chronological weighted
error budget, composes exactly across schedule chunks, and includes closed
algebraic laws for geometric and resonant error schedules.

The theorem is deliberately conditional on a contraction certificate and
uniform stagewise approximation.  It does not infer either condition from an
unmeasured neural settling loop.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace InexactContractionSchedule

open AmortizedInitialization
open InexactForwardBackward

noncomputable section

variable {State : Type*} [NormedAddCommGroup State]

/-! ## Proof-carrying chronological schedules -/

/-- One approximate solver stage, with its own nonnegative uniform error. -/
structure Stage (exact : State → State) where
  approximate : State → State
  error : ℝ
  error_nonneg : 0 ≤ error
  approximates : UniformApproximation exact approximate error

/-- Execute scheduled maps in list order. -/
def runSchedule (exact : State → State) :
    List (Stage exact) → State → State
  | [], state => state
  | stage :: rest, state =>
      runSchedule exact rest (stage.approximate state)

/-- Chronological contraction weighting.  The first error is contracted by
every later stage, whereas the last error is not contracted again. -/
def weightedErrorBudget (factor : ℝ) : List ℝ → ℝ
  | [] => 0
  | error :: rest =>
      factor ^ rest.length * error + weightedErrorBudget factor rest

@[simp] theorem runSchedule_nil
    (exact : State → State) (state : State) :
    runSchedule exact [] state = state := rfl

@[simp] theorem runSchedule_cons
    (exact : State → State) (stage : Stage exact)
    (rest : List (Stage exact)) (state : State) :
    runSchedule exact (stage :: rest) state =
      runSchedule exact rest (stage.approximate state) := rfl

@[simp] theorem weightedErrorBudget_nil (factor : ℝ) :
    weightedErrorBudget factor [] = 0 := rfl

@[simp] theorem weightedErrorBudget_cons
    (factor error : ℝ) (rest : List ℝ) :
    weightedErrorBudget factor (error :: rest) =
      factor ^ rest.length * error +
        weightedErrorBudget factor rest := rfl

/-- Executing two schedule chunks agrees exactly with executing the first
chunk and feeding its result to the second. -/
theorem runSchedule_append
    (exact : State → State)
    (first second : List (Stage exact)) (state : State) :
    runSchedule exact (first ++ second) state =
      runSchedule exact second (runSchedule exact first state) := by
  induction first generalizing state with
  | nil =>
      rfl
  | cons stage rest inductionHypothesis =>
      simp only [List.cons_append, runSchedule_cons]
      exact inductionHypothesis (stage.approximate state)

/-- Error budgets compose with exactly the same chronological weighting as
the solver schedule. -/
theorem weightedErrorBudget_append
    (factor : ℝ) (first second : List ℝ) :
    weightedErrorBudget factor (first ++ second) =
      factor ^ second.length * weightedErrorBudget factor first +
        weightedErrorBudget factor second := by
  induction first with
  | nil =>
      simp
  | cons error rest inductionHypothesis =>
      simp only [List.cons_append, weightedErrorBudget_cons,
        List.length_append]
      rw [inductionHypothesis, pow_add]
      ring

theorem weightedErrorBudget_nonnegative
    {factor : ℝ} (factorNonnegative : 0 ≤ factor) :
    ∀ errors : List ℝ,
      (∀ error ∈ errors, 0 ≤ error) →
      0 ≤ weightedErrorBudget factor errors := by
  intro errors errorsNonnegative
  induction errors with
  | nil =>
      simp
  | cons error rest inductionHypothesis =>
      rw [weightedErrorBudget_cons]
      have errorNonnegative : 0 ≤ error :=
        errorsNonnegative error (by simp)
      have restNonnegative : ∀ value ∈ rest, 0 ≤ value := by
        intro value valueMem
        exact errorsNonnegative value (by simp [valueMem])
      exact add_nonneg
        (mul_nonneg (pow_nonneg factorNonnegative _) errorNonnegative)
        (inductionHypothesis restNonnegative)

/-! ## Finite transport theorem -/

/-- Time-varying inexact inference separates geometric initializer error from
the exact chronological convolution of the declared stage errors. -/
theorem runSchedule_to_fixedPoint_le
    {exact : State → State}
    (certificate : ContractionCertificate exact)
    (target initial : State)
    (targetFixed : IsFixedPoint exact target) :
    ∀ stages : List (Stage exact),
      ‖runSchedule exact stages initial - target‖ ≤
        certificate.factor ^ stages.length * ‖initial - target‖ +
          weightedErrorBudget certificate.factor
            (stages.map Stage.error) := by
  intro stages
  induction stages generalizing initial with
  | nil =>
      simp
  | cons stage rest inductionHypothesis =>
      have oneStep :
          ‖stage.approximate initial - target‖ ≤
            stage.error +
              certificate.factor * ‖initial - target‖ := by
        calc
          ‖stage.approximate initial - target‖ ≤
              ‖stage.approximate initial - exact initial‖ +
                ‖exact initial - target‖ := by
            have triangle := norm_add_le
              (stage.approximate initial - exact initial)
              (exact initial - target)
            simpa only [sub_add_sub_cancel] using triangle
          _ ≤ stage.error + ‖exact initial - target‖ := by
            gcongr
            exact stage.approximates initial
          _ ≤ stage.error +
                certificate.factor * ‖initial - target‖ := by
            gcongr
            have contracted := certificate.contracts initial target
            rw [targetFixed] at contracted
            exact contracted
      have tailBound := inductionHypothesis (stage.approximate initial)
      have scaledOneStep :=
        mul_le_mul_of_nonneg_left oneStep
          (pow_nonneg certificate.factor_nonneg rest.length)
      calc
        ‖runSchedule exact (stage :: rest) initial - target‖ ≤
            certificate.factor ^ rest.length *
                ‖stage.approximate initial - target‖ +
              weightedErrorBudget certificate.factor
                (rest.map Stage.error) := tailBound
        _ ≤ certificate.factor ^ rest.length *
                (stage.error +
                  certificate.factor * ‖initial - target‖) +
              weightedErrorBudget certificate.factor
                (rest.map Stage.error) := by
              linarith
        _ = certificate.factor ^ (stage :: rest).length *
                ‖initial - target‖ +
              weightedErrorBudget certificate.factor
                ((stage :: rest).map Stage.error) := by
              simp only [List.length_cons, List.map_cons,
                List.length_map, weightedErrorBudget_cons, pow_succ]
              ring

/-! ## Exact recovery -/

/-- An exact stage is a zero-error member of the same interface. -/
def exactStage (exact : State → State) : Stage exact where
  approximate := exact
  error := 0
  error_nonneg := le_rfl
  approximates := by
    intro state
    simp

/-- Zero-error scheduling recovers ordinary exact iteration definitionally,
including the number and order of solver calls. -/
theorem runSchedule_replicate_exactStage
    (exact : State → State) (steps : ℕ) (initial : State) :
    runSchedule exact (List.replicate steps (exactStage exact)) initial =
      exact^[steps] initial := by
  induction steps generalizing initial with
  | zero =>
      simp
  | succ steps inductionHypothesis =>
      rw [List.replicate_succ]
      change
        runSchedule exact (List.replicate steps (exactStage exact))
            (exact initial) =
          exact^[steps + 1] initial
      rw [inductionHypothesis]
      exact Function.iterate_succ_apply exact steps initial

/-! ## Geometric error schedules -/

/-- Numeric recurrence induced by errors `coefficient * rate^iteration`. -/
def geometricErrorBudget
    (factor coefficient rate : ℝ) : ℕ → ℝ
  | 0 => 0
  | steps + 1 =>
      factor * geometricErrorBudget factor coefficient rate steps +
        coefficient * rate ^ steps

/-- Away from resonance, the geometric convolution obeys the exact
difference-of-powers identity.  This division-free form is valid even when
the two rates are equal, where both sides vanish. -/
theorem geometricErrorBudget_mul_sub
    (factor coefficient rate : ℝ) :
    ∀ steps,
      (factor - rate) *
          geometricErrorBudget factor coefficient rate steps =
        coefficient * (factor ^ steps - rate ^ steps) := by
  intro steps
  induction steps with
  | zero =>
      simp [geometricErrorBudget]
  | succ steps inductionHypothesis =>
      rw [geometricErrorBudget, pow_succ, pow_succ]
      calc
        (factor - rate) *
            (factor *
                geometricErrorBudget factor coefficient rate steps +
              coefficient * rate ^ steps) =
            factor * ((factor - rate) *
              geometricErrorBudget factor coefficient rate steps) +
              coefficient * (factor - rate) * rate ^ steps := by ring
        _ = factor *
              (coefficient * (factor ^ steps - rate ^ steps)) +
              coefficient * (factor - rate) * rate ^ steps := by
              rw [inductionHypothesis]
        _ = coefficient *
              (factor ^ steps * factor - rate ^ steps * rate) := by
              ring

/-- At the resonant boundary, every one of the `steps + 1` injected errors
receives the same final power, producing the exact polynomial prefactor. -/
theorem geometricErrorBudget_resonant
    (factor coefficient : ℝ) :
    ∀ steps,
      geometricErrorBudget factor coefficient factor (steps + 1) =
        (steps + 1 : ℕ) * coefficient * factor ^ steps := by
  intro steps
  induction steps with
  | zero =>
      simp [geometricErrorBudget]
  | succ steps inductionHypothesis =>
      rw [geometricErrorBudget, inductionHypothesis, pow_succ]
      push_cast
      ring

/-! ## Attained persistent-bias boundary -/

def biasedHalfStage : Stage halfSolver where
  approximate := biasedHalfSolver
  error := 1 / 10
  error_nonneg := by norm_num
  approximates := biasedHalfApproximation.approximates

/-- Two persistent biased stages attain the weighted error budget exactly.
The exact target is zero, but the approximate trajectory has already moved
to `3/20`; persistent error is not exact-solver convergence. -/
theorem biasedHalf_twoStage_errorBudget_attained :
    ‖runSchedule halfSolver [biasedHalfStage, biasedHalfStage] 0 - 0‖ =
      weightedErrorBudget (1 / 2) [1 / 10, 1 / 10] := by
  norm_num [
    runSchedule,
    biasedHalfStage,
    biasedHalfSolver,
    weightedErrorBudget,
    Real.norm_eq_abs,
  ]

#print axioms runSchedule_append
#print axioms weightedErrorBudget_append
#print axioms runSchedule_to_fixedPoint_le
#print axioms runSchedule_replicate_exactStage
#print axioms geometricErrorBudget_mul_sub
#print axioms geometricErrorBudget_resonant
#print axioms biasedHalf_twoStage_errorBudget_attained

end

end InexactContractionSchedule

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
