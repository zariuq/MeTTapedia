import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SafeguardedCompositeBlock

/-!
# Fixed-restart rates from subquadratic inner blocks

This module isolates the rigorous fixed-restart argument used to turn a
subquadratic inner method into a linearly convergent block method on a strongly
convex objective.  The result is phrased as a certificate on one complete
block, so it applies equally to an accelerated gradient block and to a
predictive-settling block whose endpoint has already been certified.

The contraction factor is

`(4 * smoothness / innerSteps^2) * (2 / strongConvexity)`,

equivalently `8 * smoothness / (strongConvexity * innerSteps^2)`.  Repeated
restart then gives a geometric objective-gap bound.  Positive and negative
fixtures show respectively a nontrivial contracting block and why an interval
whose certified factor is at least one supplies no linear-rate certificate.

No statement here treats the adaptive restart tests as universally valid:
their connection to local conditioning requires a separate observable
certificate.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace FixedRestartRate

noncomputable section

variable {State : Type*} [NormedAddCommGroup State]

/-- Objective gap relative to a declared minimizer. -/
def objectiveGap
    (objective : State → ℝ) (minimizer state : State) : ℝ :=
  objective state - objective minimizer

/-- The fixed-restart factor obtained by combining a `1 / k^2` block bound
with a strong-convexity distance bound. -/
def restartFactor
    (smoothness strongConvexity : ℝ) (innerSteps : ℕ) : ℝ :=
  (4 * smoothness / (innerSteps : ℝ) ^ 2) *
    (2 / strongConvexity)

/-- A complete inner block has the subquadratic endpoint estimate needed by
the fixed-restart argument.  Intermediate inner iterates are deliberately not
part of this interface. -/
structure BlockCertificate
    (objective : State → ℝ) (minimizer : State)
    (block : State → State)
    (smoothness strongConvexity : ℝ) (innerSteps : ℕ) : Prop where
  smoothness_pos : 0 < smoothness
  strongConvexity_pos : 0 < strongConvexity
  innerSteps_pos : 0 < innerSteps
  gap_nonneg : ∀ state, 0 ≤ objectiveGap objective minimizer state
  strongConvexity_lower :
    ∀ state,
      strongConvexity / 2 * ‖state - minimizer‖ ^ 2 ≤
        objectiveGap objective minimizer state
  subquadratic_endpoint :
    ∀ state,
      objectiveGap objective minimizer (block state) ≤
        4 * smoothness / (innerSteps : ℝ) ^ 2 *
          ‖state - minimizer‖ ^ 2

theorem restartFactor_nonneg
    {smoothness strongConvexity : ℝ} {innerSteps : ℕ}
    (smoothness_nonneg : 0 ≤ smoothness)
    (strongConvexity_pos : 0 < strongConvexity) :
    0 ≤ restartFactor smoothness strongConvexity innerSteps := by
  unfold restartFactor
  positivity

/-- The paper's two presentations of the fixed-restart factor agree. -/
theorem restartFactor_eq_eight_mul_div
    {smoothness strongConvexity : ℝ} {innerSteps : ℕ}
    (strongConvexity_ne : strongConvexity ≠ 0) :
    restartFactor smoothness strongConvexity innerSteps =
      8 * smoothness /
        (strongConvexity * (innerSteps : ℝ) ^ 2) := by
  unfold restartFactor
  by_cases steps_zero : innerSteps = 0
  · subst innerSteps
    simp
  · have steps_cast_ne : (innerSteps : ℝ) ≠ 0 := by
      exact_mod_cast steps_zero
    field_simp [strongConvexity_ne, steps_cast_ne]
    ring

/-- One complete block contracts the objective gap by the certified restart
factor. -/
theorem block_gap_le
    {objective : State → ℝ} {minimizer : State}
    {block : State → State}
    {smoothness strongConvexity : ℝ} {innerSteps : ℕ}
    (certificate :
      BlockCertificate objective minimizer block
        smoothness strongConvexity innerSteps)
    (state : State) :
    objectiveGap objective minimizer (block state) ≤
      restartFactor smoothness strongConvexity innerSteps *
        objectiveGap objective minimizer state := by
  have two_div_nonneg : 0 ≤ 2 / strongConvexity := by
    exact div_nonneg (by norm_num)
      (le_of_lt certificate.strongConvexity_pos)
  have distance_sq_le :
      ‖state - minimizer‖ ^ 2 ≤
        (2 / strongConvexity) *
          objectiveGap objective minimizer state := by
    calc
      ‖state - minimizer‖ ^ 2 =
          (2 / strongConvexity) *
            (strongConvexity / 2 * ‖state - minimizer‖ ^ 2) := by
        field_simp [ne_of_gt certificate.strongConvexity_pos]
      _ ≤
          (2 / strongConvexity) *
            objectiveGap objective minimizer state :=
        mul_le_mul_of_nonneg_left
          (certificate.strongConvexity_lower state) two_div_nonneg
  have endpointCoefficient_nonneg :
      0 ≤ 4 * smoothness / (innerSteps : ℝ) ^ 2 := by
    exact div_nonneg
      (mul_nonneg (by norm_num) (le_of_lt certificate.smoothness_pos))
      (sq_nonneg (innerSteps : ℝ))
  calc
    objectiveGap objective minimizer (block state) ≤
        4 * smoothness / (innerSteps : ℝ) ^ 2 *
          ‖state - minimizer‖ ^ 2 :=
      certificate.subquadratic_endpoint state
    _ ≤
        4 * smoothness / (innerSteps : ℝ) ^ 2 *
          ((2 / strongConvexity) *
            objectiveGap objective minimizer state) :=
      mul_le_mul_of_nonneg_left distance_sq_le endpointCoefficient_nonneg
    _ =
        restartFactor smoothness strongConvexity innerSteps *
          objectiveGap objective minimizer state := by
      unfold restartFactor
      ring

/-- Repeating the certified complete block yields a geometric objective-gap
bound. -/
theorem iterate_gap_le
    {objective : State → ℝ} {minimizer initial : State}
    {block : State → State}
    {smoothness strongConvexity : ℝ} {innerSteps : ℕ}
    (certificate :
      BlockCertificate objective minimizer block
        smoothness strongConvexity innerSteps)
    (blocks : ℕ) :
    objectiveGap objective minimizer (block^[blocks] initial) ≤
      restartFactor smoothness strongConvexity innerSteps ^ blocks *
        objectiveGap objective minimizer initial := by
  have factor_nonneg :
      0 ≤ restartFactor smoothness strongConvexity innerSteps :=
    restartFactor_nonneg (le_of_lt certificate.smoothness_pos)
      certificate.strongConvexity_pos
  induction blocks with
  | zero => simp
  | succ blocks inductionHypothesis =>
      rw [Function.iterate_succ_apply', pow_succ]
      calc
        objectiveGap objective minimizer
            (block (block^[blocks] initial)) ≤
            restartFactor smoothness strongConvexity innerSteps *
              objectiveGap objective minimizer (block^[blocks] initial) :=
          block_gap_le certificate _
        _ ≤
            restartFactor smoothness strongConvexity innerSteps *
              (restartFactor smoothness strongConvexity innerSteps ^ blocks *
                objectiveGap objective minimizer initial) :=
          mul_le_mul_of_nonneg_left inductionHypothesis factor_nonneg
        _ =
            restartFactor smoothness strongConvexity innerSteps ^ blocks *
              restartFactor smoothness strongConvexity innerSteps *
                objectiveGap objective minimizer initial := by
          ring

/-- The explicit interval inequality that makes the certified restart factor
strictly smaller than one. -/
theorem restartFactor_lt_one
    {smoothness strongConvexity : ℝ} {innerSteps : ℕ}
    (strongConvexity_pos : 0 < strongConvexity)
    (innerSteps_pos : 0 < innerSteps)
    (interval :
      8 * smoothness <
        strongConvexity * (innerSteps : ℝ) ^ 2) :
    restartFactor smoothness strongConvexity innerSteps < 1 := by
  rw [restartFactor_eq_eight_mul_div (ne_of_gt strongConvexity_pos)]
  have steps_cast_pos : 0 < (innerSteps : ℝ) := by
    exact_mod_cast innerSteps_pos
  have denominator_pos :
      0 < strongConvexity * (innerSteps : ℝ) ^ 2 := by
    positivity
  exact (div_lt_one denominator_pos).2 interval

/-! ## Positive and negative fixtures -/

def scalarQuadratic (state : ℝ) : ℝ :=
  state ^ 2 / 2

def scalarHalfBlock (state : ℝ) : ℝ :=
  state / 2

/-- A four-step abstract inner block represented by a nontrivial halving map
satisfies the fixed-restart certificate with factor `1 / 2`. -/
def scalarHalfBlockCertificate :
    BlockCertificate scalarQuadratic 0 scalarHalfBlock 1 1 4 where
  smoothness_pos := by norm_num
  strongConvexity_pos := by norm_num
  innerSteps_pos := by norm_num
  gap_nonneg := by
    intro state
    simp [objectiveGap, scalarQuadratic]
    positivity
  strongConvexity_lower := by
    intro state
    simp [objectiveGap, scalarQuadratic, Real.norm_eq_abs, sq_abs]
    nlinarith
  subquadratic_endpoint := by
    intro state
    simp only [objectiveGap, scalarQuadratic, scalarHalfBlock,
      Real.norm_eq_abs, sub_zero, sq_abs]
    ring_nf
    nlinarith [sq_nonneg state]

theorem scalarHalfBlock_restartFactor :
    restartFactor 1 1 4 = (1 / 2 : ℝ) := by
  norm_num [restartFactor]

theorem scalarHalfBlock_two_restarts :
    objectiveGap scalarQuadratic 0
        (scalarHalfBlock^[2] (4 : ℝ)) ≤
      (1 / 2 : ℝ) ^ 2 *
        objectiveGap scalarQuadratic 0 4 := by
  simpa [scalarHalfBlock_restartFactor] using
    iterate_gap_le scalarHalfBlockCertificate 2 (initial := (4 : ℝ))

/-- A positive smoothness and strong-convexity pair does not by itself make
an arbitrary short restart interval contractive. -/
theorem oneStep_restartFactor_not_contracting :
    ¬ restartFactor 1 1 1 < 1 := by
  norm_num [restartFactor]

#print axioms block_gap_le
#print axioms iterate_gap_le
#print axioms restartFactor_lt_one
#print axioms scalarHalfBlockCertificate
#print axioms scalarHalfBlock_two_restarts
#print axioms oneStep_restartFactor_not_contracting

end

end FixedRestartRate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
