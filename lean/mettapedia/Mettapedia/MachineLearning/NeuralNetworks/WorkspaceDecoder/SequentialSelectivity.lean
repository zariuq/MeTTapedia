import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Selectivity

/-!
# Sequential scalar selectivity with Riccati propagation

The posterior variance now evolves after every observation.  Its Riccati trace
induces a genuinely time-varying Kalman-gain schedule.  Along that optimal
trace, a fixed-prior diagnostic has an exact per-step square decomposition.
The strict two-step crown is stronger: its constant-gate competitor propagates
its own posterior covariance into the second observation.

For adjacent observations, unequal noise variances alone do not force unequal
gains: the sharp cross-product condition is
`R₂ * (P + R₁) ≠ R₁²`.  The strict constant-gate separation below uses this
condition.  These are scalar linear-Gaussian results, not claims about trained
nonlinear selective decoders.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

/-! ## Riccati covariance trace and propagated gain schedule -/

/-- Scalar posterior covariance after one optimal measurement correction. -/
noncomputable def scalarRiccatiStep
    (priorVariance noiseVariance : ℝ) : ℝ :=
  varianceGateRisk priorVariance noiseVariance
    (varianceKalmanGain priorVariance noiseVariance)

/-- Closed form of the scalar Riccati measurement step. -/
theorem scalarRiccatiStep_eq_mul_div
    (priorVariance noiseVariance : ℝ)
    (hsum : priorVariance + noiseVariance ≠ 0) :
    scalarRiccatiStep priorVariance noiseVariance =
      priorVariance * noiseVariance / (priorVariance + noiseVariance) := by
  unfold scalarRiccatiStep varianceGateRisk varianceKalmanGain
  field_simp [hsum]
  ring

/-- Positive prior and observation covariance produce positive posterior
covariance. -/
theorem scalarRiccatiStep_pos
    (priorVariance noiseVariance : ℝ)
    (hprior : 0 < priorVariance) (hnoise : 0 < noiseVariance) :
    0 < scalarRiccatiStep priorVariance noiseVariance := by
  rw [scalarRiccatiStep_eq_mul_div _ _ (ne_of_gt (add_pos hprior hnoise))]
  positivity

/-- The scalar Riccati measurement update is monotone in a positive prior
covariance when observation noise is positive. -/
theorem scalarRiccatiStep_mono
    (firstPrior secondPrior noiseVariance : ℝ)
    (hfirst : 0 < firstPrior) (hsecond : 0 < secondPrior)
    (hnoise : 0 < noiseVariance) (hle : firstPrior ≤ secondPrior) :
    scalarRiccatiStep firstPrior noiseVariance ≤
      scalarRiccatiStep secondPrior noiseVariance := by
  rw [scalarRiccatiStep_eq_mul_div _ _
      (ne_of_gt (add_pos hfirst hnoise)),
    scalarRiccatiStep_eq_mul_div _ _
      (ne_of_gt (add_pos hsecond hnoise))]
  rw [div_le_div_iff₀ (add_pos hfirst hnoise) (add_pos hsecond hnoise)]
  rw [← sub_nonneg]
  have hfactor :
      secondPrior * noiseVariance * (firstPrior + noiseVariance) -
          firstPrior * noiseVariance * (secondPrior + noiseVariance) =
        noiseVariance ^ 2 * (secondPrior - firstPrior) := by
    ring
  rw [hfactor]
  exact mul_nonneg (sq_nonneg noiseVariance) (sub_nonneg.mpr hle)

/-- Positive prior and observation variances make every scalar correction
risk positive, including for gates outside the unit interval. -/
theorem varianceGateRisk_pos
    (priorVariance noiseVariance gate : ℝ)
    (hprior : 0 < priorVariance) (hnoise : 0 < noiseVariance) :
    0 < varianceGateRisk priorVariance noiseVariance gate := by
  unfold varianceGateRisk
  by_cases hgate : gate = 0
  · simp [hgate, hprior]
  · have hgateSquare : 0 < gate ^ 2 := sq_pos_of_ne_zero hgate
    have hleft : 0 ≤ (1 - gate) ^ 2 * priorVariance := by positivity
    have hright : 0 < gate ^ 2 * noiseVariance := mul_pos hgateSquare hnoise
    linarith

/-- Prior-covariance trajectory for a sequence of observation noises,
including the initial covariance. -/
noncomputable def scalarRiccatiTrace : ℝ → List ℝ → List ℝ
  | priorVariance, [] => [priorVariance]
  | priorVariance, noiseVariance :: noises =>
      priorVariance :: scalarRiccatiTrace
        (scalarRiccatiStep priorVariance noiseVariance) noises

/-- Kalman-gain schedule induced by the evolving Riccati covariance. -/
noncomputable def sequentialKalmanGainSchedule : ℝ → List ℝ → List ℝ
  | _priorVariance, [] => []
  | priorVariance, noiseVariance :: noises =>
      varianceKalmanGain priorVariance noiseVariance ::
        sequentialKalmanGainSchedule
          (scalarRiccatiStep priorVariance noiseVariance) noises

@[simp] theorem scalarRiccatiTrace_length
    (priorVariance : ℝ) (noises : List ℝ) :
    (scalarRiccatiTrace priorVariance noises).length = noises.length + 1 := by
  induction noises generalizing priorVariance with
  | nil => rfl
  | cons noise noises ih =>
      simp [scalarRiccatiTrace, ih]

@[simp] theorem sequentialKalmanGainSchedule_length
    (priorVariance : ℝ) (noises : List ℝ) :
    (sequentialKalmanGainSchedule priorVariance noises).length = noises.length := by
  induction noises generalizing priorVariance with
  | nil => rfl
  | cons noise noises ih =>
      simp [sequentialKalmanGainSchedule, ih]

/-- A positive initial covariance and positive observation noises keep every
covariance in the T-step trace positive. -/
theorem scalarRiccatiTrace_forall_pos
    (priorVariance : ℝ) (noises : List ℝ)
    (hprior : 0 < priorVariance)
    (hnoises : ∀ noise ∈ noises, 0 < noise) :
    ∀ covariance ∈ scalarRiccatiTrace priorVariance noises, 0 < covariance := by
  induction noises generalizing priorVariance with
  | nil =>
      simpa [scalarRiccatiTrace] using hprior
  | cons noise noises ih =>
      have hnoise : 0 < noise := hnoises noise (by simp)
      have htail : ∀ nextNoise ∈ noises, 0 < nextNoise := by
        intro nextNoise hmem
        exact hnoises nextNoise (by simp [hmem])
      intro covariance hmem
      simp only [scalarRiccatiTrace, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hprior
      · exact ih (priorVariance := scalarRiccatiStep priorVariance noise)
          (scalarRiccatiStep_pos priorVariance noise hprior hnoise)
          htail covariance hmem

/-! ## T-step propagated-prior schedule risk -/

/-- Sum of one-step risks evaluated along the optimal propagated covariance
trace.  A length mismatch is deliberately outside the theorem interface. -/
noncomputable def propagatedPriorScheduleRisk : ℝ → List ℝ → List ℝ → ℝ
  | _priorVariance, [], [] => 0
  | priorVariance, noiseVariance :: noises, gate :: gates =>
      varianceGateRisk priorVariance noiseVariance gate +
        propagatedPriorScheduleRisk
          (scalarRiccatiStep priorVariance noiseVariance) noises gates
  | _priorVariance, _noises, _gates => 0

/-- Exact T-step excess-risk sum relative to the propagated Kalman schedule. -/
noncomputable def propagatedScheduleExcess : ℝ → List ℝ → List ℝ → ℝ
  | _priorVariance, [], [] => 0
  | priorVariance, noiseVariance :: noises, gate :: gates =>
      (priorVariance + noiseVariance) *
          (gate - varianceKalmanGain priorVariance noiseVariance) ^ 2 +
        propagatedScheduleExcess
          (scalarRiccatiStep priorVariance noiseVariance) noises gates
  | _priorVariance, _noises, _gates => 0

/-- T-step sequential license: schedule regret along the Riccati trace is
exactly the sum of its per-step positive squares. -/
theorem propagatedPriorScheduleRisk_sub_kalman_eq_excess
    (priorVariance : ℝ) (noises gates : List ℝ)
    (hlength : gates.length = noises.length)
    (hprior : 0 < priorVariance)
    (hnoises : ∀ noise ∈ noises, 0 < noise) :
    propagatedPriorScheduleRisk priorVariance noises gates -
        propagatedPriorScheduleRisk priorVariance noises
          (sequentialKalmanGainSchedule priorVariance noises) =
      propagatedScheduleExcess priorVariance noises gates := by
  induction noises generalizing priorVariance gates with
  | nil =>
      cases gates with
      | nil => norm_num [propagatedPriorScheduleRisk,
          sequentialKalmanGainSchedule, propagatedScheduleExcess]
      | cons gate gates => simp at hlength
  | cons noise noises ih =>
      cases gates with
      | nil => simp at hlength
      | cons gate gates =>
          have hnoise : 0 < noise := hnoises noise (by simp)
          have htail : ∀ nextNoise ∈ noises, 0 < nextNoise := by
            intro nextNoise hmem
            exact hnoises nextNoise (by simp [hmem])
          have hlengthTail : gates.length = noises.length := by
            simpa using hlength
          have hstepPos := scalarRiccatiStep_pos
            priorVariance noise hprior hnoise
          have htailIdentity := ih
            (priorVariance := scalarRiccatiStep priorVariance noise)
            (gates := gates) hlengthTail hstepPos htail
          have hone := varianceGateRisk_sub_kalman_eq_square
            priorVariance noise gate (ne_of_gt (add_pos hprior hnoise))
          simp only [propagatedPriorScheduleRisk,
            sequentialKalmanGainSchedule, propagatedScheduleExcess]
          linarith

/-! ## Genuine schedule propagation and dynamic optimality -/

/-- Cumulative posterior risk for a schedule that propagates its own
covariance.  This is the genuine competing-filter semantics. -/
noncomputable def actualSequentialScheduleRisk : ℝ → List ℝ → List ℝ → ℝ
  | _priorVariance, [], [] => 0
  | priorVariance, noiseVariance :: noises, gate :: gates =>
      let posterior := varianceGateRisk priorVariance noiseVariance gate
      posterior + actualSequentialScheduleRisk posterior noises gates
  | _priorVariance, _noises, _gates => 0

/-- Cumulative posterior risk of the propagated Kalman/Riccati schedule. -/
noncomputable def optimalSequentialRisk : ℝ → List ℝ → ℝ
  | _priorVariance, [] => 0
  | priorVariance, noiseVariance :: noises =>
      let posterior := scalarRiccatiStep priorVariance noiseVariance
      posterior + optimalSequentialRisk posterior noises

/-- The optimal cumulative risk is monotone in its positive initial
covariance. -/
theorem optimalSequentialRisk_mono
    (firstPrior secondPrior : ℝ) (noises : List ℝ)
    (hfirst : 0 < firstPrior) (hsecond : 0 < secondPrior)
    (hnoises : ∀ noise ∈ noises, 0 < noise)
    (hle : firstPrior ≤ secondPrior) :
    optimalSequentialRisk firstPrior noises ≤
      optimalSequentialRisk secondPrior noises := by
  induction noises generalizing firstPrior secondPrior with
  | nil => simp [optimalSequentialRisk]
  | cons noise noises ih =>
      have hnoise : 0 < noise := hnoises noise (by simp)
      have htail : ∀ nextNoise ∈ noises, 0 < nextNoise := by
        intro nextNoise hmem
        exact hnoises nextNoise (by simp [hmem])
      have hfirstPosterior := scalarRiccatiStep_pos
        firstPrior noise hfirst hnoise
      have hsecondPosterior := scalarRiccatiStep_pos
        secondPrior noise hsecond hnoise
      have hposteriorOrder := scalarRiccatiStep_mono
        firstPrior secondPrior noise hfirst hsecond hnoise hle
      have htailOrder := ih
        (firstPrior := scalarRiccatiStep firstPrior noise)
        (secondPrior := scalarRiccatiStep secondPrior noise)
        hfirstPosterior hsecondPosterior htail hposteriorOrder
      simp only [optimalSequentialRisk]
      linarith

/-- The recursive Riccati risk is exactly the genuine schedule risk of the
time-varying Kalman gains. -/
theorem optimalSequentialRisk_eq_actual_kalmanScheduleRisk
    (priorVariance : ℝ) (noises : List ℝ) :
    optimalSequentialRisk priorVariance noises =
      actualSequentialScheduleRisk priorVariance noises
        (sequentialKalmanGainSchedule priorVariance noises) := by
  induction noises generalizing priorVariance with
  | nil => rfl
  | cons noise noises ih =>
      simp only [optimalSequentialRisk, sequentialKalmanGainSchedule,
        actualSequentialScheduleRisk, scalarRiccatiStep]
      rw [ih]

/-- Dynamic-programming license: among equal-length schedules, the propagated
Kalman schedule minimizes cumulative posterior risk even though a competitor
propagates its own covariance. -/
theorem optimalSequentialRisk_le_actualScheduleRisk
    (priorVariance : ℝ) (noises gates : List ℝ)
    (hlength : gates.length = noises.length)
    (hprior : 0 < priorVariance)
    (hnoises : ∀ noise ∈ noises, 0 < noise) :
    optimalSequentialRisk priorVariance noises ≤
      actualSequentialScheduleRisk priorVariance noises gates := by
  induction noises generalizing priorVariance gates with
  | nil =>
      cases gates with
      | nil => rfl
      | cons gate gates => simp at hlength
  | cons noise noises ih =>
      cases gates with
      | nil => simp at hlength
      | cons gate gates =>
          have hnoise : 0 < noise := hnoises noise (by simp)
          have htail : ∀ nextNoise ∈ noises, 0 < nextNoise := by
            intro nextNoise hmem
            exact hnoises nextNoise (by simp [hmem])
          have hlengthTail : gates.length = noises.length := by
            simpa using hlength
          have hoptimalPosterior := scalarRiccatiStep_pos
            priorVariance noise hprior hnoise
          have hactualPosterior := varianceGateRisk_pos
            priorVariance noise gate hprior hnoise
          have honeStep :=
            (varianceKalmanGain_uniqueMinimizer
              priorVariance noise hprior hnoise).1 gate
          have honeStep' : scalarRiccatiStep priorVariance noise ≤
              varianceGateRisk priorVariance noise gate := by
            exact honeStep
          have htailMono := optimalSequentialRisk_mono
            (scalarRiccatiStep priorVariance noise)
            (varianceGateRisk priorVariance noise gate)
            noises hoptimalPosterior hactualPosterior htail honeStep
          have htailOptimal := ih
            (priorVariance := varianceGateRisk priorVariance noise gate)
            (gates := gates) hlengthTail hactualPosterior htail
          simp only [optimalSequentialRisk, actualSequentialScheduleRisk]
          linarith

/-! ## Sharp adjacent-gain condition and strict constant separation -/

/-- The exact sufficient condition for the first two propagated gains to
differ.  Merely assuming `firstNoise ≠ secondNoise` would be false. -/
theorem sequentialKalmanGains_ne_of_crossProduct_ne
    (priorVariance firstNoise secondNoise : ℝ)
    (hprior : 0 < priorVariance)
    (hfirst : 0 < firstNoise) (hsecond : 0 < secondNoise)
    (hcross : secondNoise * (priorVariance + firstNoise) ≠ firstNoise ^ 2) :
    varianceKalmanGain priorVariance firstNoise ≠
      varianceKalmanGain
        (scalarRiccatiStep priorVariance firstNoise) secondNoise := by
  have hsum₁ : priorVariance + firstNoise ≠ 0 :=
    ne_of_gt (add_pos hprior hfirst)
  have hposterior : 0 < scalarRiccatiStep priorVariance firstNoise :=
    scalarRiccatiStep_pos priorVariance firstNoise hprior hfirst
  have hsum₂ : scalarRiccatiStep priorVariance firstNoise + secondNoise ≠ 0 :=
    ne_of_gt (add_pos hposterior hsecond)
  intro hgains
  rw [scalarRiccatiStep_eq_mul_div _ _ hsum₁] at hgains
  unfold varianceKalmanGain at hgains
  field_simp [hsum₁, hsum₂] at hgains
  apply hcross
  nlinarith

/-- Genuine two-step risk for one constant gate.  Unlike the propagated-prior
diagnostic above, the second step uses this competitor's own first posterior
covariance. -/
noncomputable def twoStepSequentialConstantGateRisk
    (priorVariance firstNoise secondNoise gate : ℝ) : ℝ :=
  let firstPosterior := varianceGateRisk priorVariance firstNoise gate
  firstPosterior + varianceGateRisk firstPosterior secondNoise gate

/-- Two-step risk of the propagated Kalman gain schedule. -/
noncomputable def twoStepSequentialKalmanRisk
    (priorVariance firstNoise secondNoise : ℝ) : ℝ :=
  varianceGateRisk priorVariance firstNoise
      (varianceKalmanGain priorVariance firstNoise) +
    varianceGateRisk (scalarRiccatiStep priorVariance firstNoise)
      secondNoise
      (varianceKalmanGain
        (scalarRiccatiStep priorVariance firstNoise) secondNoise)

/-- Exact genuine-filter excess decomposition.  The first two terms are local
gain regrets; the last is the Riccati cost of entering step two with the
competitor's (weakly larger) posterior covariance. -/
theorem twoStepSequential_constant_sub_kalman_eq_decomposition
    (priorVariance firstNoise secondNoise gate : ℝ)
    (hprior : 0 < priorVariance)
    (hfirst : 0 < firstNoise) (hsecond : 0 < secondNoise) :
    twoStepSequentialConstantGateRisk
        priorVariance firstNoise secondNoise gate -
      twoStepSequentialKalmanRisk priorVariance firstNoise secondNoise =
        (priorVariance + firstNoise) *
            (gate - varianceKalmanGain priorVariance firstNoise) ^ 2 +
          (varianceGateRisk priorVariance firstNoise gate + secondNoise) *
            (gate - varianceKalmanGain
              (varianceGateRisk priorVariance firstNoise gate)
              secondNoise) ^ 2 +
          (scalarRiccatiStep
              (varianceGateRisk priorVariance firstNoise gate) secondNoise -
            scalarRiccatiStep
              (scalarRiccatiStep priorVariance firstNoise) secondNoise) := by
  have hcompetitor := varianceGateRisk_pos
    priorVariance firstNoise gate hprior hfirst
  have h₁ := varianceGateRisk_sub_kalman_eq_square
    priorVariance firstNoise gate (ne_of_gt (add_pos hprior hfirst))
  have h₂ := varianceGateRisk_sub_kalman_eq_square
    (varianceGateRisk priorVariance firstNoise gate) secondNoise gate
      (ne_of_gt (add_pos hcompetitor hsecond))
  unfold twoStepSequentialConstantGateRisk twoStepSequentialKalmanRisk
    scalarRiccatiStep
  linarith

/-- Sequential selectivity crown: under the sharp adjacent-gain condition,
every constant gate is strictly worse than the propagated two-gain schedule. -/
theorem everyConstantGate_strictlySuboptimal_sequential
    (priorVariance firstNoise secondNoise gate : ℝ)
    (hprior : 0 < priorVariance)
    (hfirst : 0 < firstNoise) (hsecond : 0 < secondNoise)
    (hcross : secondNoise * (priorVariance + firstNoise) ≠ firstNoise ^ 2) :
    twoStepSequentialKalmanRisk priorVariance firstNoise secondNoise <
      twoStepSequentialConstantGateRisk
        priorVariance firstNoise secondNoise gate := by
  have hposterior := scalarRiccatiStep_pos
    priorVariance firstNoise hprior hfirst
  have hgains := sequentialKalmanGains_ne_of_crossProduct_ne
    priorVariance firstNoise secondNoise hprior hfirst hsecond hcross
  have hcompetitor := varianceGateRisk_pos
    priorVariance firstNoise gate hprior hfirst
  have hfirstMin :=
    (varianceKalmanGain_uniqueMinimizer
      priorVariance firstNoise hprior hfirst).1 gate
  have hriccatiOrder := scalarRiccatiStep_mono
    (scalarRiccatiStep priorVariance firstNoise)
    (varianceGateRisk priorVariance firstNoise gate)
    secondNoise hposterior hcompetitor hsecond hfirstMin
  have hexcess := twoStepSequential_constant_sub_kalman_eq_decomposition
    priorVariance firstNoise secondNoise gate hprior hfirst hsecond
  have hsum₁ : 0 < priorVariance + firstNoise := add_pos hprior hfirst
  have hsum₂ : 0 <
      varianceGateRisk priorVariance firstNoise gate + secondNoise :=
    add_pos hcompetitor hsecond
  have hriccatiNonneg : 0 ≤
      scalarRiccatiStep
          (varianceGateRisk priorVariance firstNoise gate) secondNoise -
        scalarRiccatiStep
          (scalarRiccatiStep priorVariance firstNoise) secondNoise :=
    sub_nonneg.mpr hriccatiOrder
  have hpositive : 0 <
      (priorVariance + firstNoise) *
          (gate - varianceKalmanGain priorVariance firstNoise) ^ 2 +
        (varianceGateRisk priorVariance firstNoise gate + secondNoise) *
          (gate - varianceKalmanGain
            (varianceGateRisk priorVariance firstNoise gate)
            secondNoise) ^ 2 +
        (scalarRiccatiStep
            (varianceGateRisk priorVariance firstNoise gate) secondNoise -
          scalarRiccatiStep
            (scalarRiccatiStep priorVariance firstNoise) secondNoise) := by
    by_cases hgate : gate = varianceKalmanGain priorVariance firstNoise
    · have hposteriorEq :
          varianceGateRisk priorVariance firstNoise gate =
            scalarRiccatiStep priorVariance firstNoise := by
        simp only [hgate, scalarRiccatiStep]
      have hsecondGate : gate ≠ varianceKalmanGain
          (varianceGateRisk priorVariance firstNoise gate) secondNoise := by
        intro heq
        apply hgains
        rw [← hposteriorEq]
        exact hgate.symm.trans heq
      have hsquare : 0 <
          (gate - varianceKalmanGain
            (varianceGateRisk priorVariance firstNoise gate)
            secondNoise) ^ 2 :=
        sq_pos_of_ne_zero (sub_ne_zero.mpr hsecondGate)
      have hsecondTerm : 0 <
          (varianceGateRisk priorVariance firstNoise gate + secondNoise) *
            (gate - varianceKalmanGain
              (varianceGateRisk priorVariance firstNoise gate)
              secondNoise) ^ 2 :=
        mul_pos hsum₂ hsquare
      have hfirstTerm : 0 ≤
          (priorVariance + firstNoise) *
            (gate - varianceKalmanGain priorVariance firstNoise) ^ 2 := by
        positivity
      linarith
    · have hsquare : 0 <
          (gate - varianceKalmanGain priorVariance firstNoise) ^ 2 :=
        sq_pos_of_ne_zero (sub_ne_zero.mpr hgate)
      have hfirstTerm : 0 <
          (priorVariance + firstNoise) *
            (gate - varianceKalmanGain priorVariance firstNoise) ^ 2 :=
        mul_pos hsum₁ hsquare
      have hsecondTerm : 0 ≤
          (varianceGateRisk priorVariance firstNoise gate + secondNoise) *
            (gate - varianceKalmanGain
              (varianceGateRisk priorVariance firstNoise gate)
              secondNoise) ^ 2 := by
        positivity
      linarith
  linarith

/-- Full sequential crown for every `T ≥ 2`: after a sharp differing-gain
prefix, every constant gate remains strictly worse through any positive-noise
tail, with both filters propagating their own covariance. -/
theorem everyConstantGate_strictlySuboptimal_sequential_withTail
    (priorVariance firstNoise secondNoise gate : ℝ)
    (tailNoises : List ℝ)
    (hprior : 0 < priorVariance)
    (hfirst : 0 < firstNoise) (hsecond : 0 < secondNoise)
    (htail : ∀ noise ∈ tailNoises, 0 < noise)
    (hcross : secondNoise * (priorVariance + firstNoise) ≠ firstNoise ^ 2) :
    optimalSequentialRisk priorVariance
        (firstNoise :: secondNoise :: tailNoises) <
      actualSequentialScheduleRisk priorVariance
        (firstNoise :: secondNoise :: tailNoises)
        (gate :: gate :: List.replicate tailNoises.length gate) := by
  let optimalFirst := scalarRiccatiStep priorVariance firstNoise
  let actualFirst := varianceGateRisk priorVariance firstNoise gate
  let optimalSecond := scalarRiccatiStep optimalFirst secondNoise
  let actualSecond := varianceGateRisk actualFirst secondNoise gate
  have hoptimalFirst : 0 < optimalFirst := by
    exact scalarRiccatiStep_pos priorVariance firstNoise hprior hfirst
  have hactualFirst : 0 < actualFirst := by
    exact varianceGateRisk_pos priorVariance firstNoise gate hprior hfirst
  have hoptimalSecond : 0 < optimalSecond := by
    exact scalarRiccatiStep_pos optimalFirst secondNoise hoptimalFirst hsecond
  have hactualSecond : 0 < actualSecond := by
    exact varianceGateRisk_pos actualFirst secondNoise gate hactualFirst hsecond
  have hfirstOrder : optimalFirst ≤ actualFirst := by
    exact (varianceKalmanGain_uniqueMinimizer
      priorVariance firstNoise hprior hfirst).1 gate
  have hriccatiOrder : optimalSecond ≤
      scalarRiccatiStep actualFirst secondNoise := by
    exact scalarRiccatiStep_mono optimalFirst actualFirst secondNoise
      hoptimalFirst hactualFirst hsecond hfirstOrder
  have hsecondOrder : scalarRiccatiStep actualFirst secondNoise ≤
      actualSecond := by
    exact (varianceKalmanGain_uniqueMinimizer
      actualFirst secondNoise hactualFirst hsecond).1 gate
  have hposteriorOrder : optimalSecond ≤ actualSecond :=
    hriccatiOrder.trans hsecondOrder
  have htailMono :
      optimalSequentialRisk optimalSecond tailNoises ≤
        optimalSequentialRisk actualSecond tailNoises :=
    optimalSequentialRisk_mono optimalSecond actualSecond tailNoises
      hoptimalSecond hactualSecond htail hposteriorOrder
  have htailActual :
      optimalSequentialRisk actualSecond tailNoises ≤
        actualSequentialScheduleRisk actualSecond tailNoises
          (List.replicate tailNoises.length gate) :=
    optimalSequentialRisk_le_actualScheduleRisk
      actualSecond tailNoises (List.replicate tailNoises.length gate)
      (by simp) hactualSecond htail
  have hprefix := everyConstantGate_strictlySuboptimal_sequential
    priorVariance firstNoise secondNoise gate
    hprior hfirst hsecond hcross
  change optimalFirst + optimalSecond < actualFirst + actualSecond at hprefix
  change optimalFirst +
      (optimalSecond + optimalSequentialRisk optimalSecond tailNoises) <
    actualFirst +
      (actualSecond + actualSequentialScheduleRisk actualSecond tailNoises
        (List.replicate tailNoises.length gate))
  linarith

/-! ## Positive and negative fixtures -/

/-- With prior covariance one and noises one then three, the propagated gains
are `1/2` and `1/7`, so every constant gate is strictly worse. -/
theorem sequential_selectivity_positiveExample (gate : ℝ) :
    twoStepSequentialKalmanRisk 1 1 3 <
      twoStepSequentialConstantGateRisk 1 1 3 gate := by
  apply everyConstantGate_strictlySuboptimal_sequential
  all_goals norm_num

/-- Noise can change while adjacent sequential gains remain equal: prior one,
first noise two, and second noise `4/3` give gain `1/3` at both steps. -/
theorem unequalNoise_can_have_equalSequentialGains_negativeExample :
    (2 : ℝ) ≠ 4 / 3 ∧
      varianceKalmanGain 1 2 =
        varianceKalmanGain (scalarRiccatiStep 1 2) (4 / 3) := by
  constructor
  · norm_num
  · norm_num [varianceKalmanGain, scalarRiccatiStep, varianceGateRisk]

#print axioms scalarRiccatiTrace_forall_pos
#print axioms propagatedPriorScheduleRisk_sub_kalman_eq_excess
#print axioms sequentialKalmanGains_ne_of_crossProduct_ne
#print axioms twoStepSequential_constant_sub_kalman_eq_decomposition
#print axioms everyConstantGate_strictlySuboptimal_sequential
#print axioms optimalSequentialRisk_le_actualScheduleRisk
#print axioms everyConstantGate_strictlySuboptimal_sequential_withTail
#print axioms sequential_selectivity_positiveExample
#print axioms unequalNoise_can_have_equalSequentialGains_negativeExample

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
