import Mathlib.Analysis.Calculus.MeanValue
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.EntropyTurnover

/-!
# Trained nonlinear entropy turnover

This file closes the gap between a nonlinear reachability hypothesis and a
concrete trained model.  The model uses the genuinely nonlinear centered
sigmoid as its settling activation, a one-edge delayed readout, and a squared
probability loss.  Weight `1` is proved to be the unique zero-loss parameter
and a global minimizer.  Its entropy is uniform before the signal arrives,
strictly lower at the trained settling depth, and uniform again afterward.

The exact witness is accompanied by two boundaries.  First, contraction alone
does not imply reachability: centered sigmoid can never produce logit `1`.
Second, the entropy conclusion is robust to an explicit open neighborhood of
the trained probability.  The final section lifts the settling dynamics to
coordinatewise vector states and gives positive and negative vector fixtures.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open Set

/-! ## A genuinely nonlinear contractive settling activation -/

/-- The nonnegative real `1/4`, used as the sharp global Lipschitz constant. -/
noncomputable def oneQuarterNNReal : NNReal :=
  ⟨(1 / 4 : ℝ), by norm_num⟩

/-- Centered sigmoid fixes zero while retaining sigmoid's nonlinearity. -/
noncomputable def centeredSigmoidActivation (x : ℝ) : ℝ :=
  Real.sigmoid x - 1 / 2

@[simp] theorem centeredSigmoidActivation_zero :
    centeredSigmoidActivation 0 = 0 := by
  simp [centeredSigmoidActivation, Real.sigmoid_zero]

theorem centeredSigmoidActivation_strictMono :
    StrictMono centeredSigmoidActivation := by
  intro x y hxy
  dsimp [centeredSigmoidActivation]
  linarith [Real.sigmoid_strictMono hxy]

theorem centeredSigmoidActivation_one_pos :
    0 < centeredSigmoidActivation 1 := by
  have h := Real.sigmoid_strictMono (show (0 : ℝ) < 1 by norm_num)
  rw [Real.sigmoid_zero] at h
  simpa [centeredSigmoidActivation, one_div] using h

theorem centeredSigmoidActivation_mem_Ioo (x : ℝ) :
    centeredSigmoidActivation x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
  constructor
  · dsimp [centeredSigmoidActivation]
    linarith [Real.sigmoid_pos x]
  · dsimp [centeredSigmoidActivation]
    linarith [Real.sigmoid_lt_one x]

theorem centeredSigmoidActivation_hasDerivAt (x : ℝ) :
    HasDerivAt centeredSigmoidActivation
      (Real.sigmoid x * (1 - Real.sigmoid x)) x := by
  change HasDerivAt (fun y ↦ Real.sigmoid y - 1 / 2)
    (Real.sigmoid x * (1 - Real.sigmoid x)) x
  exact (Real.hasDerivAt_sigmoid x).sub_const (1 / 2 : ℝ)

private theorem sigmoidDerivative_nonneg (x : ℝ) :
    0 ≤ Real.sigmoid x * (1 - Real.sigmoid x) := by
  exact mul_nonneg (Real.sigmoid_nonneg x)
    (sub_nonneg.mpr (Real.sigmoid_le_one x))

private theorem sigmoidDerivative_le_oneQuarter (x : ℝ) :
    Real.sigmoid x * (1 - Real.sigmoid x) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (Real.sigmoid x - 1 / 2)]

/-- Centered sigmoid is globally `1/4`-Lipschitz. -/
theorem centeredSigmoidActivation_lipschitz :
    LipschitzWith oneQuarterNNReal centeredSigmoidActivation := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · exact differentiable_sigmoid.sub_const (1 / 2 : ℝ)
  · intro x
    rw [(centeredSigmoidActivation_hasDerivAt x).deriv]
    rw [Real.nnnorm_of_nonneg (sigmoidDerivative_nonneg x)]
    exact_mod_cast sigmoidDerivative_le_oneQuarter x

/-- Centered sigmoid, packaged as monotone contractive settling. -/
noncomputable def centeredSigmoidSettling : MonotoneContractiveSettling where
  activation := centeredSigmoidActivation
  contractionRate := 1 / 4
  zero_fixed := centeredSigmoidActivation_zero
  monotone := centeredSigmoidActivation_strictMono.monotone
  contractionRate_nonneg := by norm_num
  contractionRate_lt_one := by norm_num
  contractive := by
    intro x y
    have h := centeredSigmoidActivation_lipschitz.dist_le_mul x y
    have hquarter : ((oneQuarterNNReal : NNReal) : ℝ) = 1 / 4 := rfl
    rw [hquarter] at h
    simpa [Real.dist_eq] using h

/-- The activation is not the pointwise realization of any real-linear map. -/
theorem centeredSigmoidActivation_genuinely_nonlinear :
    ¬ ∃ L : ℝ →ₗ[ℝ] ℝ, ∀ x, L x = centeredSigmoidActivation x := by
  rintro ⟨L, hL⟩
  let a := centeredSigmoidActivation 1
  have ha_pos : 0 < a := centeredSigmoidActivation_one_pos
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hmap := L.map_smul a⁻¹ (1 : ℝ)
  have hvalue : centeredSigmoidActivation a⁻¹ = 1 := by
    calc
      centeredSigmoidActivation a⁻¹ = L a⁻¹ := (hL _).symm
      _ = a⁻¹ * L 1 := by simpa using hmap
      _ = a⁻¹ * a := by rw [hL 1]
      _ = 1 := inv_mul_cancel₀ ha_ne
  have hrange := (centeredSigmoidActivation_mem_Ioo a⁻¹).2
  rw [hvalue] at hrange
  norm_num at hrange

/-! ## A finite trained nonlinear PC problem -/

/-- A finite scalar PC training problem: settling, a finite readout depth, and
an interior target probability. -/
structure FiniteNonlinearPCTrainingProblem where
  settling : MonotoneContractiveSettling
  depth : ℕ
  depth_pos : 0 < depth
  targetProbability : ℝ
  targetProbability_interior : targetProbability ∈ Ioo (0 : ℝ) 1

/-- Probability read by a training problem from parameter/seed `weight`. -/
noncomputable def FiniteNonlinearPCTrainingProblem.probability
    (problem : FiniteNonlinearPCTrainingProblem)
    (weight : ℝ) (steps : ℕ) : ℝ :=
  nonlinearTurnoverProbability problem.settling problem.depth weight steps

/-- Squared probability error at the prescribed settling depth. -/
noncomputable def FiniteNonlinearPCTrainingProblem.loss
    (problem : FiniteNonlinearPCTrainingProblem) (weight : ℝ) : ℝ :=
  (problem.probability weight problem.depth - problem.targetProbability) ^ 2

/-- Output entropy at any finite number of settling steps. -/
noncomputable def FiniteNonlinearPCTrainingProblem.entropy
    (problem : FiniteNonlinearPCTrainingProblem)
    (weight : ℝ) (steps : ℕ) : ℝ :=
  Real.binEntropy (problem.probability weight steps)

/-- The target induced by the trained parameter `1`. -/
noncomputable def trainedCenteredSigmoidTargetProbability : ℝ :=
  twoOutcomeSoftmax (centeredSigmoidActivation 1) true

theorem trainedCenteredSigmoidTargetProbability_interior :
    trainedCenteredSigmoidTargetProbability ∈ Ioo (0 : ℝ) 1 := by
  rw [trainedCenteredSigmoidTargetProbability,
    twoOutcomeSoftmax_true_eq_sigmoid]
  exact ⟨Real.sigmoid_pos _, Real.sigmoid_lt_one _⟩

theorem trainedCenteredSigmoidTargetProbability_gt_half :
    1 / 2 < trainedCenteredSigmoidTargetProbability := by
  rw [trainedCenteredSigmoidTargetProbability,
    twoOutcomeSoftmax_true_eq_sigmoid]
  have h := Real.sigmoid_strictMono centeredSigmoidActivation_one_pos
  rw [Real.sigmoid_zero] at h
  simpa [one_div] using h

/-- The concrete one-edge nonlinear PC training problem. -/
noncomputable def trainedCenteredSigmoidProblem :
    FiniteNonlinearPCTrainingProblem where
  settling := centeredSigmoidSettling
  depth := 1
  depth_pos := by norm_num
  targetProbability := trainedCenteredSigmoidTargetProbability
  targetProbability_interior := trainedCenteredSigmoidTargetProbability_interior

theorem trainedCenteredSigmoidProbability_at_settling (weight : ℝ) :
    trainedCenteredSigmoidProblem.probability weight 1 =
      twoOutcomeSoftmax (centeredSigmoidActivation weight) true := by
  simp [FiniteNonlinearPCTrainingProblem.probability,
    trainedCenteredSigmoidProblem, nonlinearTurnoverProbability,
    nonlinearTurnoverReadoutLogit_eq, centeredSigmoidSettling]

@[simp] theorem trainedCenteredSigmoidProbability_at_trained_weight :
    trainedCenteredSigmoidProblem.probability 1 1 =
      trainedCenteredSigmoidTargetProbability := by
  rw [trainedCenteredSigmoidProbability_at_settling]
  rfl

theorem trainedCenteredSigmoidLoss_nonneg (weight : ℝ) :
    0 ≤ trainedCenteredSigmoidProblem.loss weight := by
  exact sq_nonneg _

/-- Weight `1` is the unique zero-loss parameter. -/
theorem trainedCenteredSigmoidLoss_eq_zero_iff (weight : ℝ) :
    trainedCenteredSigmoidProblem.loss weight = 0 ↔ weight = 1 := by
  rw [FiniteNonlinearPCTrainingProblem.loss, sq_eq_zero_iff]
  constructor
  · intro h
    have hp : trainedCenteredSigmoidProblem.probability weight 1 =
        trainedCenteredSigmoidTargetProbability := sub_eq_zero.mp h
    rw [trainedCenteredSigmoidProbability_at_settling,
      trainedCenteredSigmoidTargetProbability,
      twoOutcomeSoftmax_true_eq_sigmoid,
      twoOutcomeSoftmax_true_eq_sigmoid] at hp
    exact centeredSigmoidActivation_strictMono.injective
      (Real.sigmoid_injective hp)
  · rintro rfl
    exact sub_self _

/-- Training is exact and global, not merely a declared reachable seed. -/
theorem trainedCenteredSigmoidWeight_is_unique_global_minimizer :
    trainedCenteredSigmoidProblem.loss 1 = 0 ∧
      (∀ weight, trainedCenteredSigmoidProblem.loss 1 ≤
        trainedCenteredSigmoidProblem.loss weight) ∧
      (∀ weight, trainedCenteredSigmoidProblem.loss weight = 0 → weight = 1) := by
  refine ⟨(trainedCenteredSigmoidLoss_eq_zero_iff 1).2 rfl, ?_, ?_⟩
  · intro weight
    rw [(trainedCenteredSigmoidLoss_eq_zero_iff 1).2 rfl]
    exact trainedCenteredSigmoidLoss_nonneg weight
  · intro weight h
    exact (trainedCenteredSigmoidLoss_eq_zero_iff weight).1 h

/-! ## Exact and robust turnover after training -/

@[simp] theorem trainedCenteredSigmoidProbability_zero :
    trainedCenteredSigmoidProblem.probability 1 0 = 1 / 2 := by
  exact nonlinearTurnoverProbability_away_from_seed
    centeredSigmoidSettling 1 1 0 (by omega)

@[simp] theorem trainedCenteredSigmoidProbability_two :
    trainedCenteredSigmoidProblem.probability 1 2 = 1 / 2 := by
  exact nonlinearTurnoverProbability_away_from_seed
    centeredSigmoidSettling 1 1 2 (by omega)

theorem trainedCenteredSigmoidTargetEntropy_lt_uniform :
    Real.binEntropy trainedCenteredSigmoidTargetProbability <
      Real.binEntropy (1 / 2) := by
  exact binEntropy_lt_uniform_of_nonuniform
    trainedCenteredSigmoidTargetProbability
    trainedCenteredSigmoidTargetProbability_interior
    (ne_of_gt trainedCenteredSigmoidTargetProbability_gt_half)

/-- The trained nonlinear model has strict entropy turnover at depths 0,1,2. -/
theorem trainedCenteredSigmoidEntropyTurnover :
    Real.binEntropy trainedCenteredSigmoidTargetProbability <
        trainedCenteredSigmoidProblem.entropy 1 0 ∧
      trainedCenteredSigmoidProblem.entropy 1 1 =
        Real.binEntropy trainedCenteredSigmoidTargetProbability ∧
      Real.binEntropy trainedCenteredSigmoidTargetProbability <
        trainedCenteredSigmoidProblem.entropy 1 2 ∧
      ¬ Monotone (trainedCenteredSigmoidProblem.entropy 1) ∧
      ¬ Antitone (trainedCenteredSigmoidProblem.entropy 1) := by
  have hgap := trainedCenteredSigmoidTargetEntropy_lt_uniform
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [FiniteNonlinearPCTrainingProblem.entropy] using hgap
  · simp [FiniteNonlinearPCTrainingProblem.entropy]
  · simpa [FiniteNonlinearPCTrainingProblem.entropy] using hgap
  · intro hmono
    have h := hmono (show 0 ≤ 1 by omega)
    simp only [FiniteNonlinearPCTrainingProblem.entropy,
      trainedCenteredSigmoidProbability_zero,
      trainedCenteredSigmoidProbability_at_trained_weight] at h
    exact (not_lt_of_ge h) hgap
  · intro hanti
    have h := hanti (show 1 ≤ 2 by omega)
    simp only [FiniteNonlinearPCTrainingProblem.entropy,
      trainedCenteredSigmoidProbability_at_trained_weight,
      trainedCenteredSigmoidProbability_two] at h
    exact (not_lt_of_ge h) hgap

/-- Contraction alone does not imply target reachability: centered sigmoid's
range excludes logit `1`. -/
theorem centeredSigmoidContraction_does_not_reach_logit_one :
    ¬ ∃ seed : ℝ, centeredSigmoidSettling.activation seed = 1 := by
  rintro ⟨seed, hseed⟩
  have hrange := (centeredSigmoidActivation_mem_Ioo seed).2
  change centeredSigmoidActivation seed = 1 at hseed
  rw [hseed] at hrange
  norm_num at hrange

/-- An explicit open robustness radius around the trained probability. -/
noncomputable def trainedCenteredSigmoidRobustRadius : ℝ :=
  min ((trainedCenteredSigmoidTargetProbability - 1 / 2) / 2)
    ((1 - trainedCenteredSigmoidTargetProbability) / 2)

theorem trainedCenteredSigmoidRobustRadius_pos :
    0 < trainedCenteredSigmoidRobustRadius := by
  apply lt_min
  · linarith [trainedCenteredSigmoidTargetProbability_gt_half]
  · linarith [trainedCenteredSigmoidTargetProbability_interior.2]

/-- Every probability in the explicit neighborhood remains strictly more
decisive than the uniform distribution. -/
theorem entropy_lt_uniform_of_near_trainedCenteredSigmoidTarget
    (probability : ℝ)
    (hnear : |probability - trainedCenteredSigmoidTargetProbability| <
      trainedCenteredSigmoidRobustRadius) :
    Real.binEntropy probability < Real.binEntropy (1 / 2) := by
  have habs := abs_lt.mp hnear
  have hleft : trainedCenteredSigmoidRobustRadius ≤
      (trainedCenteredSigmoidTargetProbability - 1 / 2) / 2 :=
    min_le_left _ _
  have hright : trainedCenteredSigmoidRobustRadius ≤
      (1 - trainedCenteredSigmoidTargetProbability) / 2 :=
    min_le_right _ _
  have hhalf : 1 / 2 < probability := by linarith
  have hone : probability < 1 := by linarith
  exact Real.binEntropy_strictAntiOn
    (by norm_num : (1 / 2 : ℝ) ∈ Icc 2⁻¹ 1)
    ⟨by simpa [one_div] using le_of_lt hhalf, le_of_lt hone⟩
    (by simpa [one_div] using hhalf)

/-- Approximate training within the explicit probability margin still gives
the strict low-entropy middle of the turnover. -/
theorem approximateTraining_preservesCenteredSigmoidTurnoverMargin
    (weight : ℝ)
    (hnear : |trainedCenteredSigmoidProblem.probability weight 1 -
        trainedCenteredSigmoidTargetProbability| <
      trainedCenteredSigmoidRobustRadius) :
    trainedCenteredSigmoidProblem.entropy weight 1 <
      Real.binEntropy (1 / 2) := by
  exact entropy_lt_uniform_of_near_trainedCenteredSigmoidTarget _ hnear

/-! ## Coordinatewise vector-valued nonlinear PC -/

/-- Vector-valued chain state with finite-width coordinates. -/
abbrev VectorNonlinearTurnoverState (width : ℕ) := ℕ → Fin width → ℝ

/-- Coordinatewise nonlinear shift on a finite-width PC chain. -/
noncomputable def vectorNonlinearTurnoverShift
    (width : ℕ) (settling : MonotoneContractiveSettling)
    (state : VectorNonlinearTurnoverState width) :
    VectorNonlinearTurnoverState width :=
  fun n coordinate ↦ settling.activation (state (n + 1) coordinate)

theorem vectorNonlinearTurnoverShift_iterate_apply
    (width : ℕ) (settling : MonotoneContractiveSettling)
    (steps : ℕ) (state : VectorNonlinearTurnoverState width)
    (n : ℕ) (coordinate : Fin width) :
    ((vectorNonlinearTurnoverShift width settling)^[steps]) state n coordinate =
      (settling.activation^[steps]) (state (n + steps) coordinate) := by
  induction steps generalizing state n with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      simp only [vectorNonlinearTurnoverShift]
      rw [ih, Function.iterate_succ_apply']
      simp [Nat.add_comm, Nat.add_left_comm]

/-- Put a vector seed at one finite upstream depth. -/
noncomputable def vectorNonlinearTurnoverInitialState
    (width depth : ℕ) (seed : Fin width → ℝ) :
    VectorNonlinearTurnoverState width :=
  fun n coordinate ↦ if n = depth then seed coordinate else 0

/-- Vector readout logit after finite settling. -/
noncomputable def vectorNonlinearTurnoverReadoutLogit
    (width : ℕ) (settling : MonotoneContractiveSettling)
    (depth : ℕ) (seed : Fin width → ℝ) (steps : ℕ)
    (coordinate : Fin width) : ℝ :=
  ((vectorNonlinearTurnoverShift width settling)^[steps])
    (vectorNonlinearTurnoverInitialState width depth seed) 0 coordinate

/-- Each vector coordinate is exactly the corresponding scalar PC chain. -/
theorem vectorNonlinearTurnoverReadoutLogit_eq_scalar
    (width : ℕ) (settling : MonotoneContractiveSettling)
    (depth : ℕ) (seed : Fin width → ℝ) (steps : ℕ)
    (coordinate : Fin width) :
    vectorNonlinearTurnoverReadoutLogit width settling depth seed steps coordinate =
      nonlinearTurnoverReadoutLogit settling depth (seed coordinate) steps := by
  rw [vectorNonlinearTurnoverReadoutLogit,
    vectorNonlinearTurnoverShift_iterate_apply,
    nonlinearTurnoverReadoutLogit,
    nonlinearTurnoverShift_iterate_apply]
  simp [vectorNonlinearTurnoverInitialState,
    nonlinearTurnoverInitialState]

/-- Coordinate probability of the vector readout. -/
noncomputable def vectorNonlinearTurnoverProbability
    (width : ℕ) (settling : MonotoneContractiveSettling)
    (depth : ℕ) (seed : Fin width → ℝ) (steps : ℕ)
    (coordinate : Fin width) : ℝ :=
  twoOutcomeSoftmax
    (vectorNonlinearTurnoverReadoutLogit
      width settling depth seed steps coordinate) true

theorem vectorNonlinearTurnoverProbability_eq_scalar
    (width : ℕ) (settling : MonotoneContractiveSettling)
    (depth : ℕ) (seed : Fin width → ℝ) (steps : ℕ)
    (coordinate : Fin width) :
    vectorNonlinearTurnoverProbability width settling depth seed steps coordinate =
      nonlinearTurnoverProbability settling depth (seed coordinate) steps := by
  simp [vectorNonlinearTurnoverProbability, nonlinearTurnoverProbability,
    vectorNonlinearTurnoverReadoutLogit_eq_scalar]

/-- Positive vector fixture: every coordinate of an all-one seed inherits the
trained scalar turnover. -/
theorem trainedCenteredSigmoidVectorTurnover
    (width : ℕ) (coordinate : Fin width) :
    Real.binEntropy trainedCenteredSigmoidTargetProbability <
        Real.binEntropy (vectorNonlinearTurnoverProbability width
          centeredSigmoidSettling 1 (fun _ ↦ 1) 0 coordinate) ∧
      Real.binEntropy (vectorNonlinearTurnoverProbability width
          centeredSigmoidSettling 1 (fun _ ↦ 1) 1 coordinate) =
        Real.binEntropy trainedCenteredSigmoidTargetProbability ∧
      Real.binEntropy trainedCenteredSigmoidTargetProbability <
        Real.binEntropy (vectorNonlinearTurnoverProbability width
          centeredSigmoidSettling 1 (fun _ ↦ 1) 2 coordinate) := by
  simpa [vectorNonlinearTurnoverProbability_eq_scalar,
    FiniteNonlinearPCTrainingProblem.entropy,
    FiniteNonlinearPCTrainingProblem.probability,
    trainedCenteredSigmoidProblem] using
    ⟨trainedCenteredSigmoidEntropyTurnover.1,
      trainedCenteredSigmoidEntropyTurnover.2.1,
      trainedCenteredSigmoidEntropyTurnover.2.2.1⟩

/-- Negative vector boundary: an all-zero seed remains uniform at every
coordinate and every finite settling depth. -/
theorem centeredSigmoidVectorZeroSeed_uniform
    (width depth steps : ℕ) (coordinate : Fin width) :
    vectorNonlinearTurnoverProbability width centeredSigmoidSettling depth
      (fun _ ↦ 0) steps coordinate = 1 / 2 := by
  rw [vectorNonlinearTurnoverProbability_eq_scalar,
    nonlinearTurnoverProbability, nonlinearTurnoverReadoutLogit_eq]
  by_cases hsteps : steps = depth
  · rw [if_pos hsteps]
    rw [centeredSigmoidSettling.iterate_zero]
    norm_num [twoOutcomeSoftmax]
  · rw [if_neg hsteps]
    norm_num [twoOutcomeSoftmax]

/-- Crown: the concrete nonlinear activation, exact training, strict turnover,
robust approximate margin, unreachable contraction target, and vector lift are
all simultaneously witnessed. -/
theorem trainedNonlinearEntropyTurnover_crown :
    (¬ ∃ L : ℝ →ₗ[ℝ] ℝ, ∀ x, L x = centeredSigmoidActivation x) ∧
      trainedCenteredSigmoidProblem.loss 1 = 0 ∧
      (∀ weight, trainedCenteredSigmoidProblem.loss 1 ≤
        trainedCenteredSigmoidProblem.loss weight) ∧
      Real.binEntropy trainedCenteredSigmoidTargetProbability <
        trainedCenteredSigmoidProblem.entropy 1 0 ∧
      trainedCenteredSigmoidProblem.entropy 1 1 =
        Real.binEntropy trainedCenteredSigmoidTargetProbability ∧
      Real.binEntropy trainedCenteredSigmoidTargetProbability <
        trainedCenteredSigmoidProblem.entropy 1 2 ∧
      (¬ ∃ seed : ℝ, centeredSigmoidSettling.activation seed = 1) ∧
      0 < trainedCenteredSigmoidRobustRadius := by
  exact ⟨centeredSigmoidActivation_genuinely_nonlinear,
    trainedCenteredSigmoidWeight_is_unique_global_minimizer.1,
    trainedCenteredSigmoidWeight_is_unique_global_minimizer.2.1,
    trainedCenteredSigmoidEntropyTurnover.1,
    trainedCenteredSigmoidEntropyTurnover.2.1,
    trainedCenteredSigmoidEntropyTurnover.2.2.1,
    centeredSigmoidContraction_does_not_reach_logit_one,
    trainedCenteredSigmoidRobustRadius_pos⟩

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
