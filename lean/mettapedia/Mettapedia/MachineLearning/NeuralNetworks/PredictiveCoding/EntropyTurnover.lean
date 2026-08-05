import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# Entropy turnover in arbitrary-depth linear predictive-coding readouts

This file first proves a general linear-chain turnover theorem.  A target logit
may begin at any finite depth in a linear shift register.  Before it reaches
the two-outcome softmax readout the output is uniform, at the arrival depth it
equals any prescribed nondegenerate soft target, and after it passes the
readout the output is uniform again.  The entropy sequence is nonmonotone
exactly when the target is nonuniform.  A canonical more-decisive comparator
has entropy strictly below every such target.

The original two-node `3/4` fixture is retained as a concrete specialization.
These linear results do not assert that the mechanism or entropy ordering
persists for arbitrary nonlinear architectures or training objectives.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open Set

/-! ## A normalized two-outcome softmax readout -/

/-- The two-outcome softmax distribution for logits `(0, logit)`. -/
noncomputable def twoOutcomeSoftmax (logit : ℝ) : Bool → ℝ
  | false => Real.exp 0 / (Real.exp 0 + Real.exp logit)
  | true => Real.exp logit / (Real.exp 0 + Real.exp logit)

theorem twoOutcomeSoftmax_normalized (logit : ℝ) :
    twoOutcomeSoftmax logit false + twoOutcomeSoftmax logit true = 1 := by
  simp only [twoOutcomeSoftmax, Real.exp_zero]
  field_simp

theorem twoOutcomeSoftmax_positive (logit : ℝ) (outcome : Bool) :
    0 < twoOutcomeSoftmax logit outcome := by
  cases outcome <;> simp only [twoOutcomeSoftmax, Real.exp_zero] <;> positivity

theorem twoOutcomeSoftmax_true_eq_sigmoid (logit : ℝ) :
    twoOutcomeSoftmax logit true = Real.sigmoid logit := by
  rw [twoOutcomeSoftmax, Real.sigmoid_def, Real.exp_zero, Real.exp_neg]
  field_simp
  ring

theorem twoOutcomeSoftmax_true_log (mass : ℝ) (hmass : 0 < mass) :
    twoOutcomeSoftmax (Real.log mass) true = mass / (1 + mass) := by
  simp [twoOutcomeSoftmax, Real.exp_log hmass, add_comm]

/-! ## Arbitrary-depth linear-chain turnover -/

/-- State of a one-way linear chain, indexed by distance from its readout. -/
abbrev LinearTurnoverChainState := ℕ → ℝ

/-- The linear shift operator that advances every signal one position toward
the readout at index zero. -/
noncomputable def linearTurnoverShift :
    LinearTurnoverChainState →ₗ[ℝ] LinearTurnoverChainState where
  toFun state n := state (n + 1)
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro c x
    rfl

@[simp] theorem linearTurnoverShift_apply
    (state : LinearTurnoverChainState) (n : ℕ) :
    linearTurnoverShift state n = state (n + 1) := rfl

/-- Iterating the linear shift reads the state exactly `steps` positions
farther upstream. -/
theorem linearTurnoverShift_iterate_apply
    (steps : ℕ) (state : LinearTurnoverChainState) (n : ℕ) :
    (Nat.iterate linearTurnoverShift steps state) n = state (n + steps) := by
  induction steps generalizing state n with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      simp only [linearTurnoverShift_apply]
      rw [ih]
      congr 1
      omega

/-- A soft target's log-odds, used as its exact two-outcome softmax logit. -/
noncomputable def softTargetLogit (target : ℝ) : ℝ :=
  Real.log (target / (1 - target))

theorem twoOutcomeSoftmax_softTargetLogit
    (target : ℝ) (htarget : target ∈ Ioo (0 : ℝ) 1) :
    twoOutcomeSoftmax (softTargetLogit target) true = target := by
  have hden : 1 - target ≠ 0 := ne_of_gt (sub_pos.mpr htarget.2)
  rw [softTargetLogit, twoOutcomeSoftmax_true_log]
  · field_simp [hden]
    ring
  · exact div_pos htarget.1 (sub_pos.mpr htarget.2)

/-- Initial state with the target logit placed at any requested finite depth. -/
noncomputable def arbitraryDepthTurnoverInitialState
    (depth : ℕ) (target : ℝ) : LinearTurnoverChainState :=
  fun n => if n = depth then softTargetLogit target else 0

/-- Linear-chain state after `steps` settling shifts. -/
noncomputable def arbitraryDepthTurnoverState
    (depth : ℕ) (target : ℝ) (steps : ℕ) : LinearTurnoverChainState :=
  Nat.iterate linearTurnoverShift steps
    (arbitraryDepthTurnoverInitialState depth target)

/-- Logit visible at the readout after a requested number of shifts. -/
noncomputable def arbitraryDepthTurnoverReadoutLogit
    (depth : ℕ) (target : ℝ) (steps : ℕ) : ℝ :=
  arbitraryDepthTurnoverState depth target steps 0

theorem arbitraryDepthTurnoverReadoutLogit_eq
    (depth : ℕ) (target : ℝ) (steps : ℕ) :
    arbitraryDepthTurnoverReadoutLogit depth target steps =
      if steps = depth then softTargetLogit target else 0 := by
  rw [arbitraryDepthTurnoverReadoutLogit, arbitraryDepthTurnoverState,
    linearTurnoverShift_iterate_apply]
  simp [arbitraryDepthTurnoverInitialState]

/-- Positive-outcome probability at the arbitrary-depth readout. -/
noncomputable def arbitraryDepthTurnoverProbability
    (depth : ℕ) (target : ℝ) (steps : ℕ) : ℝ :=
  twoOutcomeSoftmax
    (arbitraryDepthTurnoverReadoutLogit depth target steps) true

theorem arbitraryDepthTurnoverProbability_at_target
    (depth : ℕ) (target : ℝ) (htarget : target ∈ Ioo (0 : ℝ) 1) :
    arbitraryDepthTurnoverProbability depth target depth = target := by
  rw [arbitraryDepthTurnoverProbability,
    arbitraryDepthTurnoverReadoutLogit_eq, if_pos rfl]
  exact twoOutcomeSoftmax_softTargetLogit target htarget

theorem arbitraryDepthTurnoverProbability_away_from_target
    (depth : ℕ) (target : ℝ) (steps : ℕ) (hne : steps ≠ depth) :
    arbitraryDepthTurnoverProbability depth target steps = 1 / 2 := by
  rw [arbitraryDepthTurnoverProbability,
    arbitraryDepthTurnoverReadoutLogit_eq, if_neg hne]
  norm_num [twoOutcomeSoftmax]

/-- Output entropy along the arbitrary-depth linear chain. -/
noncomputable def arbitraryDepthTurnoverEntropy
    (depth : ℕ) (target : ℝ) (steps : ℕ) : ℝ :=
  Real.binEntropy (arbitraryDepthTurnoverProbability depth target steps)

theorem arbitraryDepthTurnoverEntropy_at_target
    (depth : ℕ) (target : ℝ) (htarget : target ∈ Ioo (0 : ℝ) 1) :
    arbitraryDepthTurnoverEntropy depth target depth = Real.binEntropy target := by
  simp [arbitraryDepthTurnoverEntropy,
    arbitraryDepthTurnoverProbability_at_target depth target htarget]

theorem arbitraryDepthTurnoverEntropy_away_from_target
    (depth : ℕ) (target : ℝ) (steps : ℕ) (hne : steps ≠ depth) :
    arbitraryDepthTurnoverEntropy depth target steps = Real.binEntropy (1 / 2) := by
  simp [arbitraryDepthTurnoverEntropy,
    arbitraryDepthTurnoverProbability_away_from_target depth target steps hne]

/-- Every interior nonuniform soft target has entropy strictly below the
uniform binary distribution. -/
theorem binEntropy_lt_uniform_of_nonuniform
    (target : ℝ) (htarget : target ∈ Ioo (0 : ℝ) 1)
    (hne : target ≠ 1 / 2) :
    Real.binEntropy target < Real.binEntropy (1 / 2) := by
  have hne' : target ≠ (2 : ℝ)⁻¹ := by simpa [one_div] using hne
  rcases lt_or_gt_of_ne hne' with hlow | hhigh
  · simpa [one_div] using Real.binEntropy_strictMonoOn
      ⟨le_of_lt htarget.1, le_of_lt hlow⟩ (by norm_num) hlow
  · simpa [one_div] using Real.binEntropy_strictAntiOn
      (by norm_num) ⟨le_of_lt hhigh, le_of_lt htarget.2⟩ hhigh

theorem arbitraryDepthTurnoverEntropy_before_target
    (depth : ℕ) (target : ℝ) (htarget : target ∈ Ioo (0 : ℝ) 1)
    (hne : target ≠ 1 / 2) (hdepth : 0 < depth) :
    Real.binEntropy target < arbitraryDepthTurnoverEntropy depth target 0 := by
  rw [arbitraryDepthTurnoverEntropy_away_from_target depth target 0 (by omega)]
  exact binEntropy_lt_uniform_of_nonuniform target htarget hne

theorem arbitraryDepthTurnoverEntropy_after_target
    (depth : ℕ) (target : ℝ) (htarget : target ∈ Ioo (0 : ℝ) 1)
    (hne : target ≠ 1 / 2) :
    Real.binEntropy target <
      arbitraryDepthTurnoverEntropy depth target (depth + 1) := by
  rw [arbitraryDepthTurnoverEntropy_away_from_target depth target (depth + 1) (by omega)]
  exact binEntropy_lt_uniform_of_nonuniform target htarget hne

theorem arbitraryDepthTurnoverEntropy_not_monotone
    (depth : ℕ) (target : ℝ) (htarget : target ∈ Ioo (0 : ℝ) 1)
    (hne : target ≠ 1 / 2) (hdepth : 0 < depth) :
    ¬ Monotone (arbitraryDepthTurnoverEntropy depth target) := by
  intro hmono
  have hzeroDepth := hmono (Nat.zero_le depth)
  rw [arbitraryDepthTurnoverEntropy_away_from_target depth target 0 (by omega),
    arbitraryDepthTurnoverEntropy_at_target depth target htarget] at hzeroDepth
  exact (not_lt_of_ge hzeroDepth)
    (binEntropy_lt_uniform_of_nonuniform target htarget hne)

theorem arbitraryDepthTurnoverEntropy_not_antitone
    (depth : ℕ) (target : ℝ) (htarget : target ∈ Ioo (0 : ℝ) 1)
    (hne : target ≠ 1 / 2) :
    ¬ Antitone (arbitraryDepthTurnoverEntropy depth target) := by
  intro hanti
  have hdepthSucc := hanti (Nat.le_succ depth)
  rw [arbitraryDepthTurnoverEntropy_at_target depth target htarget,
    arbitraryDepthTurnoverEntropy_away_from_target depth target (depth + 1) (by omega)]
    at hdepthSucc
  exact (not_lt_of_ge hdepthSucc)
    (binEntropy_lt_uniform_of_nonuniform target htarget hne)

/-- A uniform target yields a constant entropy sequence, furnishing the
negative boundary for turnover. -/
theorem arbitraryDepthTurnoverEntropy_uniform
    (depth steps : ℕ) :
    arbitraryDepthTurnoverEntropy depth (1 / 2) steps =
      Real.binEntropy (1 / 2) := by
  by_cases hsteps : steps = depth
  · subst steps
    exact arbitraryDepthTurnoverEntropy_at_target depth (1 / 2) (by norm_num)
  · exact arbitraryDepthTurnoverEntropy_away_from_target depth (1 / 2) steps hsteps

theorem arbitraryDepthTurnoverEntropy_uniform_monotone
    (depth : ℕ) :
    Monotone (arbitraryDepthTurnoverEntropy depth (1 / 2)) ∧
      Antitone (arbitraryDepthTurnoverEntropy depth (1 / 2)) := by
  constructor <;> intro a b hab <;>
    rw [arbitraryDepthTurnoverEntropy_uniform,
      arbitraryDepthTurnoverEntropy_uniform]

/-- Exact nonmonotonicity condition for positive chain depth and interior soft
targets: turnover occurs exactly when the target is nonuniform. -/
theorem arbitraryDepthTurnoverEntropy_nonmonotone_iff
    (depth : ℕ) (target : ℝ) (htarget : target ∈ Ioo (0 : ℝ) 1)
    (hdepth : 0 < depth) :
    (¬ Monotone (arbitraryDepthTurnoverEntropy depth target) ∧
        ¬ Antitone (arbitraryDepthTurnoverEntropy depth target)) ↔
      target ≠ 1 / 2 := by
  constructor
  · rintro ⟨hnotMono, _hnotAnti⟩ rfl
    exact hnotMono (arbitraryDepthTurnoverEntropy_uniform_monotone depth).1
  · intro hne
    exact ⟨arbitraryDepthTurnoverEntropy_not_monotone
        depth target htarget hne hdepth,
      arbitraryDepthTurnoverEntropy_not_antitone depth target htarget hne⟩

/-- A canonical comparator that moves an interior target halfway toward the
nearer deterministic endpoint. -/
noncomputable def decisiveSoftTargetComparator (target : ℝ) : ℝ :=
  if target < (2 : ℝ)⁻¹ then target / 2 else (target + 1) / 2

/-- The canonical more-decisive comparator has entropy strictly below every
interior nonuniform soft target. -/
theorem decisiveSoftTargetComparator_entropy_lt_target
    (target : ℝ) (htarget : target ∈ Ioo (0 : ℝ) 1)
    (hne : target ≠ 1 / 2) :
    Real.binEntropy (decisiveSoftTargetComparator target) <
      Real.binEntropy target := by
  have hne' : target ≠ (2 : ℝ)⁻¹ := by simpa [one_div] using hne
  by_cases hlow : target < (2 : ℝ)⁻¹
  · have hcomparator : target / 2 ∈ Icc (0 : ℝ) (2 : ℝ)⁻¹ := by
      constructor <;> nlinarith [htarget.1]
    have htargetHalf : target ∈ Icc (0 : ℝ) (2 : ℝ)⁻¹ :=
      ⟨le_of_lt htarget.1, le_of_lt hlow⟩
    simpa [decisiveSoftTargetComparator, hlow] using
      Real.binEntropy_strictMonoOn hcomparator htargetHalf (by nlinarith [htarget.1])
  · have hhigh : (2 : ℝ)⁻¹ < target := by
      have hle : (2 : ℝ)⁻¹ ≤ target := le_of_not_gt hlow
      exact lt_of_le_of_ne hle (Ne.symm hne')
    have htargetHalf : target ∈ Icc (2 : ℝ)⁻¹ 1 :=
      ⟨le_of_lt hhigh, le_of_lt htarget.2⟩
    have hcomparator : (target + 1) / 2 ∈ Icc (2 : ℝ)⁻¹ 1 := by
      constructor <;> nlinarith [htarget.2]
    simpa [decisiveSoftTargetComparator, hlow] using
      Real.binEntropy_strictAntiOn htargetHalf hcomparator (by nlinarith [htarget.2])

/-- Crown: for every positive depth and every interior nonuniform soft target,
the arbitrary linear chain starts above target entropy, hits the target, rises
above it again, is neither monotone nor antitone, and admits a comparator below
the target. -/
theorem arbitraryDepthLinearEntropyTurnover_general
    (depth : ℕ) (target : ℝ) (htarget : target ∈ Ioo (0 : ℝ) 1)
    (hne : target ≠ 1 / 2) (hdepth : 0 < depth) :
    Real.binEntropy target < arbitraryDepthTurnoverEntropy depth target 0 ∧
      arbitraryDepthTurnoverEntropy depth target depth = Real.binEntropy target ∧
      Real.binEntropy target <
        arbitraryDepthTurnoverEntropy depth target (depth + 1) ∧
      ¬ Monotone (arbitraryDepthTurnoverEntropy depth target) ∧
      ¬ Antitone (arbitraryDepthTurnoverEntropy depth target) ∧
      Real.binEntropy (decisiveSoftTargetComparator target) <
        Real.binEntropy target := by
  exact ⟨arbitraryDepthTurnoverEntropy_before_target
      depth target htarget hne hdepth,
    arbitraryDepthTurnoverEntropy_at_target depth target htarget,
    arbitraryDepthTurnoverEntropy_after_target depth target htarget hne,
    arbitraryDepthTurnoverEntropy_not_monotone depth target htarget hne hdepth,
    arbitraryDepthTurnoverEntropy_not_antitone depth target htarget hne,
    decisiveSoftTargetComparator_entropy_lt_target target htarget hne⟩

/-- Positive fixture at depth four with the original `3/4` soft target. -/
theorem arbitraryDepthLinearEntropyTurnover_depth_four :
    Real.binEntropy (3 / 4) < arbitraryDepthTurnoverEntropy 4 (3 / 4) 0 ∧
      arbitraryDepthTurnoverEntropy 4 (3 / 4) 4 = Real.binEntropy (3 / 4) ∧
      Real.binEntropy (3 / 4) < arbitraryDepthTurnoverEntropy 4 (3 / 4) 5 := by
  have h := arbitraryDepthLinearEntropyTurnover_general 4 (3 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-! ## A two-node nilpotent linear settling chain -/

/-- State `(readout, upstream)` for the minimal linear settling chain. -/
abbrev EntropyTurnoverState := ℝ × ℝ

/-- One linear settling step shifts the upstream signal into the readout. -/
noncomputable def entropyTurnoverStep (state : EntropyTurnoverState) :
    EntropyTurnoverState := (state.2, 0)

/-- The logit whose softmax probability is the soft target `3/4`. -/
noncomputable def entropyTurnoverTargetLogit : ℝ := Real.log 3

/-- Initially the target signal is upstream of a uniform readout. -/
noncomputable def entropyTurnoverInitialState : EntropyTurnoverState :=
  (0, entropyTurnoverTargetLogit)

/-- State after a specified number of linear settling steps. -/
noncomputable def entropyTurnoverState (depth : ℕ) : EntropyTurnoverState :=
  (entropyTurnoverStep^[depth]) entropyTurnoverInitialState

/-- The first coordinate is read out as a two-outcome softmax logit. -/
noncomputable def entropyTurnoverReadoutLogit (depth : ℕ) : ℝ :=
  (entropyTurnoverState depth).1

@[simp] theorem entropyTurnoverReadoutLogit_zero :
    entropyTurnoverReadoutLogit 0 = 0 := by
  rfl

@[simp] theorem entropyTurnoverReadoutLogit_one :
    entropyTurnoverReadoutLogit 1 = entropyTurnoverTargetLogit := by
  rfl

@[simp] theorem entropyTurnoverReadoutLogit_two :
    entropyTurnoverReadoutLogit 2 = 0 := by
  rfl

/-- Probability assigned to the positive outcome at a given settling depth. -/
noncomputable def entropyTurnoverProbability (depth : ℕ) : ℝ :=
  twoOutcomeSoftmax (entropyTurnoverReadoutLogit depth) true

/-- Binary output entropy at a given settling depth. -/
noncomputable def entropyTurnoverOutputEntropy (depth : ℕ) : ℝ :=
  Real.binEntropy (entropyTurnoverProbability depth)

/-- The fitted soft target puts mass `3/4` on the positive outcome. -/
noncomputable def entropyTurnoverSoftTarget : ℝ := 3 / 4

/-- Entropy of the fitted soft target. -/
noncomputable def entropyTurnoverTargetEntropy : ℝ :=
  Real.binEntropy entropyTurnoverSoftTarget

@[simp] theorem entropyTurnoverProbability_zero :
    entropyTurnoverProbability 0 = 1 / 2 := by
  norm_num [entropyTurnoverProbability, twoOutcomeSoftmax]

@[simp] theorem entropyTurnoverProbability_one :
    entropyTurnoverProbability 1 = entropyTurnoverSoftTarget := by
  rw [entropyTurnoverProbability, entropyTurnoverReadoutLogit_one]
  norm_num [entropyTurnoverTargetLogit, entropyTurnoverSoftTarget,
    twoOutcomeSoftmax_true_log (3 : ℝ) (by norm_num)]

@[simp] theorem entropyTurnoverProbability_two :
    entropyTurnoverProbability 2 = 1 / 2 := by
  norm_num [entropyTurnoverProbability, twoOutcomeSoftmax]

@[simp] theorem entropyTurnoverOutputEntropy_zero :
    entropyTurnoverOutputEntropy 0 = Real.binEntropy (1 / 2) := by
  simp [entropyTurnoverOutputEntropy]

@[simp] theorem entropyTurnoverOutputEntropy_one :
    entropyTurnoverOutputEntropy 1 = entropyTurnoverTargetEntropy := by
  simp [entropyTurnoverOutputEntropy, entropyTurnoverTargetEntropy]

@[simp] theorem entropyTurnoverOutputEntropy_two :
    entropyTurnoverOutputEntropy 2 = Real.binEntropy (1 / 2) := by
  simp [entropyTurnoverOutputEntropy]

theorem entropyTurnover_targetEntropy_lt_uniform :
    entropyTurnoverTargetEntropy < Real.binEntropy (1 / 2) := by
  unfold entropyTurnoverTargetEntropy entropyTurnoverSoftTarget
  exact Real.binEntropy_strictAntiOn
    (by norm_num : (1 / 2 : ℝ) ∈ Icc 2⁻¹ 1)
    (by norm_num : (3 / 4 : ℝ) ∈ Icc 2⁻¹ 1)
    (by norm_num)

/-! ## The finite turnover witness -/

/-- Before the signal arrives, the uniform output is more diffuse than the target. -/
theorem entropyTurnover_underSettling_above_target :
    entropyTurnoverTargetEntropy < entropyTurnoverOutputEntropy 0 := by
  simpa using entropyTurnover_targetEntropy_lt_uniform

/-- At one settling step, the softmax readout fits the soft target exactly. -/
theorem entropyTurnover_exactSettling_hits_target :
    entropyTurnoverOutputEntropy 1 = entropyTurnoverTargetEntropy :=
  entropyTurnoverOutputEntropy_one

/-- A second shift removes the signal from the readout and increases entropy again. -/
theorem entropyTurnover_overSettling_rediffuses_above_target :
    entropyTurnoverTargetEntropy < entropyTurnoverOutputEntropy 2 := by
  simpa using entropyTurnover_targetEntropy_lt_uniform

theorem entropyTurnoverOutputEntropy_not_monotone :
    ¬ Monotone entropyTurnoverOutputEntropy := by
  intro h
  have h01 := h (show 0 ≤ 1 by omega)
  rw [entropyTurnoverOutputEntropy_zero, entropyTurnoverOutputEntropy_one] at h01
  exact (not_lt_of_ge h01) entropyTurnover_targetEntropy_lt_uniform

theorem entropyTurnoverOutputEntropy_not_antitone :
    ¬ Antitone entropyTurnoverOutputEntropy := by
  intro h
  have h12 := h (show 1 ≤ 2 by omega)
  rw [entropyTurnoverOutputEntropy_one, entropyTurnoverOutputEntropy_two] at h12
  exact (not_lt_of_ge h12) entropyTurnover_targetEntropy_lt_uniform

/-- Crown: output entropy decreases and then increases across depths `0, 1, 2`. -/
theorem entropyTurnoverOutputEntropy_nonmonotone :
    ¬ Monotone entropyTurnoverOutputEntropy ∧
      ¬ Antitone entropyTurnoverOutputEntropy :=
  ⟨entropyTurnoverOutputEntropy_not_monotone,
    entropyTurnoverOutputEntropy_not_antitone⟩

/-! ## An over-decisive hard-target gradient comparator -/

/-- Binary hard-target cross-entropy for the positive outcome. -/
noncomputable def hardTargetSoftmaxLoss (logit : ℝ) : ℝ :=
  Real.log (1 + Real.exp (-logit))

/-- The exact gradient of positive hard-target cross-entropy. -/
noncomputable def hardTargetSoftmaxGradient (logit : ℝ) : ℝ :=
  Real.sigmoid logit - 1

theorem hardTargetSoftmaxLoss_hasDerivAt (logit : ℝ) :
    HasDerivAt hardTargetSoftmaxLoss (hardTargetSoftmaxGradient logit) logit := by
  unfold hardTargetSoftmaxLoss hardTargetSoftmaxGradient
  convert! (hasDerivAt_neg' logit |>.exp.const_add 1 |>.log <| by positivity) using 1
  rw [Real.sigmoid_def]
  field_simp
  ring

/-- A positive step size chosen so one hard-target gradient step reaches logit `log 7`. -/
noncomputable def hardTargetComparatorStepSize : ℝ :=
  4 * (Real.log 7 - Real.log 3)

theorem hardTargetComparatorStepSize_pos : 0 < hardTargetComparatorStepSize := by
  unfold hardTargetComparatorStepSize
  positivity [Real.log_lt_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) < 7)]

/-- One hard-target gradient step starting from the exact soft-target logit. -/
noncomputable def hardTargetComparatorLogit : ℝ :=
  entropyTurnoverTargetLogit -
    hardTargetComparatorStepSize * hardTargetSoftmaxGradient entropyTurnoverTargetLogit

theorem hardTargetComparatorLogit_eq_log_seven :
    hardTargetComparatorLogit = Real.log 7 := by
  rw [hardTargetComparatorLogit, hardTargetSoftmaxGradient,
    ← twoOutcomeSoftmax_true_eq_sigmoid, entropyTurnoverTargetLogit,
    twoOutcomeSoftmax_true_log (3 : ℝ) (by norm_num)]
  unfold hardTargetComparatorStepSize
  ring

/-- Positive-outcome probability of the hard-target gradient comparator. -/
noncomputable def hardTargetComparatorProbability : ℝ :=
  twoOutcomeSoftmax hardTargetComparatorLogit true

theorem hardTargetComparatorProbability_eq_seven_eighths :
    hardTargetComparatorProbability = 7 / 8 := by
  rw [hardTargetComparatorProbability, hardTargetComparatorLogit_eq_log_seven,
    twoOutcomeSoftmax_true_log (7 : ℝ) (by norm_num)]
  norm_num

/-- The hard-target gradient comparator is more decisive than the fitted soft target. -/
theorem hardTargetComparatorEntropy_below_target :
    Real.binEntropy hardTargetComparatorProbability < entropyTurnoverTargetEntropy := by
  rw [hardTargetComparatorProbability_eq_seven_eighths]
  unfold entropyTurnoverTargetEntropy entropyTurnoverSoftTarget
  exact Real.binEntropy_strictAntiOn
    (by norm_num : (3 / 4 : ℝ) ∈ Icc 2⁻¹ 1)
    (by norm_num : (7 / 8 : ℝ) ∈ Icc 2⁻¹ 1)
    (by norm_num)

/-- Crown fixture: under-settling and over-settling are more diffuse, exact settling
matches the soft target, and a hard-target gradient step is over-decisive. -/
theorem entropyTurnover_three_regimes_and_gradient_comparator :
    entropyTurnoverTargetEntropy < entropyTurnoverOutputEntropy 0 ∧
      entropyTurnoverOutputEntropy 1 = entropyTurnoverTargetEntropy ∧
      entropyTurnoverTargetEntropy < entropyTurnoverOutputEntropy 2 ∧
      Real.binEntropy hardTargetComparatorProbability < entropyTurnoverTargetEntropy :=
  ⟨entropyTurnover_underSettling_above_target,
    entropyTurnover_exactSettling_hits_target,
    entropyTurnover_overSettling_rediffuses_above_target,
    hardTargetComparatorEntropy_below_target⟩

/-! ## Monotone contractive nonlinear settling -/

/-- A scalar settling nonlinearity with a fixed zero, monotonicity, and a
global contraction rate strictly below one. -/
structure MonotoneContractiveSettling where
  activation : ℝ → ℝ
  contractionRate : ℝ
  zero_fixed : activation 0 = 0
  monotone : Monotone activation
  contractionRate_nonneg : 0 ≤ contractionRate
  contractionRate_lt_one : contractionRate < 1
  contractive : ∀ x y,
    |activation x - activation y| ≤ contractionRate * |x - y|

/-- A nonlinear shift applies the settling activation while moving a signal
one node toward the readout. -/
noncomputable def nonlinearTurnoverShift
    (settling : MonotoneContractiveSettling)
    (state : LinearTurnoverChainState) : LinearTurnoverChainState :=
  fun n => settling.activation (state (n + 1))

/-- Repeated nonlinear shifting is repeated activation of the state found at
the corresponding upstream depth. -/
theorem nonlinearTurnoverShift_iterate_apply
    (settling : MonotoneContractiveSettling)
    (steps : ℕ) (state : LinearTurnoverChainState) (n : ℕ) :
    ((nonlinearTurnoverShift settling)^[steps]) state n =
      (settling.activation^[steps]) (state (n + steps)) := by
  induction steps generalizing state n with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      simp only [nonlinearTurnoverShift]
      rw [ih]
      rw [Function.iterate_succ_apply']
      simp [Nat.add_comm, Nat.add_left_comm]

theorem MonotoneContractiveSettling.iterate_zero
    (settling : MonotoneContractiveSettling) (steps : ℕ) :
    (settling.activation^[steps]) 0 = 0 := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      simp [settling.zero_fixed, ih]

/-- Contractive settling exponentially bounds every iterated logit relative
to the zero fixed point. -/
theorem MonotoneContractiveSettling.iterate_abs_le
    (settling : MonotoneContractiveSettling) (steps : ℕ) (seed : ℝ) :
    |(settling.activation^[steps]) seed| ≤
      settling.contractionRate ^ steps * |seed| := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      calc
        |settling.activation ((settling.activation^[steps]) seed)| =
            |settling.activation ((settling.activation^[steps]) seed) -
              settling.activation 0| := by rw [settling.zero_fixed, sub_zero]
        _ ≤ settling.contractionRate *
            |(settling.activation^[steps]) seed - 0| :=
          settling.contractive _ 0
        _ ≤ settling.contractionRate *
            (settling.contractionRate ^ steps * |seed|) := by
          exact mul_le_mul_of_nonneg_left (by simpa using ih)
            settling.contractionRate_nonneg
        _ = settling.contractionRate ^ (steps + 1) * |seed| := by ring

/-- Seed a nonlinear chain at an arbitrary upstream depth. -/
noncomputable def nonlinearTurnoverInitialState
    (depth : ℕ) (seed : ℝ) : LinearTurnoverChainState :=
  fun n => if n = depth then seed else 0

/-- Nonlinear readout logit after a requested number of settling steps. -/
noncomputable def nonlinearTurnoverReadoutLogit
    (settling : MonotoneContractiveSettling)
    (depth : ℕ) (seed : ℝ) (steps : ℕ) : ℝ :=
  ((nonlinearTurnoverShift settling)^[steps])
    (nonlinearTurnoverInitialState depth seed) 0

theorem nonlinearTurnoverReadoutLogit_eq
    (settling : MonotoneContractiveSettling)
    (depth : ℕ) (seed : ℝ) (steps : ℕ) :
    nonlinearTurnoverReadoutLogit settling depth seed steps =
      if steps = depth then (settling.activation^[steps]) seed else 0 := by
  rw [nonlinearTurnoverReadoutLogit,
    nonlinearTurnoverShift_iterate_apply]
  simp only [zero_add, nonlinearTurnoverInitialState]
  split_ifs with h
  · rfl
  · exact settling.iterate_zero steps

/-- Positive-outcome probability under nonlinear settling. -/
noncomputable def nonlinearTurnoverProbability
    (settling : MonotoneContractiveSettling)
    (depth : ℕ) (seed : ℝ) (steps : ℕ) : ℝ :=
  twoOutcomeSoftmax
    (nonlinearTurnoverReadoutLogit settling depth seed steps) true

/-- Binary readout entropy under nonlinear settling. -/
noncomputable def nonlinearTurnoverEntropy
    (settling : MonotoneContractiveSettling)
    (depth : ℕ) (seed : ℝ) (steps : ℕ) : ℝ :=
  Real.binEntropy
    (nonlinearTurnoverProbability settling depth seed steps)

theorem nonlinearTurnoverProbability_at_reachable_target
    (settling : MonotoneContractiveSettling)
    (depth : ℕ) (target seed : ℝ)
    (htarget : target ∈ Ioo (0 : ℝ) 1)
    (hreach : (settling.activation^[depth]) seed = softTargetLogit target) :
    nonlinearTurnoverProbability settling depth seed depth = target := by
  rw [nonlinearTurnoverProbability, nonlinearTurnoverReadoutLogit_eq,
    if_pos rfl, hreach]
  exact twoOutcomeSoftmax_softTargetLogit target htarget

theorem nonlinearTurnoverProbability_away_from_seed
    (settling : MonotoneContractiveSettling)
    (depth : ℕ) (seed : ℝ) (steps : ℕ) (hne : steps ≠ depth) :
    nonlinearTurnoverProbability settling depth seed steps = 1 / 2 := by
  rw [nonlinearTurnoverProbability, nonlinearTurnoverReadoutLogit_eq,
    if_neg hne]
  norm_num [twoOutcomeSoftmax]

/-- Sufficient conditions for nonlinear entropy turnover: a monotone global
contraction with fixed zero, together with a seed whose depth iterate reaches
the desired nonuniform soft-target logit. -/
theorem monotoneContractiveNonlinearEntropyTurnover_sufficient
    (settling : MonotoneContractiveSettling)
    (depth : ℕ) (target seed : ℝ)
    (htarget : target ∈ Ioo (0 : ℝ) 1)
    (hnonuniform : target ≠ 1 / 2) (hdepth : 0 < depth)
    (hreach : (settling.activation^[depth]) seed = softTargetLogit target) :
    Real.binEntropy target < nonlinearTurnoverEntropy settling depth seed 0 ∧
      nonlinearTurnoverEntropy settling depth seed depth =
        Real.binEntropy target ∧
      Real.binEntropy target <
        nonlinearTurnoverEntropy settling depth seed (depth + 1) ∧
      ¬ Monotone (nonlinearTurnoverEntropy settling depth seed) ∧
      ¬ Antitone (nonlinearTurnoverEntropy settling depth seed) ∧
      |softTargetLogit target| ≤
        settling.contractionRate ^ depth * |seed| := by
  have hawayZero : nonlinearTurnoverProbability settling depth seed 0 = 1 / 2 :=
    nonlinearTurnoverProbability_away_from_seed settling depth seed 0 (by omega)
  have hawaySucc : nonlinearTurnoverProbability settling depth seed (depth + 1) = 1 / 2 :=
    nonlinearTurnoverProbability_away_from_seed settling depth seed (depth + 1) (by omega)
  have hatTarget : nonlinearTurnoverProbability settling depth seed depth = target :=
    nonlinearTurnoverProbability_at_reachable_target
      settling depth target seed htarget hreach
  have hentropy := binEntropy_lt_uniform_of_nonuniform target htarget hnonuniform
  have hbound := settling.iterate_abs_le depth seed
  rw [hreach] at hbound
  refine ⟨?_, ?_, ?_, ?_, ?_, hbound⟩
  · simpa [nonlinearTurnoverEntropy, hawayZero] using hentropy
  · simp [nonlinearTurnoverEntropy, hatTarget]
  · simpa [nonlinearTurnoverEntropy, hawaySucc] using hentropy
  · intro hmono
    have h := hmono (Nat.zero_le depth)
    change Real.binEntropy
        (nonlinearTurnoverProbability settling depth seed 0) ≤
      Real.binEntropy
        (nonlinearTurnoverProbability settling depth seed depth) at h
    rw [hawayZero, hatTarget] at h
    exact (not_lt_of_ge h) hentropy
  · intro hanti
    have h := hanti (Nat.le_succ depth)
    change Real.binEntropy
        (nonlinearTurnoverProbability settling depth seed (depth + 1)) ≤
      Real.binEntropy
        (nonlinearTurnoverProbability settling depth seed depth) at h
    rw [hawaySucc, hatTarget] at h
    exact (not_lt_of_ge h) hentropy

/-- Uniform reachable targets are the negative boundary: the three observed
entropy values coincide, so strict turnover cannot be concluded. -/
theorem monotoneContractiveNonlinearEntropyTurnover_uniform_boundary
    (settling : MonotoneContractiveSettling)
    (depth : ℕ) (seed : ℝ)
    (hreach : (settling.activation^[depth]) seed = softTargetLogit (1 / 2)) :
    nonlinearTurnoverEntropy settling depth seed depth = Real.binEntropy (1 / 2) ∧
      nonlinearTurnoverEntropy settling depth seed (depth + 1) =
        Real.binEntropy (1 / 2) := by
  constructor
  · simp [nonlinearTurnoverEntropy,
      nonlinearTurnoverProbability_at_reachable_target
        settling depth (1 / 2) seed (by norm_num) hreach]
  · simp [nonlinearTurnoverEntropy,
      nonlinearTurnoverProbability_away_from_seed settling depth seed
        (depth + 1) (by omega)]

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
