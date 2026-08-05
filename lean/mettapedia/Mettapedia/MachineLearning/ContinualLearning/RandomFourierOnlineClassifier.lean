import Mathlib

/-!
# Random Fourier features and online class means

Prabhu et al., *Random Representations Outperform Online Continually Learned
Representations* (NeurIPS 2024, arXiv:2402.08823), Section 2, use a frozen
random Fourier map followed by online class means and covariance
decorrelation.

This file isolates two exact parts of that mechanism:

* the normalized cosine--sine feature inner product is the empirical average
  of cosine phase differences, has unit self-similarity, and lies in
  `[-1, 1]`;
* the count-weighted online mean update represents every sample exactly once.

A periodic collision proves that finite trigonometric features are not
injective, even though their self-similarity is normalized.  The development
does not prove approximation of the RBF kernel in probability, concentration
in feature dimension, invertibility or estimation quality of the empirical
covariance, classification accuracy, or the paper's empirical comparison
with learned representations.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace RandomFourierOnlineClassifier

noncomputable section

/-- Inner product of the source's normalized cosine--sine random Fourier
features, expressed directly in phase coordinates. -/
def rffSimilarity {features : ℕ}
    (phaseX phaseY : Fin features → ℝ) : ℝ :=
  (∑ i, (Real.cos (phaseX i) * Real.cos (phaseY i) +
    Real.sin (phaseX i) * Real.sin (phaseY i))) / features

/-- The trigonometric feature inner product is exactly an empirical average
of cosine phase differences. -/
theorem rffSimilarity_eq_average_cos_sub {features : ℕ}
    (phaseX phaseY : Fin features → ℝ) :
    rffSimilarity phaseX phaseY =
      (∑ i, Real.cos (phaseX i - phaseY i)) / features := by
  unfold rffSimilarity
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.cos_sub]

/-- Every nonempty normalized random Fourier feature vector has unit
self-similarity, independently of its sampled frequencies and input. -/
theorem rffSimilarity_self {features : ℕ}
    (features_pos : 0 < features)
    (phase : Fin features → ℝ) :
    rffSimilarity phase phase = 1 := by
  rw [rffSimilarity_eq_average_cos_sub]
  simp [Nat.ne_of_gt features_pos]

/-- Every normalized finite random Fourier similarity lies in `[-1, 1]`. -/
theorem rffSimilarity_mem_Icc {features : ℕ}
    (features_pos : 0 < features)
    (phaseX phaseY : Fin features → ℝ) :
    rffSimilarity phaseX phaseY ∈ Set.Icc (-1) 1 := by
  rw [rffSimilarity_eq_average_cos_sub]
  have cast_pos : 0 < (features : ℝ) := by exact_mod_cast features_pos
  constructor
  · apply (le_div_iff₀ cast_pos).2
    calc
      (-1 : ℝ) * features =
          ∑ _i : Fin features, (-1 : ℝ) := by simp
      _ ≤ ∑ i : Fin features, Real.cos (phaseX i - phaseY i) := by
        exact Finset.sum_le_sum fun i _ => Real.neg_one_le_cos _
  · apply (div_le_iff₀ cast_pos).2
    calc
      ∑ i : Fin features, Real.cos (phaseX i - phaseY i)
          ≤ ∑ _i : Fin features, (1 : ℝ) := by
            exact Finset.sum_le_sum fun i _ => Real.cos_le_one _
      _ = (1 : ℝ) * features := by simp

/-- Symmetry of the finite random Fourier similarity. -/
theorem rffSimilarity_comm {features : ℕ}
    (phaseX phaseY : Fin features → ℝ) :
    rffSimilarity phaseX phaseY =
      rffSimilarity phaseY phaseX := by
  unfold rffSimilarity
  apply congrArg (fun value : ℝ => value / features)
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- One-dimensional zero phase. -/
def zeroPhase : Fin 1 → ℝ := fun _ => 0

/-- A phase shifted by one full period. -/
def twoPiPhase : Fin 1 → ℝ := fun _ => 2 * Real.pi

/-- The phase arrays in the periodic-collision fixture are genuinely
different. -/
theorem zeroPhase_ne_twoPiPhase :
    zeroPhase ≠ twoPiPhase := by
  intro equal
  have at_zero := congrFun equal (0 : Fin 1)
  simp [zeroPhase, twoPiPhase] at at_zero

/-- Finite trigonometric features are not injective: distinct phase arrays
separated by one period have maximal similarity. -/
theorem periodic_phase_collision :
    rffSimilarity zeroPhase twoPiPhase = 1 := by
  rw [rffSimilarity_eq_average_cos_sub]
  simp [zeroPhase, twoPiPhase, Real.cos_neg]

section OnlineMean

variable {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]

/-- Exactly weighted update from a mean of `count` samples to the mean after
one additional sample. -/
def onlineMeanUpdate
    (count : ℕ) (mean sample : State) : State :=
  ((count : ℝ) / ((count + 1 : ℕ) : ℝ)) • mean +
    (1 / ((count + 1 : ℕ) : ℝ)) • sample

/-- The first sample becomes the mean exactly. -/
@[simp]
theorem onlineMeanUpdate_zero
    (mean sample : State) :
    onlineMeanUpdate 0 mean sample = sample := by
  simp [onlineMeanUpdate]

/-- Multiplying the updated mean by its new count recovers the old weighted
sum plus the new sample. -/
theorem onlineMeanUpdate_balance
    (count : ℕ) (mean sample : State) :
    ((count + 1 : ℕ) : ℝ) • onlineMeanUpdate count mean sample =
      (count : ℝ) • mean + sample := by
  have denominator_ne : ((count + 1 : ℕ) : ℝ) ≠ 0 := by
    positivity
  unfold onlineMeanUpdate
  rw [smul_add]
  simp only [smul_smul]
  have old_coefficient :
      ((count + 1 : ℕ) : ℝ) *
          ((count : ℝ) / (count + 1 : ℕ)) = count := by
    field_simp
  have fresh_coefficient :
      ((count + 1 : ℕ) : ℝ) *
          (1 / (count + 1 : ℕ)) = 1 := by
    field_simp
  rw [old_coefficient, fresh_coefficient]
  simp

/-- Recursive online mean. Each tail mean is updated once with the new head
sample and the exact tail count. -/
def onlineMean : List State → State
  | [] => 0
  | sample :: samples =>
      onlineMeanUpdate samples.length (onlineMean samples) sample

/-- The recursive online mean counts every list element exactly once. -/
theorem length_smul_onlineMean_eq_sum :
    ∀ samples : List State,
      (samples.length : ℝ) • onlineMean samples = samples.sum
  | [] => by simp [onlineMean]
  | sample :: samples => by
      rw [List.length_cons, onlineMean, onlineMeanUpdate_balance]
      rw [length_smul_onlineMean_eq_sum samples]
      simp [add_comm]

/-- The two-sample mean is order-independent. -/
theorem onlineMean_pair_comm
    (first second : State) :
    onlineMean [first, second] = onlineMean [second, first] := by
  simp [onlineMean, onlineMeanUpdate]
  module

/-- A concrete two-sample fixture. -/
theorem onlineMean_pair :
    onlineMean ([2, 4] : List ℝ) = 3 := by
  norm_num [onlineMean, onlineMeanUpdate]

end OnlineMean

#print axioms rffSimilarity_self
#print axioms rffSimilarity_mem_Icc
#print axioms periodic_phase_collision
#print axioms onlineMeanUpdate_balance
#print axioms length_smul_onlineMean_eq_sum
#print axioms onlineMean_pair_comm

end

end RandomFourierOnlineClassifier

end Mettapedia.MachineLearning.ContinualLearning
