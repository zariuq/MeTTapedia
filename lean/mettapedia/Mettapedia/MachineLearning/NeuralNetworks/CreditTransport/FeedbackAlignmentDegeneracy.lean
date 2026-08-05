import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FeedbackAlignmentDynamics

/-!
# Feedback alignment and degeneracy breaking

Refinetti, d'Ascoli, Ohana, and Goldt, *Align, then memorise: the dynamics
of learning with feedback alignment* (arXiv:2011.12428), identify two related
mechanisms:

* among sign-symmetric minima, feedback alignment selects the representative
  with maximal overlap with the fixed feedback vector;
* a ReLU network cannot repair a wrong output-weight sign through its positive
  rescaling symmetry, so extra hidden units increase the probability of having
  enough compatible feedback signs.

This file isolates both statements as finite exact mathematics.  The first
becomes a coordinatewise maximization theorem with a strict uniqueness
criterion.  The second derives the source's binomial recovery probability from
the finite set of compatible sign configurations and proves an exact recurrence
showing strict improvement with every additional hidden unit.

These results describe the geometry and combinatorics of the proposed
mechanism.  They do not assert that a particular optimizer reaches the selected
minimum or that independent uniform feedback signs model a trained network.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace FeedbackAlignmentDegeneracy

open scoped BigOperators

/-! ## Signed degeneracy selection -/

/-- The two sign choices relating sign-symmetric parameterizations. -/
inductive BinarySign where
  | negative
  | positive
  deriving DecidableEq

/-- Real multiplier represented by a binary sign. -/
def BinarySign.factor : BinarySign → ℝ
  | .negative => -1
  | .positive => 1

/-- The sign choice maximizing `coefficient * sign`.  At zero, the positive
choice is canonical but not uniquely optimal. -/
noncomputable def maximizingSign (coefficient : ℝ) : BinarySign :=
  if 0 ≤ coefficient then .positive else .negative

/-- The maximizing sign attains the absolute-value envelope. -/
theorem mul_maximizingSign_eq_abs (coefficient : ℝ) :
    coefficient * (maximizingSign coefficient).factor =
      |coefficient| := by
  by_cases hcoefficient : 0 ≤ coefficient
  · simp [maximizingSign, hcoefficient, BinarySign.factor,
      abs_of_nonneg hcoefficient]
  · have hnegative : coefficient < 0 := lt_of_not_ge hcoefficient
    simp [maximizingSign, hcoefficient, BinarySign.factor,
      abs_of_neg hnegative]

/-- Every binary sign lies below the absolute-value envelope. -/
theorem mul_sign_le_abs
    (coefficient : ℝ) (sign : BinarySign) :
    coefficient * sign.factor ≤ |coefficient| := by
  cases sign with
  | negative =>
      simpa [BinarySign.factor] using neg_le_abs coefficient
  | positive =>
      simpa [BinarySign.factor] using le_abs_self coefficient

/-- At a nonzero coefficient, every nonmaximizing sign is strictly worse. -/
theorem mul_sign_lt_abs_of_ne
    (coefficient : ℝ) (sign : BinarySign)
    (hcoefficient : coefficient ≠ 0)
    (hsign : sign ≠ maximizingSign coefficient) :
    coefficient * sign.factor < |coefficient| := by
  cases sign with
  | negative =>
      by_cases hnonneg : 0 ≤ coefficient
      · have hpositive : 0 < coefficient :=
          lt_of_le_of_ne hnonneg (Ne.symm hcoefficient)
        simp [BinarySign.factor, abs_of_pos hpositive]
        linarith
      · simp [maximizingSign, hnonneg] at hsign
  | positive =>
      by_cases hnonneg : 0 ≤ coefficient
      · simp [maximizingSign, hnonneg] at hsign
      · have hnegative : coefficient < 0 := lt_of_not_ge hnonneg
        simp [BinarySign.factor, abs_of_neg hnegative]
        exact hnegative

variable {ι : Type} [Fintype ι]

/-- Feedback overlap of a representative from a sign-symmetric family.  The
coefficient may combine a feedback component and the corresponding teacher
weight. -/
def feedbackOverlap
    (coefficient : ι → ℝ) (signs : ι → BinarySign) : ℝ :=
  ∑ i, coefficient i * (signs i).factor

/-- Coordinatewise representative selected by feedback overlap. -/
noncomputable def optimalSigns
    (coefficient : ι → ℝ) : ι → BinarySign :=
  fun i => maximizingSign (coefficient i)

/-- The selected representative attains the sum of absolute coordinate
overlaps. -/
theorem feedbackOverlap_optimal_eq_sum_abs
    (coefficient : ι → ℝ) :
    feedbackOverlap coefficient (optimalSigns coefficient) =
      ∑ i, |coefficient i| := by
  apply Finset.sum_congr rfl
  intro i _
  exact mul_maximizingSign_eq_abs (coefficient i)

/-- No sign-symmetric representative has greater feedback overlap. -/
theorem feedbackOverlap_le_optimal
    (coefficient : ι → ℝ) (signs : ι → BinarySign) :
    feedbackOverlap coefficient signs ≤
      feedbackOverlap coefficient (optimalSigns coefficient) := by
  rw [feedbackOverlap_optimal_eq_sum_abs]
  exact Finset.sum_le_sum fun i _ =>
    mul_sign_le_abs (coefficient i) (signs i)

/-- A wrong sign at any nonzero coordinate gives strictly smaller overlap. -/
theorem feedbackOverlap_lt_optimal_of_mismatch
    (coefficient : ι → ℝ) (signs : ι → BinarySign) (i : ι)
    (hcoefficient : coefficient i ≠ 0)
    (hmismatch : signs i ≠ optimalSigns coefficient i) :
    feedbackOverlap coefficient signs <
      feedbackOverlap coefficient (optimalSigns coefficient) := by
  rw [feedbackOverlap_optimal_eq_sum_abs]
  apply Finset.sum_lt_sum
  · intro j _
    exact mul_sign_le_abs (coefficient j) (signs j)
  · exact
      ⟨i, Finset.mem_univ i,
        mul_sign_lt_abs_of_ne
          (coefficient i) (signs i) hcoefficient hmismatch⟩

/-- If every coordinate coefficient is nonzero, the overlap maximizer is
unique. -/
theorem signs_eq_optimal_of_overlap_eq
    (coefficient : ι → ℝ) (signs : ι → BinarySign)
    (hcoefficient : ∀ i, coefficient i ≠ 0)
    (hoverlap :
      feedbackOverlap coefficient signs =
        feedbackOverlap coefficient (optimalSigns coefficient)) :
    signs = optimalSigns coefficient := by
  funext i
  by_contra hmismatch
  have hstrict :=
    feedbackOverlap_lt_optimal_of_mismatch
      coefficient signs i (hcoefficient i) hmismatch
  linarith

/-! ## The ReLU sign boundary -/

/-- Scalar ReLU. -/
def relu (x : ℝ) : ℝ :=
  max 0 x

/-- Exact positive-rescaling symmetry used in the source analysis. -/
theorem relu_positive_rescale
    (x scale : ℝ) (hscale : 0 < scale) :
    relu x = scale * relu (x / scale) := by
  by_cases hx : 0 ≤ x
  · have hdiv : 0 ≤ x / scale := div_nonneg hx hscale.le
    rw [relu, max_eq_right hx, relu, max_eq_right hdiv]
    field_simp
  · have hx' : x < 0 := lt_of_not_ge hx
    have hdiv : x / scale < 0 := div_neg_of_neg_of_pos hx' hscale
    rw [relu, max_eq_left (le_of_lt hx'), relu,
      max_eq_left (le_of_lt hdiv)]
    ring

/-- Positive rescaling cannot reverse a nonzero output-weight sign. -/
theorem positive_rescale_cannot_flip_nonzero
    (weight scale : ℝ) (hscale : 0 < scale)
    (hweight : weight ≠ 0) :
    scale * weight ≠ -weight := by
  intro heq
  have hproduct : (scale + 1) * weight = 0 := by
    linarith
  rcases mul_eq_zero.mp hproduct with hsum | hzero
  · linarith
  · exact hweight hzero

/-! ## Uniform sign recovery and over-parameterization -/

/-- Compatible sign configurations represented by the subset of hidden units
whose feedback sign agrees with the required teacher sign. -/
def recoverySignSets
    (width required : ℕ) : Finset (Finset (Fin width)) :=
  (Finset.Icc required width).disjiUnion
    (fun k =>
      Finset.powersetCard k (Finset.univ : Finset (Fin width)))
    ((Finset.pairwise_disjoint_powersetCard
      (Finset.univ : Finset (Fin width))).set_pairwise _)

/-- Membership is exactly the source criterion: at least `required` compatible
signs. -/
theorem mem_recoverySignSets_iff
    (width required : ℕ) (signSet : Finset (Fin width)) :
    signSet ∈ recoverySignSets width required ↔
      required ≤ signSet.card ∧ signSet.card ≤ width := by
  simp [recoverySignSets, Finset.mem_powersetCard]

/-- The number of compatible sign configurations is the upper binomial tail. -/
theorem card_recoverySignSets
    (width required : ℕ) :
    (recoverySignSets width required).card =
      ∑ k ∈ Finset.Icc required width, width.choose k := by
  rw [recoverySignSets, Finset.card_disjiUnion]
  simp [Finset.card_powersetCard]

/-- Partial binomial sum through index `radius`. -/
def partialChooseSum (width radius : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (radius + 1), width.choose k

/-- Adding one term to a partial binomial sum. -/
theorem partialChooseSum_succ (width radius : ℕ) :
    partialChooseSum width (radius + 1) =
      partialChooseSum width radius +
        width.choose (radius + 1) := by
  simp [partialChooseSum, Finset.sum_range_succ]

/-- Pascal recurrence for partial binomial sums. -/
theorem partialChooseSum_pascal (width radius : ℕ) :
    partialChooseSum (width + 1) (radius + 1) =
      partialChooseSum width (radius + 1) +
        partialChooseSum width radius := by
  induction radius with
  | zero =>
      simp [partialChooseSum, Finset.sum_range_succ]
      omega
  | succ radius ih =>
      calc
        partialChooseSum (width + 1) (radius + 1 + 1) =
            partialChooseSum (width + 1) (radius + 1) +
              (width + 1).choose (radius + 1 + 1) :=
          partialChooseSum_succ (width + 1) (radius + 1)
        _ =
            (partialChooseSum width (radius + 1) +
                partialChooseSum width radius) +
              (width.choose (radius + 1) +
                width.choose (radius + 1 + 1)) := by
          rw [ih, Nat.choose_succ_succ']
        _ =
            partialChooseSum width (radius + 1 + 1) +
              partialChooseSum width (radius + 1) := by
          have hfirst := partialChooseSum_succ width radius
          have hsecond := partialChooseSum_succ width (radius + 1)
          omega

/-- Binomial symmetry converts the compatible upper tail into the lower-tail
form displayed by the source. -/
theorem upperChooseSum_eq_partial
    (width required : ℕ) (hrequired : required ≤ width) :
    (∑ k ∈ Finset.Icc required width, width.choose k) =
      partialChooseSum width (width - required) := by
  unfold partialChooseSum
  apply Finset.sum_bij'
      (fun k _ => width - k)
      (fun k _ => width - k)
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Icc]
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    exact (Nat.choose_symm hk.2).symm

/-- Exact number of compatible configurations. -/
def recoveryCount (width required : ℕ) : ℕ :=
  (recoverySignSets width required).card

/-- Exact reported binomial formula for the compatible-sign count. -/
theorem recoveryCount_eq_partial
    (width required : ℕ) (hrequired : required ≤ width) :
    recoveryCount width required =
      partialChooseSum width (width - required) := by
  rw [recoveryCount, card_recoverySignSets,
    upperChooseSum_eq_partial width required hrequired]

/-- Adding one hidden unit adds a strictly identified binomial slice to twice
the preceding compatible count. -/
theorem recoveryCount_succ
    (width required : ℕ) (hrequired : required ≤ width) :
    recoveryCount (width + 1) required =
      2 * recoveryCount width required +
        width.choose (width - required + 1) := by
  rw [recoveryCount_eq_partial width required hrequired]
  rw [recoveryCount_eq_partial (width + 1) required (by omega)]
  have hsub :
      width + 1 - required = width - required + 1 := by
    omega
  rw [hsub, partialChooseSum_pascal, partialChooseSum_succ]
  omega

/-- Uniform recovery probability over all `2^width` sign configurations. -/
noncomputable def recoveryProbability
    (width required : ℕ) : ℚ :=
  recoveryCount width required / 2 ^ width

/-- Exact one-hidden-unit probability increment. -/
theorem recoveryProbability_succ
    (width required : ℕ) (hrequired : required ≤ width) :
    recoveryProbability (width + 1) required =
      recoveryProbability width required +
        width.choose (width - required + 1) /
          2 ^ (width + 1) := by
  rw [recoveryProbability, recoveryProbability,
    recoveryCount_succ width required hrequired]
  push_cast
  rw [pow_succ]
  ring

/-- Over-parameterization cannot reduce the compatible-sign probability. -/
theorem recoveryProbability_mono_width
    (width required : ℕ) (hrequired : required ≤ width) :
    recoveryProbability width required ≤
      recoveryProbability (width + 1) required := by
  rw [recoveryProbability_succ width required hrequired]
  have hterm :
      (0 : ℚ) ≤
        width.choose (width - required + 1) /
          2 ^ (width + 1) := by
    positivity
  linarith

/-- For a nonempty teacher, every added unit strictly improves the uniform
compatible-sign probability. -/
theorem recoveryProbability_strictMono_width
    (width required : ℕ) (hpositive : 0 < required)
    (hrequired : required ≤ width) :
    recoveryProbability width required <
      recoveryProbability (width + 1) required := by
  rw [recoveryProbability_succ width required hrequired]
  have hindex : width - required + 1 ≤ width := by
    omega
  have hchoose :
      0 < width.choose (width - required + 1) :=
    Nat.choose_pos hindex
  have hterm :
      (0 : ℚ) <
        width.choose (width - required + 1) /
          2 ^ (width + 1) := by
    positivity
  linarith

/-! ## Positive and negative fixtures -/

def twoCoefficient : Fin 2 → ℝ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => -3

def reversedTwoSigns : Fin 2 → BinarySign
  | ⟨0, _⟩ => .negative
  | ⟨1, _⟩ => .positive

/-- A nontrivial two-coordinate family has a strict selected representative. -/
theorem twoCoordinate_degeneracy_breaking :
    feedbackOverlap twoCoefficient (optimalSigns twoCoefficient) = 5 ∧
      feedbackOverlap twoCoefficient reversedTwoSigns = -5 := by
  norm_num [feedbackOverlap, optimalSigns, maximizingSign, twoCoefficient,
    reversedTwoSigns, BinarySign.factor, Fin.sum_univ_two]

def zeroCoefficient : Fin 1 → ℝ :=
  fun _ => 0

def negativeOne : Fin 1 → BinarySign :=
  fun _ => .negative

def positiveOne : Fin 1 → BinarySign :=
  fun _ => .positive

/-- A zero feedback/teacher coefficient cannot break the sign degeneracy. -/
theorem zeroCoefficient_does_not_break_degeneracy :
    negativeOne ≠ positiveOne ∧
      feedbackOverlap zeroCoefficient negativeOne =
        feedbackOverlap zeroCoefficient positiveOne := by
  constructor
  · intro heq
    have hpoint := congrFun heq 0
    simp [negativeOne, positiveOne] at hpoint
  · simp [feedbackOverlap, zeroCoefficient, negativeOne, positiveOne]

/-- The `M = 2` recovery probabilities reproduce the first three
over-parameterization values. -/
theorem twoRequired_recovery_probability :
    recoveryProbability 2 2 = 1 / 4 ∧
      recoveryProbability 3 2 = 1 / 2 ∧
      recoveryProbability 4 2 = 11 / 16 := by
  rw [recoveryProbability, recoveryProbability, recoveryProbability]
  rw [recoveryCount_eq_partial 2 2 (by omega)]
  rw [recoveryCount_eq_partial 3 2 (by omega)]
  rw [recoveryCount_eq_partial 4 2 (by omega)]
  norm_num [partialChooseSum, Finset.sum_range_succ, Nat.choose]

#print axioms feedbackOverlap_le_optimal
#print axioms signs_eq_optimal_of_overlap_eq
#print axioms relu_positive_rescale
#print axioms positive_rescale_cannot_flip_nonzero
#print axioms card_recoverySignSets
#print axioms upperChooseSum_eq_partial
#print axioms recoveryCount_succ
#print axioms recoveryProbability_strictMono_width
#print axioms zeroCoefficient_does_not_break_degeneracy
#print axioms twoRequired_recovery_probability

end FeedbackAlignmentDegeneracy

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
