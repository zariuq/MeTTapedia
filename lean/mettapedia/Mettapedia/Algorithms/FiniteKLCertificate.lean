import Mettapedia.Algorithms.FiniteBayesRefinement
import Mettapedia.Algorithms.CertifiedLogScore
import Mettapedia.InformationTheory.Pinsker

/-!
# Rational certificates for posterior expectation error

The checker validates both mass functions, absolute continuity and a computed
logarithmic enclosure. A successful squared comparison bounds the expectation
error for every consumer with the declared magnitude bound. Zero trial mass
contributes zero to the divergence and requires no logarithm at zero.
-/

namespace Mettapedia.Algorithms.FiniteKLCertificate

open Finset
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.Algorithms.FiniteBayes
open Mettapedia.Cybernetics.ApproximateAdequacy

variable {S : Type*} [Fintype S]

def Supported (trial posterior : S → ℚ) : Prop :=
  ∀ s, 0 < trial s → 0 < posterior s

instance (trial posterior : S → ℚ) : Decidable (Supported trial posterior) := by
  unfold Supported
  infer_instance

def logArgument (trial posterior : S → ℚ) (s : S) : ℚ :=
  if trial s = 0 then 1 else trial s / posterior s

def upper (trial posterior : S → ℚ) (terms : ℕ) : ℚ :=
  CertifiedLogScore.approximation trial (logArgument trial posterior) terms +
    CertifiedLogScore.radius trial (logArgument trial posterior) terms

def check (trial posterior : S → ℚ) (magnitude error : ℚ) (terms : ℕ) : Bool :=
  decide (checkDistribution trial = true ∧ checkDistribution posterior = true ∧
    Supported trial posterior ∧ 0 ≤ magnitude ∧ 0 ≤ error ∧
    2 * magnitude ^ 2 * upper trial posterior terms ≤ error ^ 2)

theorem accepted_data (trial posterior : S → ℚ) (magnitude error : ℚ) (terms : ℕ)
    (accepted : check trial posterior magnitude error terms = true) :
    IsDistribution trial ∧ IsDistribution posterior ∧ Supported trial posterior ∧
      0 ≤ magnitude ∧ 0 ≤ error ∧
      2 * magnitude ^ 2 * upper trial posterior terms ≤ error ^ 2 := by
  have facts : checkDistribution trial = true ∧ checkDistribution posterior = true ∧
      Supported trial posterior ∧ 0 ≤ magnitude ∧ 0 ≤ error ∧
      2 * magnitude ^ 2 * upper trial posterior terms ≤ error ^ 2 := by
    simpa only [check, decide_eq_true_eq] using accepted
  exact ⟨(checkDistribution_iff trial).mp facts.1,
    (checkDistribution_iff posterior).mp facts.2.1, facts.2.2⟩

theorem logArgument_positive (trial posterior : S → ℚ)
    (valid : IsDistribution trial) (support : Supported trial posterior) (s : S) :
    0 < logArgument trial posterior s := by
  unfold logArgument
  split_ifs with zero
  · norm_num
  · have positive := lt_of_le_of_ne (valid.nonneg s) (Ne.symm zero)
    exact div_pos positive (support s positive)

theorem real_supported (trial posterior : S → ℚ)
    (trialValid : IsDistribution trial) (posteriorValid : IsDistribution posterior)
    (support : Supported trial posterior) :
    ∀ s, 0 < (realDistribution trial trialValid).1 s →
      0 < (realDistribution posterior posteriorValid).1 s := by
  intro s positive
  change 0 < (trial s : ℝ) at positive
  change 0 < (posterior s : ℝ)
  have positiveQ : 0 < trial s := by exact_mod_cast positive
  exact_mod_cast support s positiveQ

theorem kl_eq_score (trial posterior : S → ℚ)
    (trialValid : IsDistribution trial) (posteriorValid : IsDistribution posterior) :
    klSum (realDistribution trial trialValid).1 (realDistribution posterior posteriorValid).1 =
      ∑ s, (trial s : ℝ) * Real.log (logArgument trial posterior s : ℝ) := by
  rw [klSum_eq_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases zero : trial s = 0
  · simp [realDistribution, logArgument, zero]
  · simp [realDistribution, logArgument, zero]

theorem kl_le_upper (trial posterior : S → ℚ)
    (trialValid : IsDistribution trial) (posteriorValid : IsDistribution posterior)
    (support : Supported trial posterior) (terms : ℕ) :
    klSum (realDistribution trial trialValid).1 (realDistribution posterior posteriorValid).1 ≤
      (upper trial posterior terms : ℝ) := by
  rw [kl_eq_score trial posterior trialValid posteriorValid]
  have enclosure := abs_le.mp (CertifiedLogScore.enclosure trial
    (logArgument trial posterior) (logArgument_positive trial posterior trialValid support) terms)
  simp only [upper, Rat.cast_add]
  linarith [enclosure.2]

/-- Acceptance gives a uniform guarantee for independently supplied bounded consumers. -/
theorem expectation_error (trial posterior : S → ℚ)
    (trialValid : IsDistribution trial) (posteriorValid : IsDistribution posterior)
    (magnitude error : ℚ) (terms : ℕ)
    (accepted : check trial posterior magnitude error terms = true)
    (consumer : S → ℝ) (bounded : ∀ s, |consumer s| ≤ (magnitude : ℝ)) :
    |∑ s, (trial s : ℝ) * consumer s - ∑ s, (posterior s : ℝ) * consumer s| ≤
      (error : ℝ) := by
  obtain ⟨_, _, support, magnitudeNonneg, errorNonneg, certificate⟩ :=
    accepted_data trial posterior magnitude error terms accepted
  have supportR := real_supported trial posterior trialValid posteriorValid support
  have magnitudeR : 0 ≤ (magnitude : ℝ) := by exact_mod_cast magnitudeNonneg
  have errorR : 0 ≤ (error : ℝ) := by exact_mod_cast errorNonneg
  let divergence := klSum (realDistribution trial trialValid).1
    (realDistribution posterior posteriorValid).1
  have divergenceNonneg : 0 ≤ divergence := klSum_prob_nonneg _ _ supportR
  have divergenceUpper : divergence ≤ (upper trial posterior terms : ℝ) :=
    kl_le_upper trial posterior trialValid posteriorValid support terms
  have certificateR : 2 * (magnitude : ℝ) ^ 2 * (upper trial posterior terms : ℝ) ≤
      (error : ℝ) ^ 2 := by exact_mod_cast certificate
  have squareBound : ((magnitude : ℝ) * Real.sqrt (2 * divergence)) ^ 2 ≤ (error : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left divergenceUpper (sq_nonneg (magnitude : ℝ))]
  have rootBound : (magnitude : ℝ) * Real.sqrt (2 * divergence) ≤ (error : ℝ) := by
    exact le_of_sq_le_sq squareBound errorR
  exact (abs_expectation_sub_le (realDistribution trial trialValid)
    (realDistribution posterior posteriorValid) consumer magnitudeR bounded supportR).trans rootBound

end Mettapedia.Algorithms.FiniteKLCertificate
