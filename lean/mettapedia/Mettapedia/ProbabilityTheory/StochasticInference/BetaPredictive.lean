import Mettapedia.ProbabilityTheory.BayesianNetworks.CPTLearning

/-!
# Exact predictive mass for repeated uses of a Bernoulli parameter

The initial parameter law is uniform Beta. Counts from earlier observations
are retained when scoring the next occurrence of that same parameter. The
mass here is for a particular ordered outcome sequence, with no binomial
multiplicity.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference.BetaPredictive

open Mettapedia.ProbabilityTheory.BayesianNetworks.CPTLearning

def empty : BooleanCPTEntry := ⟨0, 0⟩

def addOutcome (counts : BooleanCPTEntry) : Bool → BooleanCPTEntry
  | true => ⟨counts.n_pos + 1, counts.n_neg⟩
  | false => ⟨counts.n_pos, counts.n_neg + 1⟩

def predictive (counts : BooleanCPTEntry) (outcome : Bool) : ℚ :=
  if outcome then exactPosteriorMean 1 1 counts
  else exactPosteriorMean 1 1 ⟨counts.n_neg, counts.n_pos⟩

theorem predictive_positive (counts : BooleanCPTEntry) (outcome : Bool) :
    0 < predictive counts outcome := by
  cases outcome <;> simp only [predictive, Bool.false_eq_true, if_false, if_true, exactPosteriorMean]
  all_goals positivity

theorem predictive_total (counts : BooleanCPTEntry) :
    predictive counts false + predictive counts true = 1 := by
  simp only [predictive, Bool.false_eq_true, if_false, if_true, exactPosteriorMean]
  have positive : 0 < (1 : ℚ) + counts.n_pos + (1 + counts.n_neg) := by positivity
  have same : (1 : ℚ) + counts.n_neg + (1 + counts.n_pos) =
      1 + counts.n_pos + (1 + counts.n_neg) := by ring
  rw [same, ← add_div, div_eq_one_iff_eq positive.ne']
  ring

def wordMass (counts : BooleanCPTEntry) : ℚ :=
  (counts.n_pos.factorial : ℚ) * counts.n_neg.factorial /
    (counts.n_pos + counts.n_neg + 1).factorial

theorem wordMass_positive (counts : BooleanCPTEntry) : 0 < wordMass counts := by
  unfold wordMass
  exact div_pos (mul_pos (by exact_mod_cast Nat.factorial_pos counts.n_pos)
    (by exact_mod_cast Nat.factorial_pos counts.n_neg))
    (by exact_mod_cast Nat.factorial_pos (counts.n_pos + counts.n_neg + 1))

@[simp] theorem wordMass_empty : wordMass empty = 1 := by decide +kernel

theorem wordMass_step (counts : BooleanCPTEntry) (outcome : Bool) :
    wordMass (addOutcome counts outcome) = wordMass counts * predictive counts outcome := by
  obtain ⟨p, q⟩ := counts
  have den : (0 : ℚ) < ((p + q + 1).factorial : ℚ) := by
    exact_mod_cast Nat.factorial_pos (p + q + 1)
  cases outcome with
  | false =>
    simp only [wordMass, addOutcome, predictive, Bool.false_eq_true, if_false, exactPosteriorMean]
    rw [show p + (q + 1) + 1 = (p + q + 1) + 1 by omega,
      Nat.factorial_succ q, Nat.factorial_succ (p + q + 1)]
    push_cast
    field_simp
    ring
  | true =>
    simp only [wordMass, addOutcome, predictive, if_true, exactPosteriorMean]
    rw [show p + 1 + q + 1 = (p + q + 1) + 1 by omega,
      Nat.factorial_succ p, Nat.factorial_succ (p + q + 1)]
    push_cast
    field_simp
    ring

def sequenceMass (counts : BooleanCPTEntry) : List Bool → ℚ
  | [] => 1
  | outcome :: rest => predictive counts outcome * sequenceMass (addOutcome counts outcome) rest

theorem sequenceMass_exact (counts : BooleanCPTEntry) (outcomes : List Bool) :
    wordMass counts * sequenceMass counts outcomes =
      wordMass (outcomes.foldl addOutcome counts) := by
  induction outcomes generalizing counts with
  | nil => simp [sequenceMass]
  | cons outcome rest ih =>
    rw [sequenceMass, ← mul_assoc, ← wordMass_step, ih]
    rfl

/-- Sharing an uncertain parameter produces positive covariance between
two outcomes. The gap from the plug-in product is the Beta variance. -/
theorem shared_two_success_gap (counts : BooleanCPTEntry) :
    let a : ℚ := counts.n_pos + 1
    let b : ℚ := counts.n_neg + 1
    sequenceMass counts [true, true] - predictive counts true ^ 2 =
      a * b / ((a + b) ^ 2 * (a + b + 1)) := by
  dsimp only
  simp only [sequenceMass, predictive, addOutcome, if_true, exactPosteriorMean, mul_one]
  push_cast
  have pa : (0 : ℚ) ≤ counts.n_pos := Nat.cast_nonneg _
  have pb : (0 : ℚ) ≤ counts.n_neg := Nat.cast_nonneg _
  field_simp (disch := positivity)
  ring

end Mettapedia.ProbabilityTheory.StochasticInference.BetaPredictive
