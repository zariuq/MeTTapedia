import Mettapedia.Cybernetics.ApproximateAdequacy.Coupling
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum

/-!
# Checked rational Bayesian updates

Inputs are ordinary rational mass functions. The algorithm checks the prior,
likelihood signs and evidence before returning a normalized posterior. It
refuses invalid distributions and impossible observations. Its distribution
predicate is the existing finite, ordered-field probability interface.
-/

namespace Mettapedia.Algorithms.FiniteBayes

open Finset
open Mettapedia.Cybernetics.ApproximateAdequacy

variable {S : Type*} [Fintype S]

/-- Computable evidence under a rational prior and likelihood. -/
def normalizer (prior likelihood : S → ℚ) : ℚ := ∑ s, prior s * likelihood s

/-- Validate ordinary mass data before using it as a probability distribution. -/
def checkDistribution (mass : S → ℚ) : Bool :=
  decide ((∀ s, 0 ≤ mass s) ∧ ∑ s, mass s = 1)

theorem checkDistribution_iff (mass : S → ℚ) :
    checkDistribution mass = true ↔ IsDistribution mass := by
  simp only [checkDistribution, decide_eq_true_eq]
  constructor
  · rintro ⟨nonneg, normalized⟩
    exact ⟨nonneg, normalized⟩
  · intro valid
    exact ⟨valid.nonneg, valid.sum_eq_one⟩

/-- Bayesian conditioning with explicit refusal for invalid data or zero evidence. -/
def update (prior likelihood : S → ℚ) : Option (S → ℚ) :=
  if checkDistribution prior ∧ (∀ s, 0 ≤ likelihood s) ∧ 0 < normalizer prior likelihood then
    some (fun s => prior s * likelihood s / normalizer prior likelihood)
  else none

/-- An accepted update has positive evidence and the ordinary Bayesian mass formula. -/
theorem update_accepted (prior likelihood output : S → ℚ)
    (accepted : update prior likelihood = some output) :
    IsDistribution prior ∧ (∀ s, 0 ≤ likelihood s) ∧ 0 < normalizer prior likelihood ∧
      output = fun s => prior s * likelihood s / normalizer prior likelihood := by
  unfold update at accepted
  split_ifs at accepted with valid
  · exact ⟨(checkDistribution_iff prior).mp valid.1, valid.2.1, valid.2.2,
      (Option.some.inj accepted).symm⟩

/-- The output of the checked algorithm really is normalized and nonnegative. -/
theorem update_sound (prior likelihood output : S → ℚ)
    (accepted : update prior likelihood = some output) : IsDistribution output := by
  obtain ⟨prior_valid, nonneg, positive, rfl⟩ := update_accepted prior likelihood output accepted
  constructor
  · intro s
    exact div_nonneg (mul_nonneg (prior_valid.nonneg s) (nonneg s)) positive.le
  · rw [← Finset.sum_div]
    exact div_self positive.ne'

/-- Invalid priors cannot be accepted. -/
theorem update_invalid_prior (prior likelihood : S → ℚ) (invalid : ¬ IsDistribution prior) :
    update prior likelihood = none := by
  unfold update
  split_ifs with valid
  · exact (invalid ((checkDistribution_iff prior).mp valid.1)).elim
  · rfl

/-- An impossible observation cannot produce a posterior. -/
theorem update_impossible (prior likelihood : S → ℚ) (impossible : normalizer prior likelihood = 0) :
    update prior likelihood = none := by
  simp [update, impossible]

end Mettapedia.Algorithms.FiniteBayes
