import Mettapedia.Algorithms.FiniteBayesRefinement
import Mettapedia.Cybernetics.ApproximateAdequacy.AdaptivePolicy

/-! # Checked rational evaluation of finite observation-contingent policies -/

namespace Mettapedia.Algorithms.FiniteAdaptivePolicy

open Mettapedia.InformationTheory
open Mettapedia.Cybernetics.ApproximateAdequacy
open Mettapedia.Algorithms.FiniteBayes

variable {S O A : Type*} [Fintype S] [Fintype O]

def value (kernel : A → S → S × O → ℚ) (reward : S → ℚ) :
    {n : ℕ} → ObservationPolicy O A n → S → ℚ
  | 0, _, s => reward s
  | n + 1, policy, s =>
      ∑ next, kernel policy.1 s next * value kernel reward (n := n) (policy.2 next.2) next.1

theorem value_cast (kernel : A → S → S × O → ℚ) (reward : S → ℚ)
    (valid : ∀ a s, IsDistribution (kernel a s))
    {n : ℕ} (policy : ObservationPolicy O A n) (s : S) :
    (value kernel reward policy s : ℝ) =
      adaptiveValue (fun a s => realDistribution (kernel a s) (valid a s))
        (fun s => (reward s : ℝ)) policy s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      change ((∑ next, kernel policy.1 s next *
        value kernel reward (policy.2 next.2) next.1 : ℚ) : ℝ) = _
      simp only [Rat.cast_sum, Rat.cast_mul, adaptiveValue, expect, realDistribution]
      exact Finset.sum_congr rfl (fun next _ => congrArg
        (fun x => (kernel policy.1 s next : ℝ) * x) (ih (policy.2 next.2) next.1))

/-- Raw model rows and the initial distribution are checked before evaluation. -/
def evaluate [Fintype A] (prior : S → ℚ) (kernel : A → S → S × O → ℚ)
    (reward : S → ℚ) {n : ℕ} (policy : ObservationPolicy O A n) : Option ℚ :=
  if checkDistribution prior ∧ ∀ a s, checkDistribution (kernel a s) then
    some (∑ s, prior s * value kernel reward policy s)
  else none

theorem evaluate_refines [Fintype A] (prior : S → ℚ)
    (kernel : A → S → S × O → ℚ) (reward : S → ℚ)
    {n : ℕ} (policy : ObservationPolicy O A n) (output : ℚ)
    (accepted : evaluate prior kernel reward policy = some output) :
    ∃ prior_valid : IsDistribution prior,
      ∃ kernel_valid : ∀ a s, IsDistribution (kernel a s),
      (output : ℝ) = expect (realDistribution prior prior_valid).1
        (adaptiveValue (fun a s => realDistribution (kernel a s) (kernel_valid a s))
          (fun s => (reward s : ℝ)) policy) := by
  unfold evaluate at accepted
  split_ifs at accepted with valid
  have pv := (checkDistribution_iff prior).mp valid.1
  have kv : ∀ a s, IsDistribution (kernel a s) := fun a s =>
    (checkDistribution_iff (kernel a s)).mp (valid.2 a s)
  refine ⟨pv, kv, ?_⟩
  have output_eq := (Option.some.inj accepted).symm
  rw [output_eq]
  simp only [Rat.cast_sum, Rat.cast_mul, expect, realDistribution]
  exact Finset.sum_congr rfl (fun s _ => congrArg (fun x => (prior s : ℝ) * x)
    (value_cast kernel reward kv policy s))

end Mettapedia.Algorithms.FiniteAdaptivePolicy
