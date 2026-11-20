import Mettapedia.Algorithms.FiniteBayesRefinement
import Mettapedia.Cybernetics.ApproximateAdequacy.AdaptivePolicy
import Mathlib.Data.Finset.Lattice.Fold

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

/-- A branch of a Bayes filter retains the joint mass of its observation. -/
def advance (kernel : A → S → S × O → ℚ) (weight : S → ℚ) (action : A)
    (observation : O) (next : S) : ℚ :=
  ∑ state, weight state * kernel action state (next, observation)

def policyScore (kernel : A → S → S × O → ℚ) (reward weight : S → ℚ)
    {n : ℕ} (policy : ObservationPolicy O A n) : ℚ :=
  ∑ state, weight state * value kernel reward policy state

theorem policyScore_step (kernel : A → S → S × O → ℚ) (reward weight : S → ℚ)
    {n : ℕ} (action : A) (after : O → ObservationPolicy O A n) :
    policyScore kernel reward weight (n := n + 1) (action, after) =
      ∑ obs, policyScore kernel reward (advance kernel weight action obs) (after obs) := by
  simp only [policyScore, value, advance]
  simp_rw [Fintype.sum_prod_type_right, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro obs _
  rw [Finset.sum_comm]
  simp only [mul_assoc]

variable [Fintype A] [Nonempty A]

/-- Exact finite-horizon expectimax on unnormalized observation branches.
The model may track remaining budget or payoff in its state. -/
def bestScore (kernel : A → S → S × O → ℚ) (reward : S → ℚ) : ℕ → (S → ℚ) → ℚ
  | 0, weight => ∑ state, weight state * reward state
  | n + 1, weight =>
    Finset.univ.sup' Finset.univ_nonempty fun action =>
      ∑ obs, bestScore kernel reward n (advance kernel weight action obs)

theorem bestScore_exact (kernel : A → S → S × O → ℚ) (reward : S → ℚ)
    (n : ℕ) (weight : S → ℚ) :
    (∀ policy : ObservationPolicy O A n,
      policyScore kernel reward weight policy ≤ bestScore kernel reward n weight) ∧
      ∃ policy : ObservationPolicy O A n,
        policyScore kernel reward weight policy = bestScore kernel reward n weight := by
  induction n generalizing weight with
  | zero => exact ⟨fun _ => le_rfl, ⟨PUnit.unit, rfl⟩⟩
  | succ n ih =>
    let rank : A → ℚ := fun action =>
      ∑ obs, bestScore kernel reward n (advance kernel weight action obs)
    constructor
    · rintro ⟨action, after⟩
      rw [policyScore_step]
      calc
        _ ≤ rank action := Finset.sum_le_sum fun obs _ =>
          (ih (advance kernel weight action obs)).1 (after obs)
        _ ≤ bestScore kernel reward (n + 1) weight :=
          Finset.le_sup' rank (Finset.mem_univ action)
    · obtain ⟨action, _, maximal⟩ :=
        Finset.exists_mem_eq_sup' Finset.univ_nonempty rank
      choose after tight using fun obs => (ih (advance kernel weight action obs)).2
      refine ⟨(action, after), ?_⟩
      rw [policyScore_step]
      exact (Finset.sum_congr rfl (fun obs _ => tight obs)).trans maximal.symm

end Mettapedia.Algorithms.FiniteAdaptivePolicy
