import Mettapedia.Cybernetics.ApproximateAdequacy.AdaptivePolicy
import Mettapedia.Cybernetics.ApproximateAdequacy.DecisionBounds

/-! # Finite policy semantics and sufficient representations -/

namespace Mettapedia.Cybernetics.ApproximateAdequacy

open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob

variable {S C O A : Type*} [Fintype S] [Fintype C] [Fintype O]

noncomputable instance observationPolicyFintype (O A : Type*) [Fintype O] [Fintype A] (n : ℕ) :
    Fintype (ObservationPolicy O A n) := by
  classical
  exact match n with
    | 0 => inferInstanceAs (Fintype PUnit)
    | n + 1 =>
        letI := observationPolicyFintype O A n
        inferInstanceAs (Fintype (A × (O → ObservationPolicy O A n)))

/-- The induced terminal-state distribution, retaining the observation-contingent branches. -/
noncomputable def terminalLaw [DecidableEq S] (kernel : A → S → Prob (S × O)) :
    {n : ℕ} → ObservationPolicy O A n → S → Prob S
  | 0, _, s => Prob.dirac s
  | n + 1, policy, s =>
      Prob.bind (kernel policy.1 s)
        (fun next => terminalLaw kernel (n := n) (policy.2 next.2) next.1)

/-- The value recurrence is the expectation of the independently constructed terminal law. -/
theorem terminalLaw_value [DecidableEq S] (kernel : A → S → Prob (S × O))
    (reward : S → ℝ) {n : ℕ} (policy : ObservationPolicy O A n) (s : S) :
    (∑ t, (terminalLaw kernel policy s).1 t * reward t) =
      adaptiveValue kernel reward policy s := by
  induction n generalizing s with
  | zero =>
      change (∑ t, (Prob.dirac s).1 t * reward t) = reward s
      exact expectation_dirac s reward
  | succ n ih =>
      rw [terminalLaw, expectation_bind]
      change (∑ next, (kernel policy.1 s).1 next *
        (∑ t, (terminalLaw kernel (policy.2 next.2) next.1).1 t * reward t)) = _
      simp only [ih, adaptiveValue, expect]

/-- Exact state aggregation preserves every adaptive policy value when it
retains both next abstract state and the branch-selecting observation. -/
theorem adaptiveValue_coarsen [DecidableEq C] [DecidableEq O]
    (view : S → C) (source : A → S → Prob (S × O))
    (target : A → C → Prob (C × O))
    (compatible : ∀ a s,
      coarsen (source a s) (fun next => (view next.1, next.2)) = target a (view s))
    (reward : C → ℝ) {n : ℕ} (policy : ObservationPolicy O A n) (s : S) :
    adaptiveValue source (reward ∘ view) policy s =
      adaptiveValue target reward policy (view s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      change (∑ next, (source policy.1 s).1 next *
        adaptiveValue source (reward ∘ view) (policy.2 next.2) next.1) = _
      have step_eq := congrArg
        (fun p : Prob (C × O) => ∑ next, p.1 next *
          adaptiveValue target reward (policy.2 next.2) next.1) (compatible policy.1 s)
      rw [coarsen_expectation] at step_eq
      change (∑ next, (source policy.1 s).1 next *
        adaptiveValue source (reward ∘ view) (policy.2 next.2) next.1) =
          ∑ next, (target policy.1 (view s)).1 next *
            adaptiveValue target reward (policy.2 next.2) next.1
      rw [← step_eq]
      apply Finset.sum_congr rfl
      intro next _
      rw [ih]

/-- A factored reward has the same prior-averaged policy value in the compressed model. -/
theorem expected_adaptiveValue_coarsen [DecidableEq C] [DecidableEq O]
    (view : S → C) (source : A → S → Prob (S × O))
    (target : A → C → Prob (C × O))
    (compatible : ∀ a s,
      coarsen (source a s) (fun next => (view next.1, next.2)) = target a (view s))
    (prior : Prob S) (reward : C → ℝ) {n : ℕ} (policy : ObservationPolicy O A n) :
    expect prior.1 (adaptiveValue source (reward ∘ view) policy) =
      expect (coarsen prior view).1 (adaptiveValue target reward policy) := by
  simp only [expect]
  rw [coarsen_expectation]
  exact Finset.sum_congr rfl (fun s _ => congrArg (fun v => prior.1 s * v)
    (adaptiveValue_coarsen view source target compatible reward policy s))

/-- Nonempty admissible finite-horizon policies have an optimum. -/
theorem finite_policy_optimal_exists [Fintype A] {n : ℕ}
    (admissible : ObservationPolicy O A n → Prop) (score : ObservationPolicy O A n → ℝ)
    (nonempty : ∃ p, admissible p) :
    ∃ p, (Mettapedia.Enactive.Razor.Criterion.ofBenefit admissible score).IsOptimal p :=
  DecisionBounds.finite_optimal_exists admissible score nonempty

end Mettapedia.Cybernetics.ApproximateAdequacy
