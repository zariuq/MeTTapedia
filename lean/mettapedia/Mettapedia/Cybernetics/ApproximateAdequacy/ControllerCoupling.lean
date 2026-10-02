import Mettapedia.Cybernetics.ApproximateAdequacy.AdaptivePolicy

/-!
# Coupled executions of different adaptive controllers

The two controllers may have different actions and observation types. Each
certificate couples the actual kernels selected by those controllers and
recursively certifies their positive-mass successor branches. Identical
observation values or action choices are not assumed.
-/

namespace Mettapedia.Cybernetics.ApproximateAdequacy

open Mettapedia.InformationTheory

variable {S T O U A B : Type*}
  [Fintype S] [Fintype T] [Fintype O] [Fintype U]

/-- A finite execution certificate retains its actual joint successor law,
its discrepancy cost and the continuation certificates it needs. -/
inductive CoupledExecution
    (first : A → S → Prob (S × O)) (second : B → T → Prob (T × U))
    (firstReward : S → ℝ) (secondReward : T → ℝ) (metric : S → T → ℝ) :
    {n : ℕ} → ObservationPolicy O A n → ObservationPolicy U B n → S → T → Prop
  | terminal {p q s t} (bounded : |firstReward s - secondReward t| ≤ metric s t) :
      CoupledExecution first second firstReward secondReward metric (n := 0) p q s t
  | step {n} {p : ObservationPolicy O A (n + 1)}
      {q : ObservationPolicy U B (n + 1)} {s t}
      (coupling : Coupling (first p.1 s).1 (second q.1 t).1)
      (continues : ∀ x y, 0 < coupling.weight x y →
        CoupledExecution first second firstReward secondReward metric
          (p.2 x.2) (q.2 y.2) x.1 y.1)
      (bounded : coupling.cost (fun x y => metric x.1 y.1) ≤ metric s t) :
      CoupledExecution first second firstReward secondReward metric p q s t

/-- Different observations and action choices are safe only through the
couplings of their selected kernels and their actual continuations. -/
theorem CoupledExecution.value_bound
    {first : A → S → Prob (S × O)} {second : B → T → Prob (T × U)}
    {firstReward : S → ℝ} {secondReward : T → ℝ} {metric : S → T → ℝ}
    {n : ℕ} {p : ObservationPolicy O A n} {q : ObservationPolicy U B n} {s t}
    (certificate : CoupledExecution first second firstReward secondReward metric p q s t) :
    |adaptiveValue first firstReward p s - adaptiveValue second secondReward q t| ≤
      metric s t := by
  induction certificate with
  | terminal bounded => exact bounded
  | step coupling continues bounded ih =>
      exact (coupling.abs_expect_sub_le_on_support
        (fun x y positive => ih x y positive)).trans bounded

/-- Coupling the initial beliefs lifts the controller certificate to a score
bound between the independent processes. -/
theorem CoupledExecution.expected_bound
    {first : A → S → Prob (S × O)} {second : B → T → Prob (T × U)}
    {firstReward : S → ℝ} {secondReward : T → ℝ} {metric : S → T → ℝ}
    {n : ℕ} (p : ObservationPolicy O A n) (q : ObservationPolicy U B n)
    (firstPrior : Prob S) (secondPrior : Prob T)
    (initial : Coupling firstPrior.1 secondPrior.1)
    (certificates : ∀ s t, 0 < initial.weight s t →
      CoupledExecution first second firstReward secondReward metric p q s t) :
    |expect firstPrior.1 (adaptiveValue first firstReward p) -
      expect secondPrior.1 (adaptiveValue second secondReward q)| ≤ initial.cost metric :=
  initial.abs_expect_sub_le_on_support
    (fun s t positive => (certificates s t positive).value_bound)

end Mettapedia.Cybernetics.ApproximateAdequacy
