import Mettapedia.Cybernetics.ApproximateAdequacy.AdaptiveTrace
import Mettapedia.ProbabilityTheory.BayesianInference.Basic

/-!
# Belief updates and open-loop specialization of adaptive execution

The next joint law comes from applying the controlled kernel to the current
belief. Conditioning its state/observation pairs gives the next belief only
for a possible observation. Disintegrating this same joint law derives the
belief-state value recurrence. The execution trace theorem then supplies its
operational interpretation.
-/

namespace Mettapedia.Cybernetics.ApproximateAdequacy

open Finset
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob

variable {S O A : Type*} [Fintype S] [Fintype O]

noncomputable def observationMass (law : Prob (S × O)) (o : O) : ℝ :=
  ∑ s, law.1 (s, o)

theorem observationMass_nonneg (law : Prob (S × O)) (o : O) :
    0 ≤ observationMass law o := Finset.sum_nonneg (fun s _ => law.2.1 (s, o))

noncomputable def conditionalBelief (law : Prob (S × O)) (o : O)
    (possible : 0 < observationMass law o) : Prob S :=
  ⟨fun s => law.1 (s, o) / observationMass law o,
    (fun s => div_nonneg (law.2.1 (s, o)) possible.le), by
      rw [← Finset.sum_div]
      exact div_self possible.ne'⟩

theorem mass_zero_of_impossible (law : Prob (S × O)) (o : O)
    (impossible : ¬ 0 < observationMass law o) (s : S) : law.1 (s, o) = 0 := by
  have total_zero : observationMass law o = 0 :=
    le_antisymm (le_of_not_gt impossible) (observationMass_nonneg law o)
  have below : law.1 (s, o) ≤ observationMass law o :=
    Finset.single_le_sum (fun t _ => law.2.1 (t, o)) (Finset.mem_univ s)
  exact le_antisymm (total_zero ▸ below) (law.2.1 (s, o))

/-- A finite joint law disintegrates into its observation mass and the
conditional state law. Impossible observations contribute exactly zero. -/
theorem disintegrate_expectation (law : Prob (S × O)) (consumer : S × O → ℝ) :
    expect law.1 consumer = ∑ o,
      if possible : 0 < observationMass law o then
        observationMass law o *
          expect (conditionalBelief law o possible).1 (fun s => consumer (s, o))
      else 0 := by
  classical
  unfold expect
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  split_ifs with possible
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    change law.1 (s, o) * consumer (s, o) =
      observationMass law o * (law.1 (s, o) / observationMass law o * consumer (s, o))
    field_simp
  · apply Finset.sum_eq_zero
    intro s _
    rw [mass_zero_of_impossible law o possible s, zero_mul]

/-- The actual next-state/observation law under a current belief. -/
noncomputable def nextJoint (prior : Prob S) (kernel : A → S → Prob (S × O))
    (action : A) : Prob (S × O) := Prob.bind prior (kernel action)

/-- The belief-state Bellman recurrence follows by disintegrating the actual
next joint law; no posterior is invented on an impossible observation. -/
theorem belief_value_recurrence (prior : Prob S) (kernel : A → S → Prob (S × O))
    (reward : S → ℝ) {n : ℕ} (policy : ObservationPolicy O A (n + 1)) :
    expect prior.1 (adaptiveValue kernel reward policy) = ∑ o,
      if possible : 0 < observationMass (nextJoint prior kernel policy.1) o then
        observationMass (nextJoint prior kernel policy.1) o *
          expect (conditionalBelief (nextJoint prior kernel policy.1) o possible).1
            (adaptiveValue kernel reward (policy.2 o))
      else 0 := by
  classical
  calc
    _ = expect (nextJoint prior kernel policy.1).1
        (fun next => adaptiveValue kernel reward (policy.2 next.2) next.1) := by
      exact (expectation_bind prior (kernel policy.1)
        (fun next => adaptiveValue kernel reward (policy.2 next.2) next.1)).symm
    _ = _ := disintegrate_expectation (nextJoint prior kernel policy.1)
      (fun next => adaptiveValue kernel reward (policy.2 next.2) next.1)

/-- The belief recurrence evaluates the full execution traces as well. -/
theorem trace_belief_value_recurrence [DecidableEq S] [DecidableEq O]
    (prior : Prob S) (kernel : A → S → Prob (S × O)) (reward : S → ℝ)
    {n : ℕ} (policy : ObservationPolicy O A (n + 1)) :
    (∑ s, prior.1 s * ∑ trace,
      (traceLaw kernel policy s).1 trace * reward (traceTerminal s trace)) = ∑ o,
      if possible : 0 < observationMass (nextJoint prior kernel policy.1) o then
        observationMass (nextJoint prior kernel policy.1) o *
          expect (conditionalBelief (nextJoint prior kernel policy.1) o possible).1
            (adaptiveValue kernel reward (policy.2 o))
      else 0 := by
  simp only [traceLaw_value]
  exact belief_value_recurrence prior kernel reward policy

/-- An action sequence defines a policy which ignores every observation. -/
def openLoop : (actions : List A) → ObservationPolicy O A actions.length
  | [] => PUnit.unit
  | a :: rest => (a, fun _ => openLoop rest)

noncomputable def openLoopValue (kernel : A → S → Prob (S × O))
    (reward : S → ℝ) : List A → S → ℝ
  | [], s => reward s
  | a :: rest, s => ∑ next, (kernel a s).1 next * openLoopValue kernel reward rest next.1

theorem openLoop_value (kernel : A → S → Prob (S × O)) (reward : S → ℝ)
    (actions : List A) (s : S) :
    adaptiveValue kernel reward (openLoop (O := O) actions) s =
      openLoopValue kernel reward actions s := by
  induction actions generalizing s with
  | nil => rfl
  | cons a rest ih =>
      change (∑ next, (kernel a s).1 next *
        adaptiveValue kernel reward (openLoop rest) next.1) =
          ∑ next, (kernel a s).1 next * openLoopValue kernel reward rest next.1
      exact Finset.sum_congr rfl (fun next _ => congrArg (_ * ·) (ih next.1))

end Mettapedia.Cybernetics.ApproximateAdequacy
