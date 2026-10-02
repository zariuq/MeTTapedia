import Mettapedia.Algorithms.FiniteCoupling
import Mettapedia.Cybernetics.ApproximateAdequacy.AdaptivePolicy

/-!
# Checking finite predictive certificates for adaptive policies

Ordinary rational kernels, joint tables, rewards and discrepancy bounds are
validated. Both successor marginals and positive-mass observation agreement
are checked at each action/state pair. Successful validation constructs the
real predictive couplings consumed by the finite policy theorem.
-/

namespace Mettapedia.Algorithms.FiniteControlledCoupling

open Mettapedia.InformationTheory
open Mettapedia.Cybernetics.ApproximateAdequacy
open Mettapedia.Algorithms.FiniteBayes

variable {S T O A : Type*} [Fintype S] [Fintype T] [Fintype O] [Fintype A]
  [DecidableEq O]

def checkStep (first : S × O → ℚ) (second : T × O → ℚ)
    (table : (S × O) → (T × O) → ℚ) (metric : S → T → ℚ) (bound : ℚ) : Bool :=
  FiniteCoupling.check first second table && decide
    ((∀ x y, 0 < table x y → x.2 = y.2) ∧
      (∑ x, ∑ y, table x y * metric x.1 y.1) ≤ bound)

theorem checkStep_sound (first : S × O → ℚ) (second : T × O → ℚ)
    (table : (S × O) → (T × O) → ℚ) (metric : S → T → ℚ) (bound : ℚ)
    (accepted : checkStep first second table metric bound = true) :
    ∃ coupling : Coupling (fun x => (first x : ℝ)) (fun y => (second y : ℝ)),
      (∀ x y, 0 < coupling.weight x y → x.2 = y.2) ∧
        coupling.cost (fun x y => (metric x.1 y.1 : ℝ)) ≤ (bound : ℝ) := by
  have facts : FiniteCoupling.check first second table = true ∧
      (∀ x y, 0 < table x y → x.2 = y.2) ∧
      (∑ x, ∑ y, table x y * metric x.1 y.1) ≤ bound := by
    simpa [checkStep] using accepted
  refine ⟨FiniteCoupling.realCoupling first second table facts.1, ?_, ?_⟩
  · intro x y positive
    apply facts.2.1 x y
    change 0 < (table x y : ℝ) at positive
    exact_mod_cast positive
  · rw [FiniteCoupling.realCoupling_cost]
    exact_mod_cast facts.2.2

def checkSystem (first : A → S → S × O → ℚ) (second : A → T → T × O → ℚ)
    (tables : A → S → T → (S × O) → (T × O) → ℚ)
    (firstReward : S → ℚ) (secondReward : T → ℚ) (metric : S → T → ℚ) : Bool :=
  decide ((∀ a s, checkDistribution (first a s) = true) ∧
    (∀ a t, checkDistribution (second a t) = true) ∧
    (∀ s t, |firstReward s - secondReward t| ≤ metric s t) ∧
    ∀ a s t, checkStep (first a s) (second a t) (tables a s t) metric (metric s t) = true)

/-- Checked joint laws lift to every finite observation-contingent execution;
latent transition agreement alone is insufficient. -/
theorem checkSystem_sound
    (first : A → S → S × O → ℚ) (second : A → T → T × O → ℚ)
    (tables : A → S → T → (S × O) → (T × O) → ℚ)
    (firstReward : S → ℚ) (secondReward : T → ℚ) (metric : S → T → ℚ)
    (accepted : checkSystem first second tables firstReward secondReward metric = true) :
    ∃ firstValid : ∀ a s, IsDistribution (first a s),
      ∃ secondValid : ∀ a t, IsDistribution (second a t),
      ∀ {n : ℕ} (policy : ObservationPolicy O A n) s t,
        |adaptiveValue (fun a s => realDistribution (first a s) (firstValid a s))
            (fun s => (firstReward s : ℝ)) policy s -
          adaptiveValue (fun a t => realDistribution (second a t) (secondValid a t))
            (fun t => (secondReward t : ℝ)) policy t| ≤ (metric s t : ℝ) := by
  have facts := of_decide_eq_true accepted
  change (∀ a s, checkDistribution (first a s) = true) ∧
    (∀ a t, checkDistribution (second a t) = true) ∧
    (∀ s t, |firstReward s - secondReward t| ≤ metric s t) ∧
    (∀ a s t, checkStep (first a s) (second a t) (tables a s t) metric (metric s t) = true)
      at facts
  let fv : ∀ a s, IsDistribution (first a s) :=
    fun a s => (checkDistribution_iff _).mp (facts.1 a s)
  let sv : ∀ a t, IsDistribution (second a t) :=
    fun a t => (checkDistribution_iff _).mp (facts.2.1 a t)
  refine ⟨fv, sv, ?_⟩
  intro n policy s t
  apply abs_adaptiveValue_sub_le _ _ _ _ (fun s t => (metric s t : ℝ)) ?_ ?_ policy s t
  · intro x y
    exact_mod_cast facts.2.2.1 x y
  · intro a x y
    exact checkStep_sound _ _ _ _ _ (facts.2.2.2 a x y)

namespace Controls

def row (observed : Bool) (next : Unit × Bool) : ℚ := if next.2 = observed then 1 else 0

def table (first second : Bool) (x y : Unit × Bool) : ℚ :=
  if x.2 = first ∧ y.2 = second then 1 else 0

@[simp] theorem observed_card (observed : Bool) :
    ((Finset.univ : Finset (Unit × Bool)).filter (fun x => x.2 = observed)).card = 1 := by
  have singleton : (Finset.univ : Finset (Unit × Bool)).filter (fun x => x.2 = observed) =
      {((), observed)} := by
    ext ⟨u, b⟩
    cases u
    simp
  rw [singleton]
  simp

theorem matching_observation_accepted :
    checkStep (row false) (row false) (table false false) (fun _ _ => 0) 0 = true := by
  norm_num [checkStep, FiniteCoupling.check, row, table, Fintype.sum_prod_type,
    Fintype.sum_bool, Bool.forall_bool]

/-- Correct marginals alone admit a joint table that reverses the controller's observation. -/
theorem reversed_observation_has_correct_marginals :
    FiniteCoupling.check (row false) (row true) (table false true) = true := by
  norm_num [FiniteCoupling.check, row, table, Fintype.sum_prod_type,
    Fintype.sum_bool, Bool.forall_bool]

theorem reversed_observation_refused :
    checkStep (row false) (row true) (table false true) (fun _ _ => 0) 0 = false := by
  norm_num [checkStep, FiniteCoupling.check, row, table, Fintype.sum_prod_type,
    Fintype.sum_bool, Bool.forall_bool]

theorem wrong_marginals_refused :
    checkStep (row false) (row false) (fun _ _ => 0) (fun _ _ => 0) 0 = false := by
  norm_num [checkStep, FiniteCoupling.check, row, table, Fintype.sum_prod_type,
    Fintype.sum_bool, Bool.forall_bool]

end Controls

end Mettapedia.Algorithms.FiniteControlledCoupling
