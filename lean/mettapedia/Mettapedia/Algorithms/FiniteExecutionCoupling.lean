import Mettapedia.Algorithms.FiniteCoupling
import Mettapedia.Cybernetics.ApproximateAdequacy.ControllerCoupling

/-!
# Raw certificates for two finite adaptive executions

The certificate contains rational joint tables and their continuation tables.
Validation follows the actions selected by each controller, checks both actual
successor marginals, and visits every positive-mass paired continuation. The
controllers may have different observation and action types.
-/

namespace Mettapedia.Algorithms.FiniteExecutionCoupling

universe uS uT uO uU

open Mettapedia.InformationTheory
open Mettapedia.Cybernetics.ApproximateAdequacy
open Mettapedia.Algorithms.FiniteBayes

variable {S T O U A B : Type*}
  [Fintype S] [Fintype T] [Fintype O] [Fintype U]

/-- Finite raw data, with one joint table at each paired history. -/
def Tables (S : Type uS) (T : Type uT) (O : Type uO) (U : Type uU) :
    ℕ → Type (max uS uT uO uU)
  | 0 => PUnit
  | n + 1 => ((S × O) → (T × U) → ℚ) ×
      ((S × O) → (T × U) → Tables S T O U n)

def check (first : A → S → S × O → ℚ) (second : B → T → T × U → ℚ)
    (firstReward : S → ℚ) (secondReward : T → ℚ) (metric : S → T → ℚ) :
    {n : ℕ} → ObservationPolicy O A n → ObservationPolicy U B n →
      S → T → Tables S T O U n → Bool
  | 0, _, _, s, t, _ => decide (|firstReward s - secondReward t| ≤ metric s t)
  | n + 1, p, q, s, t, tables =>
      FiniteCoupling.check (first p.1 s) (second q.1 t) tables.1 &&
        decide ((∑ x, ∑ y, tables.1 x y * metric x.1 y.1) ≤ metric s t) &&
        decide (∀ x y, 0 < tables.1 x y →
          check first second firstReward secondReward metric (n := n)
            (p.2 x.2) (q.2 y.2) x.1 y.1 (tables.2 x y) = true)

/-- Acceptance constructs the independent execution relation from raw tables. -/
theorem check_sound
    (first : A → S → S × O → ℚ) (second : B → T → T × U → ℚ)
    (firstValid : ∀ a s, IsDistribution (first a s))
    (secondValid : ∀ b t, IsDistribution (second b t))
    (firstReward : S → ℚ) (secondReward : T → ℚ) (metric : S → T → ℚ)
    {n : ℕ} (p : ObservationPolicy O A n) (q : ObservationPolicy U B n)
    (s : S) (t : T) (tables : Tables S T O U n)
    (accepted : check first second firstReward secondReward metric p q s t tables = true) :
    CoupledExecution
      (fun a s => realDistribution (first a s) (firstValid a s))
      (fun b t => realDistribution (second b t) (secondValid b t))
      (fun s => (firstReward s : ℝ)) (fun t => (secondReward t : ℝ))
      (fun s t => (metric s t : ℝ)) p q s t := by
  induction n generalizing s t with
  | zero =>
      apply CoupledExecution.terminal
      have bound : |firstReward s - secondReward t| ≤ metric s t := by
        simpa [check] using accepted
      exact_mod_cast bound
  | succ n ih =>
      have facts :
          (FiniteCoupling.check (first p.1 s) (second q.1 t) tables.1 = true ∧
            (∑ x, ∑ y, tables.1 x y * metric x.1 y.1) ≤ metric s t) ∧
          ∀ x y, 0 < tables.1 x y →
            check first second firstReward secondReward metric
              (p.2 x.2) (q.2 y.2) x.1 y.1 (tables.2 x y) = true := by
        simpa only [check, Bool.and_eq_true, decide_eq_true_eq] using accepted
      let coupling := FiniteCoupling.realCoupling
        (first p.1 s) (second q.1 t) tables.1 facts.1.1
      apply CoupledExecution.step coupling
      · intro x y positive
        apply ih (p.2 x.2) (q.2 y.2) x.1 y.1 (tables.2 x y)
        apply facts.2 x y
        change 0 < (tables.1 x y : ℝ) at positive
        exact_mod_cast positive
      · change (∑ x, ∑ y, (tables.1 x y : ℝ) * (metric x.1 y.1 : ℝ)) ≤
          (metric s t : ℝ)
        exact_mod_cast facts.1.2

def checkKernels [Fintype A] [Fintype B]
    (first : A → S → S × O → ℚ) (second : B → T → T × U → ℚ) : Bool :=
  decide ((∀ a s, checkDistribution (first a s) = true) ∧
    ∀ b t, checkDistribution (second b t) = true)

theorem checkKernels_iff [Fintype A] [Fintype B]
    (first : A → S → S × O → ℚ) (second : B → T → T × U → ℚ) :
    checkKernels first second = true ↔
      (∀ a s, IsDistribution (first a s)) ∧ ∀ b t, IsDistribution (second b t) := by
  simp [checkKernels, checkDistribution_iff]

end Mettapedia.Algorithms.FiniteExecutionCoupling
