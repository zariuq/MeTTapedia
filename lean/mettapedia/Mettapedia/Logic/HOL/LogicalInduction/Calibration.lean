import Mettapedia.Logic.HOL.LogicalInduction.Conditioning

/-!
# Calibration and Timely-Learning Specifications for HOL Belief Processes

This module adds regression-friendly specification predicates for the
logical-induction-ready HOL belief layer.

Following Garrabrant, Benson-Tilsen, Critch, Soares, and Taylor,
*Logical Induction*, arXiv:1609.03543v5 (2020), the interesting future
properties are not only coherence but also calibration and timely learning.

The current file does **not** claim a full logical-inductor construction.
Instead it provides:

- eventual-price specifications,
- visible-theorem trust/timely-learning predicates,
- finite-sample calibration predicates,
- positive and negative toy examples against the current rational market layer.
-/

namespace Mettapedia.Logic.HOL.LogicalInduction

open Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- A belief process eventually stabilizes a coded formula at price `p`. -/
def EventuallyPriceEq
    (P : BeliefProcess Const)
    (φ : ClosedFormulaCode Const)
    (p : Price01) : Prop :=
  ∃ N : Nat, ∀ n : Nat, N ≤ n → P n φ = p

/-- Every theorem visible by day `n` is already priced at `1` on day `n`. -/
def TrustsVisibleTheorems
    (D : DeductiveProcess Const)
    (P : BeliefProcess Const) : Prop :=
  ∀ ⦃n : Nat⦄ ⦃φ : ClosedFormulaCode Const⦄, φ ∈ D.days n → P n φ = Price01.one

/-- Formulas eventually proved by the deductive process are eventually priced at `1`. -/
def TimelyLearnsAtOne
    (D : DeductiveProcess Const)
    (P : BeliefProcess Const) : Prop :=
  ∀ ⦃φ : ClosedFormulaCode Const⦄, D.eventuallyProves φ →
    EventuallyPriceEq (Const := Const) P φ Price01.one

/-- Exact pricing against a finite target table on a single day. -/
def ExactOnFiniteSample
    (target : ClosedFormulaCode Const → Price01)
    (S : Finset (ClosedFormulaCode Const))
    (P : BeliefProcess Const)
    (n : Nat) : Prop :=
  ∀ ⦃φ : ClosedFormulaCode Const⦄, φ ∈ S → P n φ = target φ

/-- Eventual exact pricing against a finite target table. -/
def EventuallyExactOnFiniteSample
    (target : ClosedFormulaCode Const → Price01)
    (S : Finset (ClosedFormulaCode Const))
    (P : BeliefProcess Const) : Prop :=
  ∃ N : Nat, ∀ n : Nat, N ≤ n → ExactOnFiniteSample (Const := Const) target S P n

theorem trustsVisibleTheorems_implies_timelyLearnsAtOne
    (D : DeductiveProcess Const)
    (P : BeliefProcess Const)
    (htrust : TrustsVisibleTheorems (Const := Const) D P) :
    TimelyLearnsAtOne (Const := Const) D P := by
  intro φ hφ
  rcases hφ with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact htrust (D.mem_of_mem_mono hn hN)

theorem processOne_trustsVisibleTheorems
    (D : DeductiveProcess Const) :
    TrustsVisibleTheorems (Const := Const) D (processOne (Const := Const)) := by
  intro n φ _hφ
  simp [processOne, constantProcess, constantDay]

theorem processOne_timelyLearnsAtOne
    (D : DeductiveProcess Const) :
    TimelyLearnsAtOne (Const := Const) D (processOne (Const := Const)) := by
  exact trustsVisibleTheorems_implies_timelyLearnsAtOne
    (Const := Const) D (processOne (Const := Const))
    (processOne_trustsVisibleTheorems (Const := Const) D)

theorem processOne_eventuallyExactOnFiniteSample_one
    (S : Finset (ClosedFormulaCode Const)) :
    EventuallyExactOnFiniteSample
      (Const := Const)
      (fun _ => Price01.one) S (processOne (Const := Const)) := by
  refine ⟨0, ?_⟩
  intro n _hn φ hφ
  simp [processOne, constantProcess, constantDay]

theorem processZero_eventuallyExactOnFiniteSample_zero
    (S : Finset (ClosedFormulaCode Const)) :
    EventuallyExactOnFiniteSample
      (Const := Const)
      (fun _ => Price01.zero) S (processZero (Const := Const)) := by
  refine ⟨0, ?_⟩
  intro n _hn φ hφ
  simp [processZero, constantProcess, constantDay]

theorem processZero_not_trustsVisibleTheorems_constant
    (φ : ClosedFormulaCode Const) :
    ¬ TrustsVisibleTheorems
      (Const := Const)
      (DeductiveProcess.constant (Const := Const) ({φ} : Finset (ClosedFormulaCode Const)))
      (processZero (Const := Const)) := by
  intro htrust
  have hφ :
      φ ∈ (DeductiveProcess.constant (Const := Const) ({φ} : Finset (ClosedFormulaCode Const))).days 0 := by
    simp [DeductiveProcess.constant]
  have hone := htrust hφ
  simp [processZero, constantProcess, constantDay] at hone
  have hval := congrArg Price01.val hone
  norm_num at hval

theorem processZero_not_timelyLearnsAtOne_constant
    (φ : ClosedFormulaCode Const) :
    ¬ TimelyLearnsAtOne
      (Const := Const)
      (DeductiveProcess.constant (Const := Const) ({φ} : Finset (ClosedFormulaCode Const)))
      (processZero (Const := Const)) := by
  intro hlearns
  have hprov :
      (DeductiveProcess.constant
        (Const := Const) ({φ} : Finset (ClosedFormulaCode Const))).eventuallyProves φ := by
    exact ⟨0, by simp [DeductiveProcess.constant]⟩
  rcases hlearns hprov with ⟨N, hN⟩
  have hone := hN N (le_rfl : N ≤ N)
  simp [processZero, constantProcess, constantDay] at hone
  have hval := congrArg Price01.val hone
  norm_num at hval

theorem processHalf_not_eventuallyExactOnFiniteSample_one
    {φ : ClosedFormulaCode Const} :
    ¬ EventuallyExactOnFiniteSample
      (Const := Const)
      (fun _ => Price01.one) ({φ} : Finset (ClosedFormulaCode Const))
      (processHalf (Const := Const)) := by
  intro hcal
  rcases hcal with ⟨N, hN⟩
  have hone := hN N (le_rfl : N ≤ N) (by simp : φ ∈ ({φ} : Finset (ClosedFormulaCode Const)))
  simp [processHalf, constantProcess, constantDay] at hone
  have hval := congrArg Price01.val hone
  norm_num at hval

end Mettapedia.Logic.HOL.LogicalInduction
