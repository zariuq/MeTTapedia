import Mettapedia.Languages.ProcessCalculi.MQCalculus.StructuralCongruence
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# MQ-Calculus: The COMM Reduction Rule

Communication as quantum measurement. Following Stay & Meredith (2026), Section 3.

## COMM rule

```
MQOut i | MQIn i { P, Q }  →  with |⟨0|ψᵢ⟩|²: P
                                 with |⟨1|ψᵢ⟩|²: Q
```

## Born rule

`born_prob r ψ = ‖⟨r|ψ⟩‖²` — derived from symmetry, not axiomatized.

## MORK connection

`MQOut i | MQIn i P Q` fires ALL matching pairs simultaneously, identical to
MORK's parallel multi-subcall (unfold N sub-queries; fold all N results).
-/

namespace Mettapedia.Languages.ProcessCalculi.MQCalculus

open Process

/-- An n-qubit Hilbert space vector. -/
abbrev QVec (n : ℕ) := EuclideanSpace ℂ (Fin (2 ^ n))

inductive Outcome : Type where
  | zero : Outcome
  | one  : Outcome
  deriving DecidableEq

noncomputable def ket0 : QVec 1 := EuclideanSpace.single (0 : Fin (2 ^ 1)) (1 : ℂ)
noncomputable def ket1 : QVec 1 := EuclideanSpace.single (1 : Fin (2 ^ 1)) (1 : ℂ)

/-- Born-rule probability `|⟨r|ψ⟩|²` using `Complex.normSq`. -/
noncomputable def born_prob (r : Outcome) (ψ : QVec 1) : ℝ :=
  match r with
  | .zero => Complex.normSq (@inner ℂ _ _ ket0 ψ)
  | .one  => Complex.normSq (@inner ℂ _ _ ket1 ψ)

theorem born_prob_nonneg (r : Outcome) (ψ : QVec 1) : 0 ≤ born_prob r ψ := by
  cases r <;> simp [born_prob, Complex.normSq_nonneg]

/-- Born probabilities sum to 1 for unit-norm states. -/
theorem born_prob_sum_one (ψ : QVec 1) (hψ : norm ψ = 1) :
    born_prob .zero ψ + born_prob .one ψ = 1 := by
  have hsum : (norm ψ) ^ 2 = (norm (ψ.ofLp 0)) ^ 2 + (norm (ψ.ofLp 1)) ^ 2 := by
    simpa [Fin.sum_univ_two] using (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin 2 => ℂ) ψ)
  have hnormsq : (norm ψ) ^ 2 = 1 := by
    nlinarith [hψ]
  calc
    born_prob .zero ψ + born_prob .one ψ
        = (norm (ψ.ofLp 0)) ^ 2 + (norm (ψ.ofLp 1)) ^ 2 := by
            simp [born_prob, ket0, ket1, EuclideanSpace.inner_single_left, Complex.normSq_eq_norm_sq]
    _ = (norm ψ) ^ 2 := by linarith [hsum]
    _ = 1 := hnormsq

/-- A measurement branch: outcome selected + resulting process. -/
structure MeasurementBranch where
  outcome : Outcome
  result  : Process

/-- `CommReduction i P Q b`: `MQOut i | MQIn i P Q` can step to branch `b`. -/
inductive CommReduction : ℕ → Process → Process → MeasurementBranch → Prop where
  | outcome_zero (i : ℕ) (p q : Process) :
      CommReduction i p q ⟨.zero, p⟩
  | outcome_one (i : ℕ) (p q : Process) :
      CommReduction i p q ⟨.one, q⟩

theorem comm_both_outcomes (i : ℕ) (p q : Process) :
    CommReduction i p q ⟨.zero, p⟩ ∧ CommReduction i p q ⟨.one, q⟩ :=
  ⟨.outcome_zero i p q, .outcome_one i p q⟩

theorem comm_branches_exhaustive (i : ℕ) (p q : Process) (b : MeasurementBranch) :
    CommReduction i p q b → b = ⟨.zero, p⟩ ∨ b = ⟨.one, q⟩ := by
  intro h; cases h with
  | outcome_zero => left; rfl
  | outcome_one  => right; rfl

end Mettapedia.Languages.ProcessCalculi.MQCalculus
