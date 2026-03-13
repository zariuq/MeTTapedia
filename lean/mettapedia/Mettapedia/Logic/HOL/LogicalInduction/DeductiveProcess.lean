import Mathlib.Data.Finset.Basic
import Mettapedia.Logic.HOL.LogicalInduction.Code

/-!
# Deductive Processes for HOL Logical-Induction Infrastructure

This module introduces the theorem-stream abstraction used by the
logical-induction-ready HOL belief layer.

Following Garrabrant, Benson-Tilsen, Critch, Soares, and Taylor,
*Logical Induction*, arXiv:1609.03543v5 (2020), the belief process is
parameterized by a slow deductive process rather than a hard-coded prover.
-/

namespace Mettapedia.Logic.HOL.LogicalInduction

open Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- A monotone theorem stream of closed HOL formulas. -/
structure DeductiveProcess (Const : Ty Base → Type v) where
  days : Nat → Finset (ClosedFormulaCode Const)
  monotone_days : ∀ {m n : Nat}, m ≤ n → days m ⊆ days n

namespace DeductiveProcess

/-- The theorem set visible by day `n`. -/
def theoryAt (D : DeductiveProcess Const) (n : Nat) : Finset (ClosedFormulaCode Const) :=
  D.days n

/-- A formula has appeared by some finite day of the deductive process. -/
def eventuallyProves (D : DeductiveProcess Const) (φ : ClosedFormulaCode Const) : Prop :=
  ∃ n : Nat, φ ∈ D.days n

theorem mem_of_mem_mono (D : DeductiveProcess Const) {m n : Nat}
    (hmn : m ≤ n) {φ : ClosedFormulaCode Const} (hφ : φ ∈ D.days m) :
    φ ∈ D.days n :=
  D.monotone_days hmn hφ

theorem theoryAt_mono (D : DeductiveProcess Const) {m n : Nat} (hmn : m ≤ n) :
    D.theoryAt m ⊆ D.theoryAt n :=
  D.monotone_days hmn

/-- Empty deductive process: never emits any theorems. -/
noncomputable def empty : DeductiveProcess Const where
  days := fun _ => ∅
  monotone_days := by
    intro _ _ _ φ hφ
    simp at hφ

/-- Constant deductive process: every day exposes the same theorem set. -/
noncomputable def constant (Γ : Finset (ClosedFormulaCode Const)) : DeductiveProcess Const where
  days := fun _ => Γ
  monotone_days := by
    intro _ _ _ φ hφ
    simpa using hφ

/-- Extend a deductive process by adding axioms that are visible from day `0`
onward. This is the v1 conditioning/axiom-extension primitive. -/
noncomputable def extendByAxioms
    (D : DeductiveProcess Const) (Γ : Finset (ClosedFormulaCode Const)) :
    DeductiveProcess Const where
  days := fun n => D.days n ∪ Γ
  monotone_days := by
    intro m n hmn φ hφ
    exact Finset.mem_union.mpr <|
      match Finset.mem_union.mp hφ with
      | Or.inl hD => Or.inl (D.monotone_days hmn hD)
      | Or.inr hΓ => Or.inr hΓ

@[simp] theorem theoryAt_empty (n : Nat) :
    (empty (Const := Const)).theoryAt n = ∅ := rfl

@[simp] theorem theoryAt_constant (Γ : Finset (ClosedFormulaCode Const)) (n : Nat) :
    (constant (Const := Const) Γ).theoryAt n = Γ := rfl

@[simp] theorem theoryAt_extendByAxioms
    (D : DeductiveProcess Const) (Γ : Finset (ClosedFormulaCode Const)) (n : Nat) :
    (extendByAxioms D Γ).theoryAt n = D.theoryAt n ∪ Γ := rfl

@[simp] theorem extendByAxioms_empty
    (D : DeductiveProcess Const) :
    extendByAxioms D (∅ : Finset (ClosedFormulaCode Const)) = D := by
  cases D
  simp [extendByAxioms]
  funext n
  simp

theorem extendByAxioms_assoc
    (D : DeductiveProcess Const)
    (Γ Δ : Finset (ClosedFormulaCode Const)) :
    extendByAxioms (extendByAxioms D Γ) Δ =
      extendByAxioms D (Γ ∪ Δ) := by
  cases D
  simp [extendByAxioms, Finset.union_left_comm, Finset.union_comm]

theorem eventuallyProves_of_mem_day
    (D : DeductiveProcess Const) {n : Nat} {φ : ClosedFormulaCode Const}
    (hφ : φ ∈ D.days n) :
    D.eventuallyProves φ := ⟨n, hφ⟩

theorem eventuallyProves_of_extend_left
    (D : DeductiveProcess Const) (Γ : Finset (ClosedFormulaCode Const))
    {φ : ClosedFormulaCode Const}
    (hφ : D.eventuallyProves φ) :
    (extendByAxioms D Γ).eventuallyProves φ := by
  rcases hφ with ⟨n, hn⟩
  exact ⟨n, Finset.mem_union.mpr (Or.inl hn)⟩

theorem eventuallyProves_of_extend_axiom
    (D : DeductiveProcess Const) (Γ : Finset (ClosedFormulaCode Const))
    {φ : ClosedFormulaCode Const}
    (hφ : φ ∈ Γ) :
    (extendByAxioms D Γ).eventuallyProves φ := by
  exact ⟨0, Finset.mem_union.mpr (Or.inr hφ)⟩

end DeductiveProcess

end Mettapedia.Logic.HOL.LogicalInduction
