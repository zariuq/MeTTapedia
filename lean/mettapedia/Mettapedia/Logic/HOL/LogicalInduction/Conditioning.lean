import Mettapedia.Logic.HOL.LogicalInduction.Market

/-!
# Theory-Extension Conditioning for HOL Logical Induction

This module packages the first conditioning/theory-extension interface for the
logical-induction-ready HOL belief layer.

Following Garrabrant, Benson-Tilsen, Critch, Soares, and Taylor,
*Logical Induction*, arXiv:1609.03543v5 (2020), conditioning should be treated
as "add axioms and continue" rather than as a semantic rewrite of HOL truth.

The present file keeps that boundary explicit:

- HOL semantics remain in `Semantics/Henkin.lean`,
- theorem streams are extended by added axioms,
- belief processes are adjusted by a toy axiom-forcing operator,
- no claim is made that this is already a full logical-inductor update rule.
-/

namespace Mettapedia.Logic.HOL.LogicalInduction

open Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Finite axiom extension used for v1 conditioning. -/
abbrev TheoryExtension (Const : Ty Base → Type v) := Finset (ClosedFormulaCode Const)

/-- Toy day-level conditioning operator: formulas in `Γ` are forced to price `1`. -/
noncomputable def forceAxiomsAtOneDay
    (Γ : TheoryExtension Const)
    (B : BeliefDay Const) : BeliefDay Const := by
  classical
  exact fun φ => if φ ∈ Γ then Price01.one else B φ

/-- Toy process-level conditioning operator: force `Γ` to price `1` on every day. -/
noncomputable def forceAxiomsAtOne
    (Γ : TheoryExtension Const)
    (P : BeliefProcess Const) : BeliefProcess Const :=
  fun n => forceAxiomsAtOneDay (Const := Const) Γ (P n)

/-- Abstract shape of a process-level conditioning operator. -/
structure ConditioningOperator (Const : Ty Base → Type v) where
  condition :
    TheoryExtension Const → BeliefProcess Const → BeliefProcess Const

/-- Basic v1 correctness shape for conditioning: newly added axioms price at `1`. -/
def RespectsTheoryExtension
    (C : ConditioningOperator Const) : Prop :=
  ∀ (Γ : TheoryExtension Const) (P : BeliefProcess Const) {φ : ClosedFormulaCode Const},
    φ ∈ Γ → ∀ n : Nat, C.condition Γ P n φ = Price01.one

/-- Optional extensionality shape for formulas outside the added axioms. -/
def PreservesOutsideAxioms
    (C : ConditioningOperator Const) : Prop :=
  ∀ (Γ : TheoryExtension Const) (P : BeliefProcess Const) {φ : ClosedFormulaCode Const},
    φ ∉ Γ → ∀ n : Nat, C.condition Γ P n φ = P n φ

/-- Canonical v1 conditioning operator for the current logical-induction-ready layer. -/
noncomputable def forceAxiomsAtOneOperator : ConditioningOperator Const where
  condition := forceAxiomsAtOne (Const := Const)

@[simp] theorem forceAxiomsAtOneDay_mem
    (Γ : TheoryExtension Const)
    (B : BeliefDay Const)
    {φ : ClosedFormulaCode Const}
    (hφ : φ ∈ Γ) :
    forceAxiomsAtOneDay (Const := Const) Γ B φ = Price01.one := by
  classical
  simp [forceAxiomsAtOneDay, hφ]

@[simp] theorem forceAxiomsAtOneDay_not_mem
    (Γ : TheoryExtension Const)
    (B : BeliefDay Const)
    {φ : ClosedFormulaCode Const}
    (hφ : φ ∉ Γ) :
    forceAxiomsAtOneDay (Const := Const) Γ B φ = B φ := by
  classical
  simp [forceAxiomsAtOneDay, hφ]

@[simp] theorem forceAxiomsAtOne_mem
    (Γ : TheoryExtension Const)
    (P : BeliefProcess Const)
    {φ : ClosedFormulaCode Const}
    (hφ : φ ∈ Γ)
    (n : Nat) :
    forceAxiomsAtOne (Const := Const) Γ P n φ = Price01.one := by
  classical
  simp [forceAxiomsAtOne, forceAxiomsAtOneDay, hφ]

@[simp] theorem forceAxiomsAtOne_not_mem
    (Γ : TheoryExtension Const)
    (P : BeliefProcess Const)
    {φ : ClosedFormulaCode Const}
    (hφ : φ ∉ Γ)
    (n : Nat) :
    forceAxiomsAtOne (Const := Const) Γ P n φ = P n φ := by
  classical
  simp [forceAxiomsAtOne, forceAxiomsAtOneDay, hφ]

theorem forceAxiomsAtOne_respectsTheoryExtension :
    RespectsTheoryExtension (Base := Base) (Const := Const)
      (forceAxiomsAtOneOperator (Const := Const)) := by
  intro Γ P φ hφ n
  exact forceAxiomsAtOne_mem (Const := Const) Γ P hφ n

theorem forceAxiomsAtOne_preservesOutsideAxioms :
    PreservesOutsideAxioms (Base := Base) (Const := Const)
      (forceAxiomsAtOneOperator (Const := Const)) := by
  intro Γ P φ hφ n
  exact forceAxiomsAtOne_not_mem (Const := Const) Γ P hφ n

@[simp] theorem forceAxiomsAtOne_empty
    (P : BeliefProcess Const) :
    forceAxiomsAtOne (Const := Const) (∅ : TheoryExtension Const) P = P := by
  funext n φ
  classical
  simp [forceAxiomsAtOne, forceAxiomsAtOneDay]

theorem forceAxiomsAtOne_idem
    (Γ : TheoryExtension Const)
    (P : BeliefProcess Const) :
    forceAxiomsAtOne (Const := Const) Γ (forceAxiomsAtOne (Const := Const) Γ P) =
      forceAxiomsAtOne (Const := Const) Γ P := by
  funext n φ
  classical
  by_cases hφ : φ ∈ Γ
  · simp [forceAxiomsAtOne, forceAxiomsAtOneDay, hφ]
  · simp [forceAxiomsAtOne, forceAxiomsAtOneDay, hφ]

theorem forceAxiomsAtOne_union
    (Γ Δ : TheoryExtension Const)
    (P : BeliefProcess Const) :
    forceAxiomsAtOne (Const := Const) (Γ ∪ Δ) P =
      forceAxiomsAtOne (Const := Const) Δ (forceAxiomsAtOne (Const := Const) Γ P) := by
  funext n φ
  classical
  by_cases hΓ : φ ∈ Γ
  · simp [forceAxiomsAtOne, forceAxiomsAtOneDay, hΓ]
  · by_cases hΔ : φ ∈ Δ
    · simp [forceAxiomsAtOne, forceAxiomsAtOneDay, hΓ, hΔ]
    · simp [forceAxiomsAtOne, forceAxiomsAtOneDay, hΓ, hΔ]

end Mettapedia.Logic.HOL.LogicalInduction
