import Mettapedia.AutoBooks.Codex.Henkin1950.CanonicalTruthQuotients

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Compositional laws for Henkin's canonical truth relation.

The quotient-class quantifier clauses now live in `CanonicalTruthQuotients`.
This file adds the propositional connectives, so the paper-facing relation
`Holds` behaves like a genuine truth predicate over complete consistent closed
Henkin theories.
-/

/-- Closed theorem: from `B`, infer `A -> B`. -/
theorem theorem_imp_of_right (A B : Sentence) :
    Mettapedia.Logic.HOL.ClosedTheory.Provable
      (Const := Primitive) [] (imp B (imp A B)) := by
  refine .impI ?_
  refine .impI ?_
  exact .hyp (show B ∈ [A, B] from by simp)

/-- Closed theorem: from `¬A`, infer `A -> B`. -/
theorem theorem_imp_of_not_left (A B : Sentence) :
    Mettapedia.Logic.HOL.ClosedTheory.Provable
      (Const := Primitive) [] (imp (not A) (imp A B)) := by
  refine .impI ?_
  refine .impI ?_
  exact .botE <|
    .notE
      (.hyp (show not A ∈ [A, not A] from by simp))
      (.hyp (show A ∈ [A, not A] from by simp))

section CompleteConsistentTheory

variable {T : ClosedTheorySet}
variable (ν : ClassAssignment T Γ)

/-- Canonical truth always contains `⊤`. -/
theorem holds_top (hT : CompleteConsistentTheory T) :
    Holds T ν (.top : Formula Γ) := by
  simpa [Holds, ClassAssignment.closeFormula, ClassAssignment.closeTerm, closeTerm, subst] using
    (hT.closed <|
      Mettapedia.Logic.HOL.ClosedTheorySet.provable_top
        (Const := Primitive) T)

/-- Canonical truth never contains `⊥`. -/
@[simp] theorem holds_bot_iff_false (hT : CompleteConsistentTheory T) :
    Holds T ν (.bot : Formula Γ) ↔ False := by
  constructor
  · intro hBot
    have hBotMem : (.bot : Sentence) ∈ T := by
      simpa [Holds, ClassAssignment.closeFormula, ClassAssignment.closeTerm, closeTerm, subst] using hBot
    exact hT.consistent <|
      Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
        (Const := Primitive) hBotMem
  · intro hFalse
    cases hFalse

/-- Negative canary for canonical truth. -/
theorem not_holds_bot (hT : CompleteConsistentTheory T) :
    ¬ Holds T ν (.bot : Formula Γ) := by
  intro hBot
  exact (holds_bot_iff_false (T := T) (ν := ν) hT).1 hBot

/-- Canonical negation is exactly meta-level negation over a complete
consistent theory. -/
@[simp] theorem holds_not_iff_not_holds
    (hT : CompleteConsistentTheory T) (φ : Formula Γ) :
    Holds T ν (not φ) ↔ ¬ Holds T ν φ := by
  simpa [Holds, ClassAssignment.closeFormula, ClassAssignment.closeTerm, closeTerm, subst, not] using
    (CompleteConsistentTheory.neg_mem_iff_not_mem
      (T := T) hT (φ := ClassAssignment.closeFormula ν φ))

/-- Canonical conjunction is truth-functional. -/
@[simp] theorem holds_and_iff
    (hT : CompleteConsistentTheory T) (φ ψ : Formula Γ) :
    Holds T ν (and φ ψ) ↔ Holds T ν φ ∧ Holds T ν ψ := by
  let A : Sentence := ClassAssignment.closeFormula ν φ
  let B : Sentence := ClassAssignment.closeFormula ν ψ
  constructor
  · intro hAnd
    have hAndMem : and A B ∈ T := by
      simpa [Holds, A, B, and, ClassAssignment.closeFormula, ClassAssignment.closeTerm, closeTerm, subst]
        using hAnd
    constructor
    · have hAProv :=
        Mettapedia.Logic.HOL.ClosedTheorySet.provable_and_left
          (Const := Primitive)
          (T := T)
          (φ := A)
          (ψ := B)
          (Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
            (Const := Primitive) hAndMem)
      have hAMem : A ∈ T := hT.closed hAProv
      simpa [Holds, A] using hAMem
    · have hBProv :=
        Mettapedia.Logic.HOL.ClosedTheorySet.provable_and_right
          (Const := Primitive)
          (T := T)
          (φ := A)
          (ψ := B)
          (Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
            (Const := Primitive) hAndMem)
      have hBMem : B ∈ T := hT.closed hBProv
      simpa [Holds, B] using hBMem
  · rintro ⟨hA, hB⟩
    have hAProv :
        SetProvable T A :=
      Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
        (Const := Primitive)
        (by simpa [Holds, A] using hA)
    have hBProv :
        SetProvable T B :=
      Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
        (Const := Primitive)
        (by simpa [Holds, B] using hB)
    have hAndMem : and A B ∈ T := by
      exact hT.closed <|
        Mettapedia.Logic.HOL.ClosedTheorySet.provable_and_intro
          (Const := Primitive)
          (T := T)
          (φ := A)
          (ψ := B)
          hAProv
          hBProv
    simpa [Holds, A, B, and, ClassAssignment.closeFormula, ClassAssignment.closeTerm, closeTerm, subst]
      using hAndMem

/-- Canonical disjunction is truth-functional. -/
@[simp] theorem holds_or_iff
    (hT : CompleteConsistentTheory T) (φ ψ : Formula Γ) :
    Holds T ν (or φ ψ) ↔ Holds T ν φ ∨ Holds T ν ψ := by
  let A : Sentence := ClassAssignment.closeFormula ν φ
  let B : Sentence := ClassAssignment.closeFormula ν ψ
  constructor
  · intro hOr
    have hOrMem : or A B ∈ T := by
      simpa [Holds, A, B, or, ClassAssignment.closeFormula, ClassAssignment.closeTerm, closeTerm, subst]
        using hOr
    rcases hT.prime_or hOrMem with hA | hB
    · exact Or.inl (by simpa [Holds, A] using hA)
    · exact Or.inr (by simpa [Holds, B] using hB)
  · intro h
    rcases h with hA | hB
    · have hAProv :
        SetProvable T A :=
          Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
            (Const := Primitive)
            (by simpa [Holds, A] using hA)
      have hOrMem : or A B ∈ T := by
        exact hT.closed <|
          Mettapedia.Logic.HOL.ClosedTheorySet.provable_or_intro_left
            (Const := Primitive)
            (T := T)
            (φ := A)
            (ψ := B)
            hAProv
      simpa [Holds, A, B, or, ClassAssignment.closeFormula, ClassAssignment.closeTerm, closeTerm, subst]
        using hOrMem
    · have hBProv :
        SetProvable T B :=
          Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
            (Const := Primitive)
            (by simpa [Holds, B] using hB)
      have hOrMem : or A B ∈ T := by
        exact hT.closed <|
          Mettapedia.Logic.HOL.ClosedTheorySet.provable_or_intro_right
            (Const := Primitive)
            (T := T)
            (φ := A)
            (ψ := B)
            hBProv
      simpa [Holds, A, B, or, ClassAssignment.closeFormula, ClassAssignment.closeTerm, closeTerm, subst]
        using hOrMem

/-- Canonical implication supports modus ponens. -/
theorem holds_imp_mp
    (hT : CompleteConsistentTheory T) {φ ψ : Formula Γ} :
    Holds T ν (imp φ ψ) →
      Holds T ν φ →
        Holds T ν ψ := by
  let A : Sentence := ClassAssignment.closeFormula ν φ
  let B : Sentence := ClassAssignment.closeFormula ν ψ
  intro hImp hA
  have hImpProv : SetProvable T (imp A B) :=
    Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
      (Const := Primitive)
      (by
        simpa [Holds, A, B, imp, ClassAssignment.closeFormula, ClassAssignment.closeTerm, closeTerm, subst]
          using hImp)
  have hAProv : SetProvable T A :=
    Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
      (Const := Primitive)
      (by simpa [Holds, A] using hA)
  have hBMem : B ∈ T := by
    exact hT.closed <|
      Mettapedia.Logic.HOL.ClosedTheorySet.provable_mp
        (Const := Primitive)
        (T := T)
        (φ := A)
        (ψ := B)
        hImpProv
        hAProv
  simpa [Holds, B] using hBMem

/-- Over a complete consistent theory, canonical implication is exactly
meta-level implication. -/
theorem holds_imp_iff
    (hT : CompleteConsistentTheory T) (φ ψ : Formula Γ) :
    Holds T ν (imp φ ψ) ↔ (Holds T ν φ → Holds T ν ψ) := by
  let A : Sentence := ClassAssignment.closeFormula ν φ
  let B : Sentence := ClassAssignment.closeFormula ν ψ
  constructor
  · intro hImp
    exact holds_imp_mp (T := T) hT (ν := ν) hImp
  · intro h
    by_cases hA : Holds T ν φ
    · have hB : Holds T ν ψ := h hA
      have hBProv : SetProvable T B :=
        Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
          (Const := Primitive)
          (by simpa [Holds, B] using hB)
      have hImpMem : imp A B ∈ T := by
        exact hT.closed <|
          Mettapedia.Logic.HOL.ClosedTheorySet.provable_mp
            (Const := Primitive)
            (T := T)
            (φ := B)
            (ψ := imp A B)
            (hImp :=
              Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_closedTheory
                (Const := Primitive)
                (T := T)
                (Δ := [])
                (hΔ := by intro ξ hξ; cases hξ)
                (hφ := theorem_imp_of_right A B))
            (hφ := hBProv)
      simpa [Holds, A, B, imp, ClassAssignment.closeFormula, ClassAssignment.closeTerm, closeTerm, subst]
        using hImpMem
    · have hNotA : Holds T ν (not φ) := by
        exact (holds_not_iff_not_holds (T := T) hT (ν := ν) φ).2 hA
      have hNotAProv : SetProvable T (not A) :=
        Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
          (Const := Primitive)
          (by simpa [Holds, A, not, ClassAssignment.closeFormula, ClassAssignment.closeTerm,
            closeTerm, subst] using hNotA)
      have hImpMem : imp A B ∈ T := by
        exact hT.closed <|
          Mettapedia.Logic.HOL.ClosedTheorySet.provable_mp
            (Const := Primitive)
            (T := T)
            (φ := not A)
            (ψ := imp A B)
            (hImp :=
              Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_closedTheory
                (Const := Primitive)
                (T := T)
                (Δ := [])
                (hΔ := by intro ξ hξ; cases hξ)
                (hφ := theorem_imp_of_not_left A B))
            (hφ := hNotAProv)
      simpa [Holds, A, B, imp, ClassAssignment.closeFormula, ClassAssignment.closeTerm, closeTerm, subst]
        using hImpMem

end CompleteConsistentTheory

end Mettapedia.AutoBooks.Codex.Henkin1950
