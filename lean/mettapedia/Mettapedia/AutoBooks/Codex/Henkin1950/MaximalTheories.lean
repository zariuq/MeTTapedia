import Mettapedia.AutoBooks.Codex.Henkin1950.CompleteTheories

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Paper-facing maximality interfaces for Henkin p. 86.

Henkin's first move after Theorem 1 is to enlarge the starting closed theory to
a maximal consistent one: every omitted closed formula makes the enlarged set
inconsistent.  The trusted HOL core does not construct such a theory directly,
but the consequence of maximality can still be formalized cleanly on top of the
existing closed-theory interface.
-/

/-- Paper-facing maximality condition from p. 86: every omitted closed formula
forces inconsistency when added to the theory. -/
def MaximalClosedTheory (T : ClosedTheorySet) : Prop :=
  ∀ {φ : Sentence}, φ ∉ T → Inconsistent (Set.insert φ T)

/-- A direct derivation bridge: if every assumption in `Γ` is either `φ` itself
or already in `Δ`, then a contradiction from `Γ` yields `¬φ` from `Δ`. -/
theorem derivation_not_of_bot
    {Δ Γ : List Sentence} {φ : Sentence}
    (hBot : ExtDerivation Primitive Γ (.bot : Sentence))
    (hSplit : ∀ {ψ : Sentence}, ψ ∈ Γ → ψ = φ ∨ ψ ∈ Δ) :
    ExtDerivation Primitive Δ (not φ) := by
  refine .notI ?_
  exact ExtDerivation.mono
    (Δ := Γ)
    (Δ' := φ :: Δ)
    (φ := (.bot : Sentence))
    (by
      intro ψ hψ
      rcases hSplit hψ with rfl | hΔ
      · simp
      · simp [hΔ])
    hBot

/-- If adjoining `φ` to a closed Henkin theory produces inconsistency, then the
base theory finitely proves `¬φ`. -/
theorem provable_not_of_inconsistent_insert
    {T : ClosedTheorySet} {φ : Sentence}
    (hIncons : Inconsistent (Set.insert φ T)) :
    SetProvable T (not φ) := by
  classical
  rcases hIncons with ⟨Γ, hΓ, hBot⟩
  let Δ : List Sentence := Γ.filter (fun ψ => ψ ≠ φ)
  have hΔ : ∀ {ψ : Sentence}, ψ ∈ Δ → ψ ∈ T := by
    intro ψ hψ
    have hψΓ : ψ ∈ Γ := (List.mem_filter.mp hψ).1
    have hψInsert : ψ = φ ∨ ψ ∈ T := Set.mem_insert_iff.mp (hΓ ψ hψΓ)
    rcases hψInsert with hEq | hψT
    · have hneq : ψ ≠ φ := by
        simpa using (List.mem_filter.mp hψ).2
      exact False.elim (hneq hEq)
    · exact hψT
  have hSplit : ∀ {ψ : Sentence}, ψ ∈ Γ → ψ = φ ∨ ψ ∈ Δ := by
    intro ψ hψ
    by_cases hEq : ψ = φ
    · exact Or.inl hEq
    · exact Or.inr (by
        simpa [Δ, hEq] using hψ)
  exact
    Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_closedTheory
      (Const := Primitive)
      (T := T)
      (Δ := Δ)
      (hΔ := by
        intro ψ hψ
        exact hΔ hψ)
      (hφ := derivation_not_of_bot hBot hSplit)

namespace MaximalClosedTheory

variable {T : ClosedTheorySet}

/-- An omitted formula in a maximal consistent theory contributes its negation. -/
theorem neg_mem_of_not_mem
    (hMax : MaximalClosedTheory T)
    (hClosed : DeductivelyClosed T)
    {φ : Sentence}
    (hφ : φ ∉ T) :
    not φ ∈ T := by
  have hProv : SetProvable T (not φ) :=
    provable_not_of_inconsistent_insert (hMax hφ)
  exact hClosed hProv

/-- Maximal consistent theories satisfy Henkin's complete-theory property. -/
theorem complete
    (hMax : MaximalClosedTheory T)
    (hClosed : DeductivelyClosed T) :
    CompleteTheory T := by
  intro φ
  by_cases hφ : φ ∈ T
  · exact Or.inl hφ
  · exact Or.inr (neg_mem_of_not_mem hMax hClosed hφ)

end MaximalClosedTheory

/-- Paper-facing package for a closed theory that is deductively closed,
consistent, and maximal in Henkin's p. 86 sense. -/
structure MaximalConsistentTheory (T : ClosedTheorySet) : Prop where
  closed : DeductivelyClosed T
  consistent : Consistent T
  maximal : MaximalClosedTheory T

namespace MaximalConsistentTheory

variable {T : ClosedTheorySet}

/-- Every maximal consistent Henkin theory is a complete consistent theory in
the sense isolated in `CompleteTheories.lean`. -/
theorem to_completeConsistentTheory
    (hT : MaximalConsistentTheory T) :
    CompleteConsistentTheory T := by
  exact
    { closed := hT.closed
      consistent := hT.consistent
      complete := MaximalClosedTheory.complete hT.maximal hT.closed }

end MaximalConsistentTheory

end Mettapedia.AutoBooks.Codex.Henkin1950
