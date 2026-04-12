import Mettapedia.AutoBooks.Codex.Henkin1950.Syntax
import Mettapedia.Logic.HOL.PrimeHenkinExtension

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Paper-facing specialization of the trusted prime-extension layer.

Henkin's pp. 86-88 argument first passes through a maximal consistent set of
closed formulas.  The current trusted HOL foundation already provides a
constructive prime, deductively closed, consistent extension for any consistent
closed theory.  This file exposes that layer directly in the Henkin (1950)
Codex namespace, while keeping the distinction between "prime" and fully
classical "maximal" explicit.
-/

/-- Paper-facing deductive closure for closed Henkin theories. -/
abbrev DeductivelyClosed (T : ClosedTheorySet) : Prop :=
  Mettapedia.Logic.HOL.ClosedTheorySet.DeductivelyClosed (Const := Primitive) T

/-- Paper-facing inconsistency for closed Henkin theories. -/
abbrev Inconsistent (T : ClosedTheorySet) : Prop :=
  Mettapedia.Logic.HOL.ClosedTheorySet.Inconsistent (Const := Primitive) T

/-- A closed Henkin theory is prime for disjunction when membership of `A ∨ B`
forces membership of one side. -/
def PrimeDisjunctionClosed (T : ClosedTheorySet) : Prop :=
  ∀ {A B : Sentence}, (or A B) ∈ T → A ∈ T ∨ B ∈ T

/-- A paper-facing prime consistent extension of a closed Henkin theory. -/
structure PrimeConsistentExtension (T U : ClosedTheorySet) : Prop where
  contains_base : ∀ {φ : Sentence}, φ ∈ T → φ ∈ U
  closed : DeductivelyClosed U
  consistent : Consistent U
  prime_or : PrimeDisjunctionClosed U

/-- Any formula finitely provable from the base theory belongs to its prime
consistent extension. -/
theorem PrimeConsistentExtension.mem_of_setProvable
    {T U : ClosedTheorySet} (hTU : PrimeConsistentExtension T U)
    {φ : Sentence} :
    SetProvable T φ → φ ∈ U := by
  intro hφ
  apply hTU.closed
  exact Mettapedia.Logic.HOL.ClosedTheorySet.provable_mono
    (Const := Primitive)
    (T := T) (U := U)
    (hTU := by
      intro ψ hψ
      exact hTU.contains_base hψ)
    hφ

/-- Constructive prime-extension counterpart of Henkin's maximal-consistent-set
step: every consistent closed Henkin theory admits a prime deductively closed
consistent extension. -/
theorem exists_primeConsistentExtension_of_consistent
    {T : ClosedTheorySet} (hCons : Consistent T) :
    ∃ U : ClosedTheorySet, PrimeConsistentExtension T U := by
  rcases Mettapedia.Logic.HOL.ClosedTheorySet.exists_prime_extension_of_consistent
      (Const := Primitive) (T := T) hCons with
    ⟨U, hExt, hClosed, hUCons, hPrime⟩
  exact ⟨U, ⟨hExt, hClosed, hUCons, hPrime⟩⟩

/-- Separation form of the prime-extension step: if `φ` is not finitely
provable from `T`, there is a prime consistent extension omitting `φ`. -/
theorem exists_primeConsistentExtension_separating
    {T : ClosedTheorySet} {φ : Sentence}
    (hNot : ¬ SetProvable T φ) :
    ∃ U : ClosedTheorySet, PrimeConsistentExtension T U ∧ φ ∉ U := by
  rcases Mettapedia.Logic.HOL.ClosedTheorySet.exists_prime_extension_separating
      (Const := Primitive) (T := T) (φ := φ) hNot with
    ⟨U, hExt, hClosed, hUCons, hPrime, hOmit⟩
  exact ⟨U, ⟨⟨hExt, hClosed, hUCons, hPrime⟩, hOmit⟩⟩

end Mettapedia.AutoBooks.Codex.Henkin1950
