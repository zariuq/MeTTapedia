import Mettapedia.AutoBooks.Codex.Henkin1950.PrimeExtensions
import Mettapedia.Logic.HOL.CanonicalTheory
import Mettapedia.Logic.HOL.LindenbaumSet

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Paper-facing closed-theory interfaces for Henkin pp. 86-88.

Henkin first constructs a maximal consistent closed theory `Γ`, then uses the
resulting completeness-at-closed-formulas property and the quotient by provable
equivalence to define the denumerable domains of the canonical general model.

The trusted HOL core currently gives a constructive prime extension and a
Lindenbaum quotient for closed formulas, but it does not directly construct the
paper's classical maximal theory.  This file isolates the exact closed-theory
properties the paper uses next, proves their immediate consequences, and
packages the bridge into the existing canonical-world interface.
-/

/-- A complete closed Henkin theory decides each closed formula by membership of
the formula or its negation.  This is the paper-facing property extracted from
Henkin's maximal consistent set on p. 86. -/
def CompleteTheory (T : ClosedTheorySet) : Prop :=
  ∀ φ : Sentence, φ ∈ T ∨ not φ ∈ T

/-- Paper-facing package of the closed-theory properties used after Henkin's
maximal-consistent-set construction. -/
structure CompleteConsistentTheory (T : ClosedTheorySet) : Prop where
  closed : DeductivelyClosed T
  consistent : Consistent T
  complete : CompleteTheory T

/-- The quotient of closed Henkin formulas by provable equivalence over a fixed
closed theory.  This is the formula-level quotient actually available in the
trusted HOL core. -/
abbrev SentenceLindenbaumSet (T : ClosedTheorySet) :=
  Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent.LindenbaumSet
    (Const := Primitive) T

/-- Intuitionistically derivable helper used to recover a disjunct from `¬A`
and `A ∨ B`. -/
theorem theorem_or_right_of_not_left (A B : Sentence) :
    ExtDerivation.Theorem Primitive (imp (not A) (imp (or A B) B)) := by
  refine .impI ?_
  refine .impI ?_
  have hOr : ExtDerivation Primitive [or A B, not A] (or A B) :=
    .hyp (show or A B ∈ [or A B, not A] from by simp)
  refine .orE hOr ?_ ?_
  · have hNotA : ExtDerivation Primitive [A, or A B, not A] (not A) :=
      .hyp (show not A ∈ [A, or A B, not A] from by simp)
    have hA : ExtDerivation Primitive [A, or A B, not A] A :=
      .hyp (show A ∈ [A, or A B, not A] from by simp)
    exact .botE (.notE hNotA hA)
  · exact .hyp (show B ∈ [B, or A B, not A] from by simp)

/-- Symmetric intuitionistic helper: from `¬B` and `A ∨ B`, recover `A`. -/
theorem theorem_or_left_of_not_right (A B : Sentence) :
    ExtDerivation.Theorem Primitive (imp (not B) (imp (or A B) A)) := by
  refine .impI ?_
  refine .impI ?_
  have hOr : ExtDerivation Primitive [or A B, not B] (or A B) :=
    .hyp (show or A B ∈ [or A B, not B] from by simp)
  refine .orE hOr ?_ ?_
  · exact .hyp (show A ∈ [A, or A B, not B] from by simp)
  · have hNotB : ExtDerivation Primitive [B, or A B, not B] (not B) :=
      .hyp (show not B ∈ [B, or A B, not B] from by simp)
    have hB : ExtDerivation Primitive [B, or A B, not B] B :=
      .hyp (show B ∈ [B, or A B, not B] from by simp)
    exact .botE (.notE hNotB hB)

namespace CompleteConsistentTheory

variable {T S : ClosedTheorySet}

/-- Closed-theory completeness gives a direct `φ ∉ T -> ¬φ ∈ T` bridge. -/
theorem neg_mem_of_not_mem (hT : CompleteConsistentTheory T) {φ : Sentence}
    (hφ : φ ∉ T) :
    not φ ∈ T := by
  rcases hT.complete φ with hMem | hNeg
  · exact False.elim (hφ hMem)
  · exact hNeg

/-- Consistency forbids membership of a formula together with its negation. -/
theorem not_mem_of_neg_mem (hT : CompleteConsistentTheory T) {φ : Sentence}
    (hNeg : not φ ∈ T) :
    φ ∉ T := by
  intro hφ
  exact hT.consistent <|
    Mettapedia.Logic.HOL.ClosedTheorySet.provable_bot_of_not
      (Const := Primitive)
      (T := T)
      (hNot := Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
        (Const := Primitive) hNeg)
      (hφ := Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
        (Const := Primitive) hφ)

/-- In a complete consistent closed Henkin theory, omission of `φ` is exactly
membership of `¬φ`. -/
theorem neg_mem_iff_not_mem (hT : CompleteConsistentTheory T) {φ : Sentence} :
    not φ ∈ T ↔ φ ∉ T := by
  constructor
  · exact not_mem_of_neg_mem hT
  · exact neg_mem_of_not_mem hT

/-- Deductive closure identifies set-membership with finite provability. -/
theorem provable_iff_mem (hT : CompleteConsistentTheory T) {φ : Sentence} :
    SetProvable T φ ↔ φ ∈ T := by
  constructor
  · exact hT.closed
  · intro hφ
    exact Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
      (Const := Primitive) hφ

/-- The closed-theory completeness property implies the disjunction-prime
condition used in the paper's canonical construction. -/
theorem prime_or (hT : CompleteConsistentTheory T) :
    PrimeDisjunctionClosed T := by
  intro A B hOr
  rcases hT.complete A with hA | hNotA
  · exact Or.inl hA
  · have hStep₁ : SetProvable T (imp (or A B) B) :=
      Mettapedia.Logic.HOL.ClosedTheorySet.provable_mp
        (T := T)
        (φ := not A)
        (ψ := imp (or A B) B)
        (hImp :=
          Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_closedTheory
            (Const := Primitive)
            (T := T)
            (Δ := [])
            (hΔ := by intro ξ hξ; cases hξ)
            (hφ := theorem_or_right_of_not_left A B))
        (hφ :=
          Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
            (Const := Primitive) hNotA)
    have hB : SetProvable T B :=
      Mettapedia.Logic.HOL.ClosedTheorySet.provable_mp
        (T := T)
        (φ := or A B)
        (ψ := B)
        (hImp := hStep₁)
        (hφ :=
          Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
            (Const := Primitive) hOr)
    exact Or.inr (hT.closed hB)

/-- A complete consistent theory is already a prime consistent extension of any
smaller closed theory contained in it. -/
theorem to_primeConsistentExtension
    (hT : CompleteConsistentTheory T)
    (hST : ∀ {φ : Sentence}, φ ∈ S → φ ∈ T) :
    PrimeConsistentExtension S T := by
  exact
    { contains_base := by
        intro φ hφ
        exact hST hφ
      closed := hT.closed
      consistent := hT.consistent
      prime_or := hT.prime_or }

/-- In particular, every complete consistent theory is a prime consistent
extension of itself. -/
theorem self_primeConsistentExtension (hT : CompleteConsistentTheory T) :
    PrimeConsistentExtension T T :=
  hT.to_primeConsistentExtension (fun h => h)

/-- For deductively closed theories, Henkin's closed-formula quotient detects
membership by equality with `⊤`. -/
theorem class_eq_top_iff_mem (hT : CompleteConsistentTheory T) {φ : Sentence} :
    (⟦φ⟧ : SentenceLindenbaumSet T) = ⊤ ↔ φ ∈ T := by
  constructor
  · intro hEq
    exact hT.closed <|
      (Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent.LindenbaumSet.provable_iff_eq_top
        (Const := Primitive) (T := T) (φ := φ)).2 hEq
  · intro hφ
    exact
      (Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent.LindenbaumSet.provable_iff_eq_top
        (Const := Primitive) (T := T) (φ := φ)).1 <|
        Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
          (Const := Primitive) hφ

end CompleteConsistentTheory

/-- Paper-facing witness condition: existential closed formulas carry a closed
term witness already inside the theory. -/
def ExistentialWitnessClosed (T : ClosedTheorySet) : Prop :=
  ∀ {α : HTy} {φ : Formula [α]},
    (.ex φ : Sentence) ∈ T → ∃ t : ClosedTerm α, instantiate t φ ∈ T

/-- Paper-facing universal counterexample condition: if a universal closed
formula is absent from the theory, then some closed instance is absent too. -/
def UniversalCounterexampleClosed (T : ClosedTheorySet) : Prop :=
  ∀ {α : HTy} {φ : Formula [α]},
    (.all φ : Sentence) ∉ T → ∃ t : ClosedTerm α, instantiate t φ ∉ T

/-- A complete consistent theory with the expected witness and counterexample
closure properties determines a canonical-world object in the trusted HOL core. -/
def CompleteConsistentTheory.toWorld
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hEx : ExistentialWitnessClosed T)
    (hAll : UniversalCounterexampleClosed T) :
    Mettapedia.Logic.HOL.ClosedTheorySet.World Primitive where
  carrier := T
  closed := hT.closed
  consistent := hT.consistent
  prime_or := hT.prime_or
  exists_witness := hEx
  all_counterexample := hAll

end Mettapedia.AutoBooks.Codex.Henkin1950
