import Mettapedia.AutoBooks.Codex.Henkin1950.CompleteTheories
import Mettapedia.Logic.HOL.LindenbaumSet

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Closed proposition classes for Henkin p. 86.

Henkin first treats the type-`o` quotient separately: a closed proposition class
is sent to `T` or `F` according as the formula or its negation belongs to the
maximal consistent theory.  The trusted HOL core already provides the
Lindenbaum-set quotient of closed formulas by provable implication
equivalence.  This file isolates the corresponding two-valued collapse for
complete consistent Henkin theories.
-/

/-- Base-calculus theorem: from `¬A`, infer `A -> ⊥`. -/
theorem theorem_imp_bot_of_not (φ : Sentence) :
    Mettapedia.Logic.HOL.ExtDerivation.Theorem Primitive
      (imp (not φ) (imp φ (.bot : Sentence))) := by
  refine .impI ?_
  refine .impI ?_
  exact .notE
    (.hyp (show not φ ∈ [φ, not φ] from by simp))
    (.hyp (show φ ∈ [φ, not φ] from by simp))

/-- Base-calculus theorem: from `A -> ⊥`, infer `¬A`. -/
theorem theorem_not_of_imp_bot (φ : Sentence) :
    Mettapedia.Logic.HOL.ExtDerivation.Theorem Primitive
      (imp (imp φ (.bot : Sentence)) (not φ)) := by
  refine .impI ?_
  refine .notI ?_
  exact .impE
    (.hyp (show imp φ (.bot : Sentence) ∈ [φ, imp φ (.bot : Sentence)] from by simp))
    (.hyp (show φ ∈ [φ, imp φ (.bot : Sentence)] from by simp))

/-- In the trusted closed-theory calculus, membership of `¬A` yields a proof of
`A -> ⊥`. -/
theorem provable_imp_bot_of_not
    {T : ClosedTheorySet} {φ : Sentence}
    (hNot : SetProvable T (not φ)) :
    SetProvable T (imp φ (.bot : Sentence)) := by
  exact
    Mettapedia.Logic.HOL.ClosedTheorySet.provable_mp
      (T := T)
      (φ := not φ)
      (ψ := imp φ (.bot : Sentence))
      (hImp :=
        Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_closedTheory
          (Const := Primitive)
          (T := T)
          (Δ := [])
          (hΔ := by intro ψ hψ; cases hψ)
          (hφ := theorem_imp_bot_of_not φ))
      (hφ := hNot)

/-- Conversely, a proof of `A -> ⊥` yields a proof of `¬A`. -/
theorem provable_not_of_imp_bot
    {T : ClosedTheorySet} {φ : Sentence}
    (hImpBot : SetProvable T (imp φ (.bot : Sentence))) :
    SetProvable T (not φ) := by
  exact
    Mettapedia.Logic.HOL.ClosedTheorySet.provable_mp
      (T := T)
      (φ := imp φ (.bot : Sentence))
      (ψ := not φ)
      (hImp :=
        Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_closedTheory
          (Const := Primitive)
          (T := T)
          (Δ := [])
          (hΔ := by intro ψ hψ; cases hψ)
          (hφ := theorem_not_of_imp_bot φ))
      (hφ := hImpBot)

namespace CompleteConsistentTheory

variable {T : ClosedTheorySet}

/-- In a complete consistent Henkin theory, the Lindenbaum class of a closed
proposition is `⊥` exactly when its negation belongs to the theory. -/
theorem class_eq_bot_iff_neg_mem
    (hT : CompleteConsistentTheory T) {φ : Sentence} :
    (⟦φ⟧ : SentenceLindenbaumSet T) = ⊥ ↔ not φ ∈ T := by
  constructor
  · intro hEq
    rw [Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent.LindenbaumSet.bot_def] at hEq
    have hEqv :
        Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent
          (Const := Primitive) T φ (.bot : Sentence) :=
      (Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent.LindenbaumSet.eq_iff
        (Const := Primitive) (T := T) (φ := φ) (ψ := (.bot : Sentence))).1 hEq
    exact hT.closed (provable_not_of_imp_bot hEqv.1)
  · intro hNeg
    rw [Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent.LindenbaumSet.bot_def]
    refine
      (Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent.LindenbaumSet.eq_iff
        (Const := Primitive) (T := T) (φ := φ) (ψ := (.bot : Sentence))).2 ?_
    exact
      ⟨provable_imp_bot_of_not
          (T := T)
          (hNot :=
            Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
              (Const := Primitive) hNeg),
        Mettapedia.Logic.HOL.ClosedTheorySet.Provable.bot_imp
          (Const := Primitive) T φ⟩

/-- Positive canary for Henkin's p. 86 proposition domain: every closed
proposition class collapses to `⊤` or `⊥`. -/
theorem class_eq_top_or_eq_bot
    (hT : CompleteConsistentTheory T) (φ : Sentence) :
    (⟦φ⟧ : SentenceLindenbaumSet T) = ⊤ ∨
      (⟦φ⟧ : SentenceLindenbaumSet T) = ⊥ := by
  rcases hT.complete φ with hMem | hNeg
  · exact Or.inl ((class_eq_top_iff_mem (T := T) hT).2 hMem)
  · exact Or.inr ((class_eq_bot_iff_neg_mem (T := T) hT).2 hNeg)

/-- Negative canary: the proposition quotient of a complete consistent Henkin
theory does not collapse `⊤` and `⊥`. -/
theorem top_ne_bot
    (hT : CompleteConsistentTheory T) :
    (⊤ : SentenceLindenbaumSet T) ≠ ⊥ := by
  intro hEq
  have hBotTop : (⟦(.bot : Sentence)⟧ : SentenceLindenbaumSet T) = ⊤ := by
    simpa [Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent.LindenbaumSet.bot_def]
      using hEq.symm
  have hBotMem : (.bot : Sentence) ∈ T :=
    (class_eq_top_iff_mem (T := T) hT (φ := (.bot : Sentence))).1 hBotTop
  exact hT.consistent <|
    Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
      (Const := Primitive) hBotMem

end CompleteConsistentTheory

end Mettapedia.AutoBooks.Codex.Henkin1950
