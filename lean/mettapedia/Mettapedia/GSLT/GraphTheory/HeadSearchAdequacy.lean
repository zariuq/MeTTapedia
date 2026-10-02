import Mettapedia.GSLT.GraphTheory.BohmTree
import Mettapedia.GSLT.GraphTheory.Solvability

/-!
# Adequacy of executable head search

The deterministic search implements the existing head-reduction relation.
Head-normalization completeness therefore gives eventual search success for
every solvable term. Failure at one budget is inconclusive; failure at every
budget is exactly unsolvability.
-/

namespace Mettapedia.GSLT.GraphTheory

theorem WeakHeadStep.headReduce_eq {term result : LambdaTerm}
    (step : WeakHeadStep term result) : headReduce term = some result := by
  induction step with
  | beta => rfl
  | @appLeft fn fn' arg step ih =>
      cases fn with
      | var n => cases step
      | lam body => cases step
      | app f a => simp only [headReduce, ih]

theorem WeakHeadStep.isAppHead_eq_false {term result : LambdaTerm}
    (step : WeakHeadStep term result) : term.isAppHead = false := by
  induction step with
  | beta => rfl
  | appLeft _ _ ih => exact ih

theorem WeakHeadStep.isHNF_eq_false {term result : LambdaTerm}
    (step : WeakHeadStep term result) : term.isHNF = false := by
  cases step with
  | beta => rfl
  | appLeft _ step => exact step.isAppHead_eq_false

theorem HeadStep.headReduce_eq {term result : LambdaTerm}
    (step : HeadStep term result) : headReduce term = some result := by
  induction step with
  | weak step => exact step.headReduce_eq
  | lam _ ih => simp only [headReduce, ih]

theorem HeadStep.isHNF_eq_false {term result : LambdaTerm}
    (step : HeadStep term result) : term.isHNF = false := by
  induction step with
  | weak step => exact step.isHNF_eq_false
  | lam _ ih => exact ih

/-- A real finite head-normalization derivation is realized by finite search. -/
theorem HeadNormalizes.search_exists {term : LambdaTerm} (normalizes : HeadNormalizes term) :
    ∃ fuel hnf, toHNF fuel term = some hnf := by
  induction normalizes with
  | @hnf hnf head =>
      refine ⟨1, hnf, ?_⟩
      simp only [toHNF, extractHNF_isSome_eq_isHNF, head, ite_true]
  | @step term result step _ ih =>
      obtain ⟨fuel, hnf, success⟩ := ih
      refine ⟨fuel + 1, hnf, ?_⟩
      simp only [toHNF, extractHNF_isSome_eq_isHNF, step.isHNF_eq_false,
        Bool.false_eq_true, ite_false, step.headReduce_eq]
      exact success

theorem solvable_iff_search_exists (term : LambdaTerm) :
    term.Solvable ↔ ∃ fuel hnf, toHNF fuel term = some hnf := by
  constructor
  · intro solvable
    exact (headNormalizes_of_solvable solvable).search_exists
  · rintro ⟨_, _, success⟩
    exact solvable_of_toHNF success

/-- Universal failure is semantically meaningful; a single timeout is not. -/
theorem semanticUnsolvable_iff_unsolvable (term : LambdaTerm) :
    SemanticUnsolvable term ↔ term.Unsolvable := by
  constructor
  · intro failure solvable
    obtain ⟨fuel, hnf, success⟩ := (solvable_iff_search_exists term).mp solvable
    rw [failure fuel] at success
    cases success
  · exact unsolvable_toHNF_none

end Mettapedia.GSLT.GraphTheory
