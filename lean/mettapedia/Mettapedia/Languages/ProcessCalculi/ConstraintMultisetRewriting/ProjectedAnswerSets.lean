import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Prod

/-!
# Counting visible answers

A finite answer set is a set of pairs (visible part, hidden part). Projection keeps the
visible part.

* Alternatives whose visible projections are disjoint have additive visible counts
  (determinism relative to the visible variables).
* Disjoint full answers are not enough: two incompatible answers may project to one
  visible answer.
* If the hidden part is a function of the visible part (functional auxiliaries), projection
  preserves the count.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProjectedAnswerSets

variable {V W : Type} [DecidableEq V] [DecidableEq W]

/-- **Determinism relative to the visible variables makes visible counts add.** -/
theorem visible_count_additive (first second : Finset (V × W))
    (deterministic : Disjoint (first.image Prod.fst) (second.image Prod.fst)) :
    ((first ∪ second).image Prod.fst).card =
      (first.image Prod.fst).card + (second.image Prod.fst).card := by
  rw [Finset.image_union, Finset.card_union_of_disjoint deterministic]

omit [DecidableEq W] in
/-- **Functional hidden parts: projection preserves the count.** -/
theorem functional_projection_count (answers : Finset (V × W))
    (functional : ∀ a ∈ answers, ∀ b ∈ answers, a.1 = b.1 → a.2 = b.2) :
    (answers.image Prod.fst).card = answers.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb same
  exact Prod.ext same (functional a ha b hb same)

/-- **Separating example**: two disjoint full answers `(X = a, Y = b)` and `(X = a, Y = c)`,
one visible answer. Determinism on all variables does not give additive visible counts. -/
theorem full_determinism_is_not_enough :
    Disjoint ({(0, 1)} : Finset (Nat × Nat)) {(0, 2)} ∧
      (({(0, 1)} ∪ {(0, 2)} : Finset (Nat × Nat)).image Prod.fst).card = 1 ∧
      (({(0, 1)} : Finset (Nat × Nat)).image Prod.fst).card +
        (({(0, 2)} : Finset (Nat × Nat)).image Prod.fst).card = 2 := by
  decide


end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProjectedAnswerSets
