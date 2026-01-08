import Mathlib.Data.Fintype.EquivFin
import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples

open Classical KnuthSkillingAlgebra

/-!
# No nontrivial finite `KnuthSkillingAlgebra`

This is a small but useful obstruction lemma for countermodel search:

- If `α` is a `KnuthSkillingAlgebra` with at least two elements, then there exists `a > ident`,
  hence `iterate_op a : ℕ → α` is strictly monotone, hence injective, contradicting finiteness.

So any finite `KnuthSkillingAlgebra` must be the degenerate one-element model.

This does **not** refute Knuth–Skilling Appendix A; it only rules out a common false lead:
brute-forcing finite countermodels.
-/

variable {α : Type*} [Fintype α] [KnuthSkillingAlgebra α]

theorem card_le_one_of_fintype_knuthskilling : Fintype.card α ≤ 1 := by
  classical
  by_contra hcard
  have htwo : 1 < Fintype.card α := Nat.lt_of_not_ge hcard
  -- Pick some `a ≠ ident`, hence `ident < a` since `ident` is bottom.
  obtain ⟨a, ha_ne⟩ := Fintype.exists_ne_of_one_lt_card htwo (ident : α)
  have ha_pos : ident < a :=
    lt_of_le_of_ne (ident_le a) (Ne.symm ha_ne)

  -- `iterate_op a` is strictly monotone, hence injective, contradicting finiteness of `α`.
  have hinj : Function.Injective (iterate_op a) :=
    (iterate_op_strictMono a ha_pos).injective
  have hnot : ¬ Function.Injective (iterate_op a) := by
    -- Any map from an infinite type to a finite type cannot be injective.
    haveI : Infinite ℕ := inferInstance
    haveI : Finite α := inferInstance
    simpa using (not_injective_infinite_finite (f := iterate_op a) : ¬Function.Injective (iterate_op a))
  exact hnot hinj

theorem subsingleton_of_fintype_knuthskilling : Subsingleton α := by
  classical
  -- If the type has at most one element, it is a subsingleton.
  have h : Fintype.card α ≤ 1 := card_le_one_of_fintype_knuthskilling (α := α)
  simpa using Fintype.card_le_one_iff_subsingleton.mp h

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples
