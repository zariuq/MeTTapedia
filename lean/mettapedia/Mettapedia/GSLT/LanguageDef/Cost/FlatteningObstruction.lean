import Mettapedia.Algebra.Injective2
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.List.Basic
import Mathlib.Data.Multiset.AddSub

/-!
# Quote-faithfulness obstruction for cost multiplication

The June 22, 2026 manuscript *Continued Interactive GSLTs and the Cost
Endofunctor: Wrapping by Construction* (source SHA-256
`c91a5f2f75ff960e78c415249945084583d493c31bf7b1d7b1a5088a898cc9b6`)
requires the multiplication that flattens two cost layers to be injective on
signature keys.  This module records the elementary obstruction independently
of any particular GSLT encoding.

Injectivity after fixing either argument is cancellation.  Injectivity in both
arguments jointly is much stronger: for any nontrivial type, it is incompatible
with a two-sided unit.  Consequently, neither a cancellative signature monoid
nor the free monoid of event words can make flattening globally injective on
factorizations.
-/

namespace Mettapedia.GSLT.LanguageDef.Cost.FlatteningObstruction

/-- Hence multiplication in a nontrivial monoid cannot retain the boundary
between its two arguments. -/
theorem mul_not_injective2 {M : Type*} [Monoid M] [Nontrivial M] :
    ¬Function.Injective2 (fun left right : M => left * right) := by
  intro injective
  exact not_subsingleton M
    (Mettapedia.Algebra.mul_injective2_iff_subsingleton.mp injective)

/-- Cancellation still proves the valid fixed-left claim from the manuscript. -/
theorem fixedLeftMul_injective {M : Type*} [Mul M] [IsLeftCancelMul M]
    (left : M) : Function.Injective (fun right => left * right) :=
  mul_right_injective left

/-- Natural-number addition is injective after fixing its left argument. -/
theorem nat_fixedLeftAdd_injective (left : Nat) :
    Function.Injective (fun right => left + right) := by
  intro first second equality
  exact Nat.add_left_cancel equality

/-- Nevertheless, natural-number addition is not jointly injective on a pair
of summands. -/
theorem nat_add_not_injective2 :
    ¬Function.Injective2 (fun left right : Nat => left + right) := by
  intro injective
  exact not_subsingleton Nat
    ((Mettapedia.Algebra.add_injective2_iff_subsingleton (A := Nat)).mp
      injective)

/-- List concatenation already forgets the boundary in the unit cases. -/
theorem list_append_not_injective (element : α) :
    ¬Function.Injective2 (fun left right : List α => left ++ right) := by
  intro injective
  have pairEquality : ([] : List α) = [element] ∧ [element] = [] := by
    apply injective
    simp
  have lengthEquality := congrArg List.length pairEquality.1
  simp at lengthEquality

/-- Even with both factors nonempty, concatenation forgets where one factor
ends and the next begins. -/
theorem list_append_forgets_nonempty_boundary (first second third : α) :
    (([first], [second, third]) : List α × List α) ≠
        ([first, second], [third]) ∧
      [first] ++ [second, third] = [first, second] ++ [third] := by
  constructor
  · intro pairEquality
    have lengthEquality := congrArg (fun pair => pair.1.length) pairEquality
    simp at lengthEquality
  · rfl

/-- Writer-style multiplication combines the outer and inner accounts and
forgets which unit embedding supplied a nontrivial account. -/
def writerFlatten {M X : Type*} [Monoid M] (value : M × (M × X)) : M × X :=
  (value.1 * value.2.1, value.2.2)

/-- Writer multiplication is not injective for a nontrivial account monoid.
The two monad-unit embeddings already supply a collision. -/
theorem writerFlatten_not_injective {M X : Type*} [Monoid M] [Nontrivial M]
    (value : X) : ¬Function.Injective (writerFlatten (M := M) (X := X)) := by
  intro injective
  obtain ⟨account, account_ne⟩ := exists_ne (1 : M)
  have nestedEquality :
      ((1, (account, value)) : M × (M × X)) =
        (account, (1, value)) := by
    apply injective
    simp [writerFlatten]
  have outerEquality : (1 : M) = account :=
    congrArg Prod.fst nestedEquality
  exact account_ne outerEquality.symm

/-- Free commutative-monoid addition forgets a nonempty factor boundary even
though it retains every element and multiplicity. -/
theorem multiset_add_forgets_nonempty_boundary (first second third : α) :
    (({first}, {second, third}) : Multiset α × Multiset α) ≠
        ({first, second}, {third}) ∧
      ((({first} : Multiset α) + ({second, third} : Multiset α)) : Multiset α) =
        ((({first, second} : Multiset α) + ({third} : Multiset α)) : Multiset α) := by
  constructor
  · intro pairEquality
    have cardEquality := congrArg (fun pair => pair.1.card) pairEquality
    simp at cardEquality
  · rfl

end Mettapedia.GSLT.LanguageDef.Cost.FlatteningObstruction
