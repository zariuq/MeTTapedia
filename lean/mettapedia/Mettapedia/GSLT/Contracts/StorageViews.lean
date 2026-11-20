import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# When a bag fold can use a set view

An observation of an ordered occurrence word may see its order. A
commutative fold factors through the bag, but can additionally pass
through the support set precisely when each individual contribution
is idempotent. This is a criterion on the declared readout, not on
the memory layout of the collection.

The keys can come from any qualified equation view. Moving the
observer to a support set erases multiplicity even when distinct
original payloads happen to have the same key. Nothing here turns
a count, a queue operation, or an occurrence take into a set read.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.StorageViews

open scoped BigOperators

variable {Key Grade : Type*} [AddCommMonoid Grade]

def orderedFold (weight : Key → Grade) (word : List Key) : Grade :=
  (word.map weight).sum

def bagFold (weight : Key → Grade) (bag : Multiset Key) : Grade :=
  (bag.map weight).sum

theorem fold_through_bag (weight : Key → Grade) (word : List Key) :
    bagFold weight (word : Multiset Key) = orderedFold weight word := rfl

variable [DecidableEq Key]

def supportFold (weight : Key → Grade) (support : Finset Key) : Grade :=
  ∑ key ∈ support, weight key

theorem supportFold_exact (weight : Key → Grade)
    (idempotent : ∀ key, weight key + weight key = weight key) (word : List Key) :
    supportFold weight word.toFinset = orderedFold weight word := by
  induction word with
  | nil => simp [supportFold, orderedFold]
  | cons key rest ih =>
      simp only [List.toFinset_cons, orderedFold, List.map_cons, List.sum_cons]
      change supportFold weight (insert key rest.toFinset) =
        weight key + orderedFold weight rest
      rw [← ih]
      unfold supportFold
      by_cases present : key ∈ rest.toFinset
      · rw [Finset.insert_eq_of_mem present]
        have expanded := Finset.add_sum_erase rest.toFinset weight present
        rw [← expanded]
        rw [← add_assoc, idempotent]
      · exact Finset.sum_insert present

/-- Dropping duplicate keys is lawful for a commutative readout
exactly when a duplicate contributes nothing new. -/
theorem factors_through_support_iff (weight : Key → Grade) :
    (∃! readout : Finset Key → Grade,
      ∀ word, readout word.toFinset = orderedFold weight word) ↔
      ∀ key, weight key + weight key = weight key := by
  constructor
  · rintro ⟨readout, exactOnWord, _⟩ key
    have same := (exactOnWord [key, key]).symm.trans
      ((congrArg readout (by simp : [key, key].toFinset = [key].toFinset)).trans (exactOnWord [key]))
    simpa [orderedFold] using same
  · intro law
    refine ⟨supportFold weight, supportFold_exact weight law, ?_⟩
    intro other calculates
    funext support
    have prior := calculates support.toList
    have now := supportFold_exact weight law support.toList
    simpa using prior.trans now.symm

namespace Controls

theorem presence_survives_support (word : List Nat) (key : Nat) :
    (word.any (· == key)) = decide (key ∈ word.toFinset) := by
  apply Bool.eq_iff_iff.mpr
  change word.any (· == key) = true ↔ decide (key ∈ word.toFinset) = true
  simp only [List.any_eq_true, beq_iff_eq, decide_eq_true_eq, List.mem_toFinset]
  constructor
  · rintro ⟨other, present, rfl⟩
    exact present
  · intro present
    exact ⟨key, present, rfl⟩

theorem count_does_not_factor_through_support :
    ¬ ∃ f : Finset Nat → Nat, ∀ word : List Nat, f word.toFinset = word.length := by
  rintro ⟨f, exactOnWord⟩
  have first := exactOnWord [1]
  have second := exactOnWord [1, 1]
  have equal : ([1, 1] : List Nat).toFinset = ([1] : List Nat).toFinset := by simp
  rw [equal, first] at second
  cases second

/-- The order observer also fails to factor, even before taking
support. A priority view is a separate order policy from a queue. -/
theorem queue_head_does_not_factor_through_bags :
    ¬ ∃ f : Multiset Nat → Option Nat, ∀ word : List Nat, f word = word.head? := by
  rintro ⟨f, exactOnWord⟩
  have sameBag : (([1, 2] : List Nat) : Multiset Nat) = ([2, 1] : List Nat) :=
    Multiset.coe_eq_coe.mpr (List.Perm.swap ..)
  have same := (exactOnWord [1, 2]).symm.trans ((congrArg f sameBag).trans (exactOnWord [2, 1]))
  cases same

end Controls

#print axioms fold_through_bag
#print axioms factors_through_support_iff
#print axioms Controls.presence_survives_support
#print axioms Controls.count_does_not_factor_through_support
#print axioms Controls.queue_head_does_not_factor_through_bags

end Mettapedia.GSLT.Contracts.StorageViews
