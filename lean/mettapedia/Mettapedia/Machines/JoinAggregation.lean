import Mettapedia.Algebra.CollectionFold
import Mathlib.Algebra.Group.Pi.Basic

/-!
# Aggregates computed inside a join

A join may fold each solution into an aggregate as it enumerates them, while
an evaluator that collects the answers first folds the collected bag.  The
join's enumeration is a permutation of the collected order, so:

* a fold whose generator values commute gives one value for every
  enumeration (`fold_perm`); these are exactly the folds that consume bags
  (`CollectionFold.Boom.foldList_factors_bag_iff`);
* grouping is one fold into the product monoid over the keys: its value at a
  key is the fold of that key's group (`groupFold_apply`); it maps
  concatenation to product, so the solutions may be split among workers and
  their partial groups multiplied (`groupFold_append`); and it is one value
  for every enumeration when the values commute (`groupFold_perm`);
* a variable summed out leaves each instance with a multiplicity: folding each
  distinct instance once, raised to its count, folds the bag
  (`foldBag_eq_weighted`); when the aggregate is idempotent, as adding rows to
  a set space is, each distinct instance once suffices (`foldBag_eq_distinct`).

Controls: counting the answers after merging equal instances counts fewer
(`Controls.count_merged_differs`), while their maximum is unchanged
(`Controls.max_merged_same`); a fold that keeps the order of its values, as
taking the first answer does, depends on the enumeration
(`Controls.order_kept_depends_on_enumeration`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.JoinAggregation

open Mettapedia.Algebra.CollectionFold Boom

variable {α K M : Type*}

/-- **Any enumeration of the join folds to the same value** when the
generator's values commute. -/
theorem fold_perm [Monoid M] (generator : α → M)
    (commute : ∀ a b, Commute (generator a) (generator b))
    {enumeration source : List α} (perm : enumeration.Perm source) :
    foldList generator enumeration = foldList generator source := by
  unfold foldList
  exact (perm.map generator).prod_eq'
    (List.pairwise_map.mpr (List.pairwise_of_forall fun a b => commute a b))

section Group

variable [DecidableEq K]

/-- The fold of each key's group, as one fold into the product monoid. -/
def groupFold [Monoid M] (key : α → K) (value : α → M) (solutions : List α) : K → M :=
  foldList (fun a => Pi.mulSingle (key a) (value a)) solutions

/-- **A group's aggregate is the fold of the group.** -/
theorem groupFold_apply [Monoid M] (key : α → K) (value : α → M) (solutions : List α)
    (k : K) :
    groupFold key value solutions k = foldList value (solutions.filter fun a => key a = k) := by
  induction solutions with
  | nil => simp [groupFold, foldList]
  | cons a rest ih =>
      unfold groupFold foldList at ih ⊢
      rw [List.map_cons, List.prod_cons, Pi.mul_apply, ih]
      by_cases h : key a = k
      · subst h
        simp
      · rw [Pi.mulSingle_eq_of_ne (Ne.symm h), one_mul]
        simp [h]

/-- **Partial groups multiply**: the solutions may be split anywhere. -/
theorem groupFold_append [Monoid M] (key : α → K) (value : α → M) (left right : List α) :
    groupFold key value (left ++ right) = groupFold key value left * groupFold key value right :=
  foldList_append _ left right

/-- **Grouping gives one value for every enumeration** of a commutative
aggregate. -/
theorem groupFold_perm [CommMonoid M] (key : α → K) (value : α → M)
    {enumeration source : List α} (perm : enumeration.Perm source) :
    groupFold key value enumeration = groupFold key value source :=
  fold_perm _ (fun _ _ => Commute.all _ _) perm

end Group

/-- **Each distinct value once, raised to its count, folds the bag.** -/
theorem foldBag_eq_weighted [CommMonoid M] [DecidableEq α] (generator : α → M)
    (values : Multiset α) :
    foldBag generator values = ∏ a ∈ values.toFinset, generator a ^ values.count a := by
  unfold foldBag
  exact Finset.prod_multiset_map_count values generator

/-- **For an idempotent aggregate each distinct value once suffices.** -/
theorem foldBag_eq_distinct [CommMonoid M] [DecidableEq α] (generator : α → M)
    (idempotent : ∀ a, IsIdempotentElem (generator a)) (values : Multiset α) :
    foldBag generator values = ∏ a ∈ values.toFinset, generator a := by
  rw [← foldSet_toFinset generator idempotent]
  rfl

/-! ## Controls -/

namespace Controls

/-- One for each answer, added. -/
def one (_ : ℕ) : Multiplicative ℕ := Multiplicative.ofAdd 1

/-- **Merging equal answers changes a count**: two answers, one distinct. -/
theorem count_merged_differs :
    foldBag one ({7, 7} : Multiset ℕ) = Multiplicative.ofAdd 2 ∧
      ∏ a ∈ ({7, 7} : Multiset ℕ).toFinset, one a = Multiplicative.ofAdd 1 := by
  constructor
  · simp [foldBag, one, ← ofAdd_add]
  · simp [one]

/-- **Merging equal answers leaves a maximum.** -/
theorem max_merged_same :
    foldBag Mettapedia.Algebra.CollectionFold.Controls.MaxNat.of ({7, 7} : Multiset ℕ) =
      ∏ a ∈ ({7, 7} : Multiset ℕ).toFinset,
        Mettapedia.Algebra.CollectionFold.Controls.MaxNat.of a := by
  apply foldBag_eq_distinct
  intro value
  exact max_self (α := ℕ) value

/-- **A fold keeping the order depends on the enumeration.** -/
theorem order_kept_depends_on_enumeration :
    foldList FreeMonoid.of [1, 2] ≠ foldList FreeMonoid.of [2, 1] := by
  intro h
  have lists := congrArg FreeMonoid.toList h
  simp [foldList] at lists

end Controls

end Mettapedia.Machines.JoinAggregation
