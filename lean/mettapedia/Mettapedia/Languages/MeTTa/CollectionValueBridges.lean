import Mettapedia.Algebra.Collections.CanonicalForm
import Mettapedia.Languages.MeTTa.SpaceValues

/-!
# Collection values and the values of spaces

Bridges between the collection values of `Algebra.Collections.CanonicalForm`
and the operations on values of `Languages.MeTTa.SpaceValues`.

* **`unique-atom` is the insertion-ordered set.** Thawing a list into an
  ordered set keeps first occurrences in order: it is `dedupFirst`, the normal
  form of the idempotent, non-commutative kind (`uniqueAtom_eq_dedupFirst`).
* **Displaying answers as a bag literal is a function of the answers.** Every
  enumeration of one bag of answers, written as a flat bag literal, has the
  canonical form of the sorted answers (`canonical_enumeration`), and two
  enumerations give equal bag literals exactly when they enumerate the same
  answers (`conv_enumerations_iff`).
* **The insertion-ordered display is not.** Two enumerations of one bag of
  answers have different first-occurrence lists
  (`Controls.first_occurrences_depend_on_enumeration`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.CollectionValueBridges

open Mettapedia.Algebra.Collections.CanonicalForm
open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra
open Mettapedia.Languages.MeTTa.SpaceKinds
open Mettapedia.Languages.MeTTa.SpaceValues

variable {α : Type*} [DecidableEq α]

theorem foldl_orderedInsert_eq_dedupFirst (values : List α) :
    ∀ start : List α, start.Nodup →
      values.foldl orderedInsert start = dedupFirst (start ++ values) := by
  induction values with
  | nil => intro start nodup; simp [dedupFirst_of_nodup nodup]
  | cons head tail ih =>
      intro start nodup
      rw [List.foldl_cons, ih _ (nodup_orderedInsert nodup head)]
      by_cases present : head ∈ start
      · rw [show orderedInsert start head = start by simp [orderedInsert, present],
          dedupFirst_append_cons_of_mem present]
      · rw [show orderedInsert start head = start ++ [head] by simp [orderedInsert, present],
          List.append_assoc, List.singleton_append]

/-- **`unique-atom` keeps first occurrences, in order**: it is the normal form
of the insertion-ordered set. -/
theorem uniqueAtom_eq_dedupFirst (values : List α) : uniqueAtom values = dedupFirst values := by
  rw [uniqueAtom, thaw_orderedSet_val, foldl_orderedInsert_eq_dedupFirst values [] List.nodup_nil,
    List.nil_append]

section Display

variable {K : Type*} [LinearOrder K] {X : Type*} [LinearOrder X]

/-- **Every enumeration of the answers, as a bag literal, has the canonical
form of the sorted answers.** -/
theorem canonical_enumeration (laws : K → KindLaws) {k : K} (bag : laws k = KindLaws.bag)
    {listed : List X} {answers : Ans ℕ X} (enumerates : Enumerates listed answers) :
    canonical laws (.node k (listed.map .leaf)) =
      .node k (((collapseBag answers).sort (· ≤ ·)).map .leaf) := by
  rw [canonical_bag_leaves laws bag, ← sort_enumeration enumerates,
    List.mergeSort_eq_insertionSort]

/-- Two enumerations give equal bag literals exactly when they enumerate the
same answers. -/
theorem conv_enumerations_iff (laws : K → KindLaws) {k : K} (bag : laws k = KindLaws.bag)
    (first second : List X) :
    Conv laws (.node k (first.map .leaf)) (.node k (second.map .leaf)) ↔
      Multiset.toFinsupp (first : Multiset X) = Multiset.toFinsupp (second : Multiset X) := by
  rw [conv_bag_leaves_iff laws bag, (Multiset.toFinsupp (α := X)).injective.eq_iff]

end Display

namespace Controls

/-- Two enumerations of the answers `{1, 2}`: their first-occurrence lists
differ, while their bag literals are one value. -/
theorem first_occurrences_depend_on_enumeration :
    uniqueAtom ([1, 2] : List ℕ) ≠ uniqueAtom [2, 1] ∧
      Enumerates ([1, 2] : List ℕ) (Multiset.toFinsupp ({1, 2} : Multiset ℕ)) ∧
      Enumerates ([2, 1] : List ℕ) (Multiset.toFinsupp ({1, 2} : Multiset ℕ)) := by
  refine ⟨?_, rfl, ?_⟩
  · rw [uniqueAtom_eq_dedupFirst, uniqueAtom_eq_dedupFirst]
    decide
  · show Multiset.toFinsupp (([2, 1] : List ℕ) : Multiset ℕ) =
      Multiset.toFinsupp ({1, 2} : Multiset ℕ)
    congr 1
    exact Multiset.coe_eq_coe.mpr (List.Perm.swap 1 2 [])

end Controls

end Mettapedia.Languages.MeTTa.CollectionValueBridges
