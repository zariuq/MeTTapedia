import Mettapedia.Languages.MeTTa.StoreAndDemand.StoreEffects

/-!
# Retraction on a captured prefix

An occurrence contraction can carry its selected prefix through an append.
For an exact predicate removal in the current store, the predicate must still
select the same old occurrences and reject every new occurrence. These laws
state that comparison for ordered rows and for occurrence commits.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.StoreAndDemand.StoreEffects

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

/-- Contracting the captured prefix and keeping the suffix agrees with
removing all current matches precisely when the suffix has no match. -/
theorem removeAll_prefix_eq_current_iff {Row : Type*} (select : Row → Bool)
    (captured appended : List Row) :
    ((removeAll select captured).1 ++ appended, (removeAll select captured).2) =
      removeAll select (captured ++ appended) ↔ appended.any select = false := by
  constructor
  · intro same
    have survivors := congrArg Prod.fst same
    rw [show (removeAll select (captured ++ appended)).1 =
        (removeAll select captured).1 ++ (removeAll select appended).1 by
      simp [removeAll, List.filter_append]] at survivors
    exact (removeAll_false_iff_unchanged select appended).mpr
      (List.append_cancel_left survivors).symm
  · intro none
    have unchanged := (removeAll_false_iff_unchanged select appended).mp none
    apply Prod.ext
    · simpa only [removeAll, List.filter_append] using
        congrArg ((removeAll select captured).1 ++ ·) unchanged.symm
    · simp [removeAll, List.any_append, none]

/-- The exact revalidation condition for selected old occurrences, allowing
both the labels and the selector to depend on the entry or publication view.
The prefix and appended suffix have disjoint occurrence identities. -/
theorem captured_retraction_eq_current_iff {Occurrence Label : Type*}
    [DecidableEq Occurrence] (entryLabel publishLabel : Occurrence → Label)
    (entrySelect publishSelect : Label → Bool)
    (captured appended : Finset Occurrence) (apart : Disjoint captured appended) :
    appended ∪ fire captured (selectedRemoval entryLabel entrySelect captured) =
      fire (captured ∪ appended)
        (selectedRemoval publishLabel publishSelect (captured ∪ appended)) ↔
      (∀ o ∈ captured, entrySelect (entryLabel o) = publishSelect (publishLabel o)) ∧
      (∀ o ∈ appended, publishSelect (publishLabel o) = false) := by
  rw [selectedRemoval_fire, selectedRemoval_fire]
  constructor
  · intro same
    refine ⟨fun o old => ?_, fun o new => ?_⟩
    · have notNew := Finset.disjoint_left.mp apart old
      have stillSelected :
          entrySelect (entryLabel o) = false ↔ publishSelect (publishLabel o) = false := by
        simpa [Finset.mem_union, Finset.mem_filter, old, notNew] using
          Finset.ext_iff.mp same o
      cases before : entrySelect (entryLabel o) <;>
        cases after : publishSelect (publishLabel o) <;> simp_all
    · simpa [Finset.mem_union, Finset.mem_filter, new] using
        Finset.ext_iff.mp same o
  · rintro ⟨agrees, none⟩
    ext o
    by_cases new : o ∈ appended
    · simp [Finset.mem_union, Finset.mem_filter, new, none o new]
    · by_cases old : o ∈ captured
      · simp [Finset.mem_union, Finset.mem_filter, new, old, agrees o old]
      · simp [Finset.mem_union, Finset.mem_filter, new, old]

/-- A captured contraction retains a later matching copy. -/
example : (((removeAll (· == 1) ([1, 2] : List Nat)).1 ++ [1]), true) ≠
    removeAll (· == 1) [1, 2, 1] := by decide

/-- A later nonmatch is retained by both operations. -/
example : (((removeAll (· == 1) ([1, 2] : List Nat)).1 ++ [3]), true) =
    removeAll (· == 1) [1, 2, 3] := by decide

#print axioms removeAll_prefix_eq_current_iff
#print axioms captured_retraction_eq_current_iff

end Mettapedia.Languages.MeTTa.StoreAndDemand.StoreEffects

