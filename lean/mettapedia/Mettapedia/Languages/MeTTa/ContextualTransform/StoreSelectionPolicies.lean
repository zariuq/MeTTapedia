import Mettapedia.Languages.MeTTa.ContextualTransform.StoreOperations

/-!
# First-occurrence removal and complete negative observations

First selection is a source ordering obligation. Once that occurrence has
been selected, the target publishes its take. Absence is different: it depends
on the complete selected region, so a newly added matching occurrence changes
admission even when it overlaps no positive take.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.StoreSelectionPolicies

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Interface
open StoreAndDemand StoreOperations

universe uO uT uH uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) (a : Obj) {O : Type uOcc} [DecidableEq O]
  (label : O → Tm a)

def takeRequest (chosen : O) : OrderedStore.Publication (Tm a) O :=
  ⟨⟨[chosen], [], []⟩, []⟩

theorem take_admits_exact (knowledge : EquationStore (Tm a)) (rows : List O) (chosen : O) :
    (OrderedStore.step X a label).Admits (s := (knowledge, rows)) (takeRequest (a := a) chosen) ↔
      rows.Nodup ∧ chosen ∈ rows ∧ X.Solvable knowledge := by
  constructor
  · rintro ⟨shape, enabled, consistent⟩
    refine ⟨shape.1, ?_, consistent⟩
    exact List.mem_toFinset.mp (enabled.taken_subset (by simp [takeRequest,
      OrderedStore.Publication.commit, Selection.commit]))
  · rintro ⟨unique, present, consistent⟩
    refine ⟨⟨unique, by simp [takeRequest], List.nodup_nil⟩, ?_, consistent⟩
    refine ⟨?_, by simp [takeRequest, OrderedStore.Publication.commit, Selection.commit],
      by simp [takeRequest, OrderedStore.Publication.commit, Selection.commit],
      by simp [takeRequest, OrderedStore.Publication.commit, Selection.commit], ?_⟩
    · simpa [takeRequest, OrderedStore.Publication.commit, Selection.commit] using present
    · intro query member
      simp [takeRequest, OrderedStore.Publication.commit] at member

theorem contraction_at_occurrence (before after : List O) (chosen : O)
    (unique : (before ++ chosen :: after).Nodup) :
    OrderedStore.publish (before ++ chosen :: after) ⟨[chosen], [], []⟩ = before ++ after := by
  have absent := (List.nodup_cons.mp (List.nodup_middle.mp unique)).1
  have unchanged : OrderedStore.survivors (before ++ after) [chosen] = before ++ after := by
    apply List.filter_eq_self.mpr
    intro occurrence member
    simp only [List.mem_singleton, decide_eq_true_eq]
    intro same
    subst occurrence
    exact absent member
  calc
    OrderedStore.publish (before ++ chosen :: after) ⟨[chosen], [], []⟩ =
        OrderedStore.survivors (before ++ after) [chosen] := by
      simp [OrderedStore.publish, OrderedStore.survivors, List.filter_append]
    _ = before ++ after := unchanged

/-- First-match source deletion corresponds to one admitted take, retaining
every later equal payload occurrence and the original survivor order. -/
theorem remove_one_correspondence (select : Tm a → Bool)
    (knowledge : EquationStore (Tm a)) (before after : List O) (chosen : O)
    (unique : (before ++ chosen :: after).Nodup)
    (noEarlier : (before.map label).any select = false) (matched : select (label chosen) = true)
    (admitted : (OrderedStore.step X a label).Admits (s := (knowledge, before ++ chosen :: after))
      (takeRequest (a := a) chosen)) :
    StoreEffects.removeOne select ((before ++ chosen :: after).map label) =
      (((OrderedStore.step X a label).result (takeRequest (a := a) chosen) admitted).2.map label) := by
  rw [OrderedStore.result_rows]
  rw [show (takeRequest (a := a) chosen).selection = ⟨[chosen], [], []⟩ from rfl]
  rw [contraction_at_occurrence before after chosen unique]
  simp only [List.map_append, List.map_cons]
  exact StoreEffects.removeOne_at_first select _ _ _ noEarlier matched

def absentRequest (select : Tm a → Bool) : OrderedStore.Publication (Tm a) O :=
  ⟨⟨[], [], []⟩, [⟨select, ∅⟩]⟩

theorem absence_observation_exact (select : Tm a → Bool) (rows : List O) :
    (PredicateQuery.mk select (∅ : Finset O)).Holds label rows.toFinset ↔
      (rows.map label).any select = false := by
  simp [PredicateQuery.Holds, regionOf, Finset.filter_eq_empty_iff, List.any_eq_false]

theorem absence_admits_exact (select : Tm a → Bool)
    (knowledge : EquationStore (Tm a)) (rows : List O) :
    (OrderedStore.step X a label).Admits (s := (knowledge, rows)) (absentRequest (a := a) select) ↔
      rows.Nodup ∧ X.Solvable knowledge ∧ (rows.map label).any select = false := by
  constructor
  · rintro ⟨shape, enabled, consistent⟩
    refine ⟨shape.1, consistent, (absence_observation_exact a label select rows).mp ?_⟩
    exact enabled.queries_hold _ (by simp [absentRequest, OrderedStore.Publication.commit])
  · rintro ⟨unique, consistent, absent⟩
    refine ⟨⟨unique, List.nodup_nil, List.nodup_nil⟩, ?_, consistent⟩
    refine ⟨by simp [absentRequest, OrderedStore.Publication.commit, Selection.commit],
      by simp [absentRequest, OrderedStore.Publication.commit, Selection.commit],
      by simp [absentRequest, OrderedStore.Publication.commit, Selection.commit],
      by simp [absentRequest, OrderedStore.Publication.commit, Selection.commit], ?_⟩
    intro query member
    have same : query = ⟨select, ∅⟩ := by
      simpa [absentRequest, OrderedStore.Publication.commit] using member
    subst query
    exact (absence_observation_exact a label select rows).mpr absent

/-- A later matching addition invalidates an absence observation without
needing to consume any of its positive footprint. -/
theorem matching_addition_rejects_absence (select : Tm a → Bool)
    (knowledge : EquationStore (Tm a)) (rows : List O) (added : O)
    (matched : select (label added) = true) :
    ¬(OrderedStore.step X a label).Admits (s := (knowledge, rows ++ [added]))
      (absentRequest (a := a) select) := by
  intro admitted
  have absent := ((absence_admits_exact X a label select knowledge _).mp admitted).2.2
  simp [matched] at absent

theorem uniqueness_observation_exact (select : Tm a → Bool) (rows : List O) :
    (readRequest (a := a) label select rows).selection.read.length = 1 ↔
      ((rows.map label).filter select).length = 1 := by
  have counted := congrArg List.length (read_answers_exact a label select rows)
  exact Iff.of_eq (by simpa only [List.length_map] using congrArg (· = 1) counted)

end Mettapedia.Languages.MeTTa.ContextualTransform.StoreSelectionPolicies
