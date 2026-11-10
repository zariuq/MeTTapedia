import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.OrderedStore
import Mettapedia.Languages.MeTTa.StoreAndDemand.StoreEffects

/-!
# List-store operations interpreted as admitted transform effects

The source operations are the independent ordered-list contracts in
StoreAndDemand. The target retains unique occurrence identities and arbitrary
ambient frame knowledge. Decoding forgets identities but retains order and
equal payload occurrences. Matching is a separate completed selection service;
these laws do not replace scoped unification by syntactic equality.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.StoreOperations

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Interface
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open StoreAndDemand

universe uO uT uH uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) (a : Obj) {O : Type uOcc} [DecidableEq O]
  (label : O → Tm a)

def appendRequest (made : List O) : OrderedStore.Publication (Tm a) O :=
  ⟨⟨[], [], made⟩, []⟩

def removeRequest (select : Tm a → Bool) (rows : List O) :
    OrderedStore.Publication (Tm a) O :=
  let chosen := rows.filter fun occurrence => select (label occurrence)
  ⟨⟨chosen, [], []⟩, [⟨select, chosen.toFinset⟩]⟩

def readRequest (select : Tm a → Bool) (rows : List O) :
    OrderedStore.Publication (Tm a) O :=
  let chosen := rows.filter fun occurrence => select (label occurrence)
  ⟨⟨[], chosen, []⟩, [⟨select, chosen.toFinset⟩]⟩

theorem census_holds (select : Tm a → Bool) (rows : List O) :
    (PredicateQuery.mk select (rows.filter (fun occurrence => select (label occurrence))).toFinset).Holds
      label rows.toFinset := by
  ext occurrence
  simp [regionOf]

theorem append_admits_exact (knowledge : EquationStore (Tm a)) (rows made : List O) :
    (OrderedStore.step X a label).Admits (s := (knowledge, rows)) (appendRequest (a := a) made) ↔
      rows.Nodup ∧ made.Nodup ∧ Disjoint made.toFinset rows.toFinset ∧ X.Solvable knowledge := by
  constructor
  · rintro ⟨shape, enabled, consistent⟩
    exact ⟨shape.1, shape.2.2, enabled.fresh, consistent⟩
  · rintro ⟨unique, madeUnique, fresh, consistent⟩
    refine ⟨⟨unique, List.nodup_nil, madeUnique⟩, ?_, consistent⟩
    refine ⟨by simp [appendRequest, OrderedStore.Publication.commit, Selection.commit],
      by simp [appendRequest, OrderedStore.Publication.commit, Selection.commit],
      by simp [appendRequest, OrderedStore.Publication.commit, Selection.commit], fresh, ?_⟩
    intro query member
    simp [appendRequest, OrderedStore.Publication.commit] at member

theorem remove_admits_exact (select : Tm a → Bool)
    (knowledge : EquationStore (Tm a)) (rows : List O) :
    (OrderedStore.step X a label).Admits (s := (knowledge, rows)) (removeRequest (a := a) label select rows) ↔
      rows.Nodup ∧ X.Solvable knowledge := by
  constructor
  · rintro ⟨shape, _, consistent⟩
    exact ⟨shape.1, consistent⟩
  · rintro ⟨unique, consistent⟩
    refine ⟨⟨unique, unique.filter _, List.nodup_nil⟩, ?_, consistent⟩
    refine ⟨?_, by simp [removeRequest, OrderedStore.Publication.commit, Selection.commit],
      by simp [removeRequest, OrderedStore.Publication.commit, Selection.commit],
      by simp [removeRequest, OrderedStore.Publication.commit, Selection.commit], ?_⟩
    · intro occurrence member
      simp only [removeRequest, OrderedStore.Publication.commit, Selection.commit,
        List.mem_toFinset, List.mem_filter] at member
      exact List.mem_toFinset.mpr member.1
    · intro query member
      have same : query = ⟨select, (rows.filter (fun occurrence => select (label occurrence))).toFinset⟩ := by
        simpa [removeRequest, OrderedStore.Publication.commit] using member
      subst query
      exact census_holds (a := a) label select rows

theorem read_admits_exact (select : Tm a → Bool)
    (knowledge : EquationStore (Tm a)) (rows : List O) :
    (OrderedStore.step X a label).Admits (s := (knowledge, rows)) (readRequest (a := a) label select rows) ↔
      rows.Nodup ∧ X.Solvable knowledge := by
  constructor
  · rintro ⟨shape, _, consistent⟩
    exact ⟨shape.1, consistent⟩
  · rintro ⟨unique, consistent⟩
    refine ⟨⟨unique, List.nodup_nil, List.nodup_nil⟩, ?_, consistent⟩
    refine ⟨by simp [readRequest, OrderedStore.Publication.commit, Selection.commit], ?_,
      by simp [readRequest, OrderedStore.Publication.commit, Selection.commit],
      by simp [readRequest, OrderedStore.Publication.commit, Selection.commit], ?_⟩
    · intro occurrence member
      simp only [readRequest, OrderedStore.Publication.commit, Selection.commit,
        List.mem_toFinset, List.mem_filter] at member
      exact List.mem_toFinset.mpr member.1
    · intro query member
      have same : query = ⟨select, (rows.filter (fun occurrence => select (label occurrence))).toFinset⟩ := by
        simpa [readRequest, OrderedStore.Publication.commit] using member
      subst query
      exact census_holds (a := a) label select rows

/-- Appending one payload, including a comma-shaped payload, is one make.
The target's occurrence allocation is independent of the source list append. -/
theorem add_correspondence (knowledge : EquationStore (Tm a)) (rows : List O) (fresh : O)
    (admitted : (OrderedStore.step X a label).Admits (s := (knowledge, rows))
      (appendRequest (a := a) [fresh])) :
    StoreEffects.add (rows.map label) (label fresh) =
      (((OrderedStore.step X a label).result (appendRequest (a := a) [fresh]) admitted).2.map label) := by
  rw [OrderedStore.result_rows]
  simp [appendRequest, OrderedStore.append_only, StoreEffects.add]

theorem route_correspondence (knowledge : EquationStore (Tm a)) (rows made : List O)
    (admitted : (OrderedStore.step X a label).Admits (s := (knowledge, rows))
      (appendRequest (a := a) made)) :
    StoreEffects.route (rows.map label) (made.map label) =
      ((((OrderedStore.step X a label).result (appendRequest (a := a) made) admitted).2.map label),
        made.length) := by
  rw [OrderedStore.result_rows]
  simp [appendRequest, OrderedStore.append_only, StoreEffects.route]

omit [DecidableEq O] in
private theorem filter_nonempty (select : O → Bool) (rows : List O) :
    rows.any select = !(rows.filter select).isEmpty := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      cases selected : select row <;> simp [selected, ih]

/-- Complete removal preserves survivor order and reports whether at least
one occurrence was selected. Distinct matching bindings never get conjoined. -/
theorem remove_all_correspondence (select : Tm a → Bool)
    (knowledge : EquationStore (Tm a)) (rows : List O)
    (admitted : (OrderedStore.step X a label).Admits (s := (knowledge, rows))
      (removeRequest (a := a) label select rows)) :
    StoreEffects.removeAll select (rows.map label) =
      ((((OrderedStore.step X a label).result (removeRequest (a := a) label select rows) admitted).2.map label),
        !(removeRequest (a := a) label select rows).selection.taken.isEmpty) := by
  rw [OrderedStore.result_rows]
  simp only [removeRequest, OrderedStore.selected_removal, StoreEffects.removeAll,
    List.filter_map, List.any_map]
  exact Prod.ext rfl (filter_nonempty _ _)

theorem read_store_unchanged (select : Tm a → Bool)
    (knowledge : EquationStore (Tm a)) (rows : List O)
    (admitted : (OrderedStore.step X a label).Admits (s := (knowledge, rows))
      (readRequest (a := a) label select rows)) :
    (OrderedStore.step X a label).result (readRequest (a := a) label select rows) admitted = (knowledge, rows) := by
  apply Prod.ext
  · exact OrderedStore.result_knowledge X a label admitted
  · rw [OrderedStore.result_rows]
    exact OrderedStore.reads_only _ _

/-- The answer observation survives even though read-only publication is
identity on the store. This is ordered list equality, not set equality. -/
theorem read_answers_exact (select : Tm a → Bool) (rows : List O) :
    (readRequest (a := a) label select rows).selection.read.map label = (rows.map label).filter select := by
  simp [readRequest, List.filter_map, Function.comp_def]

/-- Counts concern physical occurrences, including equal payload copies. -/
theorem read_count_exact (select : Tm a → Bool) (rows : List O) (unique : rows.Nodup) :
    (regionOf label rows.toFinset select).card = ((rows.map label).filter select).length := by
  have same := census_holds (a := a) label select rows
  change regionOf label rows.toFinset select = _ at same
  rw [same, List.toFinset_card_of_nodup (unique.filter _)]
  simp [List.filter_map, Function.comp_def]

end Mettapedia.Languages.MeTTa.ContextualTransform.StoreOperations
