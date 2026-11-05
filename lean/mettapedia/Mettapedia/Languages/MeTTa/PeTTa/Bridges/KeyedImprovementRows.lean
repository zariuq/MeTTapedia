import Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementSource
import Mettapedia.Machines.OrderedKeyedRows

/-!
# Ordered distance rows refine the logical keyed store

The distance space holds literal natural key/value rows. Its exact key fibres
must represent a partial map: duplicate occurrences are not quotiented away.
Actual PeTTa matching recovers those fibres, and the completed source update
preserves the representation and strict improvement flag. Other spaces and
state cells remain untouched. This is a source-level representation bridge,
not an atomic native publication or whole-frontier scheduling theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementRows

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics NamedSpaces KeyedImprovementSource
open FlatQueryRelationCompilation (sourceScan)
open Mettapedia.Machines.KeyedImprovement

def encode (head : String) (entry : Nat × Nat) : Atom := row head (number entry.1) (number entry.2)
def encodeRows (head : String) (rows : List (Nat × Nat)) : List Atom := rows.map (encode head)

theorem encode_injective (head : String) : Function.Injective (encode head) := by
  intro first second same
  rcases first with ⟨key, value⟩
  rcases second with ⟨other, held⟩
  simpa [encode, row, number] using same

theorem encoded_match (names : Names) (head : String) (ordinary : head ≠ "cons")
    (target : Handle) (key candidate : Nat) (entry : Nat × Nat) :
    matchValue (bindings names target key candidate) (pattern names head) (encode head entry) =
      if entry.1 = key then some ((names.previous, number entry.2) :: bindings names target key candidate) else none := by
  have apart := names.distinct
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at apart
  have keyRead : Subst.lookup (bindings names target key candidate) names.vertex = some (number key) := by
    simp [bindings, Subst.lookup, Ne.symm apart.2.1.1]
  have oldFresh : Subst.lookup (bindings names target key candidate) names.previous = none := by
    simp_all [bindings, Subst.lookup]
  unfold pattern encode row
  rw [matchValue_expression_of_not_cons _ _ _ (by
    intro first rest same
    exact ordinary (by simpa using (List.cons.inj same).1))]
  by_cases same : entry.1 = key <;>
    simp [matchValue.matchValues, matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
      keyRead, oldFresh, number, same]

theorem scanned_values (names : Names) (head : String) (ordinary : head ≠ "cons")
    (target : Handle) (key candidate : Nat) (rows : List (Nat × Nat)) (start : Nat) :
    (sourceScan (bindings names target key candidate) (pattern names head) start (encodeRows head rows)).map
      (fun result => applySubst result.2 (.var names.previous)) = (OrderedRows.fibre rows key).map number := by
  induction rows generalizing start with
  | nil => rfl
  | cons entry rows ih =>
      simp only [encodeRows, List.map_cons, sourceScan, encoded_match names head ordinary,
        List.map_append, OrderedRows.fibre_cons]
      by_cases same : entry.1 = key <;>
        simp [same, applySubst, Subst.lookup]
      all_goals exact ih (start + 1)

theorem values_exact (names : Names) (head : String) (ordinary : head ≠ "cons")
    (target : Handle) (key candidate : Nat) (rows : List (Nat × Nat)) :
    values names head (bindings names target key candidate) (encodeRows head rows) = (OrderedRows.fibre rows key).map number :=
  scanned_values names head ordinary target key candidate rows 0

theorem encoded_rows_ready (names : Names) (head : String) (rows : List (Nat × Nat)) :
    ClosedQueryAdmission.rowsReady (pattern names head) (encodeRows head rows) = true := by
  apply ClosedQueryAdmission.ground_rows_are_ready
  intro atom member
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
  rfl

theorem encoded_removal (head : String) (rows : List (Nat × Nat)) (entry : Nat × Nat) :
    (encodeRows head rows).filter (· != encode head entry) = encodeRows head (rows.filter (· != entry)) := by
  rw [encodeRows, List.filter_map]
  congr 1
  apply List.filter_congr
  intro other _
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, bne_iff_ne]
  exact not_congr (encode_injective head).eq_iff

theorem updated_rows_exact (head : String) (rows : List (Nat × Nat)) (key candidate : Nat) (old : Option Nat) :
    updatedRows head key candidate old (encodeRows head rows) =
      encodeRows head (OrderedRows.publish rows key candidate old).1 := by
  cases old with
  | none => simp [updatedRows, OrderedRows.publish, encodeRows, encode]
  | some previous =>
      by_cases better : candidate < previous
      · simp only [updatedRows, OrderedRows.publish, if_pos better]
        rw [show row head (number key) (number previous) = encode head (key, previous) from rfl, encoded_removal]
        simp [encodeRows, encode]
      · simp [updatedRows, OrderedRows.publish, better]

theorem write_complete (before : Effects.State) (target : Handle) (head : String) (key candidate : Nat)
    (old : Option Nat) (rows : List Atom) (snapshot : before.read target = some rows) :
    ∃ after answers, write before target head key candidate old = some (after, answers) := by
  cases old with
  | none =>
      obtain ⟨after, inserted⟩ := Effects.insert_exists_of_read_some snapshot (row head (number key) (number candidate))
      exact ⟨after, [number key], by simp [write, inserted]⟩
  | some previous =>
      by_cases better : candidate < previous
      · obtain ⟨middle, erased⟩ := Effects.erase_exists_of_read_some snapshot (row head (number key) (number previous))
        obtain ⟨_, _, middleRead⟩ := Effects.erase_reads_back erased
        obtain ⟨after, inserted⟩ := Effects.insert_exists_of_read_some middleRead (row head (number key) (number candidate))
        exact ⟨after, [number key], by simp [write, better, erased, inserted]⟩
      · exact ⟨before, [], by simp [write, better]⟩

def Represents (head : String) (state : Effects.State) (target : Handle)
    (store : Mettapedia.Machines.KeyedImprovement.Store Nat Nat) : Prop :=
  ∃ rows, state.read target = some (encodeRows head rows) ∧ OrderedRows.Represents rows store

theorem run_total_refines (names : Names) (head : String)
    (ordinary : head ∉ ["=", ":", ",", "cons"]) (target : Handle) (key candidate : Nat)
    (before : Effects.State) (store : Mettapedia.Machines.KeyedImprovement.Store Nat Nat)
    (represented : Represents head before target store) :
    ∃ after answers,
      KeyedImprovementSource.run names head target key candidate before = some (after, answers) ∧
      Represents head after target (Mettapedia.Machines.KeyedImprovement.improve store key candidate).1 ∧
      answers = (if (Mettapedia.Machines.KeyedImprovement.improve store key candidate).2 then [number key] else []) ∧
      (∀ other, other ≠ target → after.read other = before.read other) ∧ after.cells = before.cells := by
  obtain ⟨rows, snapshot, rowRepresentation⟩ := represented
  have notCons : head ≠ "cons" := by intro same; simp [same] at ordinary
  have queryValues := values_exact names head notCons target key candidate rows
  rw [rowRepresentation key] at queryValues
  have decoded : decodeFibre (values names head (bindings names target key candidate) (encodeRows head rows)) = some (store key) := by
    rw [queryValues]
    cases store key <;> rfl
  obtain ⟨after, answers, completed⟩ := write_complete before target head key candidate (store key) _ snapshot
  have observation := write_observation before after target head notCons key candidate (store key) answers _ snapshot completed
  obtain ⟨preserved, _⟩ := OrderedRows.publish_refines rowRepresentation key candidate
  refine ⟨after, answers, ?_, ⟨(OrderedRows.publish rows key candidate (store key)).1, ?_, preserved⟩, ?_, observation.2.2⟩
  · simp only [KeyedImprovementSource.run, if_neg ordinary, snapshot, bind, Option.bind,
      encoded_rows_ready, ↓reduceIte, decoded, completed]
  · simpa only [updated_rows_exact] using observation.1
  · have flag := observation.2.1
    cases held : store key with
    | none => simpa [improve, held] using flag
    | some previous =>
        by_cases better : candidate < previous <;> simpa [improve, held, better] using flag

theorem source_update_refines (names : Names) (head : String)
    (ordinary : head ∉ ["=", ":", ",", "cons"]) (program : Program) (target : Handle) (key candidate : Nat)
    (before : Effects.State) (store : Mettapedia.Machines.KeyedImprovement.Store Nat Nat)
    (represented : Represents head before target store) :
    ∃ after answers,
      Eval.Returns program (bindings names target key candidate) before (source names head) after answers ∧
      Represents head after target (Mettapedia.Machines.KeyedImprovement.improve store key candidate).1 ∧
      answers = (if (Mettapedia.Machines.KeyedImprovement.improve store key candidate).2 then [number key] else []) := by
  obtain ⟨after, answers, completed, preserved, flags, _⟩ := run_total_refines names head ordinary target key candidate before store represented
  exact ⟨after, answers, returns names head program target key candidate before after answers completed, preserved, flags⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementRows
