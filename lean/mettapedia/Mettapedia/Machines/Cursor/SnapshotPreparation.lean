import Mettapedia.Machines.Cursor.FilteredSnapshot

/-!
# Snapshot opening belongs in the demand cost account

An eager reader actually gathers and decodes every accepted row at opening.
The retained reader instead holds the existing array. They implement the
same ordered sequence protocol, but have different preparation costs even
when a consumer requests no answers. Density does not change that contract.

These are counts of inspected cells and decoder calls for the constructed
algorithms. Predicate costs, native retention, allocation, array construction
and elapsed time are not identified with these counts. An already available
array is a premise of the retained route, not a claim that converting another
representation is free. The pure meters observe work; they are not an extra
matching pass that a runtime is required to execute.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.SnapshotPreparation

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial

variable {Row Item : Type}

structure Gathered (Item : Type) where
  values : List Item
  inspected : Nat
  decoded : Nat

/-- An independent eager implementation, including preparation of the tail
even when the first row already matches. -/
def gather (accept : Row → Bool) (decode : Row → Item) : List Row → Gathered Item
  | [] => ⟨[], 0, 0⟩
  | row :: rows =>
      let later := gather accept decode rows
      if accept row then
        ⟨decode row :: later.values, 1 + later.inspected, 1 + later.decoded⟩
      else
        ⟨later.values, 1 + later.inspected, later.decoded⟩

theorem gather_meaning (accept : Row → Bool) (decode : Row → Item) (rows : List Row) :
    (gather accept decode rows).values = rows.filterMap
      (fun row => if accept row then some (decode row) else none) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      by_cases accepted : accept row = true
      · simp [gather, accepted, ih]
      · simp [gather, accepted, ih]

theorem gather_inspections (accept : Row → Bool) (decode : Row → Item) (rows : List Row) :
    (gather accept decode rows).inspected = rows.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      by_cases accepted : accept row = true <;> simp [gather, accepted, ih, Nat.add_comm]

theorem gather_decodings (accept : Row → Bool) (decode : Row → Item) (rows : List Row) :
    (gather accept decode rows).decoded = (gather accept decode rows).values.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      by_cases accepted : accept row = true <;> simp [gather, accepted, ih, Nat.add_comm]

variable {Return : Unit → Unit → Type}

/-- All row inspections occur at opening, before the first client inspection.
Later pulls consume the already decoded list without reading backing rows. -/
def preparedRun (accept : Row → Bool) (decode : Row → Item)
    (C : Client (P := Sequence.protocol Item) (Return := Return))
    (fuel : Nat) (control : C.V () ()) (storage : Array Row) :
    Nat × Outcome (Sequence.tails Item) C () :=
  let prepared := gather accept decode storage.toList
  (prepared.inspected,
    (advance (Sequence.tails Item) C (fun _ _ => 0) fuel
      ⟨(), control, prepared.values⟩).2)

def retainedRun (accept : Row → Bool) (decode : Row → Item)
    (C : Client (P := Sequence.protocol Item) (Return := Return))
    (fuel : Nat) (control : C.V () ()) (storage : Array Row) :
    Nat × Outcome (FilteredSnapshot.provider accept decode) C () :=
  advance (FilteredSnapshot.provider accept decode) C
    (FilteredSnapshot.inspections accept decode) fuel
    ⟨(), control, FilteredSnapshot.start storage⟩

theorem prepared_inspections_exact (accept : Row → Bool) (decode : Row → Item)
    (C : Client (P := Sequence.protocol Item) (Return := Return))
    (fuel : Nat) (control : C.V () ()) (storage : Array Row) :
    (preparedRun accept decode C fuel control storage).1 = storage.size := by
  simp [preparedRun, gather_inspections]

/-- The preparation choice preserves the full adaptive observation and live
residual, not only the completed answer bag. The common budget counts client
inspections, not an equal amount of internal row work. -/
theorem representation_observation (accept : Row → Bool) (decode : Row → Item)
    (C : Client (P := Sequence.protocol Item) (Return := Return))
    (fuel : Nat) (control : C.V () ()) (storage : Array Row) :
    (FilteredSnapshot.refinement accept decode).outcome C
        (retainedRun accept decode C fuel control storage).2 =
      (preparedRun accept decode C fuel control storage).2 := by
  simpa only [retainedRun, preparedRun, gather_meaning, Hom.packet,
    FilteredSnapshot.refinement, FilteredSnapshot.meaning_open] using
    Hom.advance C (FilteredSnapshot.refinement accept decode)
      (FilteredSnapshot.inspections accept decode) (fun _ _ => 0) fuel
      ⟨(), control, FilteredSnapshot.start storage⟩

/-- Including opening, retained traversal never inspects more backing rows
than eager gathering in this cell-inspection model. This does not compare
per-call dispatch overhead, vectorization, cache behavior or instructions. -/
theorem retained_inspections_le_prepared (accept : Row → Bool) (decode : Row → Item)
    (C : Client (P := Sequence.protocol Item) (Return := Return))
    (fuel : Nat) (control : C.V () ()) (storage : Array Row) :
    (retainedRun accept decode C fuel control storage).1 ≤
      (preparedRun accept decode C fuel control storage).1 := by
  rw [prepared_inspections_exact]
  exact FilteredSnapshot.advance_inspections_le accept decode C fuel
    ⟨(), control, FilteredSnapshot.start storage⟩

/-- No client inspection performs no deferred row work. In contrast the
eager route still pays its whole opening cost at this same boundary. -/
theorem zero_demand_costs (accept : Row → Bool) (decode : Row → Item)
    (C : Client (P := Sequence.protocol Item) (Return := Return))
    (control : C.V () ()) (storage : Array Row) :
    (retainedRun accept decode C 0 control storage).1 = 0 ∧
      (preparedRun accept decode C 0 control storage).1 = storage.size := by
  exact ⟨rfl, prepared_inspections_exact accept decode C 0 control storage⟩

/-- No row-count threshold supplies a constant startup-work bound. Even a
consumer which never polls pays for arbitrarily large eager preparation. -/
theorem preparation_exceeds_any_bound (accept : Row → Bool) (decode : Row → Item)
    (C : Client (P := Sequence.protocol Item) (Return := Return))
    (fuel : Nat) (control : C.V () ()) (row : Row) (bound : Nat) :
    ∃ storage : Array Row,
      bound < (preparedRun accept decode C fuel control storage).1 := by
  refine ⟨(List.replicate (bound + 1) row).toArray, ?_⟩
  rw [prepared_inspections_exact]
  simp

/-- A first matching row finishes the search without reading or decoding
the tail, however large that retained tail is. -/
theorem first_match_work (accept : Row → Bool) (decode : Row → Item)
    (row : Row) (rows : List Row) (accepted : accept row = true) :
    let found := FilteredSnapshot.search accept decode (row :: rows).toArray 0 (rows.length + 1)
    found.answer = some (decode row) ∧ found.inspected = 1 ∧
      found.rest.offset = 1 ∧ found.rest.remaining = rows.length := by
  simp [FilteredSnapshot.search, accepted]

theorem rejected_search_exhausts (decode : Row → Item) (storage : Array Row)
    (remaining offset : Nat) (fits : offset + remaining ≤ storage.size) :
    (FilteredSnapshot.search (fun _ => false) decode storage offset remaining).rest.remaining =
      0 := by
  induction remaining generalizing offset with
  | zero => rfl
  | succ remaining ih =>
      cases found : storage[offset]? with
      | none =>
          have outside := Array.getElem?_eq_none_iff.mp found
          omega
      | some row =>
          simp only [FilteredSnapshot.search, found, Bool.false_eq_true, ↓reduceIte]
          exact ih (offset + 1) (by omega)

/-- Requesting one answer is not a promise to inspect one row. This walk
visits the whole rejected interval. A summary or a separately recognized
predicate may license another algorithm; this is not a universal lower bound. -/
theorem all_rejected_work (decode : Row → Item) (storage : Array Row) :
    (FilteredSnapshot.search (fun _ => false) decode storage 0 storage.size).inspected =
      storage.size := by
  have conserved := FilteredSnapshot.search_conservation (fun _ => false) decode
    storage storage.size 0
  have empty := rejected_search_exhausts decode storage storage.size 0 (by omega)
  omega

/-! ## Reopening first-answer queries

Each iteration is a new query on the same entry array. Continuing one old
cursor instead would change the answers. These algorithms model the repeated
`once (match ...)` shape rather than a single fully drained reader.
-/

def repeatPrepared (accept : Row → Bool) (decode : Row → Item) (storage : Array Row) :
    Nat → Nat × List (Option Item)
  | 0 => (0, [])
  | count + 1 =>
      let prepared := gather accept decode storage.toList
      let later := repeatPrepared accept decode storage count
      (prepared.inspected + later.1, prepared.values.head? :: later.2)

def repeatRetained (accept : Row → Bool) (decode : Row → Item) (storage : Array Row) :
    Nat → Nat × List (Option Item)
  | 0 => (0, [])
  | count + 1 =>
      let found := FilteredSnapshot.search accept decode storage 0 storage.size
      let later := repeatRetained accept decode storage count
      (found.inspected + later.1, found.answer :: later.2)

theorem repeat_answers_agree (accept : Row → Bool) (decode : Row → Item)
    (storage : Array Row) (count : Nat) :
    (repeatRetained accept decode storage count).2 =
      (repeatPrepared accept decode storage count).2 := by
  have first := congrArg Prod.fst
    (FilteredSnapshot.search_correct accept decode storage storage.size 0)
  have whole := FilteredSnapshot.meaning_open accept decode storage
  simp only [FilteredSnapshot.start] at whole
  rw [whole] at first
  have sameFirst : (FilteredSnapshot.search accept decode storage 0 storage.size).answer =
      (gather accept decode storage.toList).values.head? := by
    rw [gather_meaning]
    cases semantic : storage.toList.filterMap
        (fun row => if accept row then some (decode row) else none) <;>
      simpa [semantic] using first
  induction count with
  | zero => rfl
  | succ count ih => simp only [repeatRetained, repeatPrepared, sameFirst, ih]

theorem repeat_prepared_work (accept : Row → Bool) (decode : Row → Item)
    (storage : Array Row) (count : Nat) :
    (repeatPrepared accept decode storage count).1 = count * storage.size := by
  induction count with
  | zero => simp [repeatPrepared]
  | succ count ih =>
      simp [repeatPrepared, gather_inspections, ih, Nat.add_mul, Nat.add_comm]

theorem repeat_retained_work (accept : Row → Bool) (decode : Row → Item)
    (storage : Array Row) (count : Nat) :
    (repeatRetained accept decode storage count).1 =
      count * (FilteredSnapshot.search accept decode storage 0 storage.size).inspected := by
  induction count with
  | zero => simp [repeatRetained]
  | succ count ih =>
      simp [repeatRetained, ih, Nat.add_mul, Nat.add_comm]

/-- With a matching first row, repeated fresh queries perform one inspection
each, rather than one full gather each. Both return the same first answer. -/
theorem repeated_first_match (accept : Row → Bool) (decode : Row → Item)
    (row : Row) (rows : List Row) (accepted : accept row = true) (count : Nat) :
    (repeatRetained accept decode (row :: rows).toArray count).1 = count ∧
      (repeatPrepared accept decode (row :: rows).toArray count).1 =
        count * (rows.length + 1) := by
  have one := (first_match_work accept decode row rows accepted).2.1
  constructor
  · rw [repeat_retained_work]
    simp only [List.size_toArray, List.length_cons, one, Nat.mul_one]
  · rw [repeat_prepared_work]
    simp

end Mettapedia.Machines.Cursor.SnapshotPreparation
