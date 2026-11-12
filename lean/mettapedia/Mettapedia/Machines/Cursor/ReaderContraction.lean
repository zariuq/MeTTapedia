import Mettapedia.Machines.Cursor.StampedSnapshots

/-!
# Finite reader detachment before physical contraction

Physical records carry stable logical IDs. A contraction first walks the
finite reader registry and materializes complete entry slots for attached
readers. It then filters retired physical records. Already owned readers are
reused. Complete entries preserve both the position and later rewind rights;
copying only a suffix is a different, resume-only contract.

The accounts count visited registry entries, copied snapshot slots and
inspected physical records. They are not constant-time or native byte claims.
Allocation failure, pointer ownership and concurrent publication are separate.
Full-slot copying is one concrete construction, not a lower bound: sparse
captures or persistent sharing may preserve the same rights at another cost.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderContraction

open StampedSnapshots

variable {Value : Type}

structure Cell (Value : Type) where
  id : Nat
  record : Row Value
  deriving Repr, DecidableEq

structure Physical (Value : Type) where
  clock : Nat
  next : Nat
  cells : List (Cell Value)

def logical (physical : Physical Value) : Store Value :=
  ⟨physical.clock, physical.next,
    fun id => (physical.cells.find? (fun cell => cell.id == id)).map Cell.record⟩

def Unique (physical : Physical Value) : Prop := (physical.cells.map Cell.id).Nodup

def compactRows (time : Nat) : List (Cell Value) → List (Cell Value) × Nat
  | [] => ([], 0)
  | cell :: cells =>
      let later := compactRows time cells
      (if visible time cell.record then cell :: later.1 else later.1, 1 + later.2)

theorem compactRows_result (time : Nat) (cells : List (Cell Value)) :
    (compactRows time cells).1 = cells.filter (fun cell => visible time cell.record) := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
      by_cases kept : visible time cell.record = true <;> simp [compactRows, kept, ih]

theorem compactRows_scans (time : Nat) (cells : List (Cell Value)) :
    (compactRows time cells).2 = cells.length := by
  induction cells with
  | nil => rfl
  | cons cell cells ih => simp [compactRows, ih, Nat.add_comm]

def compact (physical : Physical Value) : Physical Value :=
  { physical with cells := (compactRows physical.clock physical.cells).1 }

theorem unique_compact (physical : Physical Value) (unique : Unique physical) :
    Unique (compact physical) := by
  unfold Unique compact
  rw [compactRows_result]
  exact List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) unique

theorem find_filtered_id (cells : List (Cell Value))
    (unique : (cells.map Cell.id).Nodup) (keep : Cell Value → Bool) (id : Nat) :
    ((cells.filter keep).find? (fun cell => cell.id == id)) =
      (cells.find? (fun cell => cell.id == id)).filter keep := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
      have parts : cell.id ∉ cells.map Cell.id ∧ (cells.map Cell.id).Nodup := by
        simpa only [List.map_cons, List.nodup_cons] using unique
      by_cases same : cell.id = id
      · have absent : cells.find? (fun other => other.id == id) = none := by
          apply List.find?_eq_none.mpr
          intro other member
          simp only [beq_iff_eq]
          intro equal
          apply parts.1
          exact List.mem_map.mpr ⟨other, member, equal.trans same.symm⟩
        have absentFiltered : (cells.filter keep).find? (fun other => other.id == id) = none :=
          List.Sublist.find?_eq_none (List.filter_sublist) absent
        by_cases kept : keep cell = true
        · simp [same, kept, Option.filter_some]
        · simp [same, kept, absentFiltered, Option.filter_some]
      · by_cases kept : keep cell = true <;>
          simpa [same, kept] using ih parts.2

theorem current_lookup_compact (physical : Physical Value) (unique : Unique physical) (id : Nat) :
    atTime (logical (compact physical)) physical.clock id = atTime (logical physical) physical.clock id := by
  simp only [atTime, logical, compact, compactRows_result]
  rw [find_filtered_id physical.cells unique (fun cell => visible physical.clock cell.record) id]
  cases found : physical.cells.find? (fun cell => cell.id == id) with
  | none => rfl
  | some cell =>
      by_cases kept : visible physical.clock cell.record = true <;> simp [kept, Option.filter_some]

theorem new_reader_compact (physical : Physical Value) (unique : Unique physical) :
    capture (logical (compact physical)) (start (logical (compact physical))) =
      capture (logical physical) (start (logical physical)) := by
  unfold capture snapshot start
  congr 1
  apply List.map_congr_left
  intro id _
  exact current_lookup_compact physical unique id

inductive Handle (Value : Type) where
  | attached (reader : Reader)
  | owned (saved : Captured Value)
  deriving Repr, DecidableEq

def observe (physical : Physical Value) : Handle Value → Captured Value
  | .attached reader => capture (logical physical) reader
  | .owned saved => saved

def read (physical : Physical Value) : Handle Value → Reply Value × Handle Value
  | .attached reader =>
      let result := step (logical physical) reader
      (result.1, .attached result.2)
  | .owned saved =>
      let result := capturedStep saved
      (result.1, .owned result.2)

theorem read_refines (physical : Physical Value) (handle : Handle Value) :
    capturedStep (observe physical handle) =
      ((read physical handle).1, observe physical (read physical handle).2) := by
  cases handle with
  | attached reader => exact captured_step (logical physical) reader
  | owned saved => rfl

def clone (back : Bool) : Handle Value → Handle Value
  | .attached reader => .attached (rewind reader back)
  | .owned saved => .owned (capturedRewind saved back)

theorem clone_refines (physical : Physical Value) (handle : Handle Value) (back : Bool) :
    observe physical (clone back handle) = capturedRewind (observe physical handle) back := by
  cases handle with
  | attached reader => exact capture_rewind (logical physical) reader back
  | owned saved => rfl

/-- The list construction is explicit. An attached reader captures all entry
slots before the old physical backing may disappear. -/
def detach (physical : Physical Value) : Handle Value → Handle Value × Nat
  | .attached reader =>
      let saved := capture (logical physical) reader
      (.owned saved, saved.slots.length)
  | .owned saved => (.owned saved, 0)

theorem detach_refines (before after : Physical Value) (handle : Handle Value) :
    observe after (detach before handle).1 = observe before handle := by
  cases handle <;> rfl

theorem detach_copies (physical : Physical Value) (reader : Reader) :
    (detach physical (.attached reader)).2 = reader.ceiling := snapshot_length _ _

def detachAll (physical : Physical Value) :
    List (Option (Handle Value)) → List (Option (Handle Value)) × Nat × Nat
  | [] => ([], 0, 0)
  | none :: handles =>
      let later := detachAll physical handles
      (none :: later.1, later.2.1, 1 + later.2.2)
  | some handle :: handles =>
      let first := detach physical handle
      let later := detachAll physical handles
      (some first.1 :: later.1, first.2 + later.2.1, 1 + later.2.2)

def observeAll (physical : Physical Value) (handles : List (Option (Handle Value))) :
    List (Option (Captured Value)) := handles.map (Option.map (observe physical))

theorem detachAll_refines (before after : Physical Value) (handles : List (Option (Handle Value))) :
    observeAll after (detachAll before handles).1 = observeAll before handles := by
  induction handles with
  | nil => rfl
  | cons first rest ih =>
      cases first with
      | none => simpa [observeAll, detachAll] using congrArg (none :: ·) ih
      | some handle =>
          simp only [observeAll, detachAll, List.map_cons, Option.map_some, detach_refines]
          exact congrArg (some (observe before handle) :: ·) ih

theorem detachAll_scans (physical : Physical Value) (handles : List (Option (Handle Value))) :
    (detachAll physical handles).2.2 = handles.length := by
  induction handles with
  | nil => rfl
  | cons first rest ih => cases first <;> simp [detachAll, ih, Nat.add_comm]

def requiredCopies : List (Option (Handle Value)) → Nat
  | [] => 0
  | none :: handles => requiredCopies handles
  | some (.owned _) :: handles => requiredCopies handles
  | some (.attached reader) :: handles => reader.ceiling + requiredCopies handles

theorem detachAll_copies (physical : Physical Value) (handles : List (Option (Handle Value))) :
    (detachAll physical handles).2.1 = requiredCopies handles := by
  induction handles with
  | nil => rfl
  | cons first rest ih =>
      cases first with
      | none => simpa [detachAll, requiredCopies] using ih
      | some handle => cases handle <;> simp [detachAll, requiredCopies, detach, capture, snapshot_length, ih]

structure Contracted (Value : Type) where
  physical : Physical Value
  readers : List (Option (Handle Value))
  copiedSlots : Nat
  readerVisits : Nat
  physicalVisits : Nat

def contract (physical : Physical Value) (readers : List (Option (Handle Value))) : Contracted Value :=
  let held := detachAll physical readers
  let packed := compactRows physical.clock physical.cells
  ⟨{ physical with cells := packed.1 }, held.1, held.2.1, held.2.2, packed.2⟩

theorem contraction_preserves_readers (physical : Physical Value)
    (readers : List (Option (Handle Value))) :
    observeAll (contract physical readers).physical (contract physical readers).readers =
      observeAll physical readers := detachAll_refines _ _ _

theorem contraction_costs (physical : Physical Value) (readers : List (Option (Handle Value))) :
    (contract physical readers).copiedSlots = requiredCopies readers ∧
      (contract physical readers).readerVisits = readers.length ∧
      (contract physical readers).physicalVisits = physical.cells.length := by
  exact ⟨detachAll_copies _ _, detachAll_scans _ _, compactRows_scans _ _⟩

def lookup {Item : Type} (items : List (Option Item)) (id : Nat) : Option Item := items[id]?.join

theorem lookup_map {First Second : Type} (f : First → Second)
    (items : List (Option First)) (id : Nat) :
    lookup (items.map (Option.map f)) id = (lookup items id).map f := by
  cases found : items[id]? with
  | none => simp [lookup, List.getElem?_map, found]
  | some item => cases item <;> simp [lookup, List.getElem?_map, found]

theorem observeAll_set (physical : Physical Value) (items : List (Option (Handle Value)))
    (id : Nat) (item : Option (Handle Value)) :
    observeAll physical (items.set id item) =
      (observeAll physical items).set id (item.map (observe physical)) := by
  simp only [observeAll, List.map_set]

structure Runtime (Value : Type) where
  physical : Physical Value
  readers : List (Option (Handle Value))

inductive Op where
  | read (id : Nat)
  | clone (source target : Nat) (back : Bool)
  | close (id : Nat)
  | openReader (id : Nat)
  | compact
  deriving Repr, DecidableEq

def apply (state : Runtime Value) : Op → Runtime Value × Reply Value
  | .read id => match lookup state.readers id with
    | none => (state, .missing)
    | some handle =>
        let next := read state.physical handle
        (⟨state.physical, state.readers.set id (some next.2)⟩, next.1)
  | .clone source target back =>
      (⟨state.physical, state.readers.set target ((lookup state.readers source).map (clone back))⟩, .silent)
  | .close id => (⟨state.physical, state.readers.set id none⟩, .silent)
  | .openReader id =>
      (⟨state.physical, state.readers.set id (some (.attached (start (logical state.physical))))⟩, .silent)
  | .compact =>
      let packed := contract state.physical state.readers
      (⟨packed.physical, packed.readers⟩, .silent)

def current (physical : Physical Value) : Captured Value := capture (logical physical) (start (logical physical))

def referenceApply (entry : Captured Value) (saved : List (Option (Captured Value))) :
    Op → List (Option (Captured Value)) × Reply Value
  | .read id => match lookup saved id with
    | none => (saved, .missing)
    | some held =>
        let next := capturedStep held
        (saved.set id (some next.2), next.1)
  | .clone source target back =>
      (saved.set target ((lookup saved source).map (fun held => capturedRewind held back)), .silent)
  | .close id => (saved.set id none, .silent)
  | .openReader id => (saved.set id (some entry), .silent)
  | .compact => (saved, .silent)

theorem operation_refines (state : Runtime Value) (unique : Unique state.physical) (op : Op) :
    Unique (apply state op).1.physical ∧
      current (apply state op).1.physical = current state.physical ∧
      observeAll (apply state op).1.physical (apply state op).1.readers =
        (referenceApply (current state.physical) (observeAll state.physical state.readers) op).1 ∧
      (apply state op).2 =
        (referenceApply (current state.physical) (observeAll state.physical state.readers) op).2 := by
  cases op with
  | compact =>
      exact ⟨unique_compact state.physical unique, new_reader_compact state.physical unique,
        contraction_preserves_readers _ _, rfl⟩
  | close id => exact ⟨unique, rfl, observeAll_set _ _ _ _, rfl⟩
  | openReader id => exact ⟨unique, rfl, observeAll_set _ _ _ _, rfl⟩
  | clone source target back =>
      refine ⟨unique, rfl, ?_, rfl⟩
      simp only [apply, referenceApply, observeAll, lookup_map, List.map_set, Option.map_map]
      congr 2
      funext handle
      exact clone_refines state.physical handle back
  | read id =>
      have source : lookup (observeAll state.physical state.readers) id =
          (lookup state.readers id).map (observe state.physical) := lookup_map _ _ _
      cases found : lookup state.readers id with
      | none => simp [apply, referenceApply, source, found, unique]
      | some handle =>
          simp only [apply, found, referenceApply, source, Option.map_some, read_refines]
          exact ⟨unique, trivial, observeAll_set _ _ _ _, trivial⟩

def run : Runtime Value → List Op → Runtime Value × List (Reply Value)
  | state, [] => (state, [])
  | state, op :: ops =>
      let first := apply state op
      let later := run first.1 ops
      (later.1, first.2 :: later.2)

def referenceRun (entry : Captured Value) :
    List (Option (Captured Value)) → List Op → List (Option (Captured Value)) × List (Reply Value)
  | saved, [] => (saved, [])
  | saved, op :: ops =>
      let first := referenceApply entry saved op
      let later := referenceRun entry first.1 ops
      (later.1, first.2 :: later.2)

/-- Every finite schedule of reads, copies, rewinds, opens, closes and repeated
contractions preserves the actual captured views and ordered replies. Ordinary
store writes between contractions use the stamped visibility laws separately. -/
theorem schedule_refines (state : Runtime Value) (unique : Unique state.physical) (ops : List Op) :
    observeAll (run state ops).1.physical (run state ops).1.readers =
        (referenceRun (current state.physical) (observeAll state.physical state.readers) ops).1 ∧
      (run state ops).2 =
        (referenceRun (current state.physical) (observeAll state.physical state.readers) ops).2 := by
  induction ops generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons op ops ih =>
      obtain ⟨nextUnique, sameCurrent, sameReaders, sameReply⟩ := operation_refines state unique op
      obtain ⟨laterReaders, laterReplies⟩ := ih (apply state op).1 nextUnique
      simp only [run, referenceRun]
      rw [sameCurrent, sameReaders] at laterReaders laterReplies
      exact ⟨laterReaders, by rw [sameReply, laterReplies]⟩

end Mettapedia.Machines.Cursor.ReaderContraction
