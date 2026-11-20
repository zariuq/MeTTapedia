import Mettapedia.Machines.PreparedFrontierTransfer
import Mathlib.Data.List.Nodup

/-!
# Checked positions in the leased catalogue of equation occurrences

The handback uses the producer's ordinal as a hint. It checks both the
equation identity and its logical occurrence index before accepting that
position, with a full search as fallback. Identical payloads at different
indices remain distinguishable. An exhausted frame contributes no choice.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PreparedOccurrenceCatalog

structure Identity where
  equation : UInt64
  logicalIndex : UInt64
  deriving DecidableEq, Repr

structure Row (Job : Type) where
  identity : Identity
  payload : Job
  deriving Repr

def locate {Job : Type} (catalogue : List (Row Job)) (ordinal : Nat) (wanted : Identity) :
    Option Nat :=
  let eligible := fun row : Row Job => decide (row.identity = wanted)
  if (catalogue[ordinal]?.map eligible).getD false then some ordinal
  else catalogue.findIdx? eligible

theorem locate_reads_identity {Job : Type} (catalogue : List (Row Job)) (hint : Nat)
    (wanted : Identity) (position : Nat) (found : locate catalogue hint wanted = some position) :
    ∃ row, catalogue[position]? = some row ∧ row.identity = wanted := by
  dsimp only [locate] at found
  split at found
  next fast =>
    cases found
    cases item : catalogue[hint]? with
    | none => simp [item] at fast
    | some row => exact ⟨row, rfl, by simpa [item] using fast⟩
  next =>
    obtain ⟨within, agreeing, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
    exact ⟨catalogue[position], List.getElem?_eq_getElem within, of_decide_eq_true agreeing⟩

theorem locate_exact {Job : Type} (catalogue : List (Row Job)) (hint expected : Nat) (row : Row Job)
    (present : catalogue[expected]? = some row) (unique : (catalogue.map Row.identity).Nodup) :
    locate catalogue hint row.identity = some expected := by
  have atExpected : (catalogue.map Row.identity)[expected]? = some row.identity := by
    simp only [List.getElem?_map, present, Option.map_some]
  have only (position : Nat) (other : Row Job) (read : catalogue[position]? = some other)
      (same : other.identity = row.identity) : position = expected := by
    have inside : position < (catalogue.map Row.identity).length := by
      rw [List.length_map]
      exact (List.getElem?_eq_some_iff.mp read).choose
    apply (List.getElem?_inj inside unique).mp
    simp only [List.getElem?_map, read, Option.map_some, same, atExpected]
  cases located : locate catalogue hint row.identity with
  | none =>
    dsimp only [locate] at located
    split at located
    · contradiction
    · have absent := List.findIdx?_eq_none_iff.mp located
      have impossible := absent _ (List.mem_of_getElem? present)
      simp at impossible
  | some position =>
    obtain ⟨other, read, same⟩ := locate_reads_identity catalogue hint row.identity position located
    rw [only position other read same]

structure Frame (Job : Type) where
  catalogue : List (Row Job)
  nextOrdinal : Nat
  equationCount : Nat
  nextIdentity : Identity
  restore : Job → Job

def Frame.reference {Job : Type} (frame : Frame Job) : PreparedFrontierTransfer.Frame Job :=
  ⟨frame.catalogue.map Row.payload, frame.nextOrdinal, frame.restore⟩

def Frame.read {Job : Type} (frame : Frame Job) :
    Option (PreparedFrontierTransfer.Frame Job) := do
  let next ← locate frame.catalogue frame.nextOrdinal frame.nextIdentity
  return ⟨frame.catalogue.map Row.payload, next, frame.restore⟩

def Frame.Valid {Job : Type} (frame : Frame Job) : Prop :=
  frame.equationCount = frame.catalogue.length ∧ (frame.catalogue.map Row.identity).Nodup ∧
    (frame.nextOrdinal < frame.equationCount →
      ∃ row, frame.catalogue[frame.nextOrdinal]? = some row ∧ row.identity = frame.nextIdentity)

private theorem frame_read_refines {Job : Type} (frame : Frame Job) (valid : frame.Valid)
    (pending : frame.nextOrdinal < frame.equationCount) :
    frame.read = some frame.reference := by
  obtain ⟨row, present, identity⟩ := valid.2.2 pending
  have exactPosition := locate_exact frame.catalogue frame.nextOrdinal frame.nextOrdinal row present valid.2.1
  rw [identity] at exactPosition
  simp [Frame.read, Frame.reference, exactPosition]

def snapshots {Job : Type} (outerFirst : List (Frame Job)) :
    Option (List (PreparedFrontierTransfer.Frame Job)) :=
  (outerFirst.filter fun frame => decide (frame.nextOrdinal < frame.equationCount)).mapM Frame.read

theorem snapshots_refine {Job : Type} (outerFirst : List (Frame Job))
    (valid : ∀ frame ∈ outerFirst, frame.Valid) :
    snapshots outerFirst =
      some ((outerFirst.filter fun frame => decide (frame.nextOrdinal < frame.equationCount)).map Frame.reference) := by
  induction outerFirst with
  | nil => rfl
  | cons frame rest ih =>
    have current := valid frame (by simp)
    have restValid : ∀ later ∈ rest, later.Valid :=
      fun later member => valid later (List.mem_cons_of_mem frame member)
    have tail := ih restValid
    unfold snapshots at tail
    by_cases pending : frame.nextOrdinal < frame.equationCount
    · simp [snapshots, pending, frame_read_refines frame current pending, tail]
    · simpa [snapshots, pending] using tail

theorem leased_frontier_order {Job : Type} (entered : Job)
    (outerFirst : List (Frame Job)) (valid : ∀ frame ∈ outerFirst, frame.Valid) :
    (snapshots outerFirst).map (PreparedFrontierTransfer.install entered) =
      some (PreparedFrontierTransfer.reference entered (outerFirst.map Frame.reference)) := by
  rw [snapshots_refine outerFirst valid, Option.map_some, PreparedFrontierTransfer.installation_refines]
  congr 1
  unfold PreparedFrontierTransfer.reference
  congr 1
  induction outerFirst with
  | nil => rfl
  | cons frame rest ih =>
    have current := valid frame (by simp)
    have tail := ih (fun other member => valid other (List.mem_cons_of_mem frame member))
    by_cases pending : frame.nextOrdinal < frame.equationCount
    · simp only [List.filter_cons, decide_eq_true pending, if_true, List.map_cons, List.reverse_cons,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [tail]
    · have complete : frame.reference.equations.length ≤ frame.reference.next := by
        simp only [Frame.reference, List.length_map]
        have same := current.1
        omega
      have noneLeft : PreparedFrontierTransfer.remaining frame.reference = [] := by
        simp [PreparedFrontierTransfer.remaining, List.drop_eq_nil_iff.mpr complete]
      simp only [List.filter_cons, decide_eq_false pending, Bool.false_eq_true, if_false, List.map_cons,
        List.reverse_cons, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        noneLeft]
      exact tail

end Mettapedia.Machines.PreparedOccurrenceCatalog
