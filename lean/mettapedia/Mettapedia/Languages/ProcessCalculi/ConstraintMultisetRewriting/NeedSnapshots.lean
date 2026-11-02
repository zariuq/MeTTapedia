import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SnapshotCopy
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceSpec

/-!
# Per-cell representation of call-time-choice stores

Every suspension retains its code, captured environment and memo; the store
trace retains order and repetitions. The representation supplies the complete
snapshot-copy invariant for every source store. This is the storage component
of instruction lowering, not a whole-program adequacy claim.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedSnapshots

open SnapshotCopy
open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

def encodedCells (source : Nat) (store : Store) : Finset (Occurrence Suspension) :=
  Finset.univ.image fun index : Fin store.cells.length =>
    (index.val+3, .cell source index.val store.cells[index.val])

def encode (job source : Nat) (store : Store) : World Suspension :=
  ⟨[], {(0,.allocated source),(1,.ready source),
    (2,.metadata source store.cells.length store.trace),
    (store.cells.length+3,.request job source)} ∪ encodedCells source store⟩

theorem mem_encoded {job source : Nat} {store : Store} {occurrence : Occurrence Suspension} :
    occurrence ∈ (encode job source store).present ↔
      occurrence = (0,.allocated source) ∨ occurrence = (1,.ready source) ∨
      occurrence = (2,.metadata source store.cells.length store.trace) ∨
      occurrence = (store.cells.length+3,.request job source) ∨
      ∃ index : Fin store.cells.length,
        occurrence = (index.val+3,.cell source index.val store.cells[index.val]) := by
  simp [encode,encodedCells,eq_comm]

theorem encoded_cell {job source snapshot position : Nat} {store : Store} {value : Suspension}
    {occurrence : Occurrence Suspension}
    (present : occurrence ∈ (encode job source store).present)
    (atCell : label occurrence = .cell snapshot position value) :
    snapshot = source ∧ occurrence.1 = position+3 ∧ store.cells[position]? = some value := by
  rcases mem_encoded.mp present with rfl | rfl | rfl | rfl | ⟨index,rfl⟩
  · cases atCell
  · cases atCell
  · cases atCell
  · cases atCell
  · have fields := Row.cell.inj atCell
    rcases fields with ⟨rfl,rfl,rfl⟩
    exact ⟨rfl,rfl,List.getElem?_eq_getElem index.isLt⟩

theorem encoded_snapshot (job source : Nat) (store : Store) :
    Snapshot (encode job source store).present source store.cells store.trace := by
  refine ⟨⟨(0,.allocated source),by simp [encode],rfl⟩,
    ⟨⟨(2,.metadata source store.cells.length store.trace),by simp [encode],rfl⟩,?_⟩,
    ⟨(1,.ready source),by simp [encode],rfl⟩,⟨?_,?_⟩⟩
  · rintro count trace ⟨occurrence,present,same⟩
    rcases mem_encoded.mp present with rfl | rfl | rfl | rfl | ⟨index,rfl⟩
    · cases same
    · cases same
    · exact ⟨(Row.metadata.inj same).2.1.symm,(Row.metadata.inj same).2.2.symm⟩
    · cases same
    · cases same
  · intro index value
    constructor
    · rintro ⟨occurrence,present,same⟩
      exact (encoded_cell present same).2.2
    · intro found
      obtain ⟨bound,equal⟩ := List.getElem?_eq_some_iff.mp found
      refine ⟨(index+3,.cell source index value),?_,rfl⟩
      exact mem_encoded.mpr (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨index,bound⟩,by simp [equal]⟩))))
  · intro first present second other index firstValue secondValue sameFirst sameSecond
    have firstFields := encoded_cell present sameFirst
    have secondFields := encoded_cell other sameSecond
    have valueEq : firstValue = secondValue := Option.some.inj (firstFields.2.2.symm.trans secondFields.2.2)
    apply Prod.ext (firstFields.2.1.trans secondFields.2.1.symm)
    change label first = label second
    rw [sameFirst,sameSecond,valueEq]

theorem encoded_fresh {job source destination : Nat} (store : Store) (different : source ≠ destination) :
    Fresh (encode job source store).present destination := by
  intro occurrence present
  rcases mem_encoded.mp present with rfl | rfl | rfl | rfl | ⟨index,rfl⟩ <;>
    simpa [label,IndexedOccurrences.label,Row.mentions] using Ne.symm different

/-- Every independent source store, including undemanded cells and already
cached cells, has an ordinary transform execution copying its full contents. -/
theorem every_source_store_can_be_copied (store : Store) (job source destination : Nat)
    (different : source ≠ destination) :
    ∃ after events, Execution job source destination events (encode job source store) after ∧
      events.length = store.cells.length+2 ∧
      Snapshot after.present source store.cells store.trace ∧
      Snapshot after.present destination store.cells store.trace ∧ Has after.present (.reply job destination) := by
  apply snapshot_can_be_copied (encode job source store) job source destination store.cells store.trace
    (encoded_snapshot job source store) (encoded_fresh store different)
    (store.cells.length+3,.request job source)
  · simp [encode]
  · rfl
  · exact ⟨(),by simp [encode,SubstitutionAction.Models]⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedSnapshots
