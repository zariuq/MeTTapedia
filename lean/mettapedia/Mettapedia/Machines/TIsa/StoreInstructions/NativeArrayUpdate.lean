import Mettapedia.Machines.TIsa.StoreInstructions.NativePreparation

/-!
# Fetched TAKE and MAKE over a privately constructed snapshot

The old occurrence array supplies the survivor words. Preparation
initializes all data and index words of the successor without changing
the visible root. One final qword store selects the successor. This is
a staged code generator: locations and the modification plan are known
when emitting the block, contents of copied slots are not.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeArrayUpdate

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code)
open X86PlacedMemory (Cell Controls CodeApart footprint Encoding)
open NativeWords (Wiring touched written outside_scratch)
open NativePreparation (Native AddressMap Represents Geometry code skeleton)
open StorePublication (Update Snapshot ReadsSnapshot)
open Derivation (Matcher)
local instance : MemoryPrimitives := X86Memory.ordinary

variable {V B T : Type*} {st : StoreInstructions.State V B} {keys : ℕ}

def edit : Update st → PrivateArrayPlan.Edit V
  | .take _ _ identity _ => .take identity
  | .make _ _ value _ => .make value

theorem edit_taken (update : Update st) : (edit update).taken = update.taken := by cases update <;> rfl
theorem edit_made (update : Update st) : (edit update).made = update.made := by cases update <;> rfl

theorem assembled_result (update : Update st) (codes : PackedOccurrences.Codes V) (classify : V → Fin keys)
    {before target : Snapshot} {plan : List PrivateArrayPlan.Write}
    (packed : StorePublication.encode codes classify st.store = some before)
    (assembled : PrivateArrayPlan.assemble codes classify before (edit update) = some (target, plan)) :
    StorePublication.encode codes classify update.result.store = some target := by
  have prepares := PrivateArrayPlan.assemble_exact codes classify before (edit update)
  rw [assembled, Option.map_some, edit_taken, edit_made] at prepares
  exact (StorePublication.prepare_exact codes classify packed update.taken update.made).symm.trans prepares.symm

structure Root (w : Wiring) where
  encoding : Encoding
  pointer : Word
  displacement : BitVec 32
  cell : Cell pointer displacement
  token : Fin 16
  basePreserved : encoding.base ≠ w.scratch
  tokenPreserved : token ≠ w.scratch

def Root.bytes {w : Wiring} (root : Root w) : List ℕ :=
  root.encoding.bytes root.token root.displacement

/-- From an old snapshot to a decoded new snapshot, including the
fetched private writes. The logical result includes the normal TAKE
or MAKE effect on the selected slot. -/
theorem lower_update_x86 [DecidableEq V] (matcher : Matcher T V B) (update : Update st)
    (codes : PackedOccurrences.Codes V) (classify : V → Fin keys)
    {before target : Snapshot} {plan : List PrivateArrayPlan.Write}
    (packed : StorePublication.encode codes classify st.store = some before)
    (assembled : PrivateArrayPlan.assemble codes classify before (edit update) = some (target, plan))
    {catalog nextCatalog : Array Snapshot} {handle : Word}
    (staged : StorePublication.stage catalog target = some (nextCatalog, handle))
    (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (w : Wiring)
    {oldBase newBase : Word} (old : AddressMap oldBase) (next : AddressMap newBase) (root : Root w)
    {state : Native} {image : NativeImage.View} {base : BitVec 48} {start : ℕ}
    (point : At image state base start) (controls : Controls state)
    (readBase : lookup state w.readBase = some oldBase) (writeBase : lookup state w.writeBase.base = some newBase)
    (rootBase : lookup state root.encoding.base = some root.pointer) (rootValue : lookup state root.token = some handle)
    (view : Represents old state before) (visible : ReadsSnapshot catalog state root.cell.address before)
    (placement : Geometry w image base old next plan)
    (separateRoot : Disjoint (footprint root.cell.address) (written (skeleton old next plan)))
    (rootOutsideCode : CodeApart image base (footprint root.cell.address))
    (extent : start + (code w old next plan).length + root.encoding.length ≤ image.size)
    (prepareCode : Code image start (code w old next plan))
    (publishCode : Code image (start + (code w old next plan).length) root.bytes) :
    letI : OtherOpcodeHandlers := NativeWords.handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ privateState after abstract,
      (X86FuelPrefix.fetches (2 * plan.length)).run state = .ok () privateState ∧
      ReadsSnapshot nextCatalog privateState root.cell.address before ∧
      (X86FuelPrefix.fetches (2 * plan.length + 1)).run state = .ok () after ∧
      executeInstruction matcher st update.operation = .ok abstract ∧
      StorePublication.encode codes classify abstract.store = some target ∧
      ReadsSnapshot nextCatalog after root.cell.address target ∧ Represents next after target ∧
      X86StateFrame.Frame (touched w) (written (skeleton old next plan) ∪ footprint root.cell.address) state after ∧
      Nonempty (At image after base (start + (code w old next plan).length + root.encoding.length)) := by
  let : OtherOpcodeHandlers := NativeWords.handlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨prepared, ran, represented, targeted, framed, ⟨publication⟩⟩ :=
    NativePreparation.fetch_assembled codes classify assembled other vector w old next point controls
      readBase writeBase view placement (by omega) prepareCode
  obtain ⟨prior, oldRead, oldTarget⟩ := visible
  have stillOld := StorePublication.old_snapshot_after_staging staged
    (oldRead.preserved framed separateRoot) oldTarget
  obtain ⟨after, writtenRoot, rootFrame, shared, nextPoint⟩ :=
    X86PlacedMemory.stores (NativeWords.handlers other) vector publication
      (controls.transport framed (X86Immediate32.writes_data _)) root.encoding root.token root.displacement
      root.pointer handle root.cell
      ((framed.lookup _ (outside_scratch w _ root.basePreserved)).trans rootBase)
      ((framed.lookup _ (outside_scratch w _ root.tokenPreserved)).trans rootValue)
      extent publishCode rootOutsideCode
  have publishes : ReadsSnapshot nextCatalog after root.cell.address target :=
    ⟨handle, shared, (StorePublication.staged_exact staged).1⟩
  have survived : Represents next after target := fun field word loaded =>
    (represented field word loaded).preserved rootFrame
      (separateRoot.symm.mono_left (targeted field word loaded))
  have finishes := X86FuelPrefix.fetches_then (2 * plan.length) 1 state prepared after ran writtenRoot
  exact ⟨prepared, after, update.result, ran, stillOld, finishes, update.executed matcher,
    assembled_result update codes classify packed assembled, publishes, survived,
    (framed.trans rootFrame).mono (by simp [touched]) (Finset.Subset.refl _), nextPoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeArrayUpdate
