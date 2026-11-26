import Mettapedia.Machines.TIsa.StoreInstructions.PrivateArrayBatch
import Mettapedia.Machines.TIsa.StoreInstructions.NativeArrayUpdate
import Mettapedia.Machines.TIsa.StoreInstructions.SymbolicPublication

/-!
# One native store publication for an admitted firing

The layout plan refers to the old positions of surviving
occurrences. It also installs the index of the final array.
The old snapshot stays selected until the last fetched store.
For a symbolic firing the value words represent opened terms,
not values chosen from one resolution of the residual equations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeBatchPublication

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code)
open X86PlacedMemory (Controls CodeApart footprint Reads)
open NativeWords (Wiring touched written outside_scratch)
open NativePreparation (Native AddressMap Represents Geometry code skeleton)
open NativeArrayUpdate (Root)
open StorePublication (Snapshot ReadsSnapshot)
open Derivation (Store)
local instance : MemoryPrimitives := X86Memory.ordinary

variable {V : Type*} {keys : ℕ} {oldBase newBase : Word}

def emit (w : Wiring) (old : AddressMap oldBase) (next : AddressMap newBase) (root : Root w)
    (plan : List PrivateArrayPlan.Write) : List ℕ :=
  code w old next plan ++ root.bytes

private theorem emit_size (w : Wiring) (old : AddressMap oldBase) (next : AddressMap newBase) (root : Root w)
    (plan : List PrivateArrayPlan.Write) :
    (emit w old next root plan).length = (code w old next plan).length + root.encoding.length := by
  simp only [emit, List.length_append, NativeArrayUpdate.Root.bytes]
  congr 1
  cases root.encoding with
  | direct r _ _ => exact X86DataStore.code_length true root.token r root.displacement
  | r12 => exact X86SibQword.code_length .store root.token root.displacement

/-- The emitted preparation executes a generated batch
plan, not a supplied successor memory. All intermediate
states in this block are framed away from the publication word. -/
theorem fetched (codes : PackedOccurrences.Codes V) (classify : V → Fin keys)
    {source : Store V} {before target : Snapshot} {plan : List PrivateArrayPlan.Write}
    (packed : StorePublication.encode codes classify source = some before) (taken : List ℕ) (made : List V)
    (assembled : PrivateArrayBatch.assemble codes classify before taken made = some (target, plan))
    {catalog nextCatalog : Array Snapshot} {handle : Word}
    (stage : StorePublication.stage catalog target = some (nextCatalog, handle))
    (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (w : Wiring)
    (old : AddressMap oldBase) (next : AddressMap newBase) (root : Root w)
    {state : Native} {image : NativeImage.View} {base : BitVec 48} {start : ℕ}
    (point : At image state base start) (controls : Controls state)
    (readBase : lookup state w.readBase = some oldBase) (writeBase : lookup state w.writeBase.base = some newBase)
    (rootBase : lookup state root.encoding.base = some root.pointer) (rootValue : lookup state root.token = some handle)
    (view : Represents old state before) (visible : ReadsSnapshot catalog state root.cell.address before)
    (geometry : Geometry w image base old next plan)
    (separateRoot : Disjoint (footprint root.cell.address) (written (skeleton old next plan)))
    (outsideCode : CodeApart image base (footprint root.cell.address))
    (extent : start + (emit w old next root plan).length ≤ image.size)
    (placed : Code image start (emit w old next root plan)) :
    letI : OtherOpcodeHandlers := NativeWords.handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ prepared after,
      (X86FuelPrefix.fetches (2 * plan.length)).run state = .ok () prepared ∧
      X86StateFrame.Frame (touched w) (written (skeleton old next plan)) state prepared ∧
      ReadsSnapshot nextCatalog prepared root.cell.address before ∧
      (X86FuelPrefix.fetches (2 * plan.length + 1)).run state = .ok () after ∧
      StorePublication.encode codes classify ((source.takeAll taken).makeAll made) = some target ∧
      ReadsSnapshot nextCatalog after root.cell.address target ∧ Reads after root.cell.address handle ∧ Represents next after target ∧
      X86StateFrame.Frame (touched w) (written (skeleton old next plan) ∪ footprint root.cell.address) state after ∧
      Nonempty (At image after base (start + (emit w old next root plan).length)) := by
  let : OtherOpcodeHandlers := NativeWords.handlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨prepareCode, publishCode⟩ := NativeWords.code_append (show Code image start (code w old next plan ++ _) from placed)
  have remaining := extent
  rw [emit_size, ← Nat.add_assoc] at remaining
  obtain ⟨encoded, evaluated⟩ := PrivateArrayBatch.assembled codes classify packed assembled
  obtain ⟨prepared, ran, frame, initialized, ⟨atPublish⟩⟩ := NativePreparation.fetch_plan other vector w old next before plan
    evaluated point controls readBase writeBase view geometry (by omega) prepareCode
  obtain ⟨prior, stillVisible, previous⟩ := visible
  have oldSnapshot := StorePublication.old_snapshot_after_staging stage (stillVisible.preserved frame separateRoot) previous
  obtain ⟨after, committed, writeFrame, published, endpoint⟩ := X86PlacedMemory.stores (NativeWords.handlers other) vector
    atPublish (controls.transport frame (X86Immediate32.writes_data _)) root.encoding root.token root.displacement
    root.pointer handle root.cell
    ((frame.lookup _ (outside_scratch w _ root.basePreserved)).trans rootBase)
    ((frame.lookup _ (outside_scratch w _ root.tokenPreserved)).trans rootValue) remaining publishCode outsideCode
  refine ⟨prepared, after, ran, frame, oldSnapshot, X86FuelPrefix.fetches_then (2 * plan.length) 1 state prepared after ran committed,
    encoded, ⟨handle, published, (StorePublication.staged_exact stage).1⟩, published, ?_,
    (frame.trans writeFrame).mono (by simp [touched]) (Finset.Subset.refl _), ?_⟩
  · intro field word read
    obtain ⟨exact, inPrivate⟩ := initialized (field, word) (PrivateArrayPlan.read_mem_contents read)
    exact exact.preserved writeFrame (separateRoot.symm.mono_left inPrivate)
  · simpa only [emit_size, ← Nat.add_assoc] using endpoint

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Derivation.SymbolicFiring (Rules LiveWorld act)
open SymbolicExecution (storeOf)

universe u p
variable {σ : LPSignature.{u,u,p,u}} {rules : Rules σ}

theorem source_firing (world : LiveWorld σ)
    (firing : RuleSyntax.Firing ℕ (RuleSyntax.OneFrame.ext (FirstOrder.action σ)) rules.program world.state.frame)
    (shape : firing.Shapes (act σ) world.state)
    (fresh : firing.selection.made = world.reserve 0 firing.selection.made.length)
    (codes : PackedOccurrences.Codes (Term σ)) (classify : Term σ → Fin keys)
    {before target : Snapshot} {plan : List PrivateArrayPlan.Write}
    (packed : StorePublication.encode codes classify (storeOf world) = some before)
    (assembled : PrivateArrayBatch.assemble codes classify before firing.selection.taken (firing.opened (act σ)).produce =
      some (target, plan)) :
    StorePublication.encode codes classify (storeOf (world.commit firing fresh)) = some target ∧
      PrivateArrayPlan.evaluate before plan = some (PrivateArrayPlan.contents target) := by
  rw [SymbolicPublication.storeOf_commit world firing shape fresh]
  exact PrivateArrayBatch.assembled codes classify packed assembled

end Mettapedia.Machines.TIsa.StoreInstructions.NativeBatchPublication
