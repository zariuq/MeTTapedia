import Mettapedia.Machines.TIsa.StoreInstructions.NativeFiringGate
import Mettapedia.Machines.TIsa.StoreInstructions.NativeBatchPublication

/-!
# A refused firing never enters its publication block

Selection, funding, private preparation, and the root store
have distinct instruction endpoints. Only the funded edge
can construct and expose the successor snapshot. Fuel and
workset capacity are independent of source logical refusal.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeFundedPublication

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code)
open X86PlacedMemory (Controls CodeApart Reads footprint)
open NativeWords (Wiring touched written)
open NativePreparation (Native AddressMap Represents Geometry skeleton)
open NativeArrayUpdate (Root)
open NativeFiringGate (Decision decideFiring)
open StorePublication (Snapshot ReadsSnapshot)
open Derivation (Store)
local instance : MemoryPrimitives := X86Memory.ordinary

variable {V : Type*} {keys : ℕ} {oldBase newBase : Word}

def emit (w : Wiring) (old : AddressMap oldBase) (next : AddressMap newBase) (root : Root w)
    (plan : List PrivateArrayPlan.Write) (start refused exhausted : ℕ) : List ℕ :=
  NativeFiringGate.emit start refused exhausted ++ NativeBatchPublication.emit w old next root plan

def clobbers (w : Wiring) : Finset Register := NativeFiringGate.clobbers ∪ touched w

def writes (w : Wiring) (old : AddressMap oldBase) (next : AddressMap newBase) (root : Root w)
    (plan : List PrivateArrayPlan.Write) : Decision → Finset ℕ
  | .paid _ => written (skeleton old next plan) ∪ footprint root.cell.address
  | _ => ∅

structure WiringFits (w : Wiring) (root : Root w) : Prop where
  readBase : key w.readBase ∉ NativeFiringGate.clobbers
  writeBase : key w.writeBase.base ∉ NativeFiringGate.clobbers
  rootBase : key root.encoding.base ∉ NativeFiringGate.clobbers
  token : key root.token ∉ NativeFiringGate.clobbers
  allowance : key (14 : Fin 16) ∉ touched w

def Result (codes : PackedOccurrences.Codes V) (classify : V → Fin keys)
    (source : Store V) (taken : List ℕ) (made : List V)
    (before target : Snapshot) (old : AddressMap oldBase) (next : AddressMap newBase)
    (catalog nextCatalog : Array Snapshot) (handle : Word) {w : Wiring} (root : Root w)
    (image : NativeImage.View) (base : BitVec 48) (finished refused exhausted : ℕ) (state : Native) : Decision → Prop
  | .refused =>
    ReadsSnapshot catalog state root.cell.address before ∧ Represents old state before ∧ Nonempty (At image state base refused)
  | .exhausted =>
    ReadsSnapshot catalog state root.cell.address before ∧ Represents old state before ∧ Nonempty (At image state base exhausted)
  | .paid _ =>
    ReadsSnapshot nextCatalog state root.cell.address target ∧ Reads state root.cell.address handle ∧ Represents next state target ∧
      StorePublication.encode codes classify ((source.takeAll taken).makeAll made) = some target ∧
      Nonempty (At image state base finished)

/-- A declined or unfunded firing preserves the old native
snapshot, with an empty write footprint. The funded firing
executes the entire generated store/index block. -/
theorem fetched (codes : PackedOccurrences.Codes V) (classify : V → Fin keys)
    {source : Store V} {before target : Snapshot} {plan : List PrivateArrayPlan.Write}
    (packed : StorePublication.encode codes classify source = some before) (taken : List ℕ) (made : List V)
    (assembled : PrivateArrayBatch.assemble codes classify before taken made = some (target, plan))
    {catalog nextCatalog : Array Snapshot} {handle : Word}
    (stage : StorePublication.stage catalog target = some (nextCatalog, handle))
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (w : Wiring) (old : AddressMap oldBase) (next : AddressMap newBase) (root : Root w) (registers : WiringFits w root)
    {state : Native} {image : NativeImage.View} {base : BitVec 48} {start refused exhausted : ℕ}
    (point : At image state base start) (controls : Controls state)
    (readBase : lookup state w.readBase = some oldBase) (writeBase : lookup state w.writeBase.base = some newBase)
    (rootBase : lookup state root.encoding.base = some root.pointer) (rootValue : lookup state root.token = some handle)
    (view : Represents old state before) (visible : ReadsSnapshot catalog state root.cell.address before)
    (geometry : Geometry w image base old next plan)
    (separateRoot : Disjoint (footprint root.cell.address) (written (skeleton old next plan)))
    (outsideCode : CodeApart image base (footprint root.cell.address))
    (extent : start + (emit w old next root plan start refused exhausted).length ≤ image.size)
    (denied : refused ≤ image.size) (noFuel : exhausted ≤ image.size) (short : image.size < 2 ^ 31)
    (placed : Code image start (emit w old next root plan start refused exhausted))
    (confirmed : Bool) (balance : Word) (bit : lookup state 0 = some (booleanWord confirmed))
    (zero : lookup state 12 = some 0) (one : lookup state 13 = some 1) (allowance : lookup state 14 = some balance) :
    let decision := decideFiring confirmed balance
    letI : OtherOpcodeHandlers := NativeFiringGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run state = .ok () after ∧
      X86StateFrame.Frame (clobbers w) (writes w old next root plan decision) state after ∧
      lookup after 14 = some (decision.allowance balance) ∧
      Result codes classify source taken made before target old next catalog nextCatalog handle root image base
        (start + (emit w old next root plan start refused exhausted).length) refused exhausted after decision := by
  let : OtherOpcodeHandlers := NativeFiringGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨guard, payload⟩ := NativeWords.code_append (show Code image start
    (NativeFiringGate.emit start refused exhausted ++ _) from placed)
  rw [NativeFiringGate.emit_size] at payload
  have needed := extent
  simp only [emit, List.length_append, NativeFiringGate.emit_size, ← Nat.add_assoc] at needed
  have fitted := NativeFiringGate.placed_of_emitted image start refused exhausted (by omega) denied noFuel short guard
  obtain ⟨middle, early, gated, fuel, ⟨atNext⟩⟩ :=
    NativeFiringGate.fetched other extra vector fitted point confirmed balance bit zero one allowance
  have oldView : Represents old middle before := fun field word read => (view field word read).preserved gated (by simp)
  obtain ⟨older, oldRoot, oldSnapshot⟩ := visible
  have oldVisible : ReadsSnapshot catalog middle root.cell.address before :=
    ⟨older, oldRoot.preserved gated (by simp), oldSnapshot⟩
  dsimp only
  generalize outcome : decideFiring confirmed balance = decision at early fuel atNext ⊢
  cases decision with
  | refused =>
    exact ⟨middle, 2, early, gated.mono Finset.subset_union_left (Finset.Subset.refl _), fuel, oldVisible, oldView, ⟨atNext⟩⟩
  | exhausted =>
    exact ⟨middle, 4, early, gated.mono Finset.subset_union_left (Finset.Subset.refl _), fuel, oldVisible, oldView, ⟨atNext⟩⟩
  | paid remaining =>
    obtain ⟨_, after, _, _, _, ran, exact, published, selected, physical, framed, endpoint⟩ := NativeBatchPublication.fetched codes classify
      packed taken made assembled stage (NativeFiringGate.handlers other extra) vector w old next root
      (show At image middle base (start + 21) from atNext)
      (controls.transport gated NativeFiringGate.clobbers_data)
      ((gated.lookup _ registers.readBase).trans readBase) ((gated.lookup _ registers.writeBase).trans writeBase)
      ((gated.lookup _ registers.rootBase).trans rootBase) ((gated.lookup _ registers.token).trans rootValue)
      oldView oldVisible geometry separateRoot outsideCode needed payload
    have linked : NativeWords.handlers (NativeFiringGate.handlers other extra) = NativeFiringGate.handlers other extra := rfl
    rw [linked] at ran
    have whole : X86StateFrame.Frame (clobbers w) (writes w old next root plan (.paid remaining)) state after :=
      (gated.trans framed).mono (Finset.Subset.refl _) (by simp only [Finset.empty_union, writes]; exact Finset.Subset.refl _)
    have atEnd : Nonempty (At image after base (start + (emit w old next root plan start refused exhausted).length)) := by
      simpa only [emit, List.length_append, NativeFiringGate.emit_size, ← Nat.add_assoc] using endpoint
    exact ⟨after, 5 + (2 * plan.length + 1), X86FuelPrefix.fetches_then 5 _ state middle after early ran, whole,
      (framed.lookup 14 registers.allowance).trans fuel, published, selected, physical, exact, atEnd⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeFundedPublication
