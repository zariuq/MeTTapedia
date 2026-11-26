import Mettapedia.Machines.TIsa.StoreInstructions.PackedOccurs
import Mettapedia.Machines.TIsa.StoreInstructions.NativeRoleEmission
import Mettapedia.Machines.TIsa.StoreInstructions.NativeDecisions
import Mettapedia.Machines.TIsa.StoreInstructions.NativeStores

/-!
# Native propagation of an application occurrence bit

The application reads the bits of its children. It stops at
the first set bit, writes the resulting bit to its own cell,
and preserves the previously computed bits.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeOccurs

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Cell Controls CodeApart footprint Reads)
open X86PlacedScalar (Code)
open NativeRoleGate (WordAt resident)
open MemoryBinding (Native handlers storeEncoding)
local instance : MemoryPrimitives := X86Memory.ordinary

def code : Bool → ℕ
  | false => 0
  | true => 1

theorem hit_iff (bits : List Bool) : 1 ∈ bits.map code ↔ bits.any id = true := by
  simp only [List.mem_map, List.any_eq_true]
  constructor
  · rintro ⟨bit, present, equal⟩
    cases bit
    · contradiction
    · exact ⟨true, present, rfl⟩
  · rintro ⟨bit, present, equal⟩
    cases bit
    · contradiction
    · exact ⟨true, present, rfl⟩

def word (bit : Bool) : Word := BitVec.ofNat 64 (code bit)

def probeCost (bits : List Bool) : ℕ := 3 * NativeRoleGate.probes 1 (bits.map code)

def placement (image : NativeImage.View) (start absent found joined : ℕ) {pointer : Word}
    (spots : List (WordAt pointer)) : Prop :=
  NativeRoleGate.Placed image found start absent spots ∧
  NativeDecisions.Placed image 8 joined absent (.leaf 0) ∧
  NativeDecisions.Placed image 8 joined found (.leaf 1)

abbrev probesClobber : Finset Register := {.rax, .r8, .rflags, .rip}

theorem probes_clobber_data : probesClobber ⊆ dataRegisters := by decide

theorem fetched_disjunction (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start absent found joined : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before)
    {pointer : Word} (spots : List (WordAt pointer)) (bits : List Bool)
    (placed : placement image start absent found joined spots)
    (values : resident spots before (bits.map code))
    (baseRead : lookup before 6 = some pointer) (ones : lookup before 2 = some 1) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (probeCost bits + 2)).run before = .ok () after ∧
      X86StateFrame.Frame probesClobber ∅ before after ∧
      lookup after 8 = some (word (bits.any id)) ∧ Nonempty (At image after base joined) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨tested, read, frame, ⟨arrived⟩⟩ := NativeRoleGate.scan_fetches other extra vector placed.1 1
    (by decide) point controls baseRead ones values
  cases foundBit : bits.any id with
  | false =>
    have atNo : At image tested base absent := by simpa [hit_iff, foundBit] using arrived
    obtain ⟨after, ran, body, value, continuation⟩ := NativeDecisions.fetched
      (X86FrameLoad.linkedHandlers other) extra vector 8 (.leaf 0) (fun _ => 0) atNo placed.2.1
      (fun _ impossible => (Finset.notMem_empty _ impossible).elim)
    refine ⟨after, X86FuelPrefix.fetches_then _ 2 before tested after read ran,
      (frame.trans body).mono (by decide) (by simp), value, continuation⟩
  | true =>
    have atYes : At image tested base found := by simpa [hit_iff, foundBit] using arrived
    obtain ⟨after, ran, body, value, continuation⟩ := NativeDecisions.fetched
      (X86FrameLoad.linkedHandlers other) extra vector 8 (.leaf 1) (fun _ => 0) atYes placed.2.2
      (fun _ impossible => (Finset.notMem_empty _ impossible).elim)
    refine ⟨after, X86FuelPrefix.fetches_then _ 2 before tested after read ran,
      (frame.trans body).mono (by decide) (by simp), value, continuation⟩

/-- A computed child disjunction is stored as the parent's bit.
Earlier bits and every byte outside that qword stay unchanged. -/
theorem fetched_application (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start absent found atStore : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before)
    {pointer : Word} (spots : List (WordAt pointer)) (bits : List Bool)
    (placed : placement image start absent found atStore spots)
    (values : resident spots before (bits.map code))
    (baseRead : lookup before 6 = some pointer) (ones : lookup before 2 = some 1)
    (target : WordAt pointer) (space : atStore + 7 ≤ image.size)
    (store : Code image atStore (storeEncoding.bytes 8 target.offset))
    (apart : CodeApart image base (footprint target.cell.address))
    (childrenKept : ∀ spot ∈ spots, Disjoint (footprint spot.cell.address) (footprint target.cell.address)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (probeCost bits + 3)).run before = .ok () after ∧
      X86StateFrame.Frame probesClobber (footprint target.cell.address) before after ∧
      Reads after target.cell.address (word (bits.any id)) ∧
      resident spots after (bits.map code) ∧ Nonempty (At image after base (atStore + 7)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨ready, probed, frame, bit, ⟨next⟩⟩ := fetched_disjunction other extra vector point controls
    spots bits placed values baseRead ones
  obtain ⟨after, stored, final, written, endpoint⟩ := X86PlacedMemory.stores
    (handlers other extra) vector next (controls.transport frame probes_clobber_data)
    storeEncoding 8 target.offset pointer (word (bits.any id)) target.cell
    ((frame.lookup 6 (by decide)).trans baseRead) bit space store apart
  have all : X86StateFrame.Frame probesClobber (footprint target.cell.address) before after :=
    (frame.trans final).mono (by simp) (by simp)
  exact ⟨after, X86FuelPrefix.fetches_then _ 1 before ready after probed stored, all, written,
    NativeRoleGate.resident_kept values all childrenKept, endpoint⟩

/-- The native cell contains the semantic occurrence test for the packed
application, not a Boolean supplied by the caller. -/
theorem fetched_packed_application
    {σ : Mettapedia.Logic.LP.LPSignature} [DecidableEq σ.vars]
    (symbols : UnifierHeaders.Symbols σ) (variableName : σ.vars) (query : Word)
    (key : symbols.vars.encode variableName = some query)
    (earlier : Array (Mettapedia.Logic.LP.Term σ)) (header : UnifierHeaders.Header)
    (children : Array Word) (term : Mettapedia.Logic.LP.Term σ)
    (application : header.tag = 2)
    (formed : PackedTerms.build symbols earlier header children = some term)
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start absent found atStore : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before)
    {pointer : Word} (spots : List (WordAt pointer)) (bits : List Bool)
    (selected : PackedOccurs.childrenBits (earlier.map fun t => t.occursIn variableName) children = some bits)
    (placed : placement image start absent found atStore spots)
    (values : resident spots before (bits.map code))
    (baseRead : lookup before 6 = some pointer) (ones : lookup before 2 = some 1)
    (target : WordAt pointer) (space : atStore + 7 ≤ image.size)
    (store : Code image atStore (storeEncoding.bytes 8 target.offset))
    (apart : CodeApart image base (footprint target.cell.address))
    (childrenKept : ∀ spot ∈ spots, Disjoint (footprint spot.cell.address) (footprint target.cell.address)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (probeCost bits + 3)).run before = .ok () after ∧
      X86StateFrame.Frame probesClobber (footprint target.cell.address) before after ∧
      Reads after target.cell.address (word (term.occursIn variableName)) ∧
      resident spots after (bits.map code) ∧ Nonempty (At image after base (atStore + 7)) := by
  have exactBit := PackedOccurs.mark_exact symbols variableName query key earlier header children formed
  simp [PackedOccurs.mark, application, selected] at exactBit
  obtain ⟨after, run, frame, written, kept, endpoint⟩ := fetched_application other extra vector point controls
    spots bits placed values baseRead ones target space store apart childrenKept
  exact ⟨after, run, frame, exactBit ▸ written, kept, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeOccurs
