import Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionReserve
import Mettapedia.Machines.TIsa.StoreInstructions.NativeRemapSnapshot

/-!
# Addressing the reserved edge suffix

Use the edge base in the agenda metadata and the checked staged
ordinal, not an address supplied by the caller. This short block
temporarily lends RBX to the copy loop.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionCopyEntry

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads footprint)
open X86PlacedScalar (Code registerCode)
open NativeAgendaRead (fieldSource)
open NativeArenaGeometry (Region)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def contextCode : List ℕ := registerCode 0x89 5 0
def poolCode : List ℕ := X86DataLoad.code true 3 0 8
def cursorCode : List ℕ := registerCode 0x89 10 0
def edgeIndex : X86PreparedLea.Index := ⟨0, by decide⟩
def edgeBase : X86IndexedAddress.Base := ⟨3, by decide⟩
def addressCode : List ℕ := X86IndexedAddress.addressCode 3 edgeIndex 3 edgeBase

def emit : List ℕ := contextCode ++ (poolCode ++ (cursorCode ++ addressCode))

theorem emit_size : emit.length = 17 := rfl

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rax, .rbx, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

def wire : NativeWords.Wiring :=
  ⟨0, by decide, by decide, MemoryBinding.storeEncoding, 3, by decide, by decide⟩

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (room : start + 17 ≤ image.size)
    (code : Code image start emit)
    {agendaCapacity edgeCapacity : ℕ} (agenda : NativeAgendaRecords.Layout agendaCapacity) (edges : Region edgeCapacity)
    (ordinal : ℕ) (fits : ordinal ≤ edgeCapacity)
    (baseRead : lookup before 5 = some agenda.words.pointer)
    (pool : Reads before (agenda.metadata.cell 1).address edges.pointer)
    (cursor : lookup before 10 = some (BitVec.ofNat 64 ordinal)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧ lookup after 3 = some (edges.atWord ordinal) ∧
      Nonempty (At image after base (start + 17)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨context, tail⟩ := NativeWords.code_append (show Code image start (contextCode ++ _) from code)
  obtain ⟨placedPool, tail⟩ := NativeWords.code_append tail
  obtain ⟨placedCursor, placedAddress⟩ := NativeWords.code_append tail
  obtain ⟨a, opened, regFrame, baseValue, ⟨atPool⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 5 0 agenda.words.pointer baseRead context
  have first := X86StateFrame.registerOnly regFrame
  have exactBase : agenda.metadata.pointer = agenda.words.pointer := BitVec.add_zero _
  obtain ⟨b, loaded, loadFrame, edgePointer, ⟨atCursor⟩⟩ := (fieldSource agenda.metadata 1).fetch
    (handlers other extra) vector wire edges.pointer atPool (controls.transport first (by decide))
    (exactBase.symm ▸ baseValue) (pool.preserved first (by simp)) (show start + 10 ≤ image.size by omega) placedPool
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  rw [linked] at loaded
  have throughLoad := first.trans loadFrame
  obtain ⟨c, moved, cursorFrame, edgeIndexWord, ⟨atAddress⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector (show At image b base (start + 10) from atCursor) (by omega)
    10 0 (BitVec.ofNat 64 ordinal) ((throughLoad.lookup 10 (by decide)).trans cursor) placedCursor
  obtain ⟨after, located, addressFrame, pointer, endpoint⟩ := X86IndexedAddress.forms_address other extra vector
    (show At image c base (start + 13) from atAddress) room 3 edgeIndex 3 edgeBase placedAddress
    edges.pointer (BitVec.ofNat 64 ordinal) ((cursorFrame.lookup 3 (by decide)).trans edgePointer) edgeIndexWord
  have looked : lookup after 3 = some (edges.atWord ordinal) := by
    have scaled := NativeArenaGeometry.word_scale8 (BitVec.ofNat 64 ordinal)
    rw [NativeSubstitutionReserve.word_of_region edges _ fits] at scaled
    unfold Region.atWord
    rw [scaled]
    exact pointer
  have runTwo := X86FuelPrefix.fetches_then 1 1 before a b opened loaded
  have runThree := X86FuelPrefix.fetches_then 2 1 before b c runTwo moved
  exact ⟨after, X86FuelPrefix.fetches_then 3 1 before c after runThree located,
    (throughLoad.trans (X86StateFrame.registerOnly (cursorFrame.trans addressFrame))).mono (by decide) (by simp),
    looked, endpoint⟩

/-- Copying to a fresh suffix preserves every initialized cell
of the staged view, not just those in the original source. -/
theorem target_kept {nodeCapacity edgeCapacity : ℕ} {layout : NativeTermArena.Layout nodeCapacity edgeCapacity}
    {target : PackedTerms.Arena} {before after : Native} {lo hi : ℕ} {reg : Finset Register} {bytes : Finset ℕ}
    (ready : NativeTermArena.Ready layout target before) (run : X86StateFrame.Frame reg bytes before after)
    (fresh : NativeMarkTable.Within layout.edges lo hi bytes) (afterLive : target.children.size ≤ lo)
    (apart : ∀ (i : Fin nodeCapacity) (j : Fin 4) (edge : Fin edgeCapacity),
      Disjoint (footprint ((layout.record i).cell j).address) (footprint ((layout.edges.wordCell edge).cell 0).address)) :
    NativeTermArena.Ready layout target after := by
  refine ⟨ready.nodesFit, ready.edgesFit, fun i j => (ready.node i j).preserved run (fresh.apart _ (apart _ j)), ?_⟩
  intro i
  apply (ready.child i).preserved run
  apply fresh.apart_interval
  intro edge lower _
  apply layout.edges.wordCells_disjoint
  intro same
  have index := congrArg Fin.val same
  change i.val = edge.val at index
  have live := i.isLt
  omega

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionCopyEntry
