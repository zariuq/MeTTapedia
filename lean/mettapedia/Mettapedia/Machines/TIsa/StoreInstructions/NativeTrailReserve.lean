import Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionFrame
import Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaReserve

/-!
# Reserving one entry of the native binding trail

The newest trail entry is its last record, so its live count
is also the root used to decode the trail. The descriptor
adds one trail pointer to the existing substitution frame.
Checking trail capacity does not consume the binding operands.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeTrailReserve

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads)
open X86PlacedScalar (Code CompareBranch registerCode)
open NativeArenaGeometry (Region)
open NativeAgendaRecords (Ready)
open PackedEquations (Arena)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Descriptor := WordRegion.Region 8

def Descriptor.region (frame : Descriptor) : Region 8 := ⟨frame.pointer, frame.aligned, frame.area⟩

def Descriptor.substitution (frame : Descriptor) : NativeSubstitutionFrame.Table :=
  frame.region.slice 0 7 (by decide) (by decide) (by decide)

theorem Descriptor.substitution_pointer (frame : Descriptor) : frame.substitution.pointer = frame.pointer :=
  BitVec.add_zero _

theorem Descriptor.substitution_cell (frame : Descriptor) (i : Fin 7) :
    (frame.substitution.cell i).address = (frame.cell ⟨i.val, by have := i.isLt; omega⟩).address := by
  simp only [Descriptor.substitution, Region.slice_address, Nat.zero_add]
  rfl

def stackCode : List ℕ := registerCode 0x89 4 6
def pointerCode : List ℕ := X86DataLoad.code true 2 6 56
def headerCode : List ℕ := X86DataLoad.code true 14 2 0 ++ X86DataLoad.code true 0 2 16
def pointerWire : NativeWords.Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 2, by decide, by decide⟩
def trailBase : NativeLoads.Base := ⟨2, by decide, by decide⟩

def emit (start exhausted : ℕ) : List ℕ :=
  stackCode ++ (pointerCode ++ (headerCode ++ NativeDecisions.compareBytes .lessUnsigned 14 0 (start + 24) exhausted))

theorem emit_size (start exhausted : ℕ) : (emit start exhausted).length = 33 := rfl

structure Placed (image : NativeImage.View) (start exhausted : ℕ) : Prop where
  extent : start + 33 ≤ image.size
  stack : Code image start stackCode
  pointer : Code image (start + 3) pointerCode
  header : Code image (start + 10) headerCode
  test : CompareBranch image (start + 24) exhausted .lessUnsigned 14 0

theorem placed_of_emitted (image : NativeImage.View) (start exhausted : ℕ)
    (extent : start + 33 ≤ image.size) (lack : exhausted ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit start exhausted)) : Placed image start exhausted := by
  obtain ⟨stack, rest⟩ := NativeWords.code_append (show Code image start (stackCode ++ _) from code)
  obtain ⟨pointer, rest⟩ := NativeWords.code_append rest
  obtain ⟨header, test⟩ := NativeWords.code_append rest
  exact ⟨extent, stack, pointer, header, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) lack short test⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rax, .rdx, .rsi, .r14, .rflags, .rip}
theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {capacity : ℕ} {layout : NativeAgendaRecords.Layout capacity} {arena : Arena}

private def liveLoad (layout : NativeAgendaRecords.Layout capacity) (arena : Arena) :
    NativeLoads.Load trailBase layout.metadata.pointer :=
  ⟨14, by decide, 0, layout.metadata.cell 0, BitVec.ofNat 64 arena.size⟩

private def limitLoad (layout : NativeAgendaRecords.Layout capacity) : NativeLoads.Load trailBase layout.metadata.pointer :=
  ⟨0, by decide, 16, layout.metadata.cell 2, BitVec.ofNat 64 capacity⟩

private def loads (layout : NativeAgendaRecords.Layout capacity) (arena : Arena) :
    List (NativeLoads.Load trailBase layout.metadata.pointer) :=
  [liveLoad layout arena, limitLoad layout]

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start exhausted : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start exhausted)
    (frame : Descriptor) (stack : lookup before 4 = some frame.pointer) (live : Ready layout arena before)
    (trail : Reads before (frame.cell 7).address layout.words.pointer)
    (limit : Reads before (layout.metadata.cell 2).address (BitVec.ofNat 64 capacity)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 6).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧
      lookup after 2 = some layout.words.pointer ∧ lookup after 14 = some (BitVec.ofNat 64 arena.size) ∧
      Nonempty (At image after base (if arena.size < capacity then start + 33 else exhausted)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  obtain ⟨a, moved, stackFrame, stackBase, ⟨atTrail⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 4 6 frame.pointer stack placed.stack
  have movedFrame := X86StateFrame.registerOnly stackFrame
  obtain ⟨b, followed, trailFrame, trailBaseWord, ⟨atHeader⟩⟩ := (NativeAgendaRead.fieldSource frame 7).fetch
    (handlers other extra) vector pointerWire layout.words.pointer atTrail (controls.transport movedFrame (by decide))
    stackBase (trail.preserved movedFrame (by simp)) (show start + 10 ≤ image.size by omega) placed.pointer
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  rw [linked] at followed
  have throughPtr := movedFrame.trans trailFrame
  have placement : layout.metadata.pointer = layout.words.pointer := BitVec.add_zero _
  have resident (move : NativeLoads.Load trailBase layout.metadata.pointer) (present : move ∈ loads layout arena) :
      Reads b move.cell.address move.value := by
    simp only [loads, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact live.count.preserved throughPtr (by simp)
    · exact limit.preserved throughPtr (by simp)
  obtain ⟨c, headers, readFrame, values, ⟨atTest⟩⟩ := NativeLoads.fetched other extra vector
    (show At image b base (start + 10) from atHeader) (controls.transport throughPtr (by decide))
    (loads layout arena) (by change start + 10 + 14 ≤ image.size; omega) placed.header
    (placement.symm ▸ trailBaseWord) resident (by simp [loads, liveLoad, limitLoad])
  have loadEffects : NativeLoads.clobbers (loads layout arena) =
      ({key 14, .rip} ∪ ({key 0, .rip} ∪ ∅) : Finset Register) := rfl
  rw [loadEffects] at readFrame
  obtain ⟨after, tested, cmp, ⟨whereTo⟩⟩ := X86PlacedScalar.compare_branch
    (X86PlacedFrameAddress.nativeBase other) extra vector (show At image c base (start + 24) from atTest)
    .lessUnsigned 14 0 placed.test _ _ (values (liveLoad layout arena) (by simp [loads]))
    (values (limitLoad layout) (by simp [loads]))
  change At image after base (if decide ((BitVec.ofNat 64 arena.size).toNat < (BitVec.ofNat 64 capacity).toNat)
    then start + 24 + 9 else exhausted) at whereTo
  rw [live.count_word, NativeAgendaReserve.capacity_word layout] at whereTo
  simp only [decide_eq_true_eq] at whereTo
  have overall : X86StateFrame.Frame clobbers ∅ before after :=
    ((throughPtr.trans readFrame).trans (X86StateFrame.registerOnly cmp)).mono
      (by decide) (by simp)
  have run := X86FuelPrefix.fetches_then 4 2 before c after
    (X86FuelPrefix.fetches_then 2 2 before b c (X86FuelPrefix.fetches_then 1 1 before a b moved followed) headers) tested
  exact ⟨after, run, overall, ((readFrame.trans (X86StateFrame.registerOnly cmp)).lookup 2
    (by decide)).trans trailBaseWord,
    (cmp.lookup 14 (by decide)).trans (values (liveLoad layout arena) (by simp [loads])), ⟨whereTo⟩⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeTrailReserve
