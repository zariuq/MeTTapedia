import Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardWorkspace

/-!
# Fetching one occurrence of a normalized guard

The directory has one slot per occurrence, not per distinct
term handle. The ordinal is checked before it is scaled.
The pattern is shared across the whole scan.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardOperands

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Reads Controls)
open X86PlacedScalar (Code CompareBranch registerCode)
open NativeGuardWorkspace (Frame)
open NativeArenaGeometry (Region)
open NativeSubstLeaf (MapReady)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def stackCode : List ℕ := registerCode 0x89 4 6
def indexCode : List ℕ := X86DataLoad.code true 1 6 112
def countCode : List ℕ := X86DataLoad.code true 10 6 104
def pointerCode : List ℕ := X86DataLoad.code true 2 6 96
def patternCode : List ℕ := X86DataLoad.code true 1 6 88
def indexWire : NativeWords.Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 1, by decide, by decide⟩
def countWire : NativeWords.Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 10, by decide, by decide⟩
def pointerWire : NativeWords.Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 2, by decide, by decide⟩
def directoryRegister : X86IndexedAddress.Base := ⟨2, by decide⟩
def indexRegister : X86PreparedLea.Index := ⟨1, by decide⟩

def emit (start done : ℕ) : List ℕ :=
  stackCode ++ (indexCode ++ (countCode ++ (NativeDecisions.compareBytes .lessUnsigned 1 10 (start + 17) done ++
    (pointerCode ++ (NativeIndexedWord.loadToCode directoryRegister indexRegister 2 ++ patternCode)))))

theorem emit_size (start done : ℕ) : (emit start done).length = 51 := rfl

structure Placed (image : NativeImage.View) (start done : ℕ) : Prop where
  extent : start + 51 ≤ image.size
  stack : Code image start stackCode
  loadIndex : Code image (start + 3) indexCode
  loadCount : Code image (start + 10) countCode
  check : CompareBranch image (start + 17) done .lessUnsigned 1 10
  pointer : Code image (start + 26) pointerCode
  value : Code image (start + 33) (NativeIndexedWord.loadToCode directoryRegister indexRegister 2)
  pattern : Code image (start + 44) patternCode

theorem placed_of_emitted (image : NativeImage.View) (start done : ℕ) (extent : start + 51 ≤ image.size)
    (finish : done ≤ image.size) (short : image.size < 2 ^ 31) (code : Code image start (emit start done)) :
    Placed image start done := by
  obtain ⟨stack, tail⟩ := NativeWords.code_append (show Code image start (stackCode ++ _) from code)
  obtain ⟨loadIndex, tail⟩ := NativeWords.code_append tail
  obtain ⟨loadCount, tail⟩ := NativeWords.code_append tail
  change Code image (start + 17) _ at tail
  obtain ⟨check, tail⟩ := NativeWords.code_append tail
  rw [NativeDecisions.compare_size] at tail
  obtain ⟨pointer, tail⟩ := NativeWords.code_append tail
  obtain ⟨value, pattern⟩ := NativeWords.code_append tail
  rw [NativeIndexedWord.load_to_size] at pattern
  exact ⟨extent, stack, loadIndex, loadCount,
    NativeDecisions.compare_placed image _ _ _ _ _ (by omega) finish short check, pointer, value, pattern⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rcx, .rdx, .rsi, .r10, .rflags, .rip}
theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

structure Directory {capacity : ℕ} (table : Region capacity) (frame : Frame)
    (pattern : Word) (handles : Array Word) (native : Native) : Prop where
  pattern : Reads native (frame.cell 11).address pattern
  pointer : Reads native (frame.cell 12).address (table.atWord 0)
  count : Reads native (frame.cell 13).address (BitVec.ofNat 64 handles.size)
  occurrences : MapReady table handles native

variable {capacity : ℕ} {table : Region capacity} {frame : Frame} {handles : Array Word}

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start done : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (code : Placed image start done)
    (stack : lookup before 4 = some frame.pointer) (needle : Word) (index : ℕ)
    (cursor : Reads before (frame.cell 14).address (BitVec.ofNat 64 index))
    (directory : Directory table frame needle handles before) (indexBound : index ≤ handles.size) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after count, (X86FuelPrefix.fetches count).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧
      if inside : index < handles.size then
        count = 9 ∧ lookup after 1 = some needle ∧ lookup after 2 = some handles[index] ∧
        Nonempty (At image after base (start + 51))
      else count = 5 ∧ Nonempty (At image after base done) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let offset := BitVec.ofNat 64 index
  have extent := code.extent
  have countExact := NativeSubstitutionReserve.word_of_region table handles.size directory.occurrences.fits
  have indexExact : offset.toNat = index :=
    NativeSubstitutionReserve.word_of_region table index (indexBound.trans directory.occurrences.fits)
  obtain ⟨a, opened, openedFrame, stackPointer, ⟨atIndex⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 4 6 frame.pointer stack code.stack
  have first := X86StateFrame.registerOnly openedFrame
  obtain ⟨b, loadedIndex, indexFrame, knownIndex, ⟨atCount⟩⟩ := (NativeAgendaRead.fieldSource frame 14).fetch
    (handlers other extra) vector indexWire offset atIndex (controls.transport first (by decide)) stackPointer
    (cursor.preserved first (by simp)) (show start + 10 ≤ image.size by omega) code.loadIndex
  have two := first.trans indexFrame
  obtain ⟨c, loadedCount, countFrame, knownCount, ⟨atTest⟩⟩ := (NativeAgendaRead.fieldSource frame 13).fetch
    (handlers other extra) vector countWire (BitVec.ofNat 64 handles.size) (show At image b base (start + 10) from atCount)
    (controls.transport two (by decide)) ((indexFrame.lookup 6 (by decide)).trans stackPointer)
    (directory.count.preserved two (by simp)) (show start + 17 ≤ image.size by omega) code.loadCount
  have three := two.trans countFrame
  obtain ⟨d, tested, testFrame, ⟨decision⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
    extra vector (show At image c base (start + 17) from atTest) .lessUnsigned 1 10 code.check offset _
    ((countFrame.lookup 1 (by decide)).trans knownIndex) knownCount
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  rw [linked] at loadedIndex loadedCount
  have prelude := X86FuelPrefix.fetches_then 3 2 before c d (X86FuelPrefix.fetches_then 2 1 before b c
    (X86FuelPrefix.fetches_then 1 1 before a b opened loadedIndex) loadedCount) tested
  have scanned := three.trans (X86StateFrame.registerOnly testFrame)
  change At image d base (if decide (offset.toNat < (BitVec.ofNat 64 handles.size).toNat) then start + 26 else done) at decision
  rw [indexExact, countExact] at decision
  by_cases inside : index < handles.size
  · have live : At image d base (start + 26) := by simpa [inside] using decision
    obtain ⟨e, followed, pointerFrame, pointer, ⟨atFetch⟩⟩ := (NativeAgendaRead.fieldSource frame 12).fetch
      (handlers other extra) vector pointerWire (table.atWord 0) live (controls.transport scanned (by decide))
      (((indexFrame.trans countFrame).trans (X86StateFrame.registerOnly testFrame)).lookup 6 (by decide) |>.trans stackPointer)
      (directory.pointer.preserved scanned (by simp)) (show start + 33 ≤ image.size by omega) code.pointer
    rw [linked] at followed
    have beforeRead : X86StateFrame.Frame clobbers ∅ before e := (scanned.trans pointerFrame).mono (by decide) (by simp)
    have inTable : 0 + offset.toNat < capacity := by rw [Nat.zero_add, indexExact]; exact inside.trans_le directory.occurrences.fits
    have slot : (⟨0 + offset.toNat, inTable⟩ : Fin capacity) =
        ⟨index, inside.trans_le directory.occurrences.fits⟩ := Fin.ext ((Nat.zero_add _).trans indexExact)
    have resident := (directory.occurrences.read ⟨index, inside⟩).preserved beforeRead (by simp)
    obtain ⟨f, read, readFrame, rightWord, ⟨atPattern⟩⟩ := NativeIndexedWord.fetched_load_to other extra vector
      (show At image e base (start + 33) from atFetch) (controls.transport beforeRead clobbers_data) (by omega)
      directoryRegister indexRegister 2 (by decide) table 0 offset handles[index] inTable pointer
      (((countFrame.trans (X86StateFrame.registerOnly testFrame)).trans pointerFrame).lookup 1 (by decide) |>.trans knownIndex)
      (by rw [slot]; exact resident) code.value
    have throughRead := beforeRead.trans readFrame
    have fromStack := (((indexFrame.trans countFrame).trans (X86StateFrame.registerOnly testFrame)).trans pointerFrame).trans readFrame
    have baseStillThere := (fromStack.lookup 6 (by decide)).trans stackPointer
    obtain ⟨after, patternRead, patternFrame, leftWord, endpoint⟩ := (NativeAgendaRead.fieldSource frame 11).fetch
      (handlers other extra) vector indexWire needle (show At image f base (start + 44) from atPattern)
      (controls.transport throughRead (by decide))
      baseStillThere (directory.pattern.preserved throughRead (by simp)) extent code.pattern
    rw [linked] at patternRead
    have run := X86FuelPrefix.fetches_then 8 1 before f after
      (X86FuelPrefix.fetches_then 6 2 before e f (X86FuelPrefix.fetches_then 5 1 before d e prelude followed) read) patternRead
    refine ⟨after, 9, run, (throughRead.trans patternFrame).mono (by decide) (by simp), ?_⟩
    rw [dif_pos inside]
    exact ⟨rfl, leftWord, (patternFrame.lookup 2 (by decide)).trans rightWord, endpoint⟩
  · have finished : At image d base done := by simpa [inside] using decision
    refine ⟨d, 5, prelude, scanned.mono (by decide) (by simp), ?_⟩
    rw [dif_neg inside]
    exact ⟨rfl, ⟨finished⟩⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardOperands
