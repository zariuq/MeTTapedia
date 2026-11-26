import Mettapedia.Machines.TIsa.StoreInstructions.NativePendingCount
import Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaReserve

/-!
# Reserving the remapped agenda suffix

The exact pending count has already been computed. A subtract
then compare guards the new extent before any writes or
addition. Two copies of the resulting ordinal serve different
roles: the retained final extent and the descending write cursor.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativePendingReserve

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads)
open X86PlacedScalar (Code CompareBranch registerCode)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def capacityCode : List ℕ := X86DataLoad.code true 10 6 16
def capacityWire : NativeWords.Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 10, by decide, by decide⟩
def subtractCode : List ℕ := registerCode (X86Arithmetic.opcode .sub) 14 10
def floorCode : List ℕ := registerCode 0x89 14 3
def addCode : List ℕ := registerCode (X86Arithmetic.opcode .add) 0 14
def endCode : List ℕ := registerCode 0x89 14 0

def emit (start exhausted : ℕ) : List ℕ :=
  NativeAgendaRead.baseCode ++ (capacityCode ++ (subtractCode ++
    (NativeDecisions.compareBytes .lessEqualUnsigned 0 10 (start + 13) exhausted ++
      (floorCode ++ (addCode ++ endCode)))))

theorem emit_size (start exhausted : ℕ) : (emit start exhausted).length = 31 := rfl

structure Placed (image : NativeImage.View) (start exhausted : ℕ) : Prop where
  extent : start + 31 ≤ image.size
  base : Code image start NativeAgendaRead.baseCode
  capacity : Code image (start + 3) capacityCode
  subtract : Code image (start + 10) subtractCode
  check : CompareBranch image (start + 13) exhausted .lessEqualUnsigned 0 10
  floor : Code image (start + 22) floorCode
  add : Code image (start + 25) addCode
  retain : Code image (start + 28) endCode

theorem placed_of_emitted (image : NativeImage.View) (start exhausted : ℕ)
    (space : start + 31 ≤ image.size) (lack : exhausted ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit start exhausted)) : Placed image start exhausted := by
  obtain ⟨base, rest⟩ := NativeWords.code_append (show Code image start (NativeAgendaRead.baseCode ++ _) from code)
  obtain ⟨limit, rest⟩ := NativeWords.code_append rest
  obtain ⟨subtract, rest⟩ := NativeWords.code_append rest
  change Code image (start + 13) _ at rest
  obtain ⟨check, rest⟩ := NativeWords.code_append rest
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨floor, rest⟩ := NativeWords.code_append rest
  obtain ⟨add, retain⟩ := NativeWords.code_append rest
  exact ⟨space, base, limit, subtract, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) lack short check,
    floor, add, retain⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rax, .rbx, .rsi, .r10, .r14, .rflags, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {capacity : ℕ} {layout : NativeAgendaRecords.Layout capacity} {arena : PackedEquations.Arena}

/-- Success returns the actual interval of writable equation
ordinals. Exhaustion branches without altering either the old
agenda or any part of a future suffix. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start exhausted : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start exhausted)
    (live : NativeAgendaRecords.Ready layout arena before) (agenda : lookup before 5 = some layout.words.pointer)
    (limit : Reads before (layout.metadata.cell 2).address (BitVec.ofNat 64 capacity))
    (oldLen : lookup before 14 = some (BitVec.ofNat 64 arena.size))
    (width : Word) (requested : lookup before 0 = some width) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧
      if arena.size + width.toNat ≤ capacity then
        steps = 8 ∧ lookup after 3 = some (BitVec.ofNat 64 arena.size) ∧
        lookup after 14 = some (BitVec.ofNat 64 (arena.size + width.toNat)) ∧
        lookup after 0 = some (BitVec.ofNat 64 (arena.size + width.toNat)) ∧
        Nonempty (At image after base (start + 31))
      else steps = 5 ∧ Nonempty (At image after base exhausted) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  obtain ⟨a, based, move, pointer, ⟨atLoad⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 5 6 layout.words.pointer agenda placed.base
  have metadata : layout.metadata.pointer = layout.words.pointer := BitVec.add_zero _
  obtain ⟨b, loaded, loadFrame, cap, ⟨atSubtract⟩⟩ := (NativeAgendaRead.fieldSource layout.metadata 2).fetch
    (handlers other extra) vector capacityWire (BitVec.ofNat 64 capacity) atLoad
    (controls.transport (X86StateFrame.registerOnly move) (by decide))
    (metadata.symm ▸ pointer) (limit.preserved (X86StateFrame.registerOnly move) (by simp))
    (show start + 10 ≤ image.size by omega) placed.capacity
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  rw [linked] at loaded
  have afterLoad := (X86StateFrame.registerOnly move).trans loadFrame
  obtain ⟨c, subtracted, sub, difference, ⟨atCheck⟩⟩ := X86PlacedArithmetic.executes
    (handlers other extra) vector (show At image b base (start + 10) from atSubtract) (by omega) .sub 14 10
    (BitVec.ofNat 64 capacity) (BitVec.ofNat 64 arena.size) ((afterLoad.lookup 14 (by decide)).trans oldLen) cap
    placed.subtract
  have arithmetic : X86Arithmetic.linkedHandlers (handlers other extra) = handlers other extra := rfl
  rw [arithmetic] at subtracted
  let remaining := BitVec.ofNat 64 capacity - BitVec.ofNat 64 arena.size
  have availability : remaining.toNat = capacity - arena.size := NativeAgendaReserve.free_exact live
  have beforeCheck := afterLoad.trans (X86StateFrame.registerOnly sub)
  obtain ⟨d, checked, guard, ⟨verdict⟩⟩ := X86PlacedScalar.compare_branch
    (X86PlacedFrameAddress.nativeBase other) extra vector (show At image c base (start + 13) from atCheck)
    .lessEqualUnsigned 0 10 placed.check width remaining ((beforeCheck.lookup 0 (by decide)).trans requested) difference
  change At image d base (if decide (width.toNat ≤ remaining.toNat) then start + 22 else exhausted) at verdict
  rw [availability] at verdict
  have capacityLaw : width.toNat ≤ capacity - arena.size ↔ arena.size + width.toNat ≤ capacity := by
    have h := live.fits
    omega
  simp only [capacityLaw, decide_eq_true_eq] at verdict
  have throughCheck := beforeCheck.trans (X86StateFrame.registerOnly guard)
  have firstFive := X86FuelPrefix.fetches_then 3 2 before c d
    (X86FuelPrefix.fetches_then 2 1 before b c (X86FuelPrefix.fetches_then 1 1 before a b based loaded) subtracted) checked
  by_cases fits : arena.size + width.toNat ≤ capacity
  · simp only [if_pos fits] at verdict
    obtain ⟨e, copied, copyFrame, first, ⟨atAdd⟩⟩ := X86PlacedRegisterMove.executes
      (handlers other extra) vector verdict (by omega) 14 3 (BitVec.ofNat 64 arena.size)
      ((throughCheck.lookup 14 (by decide)).trans oldLen) placed.floor
    have beforeAdd := throughCheck.trans (X86StateFrame.registerOnly copyFrame)
    obtain ⟨f, added, addFrame, ordinal, ⟨atRetain⟩⟩ := X86PlacedArithmetic.executes
      (handlers other extra) vector (show At image e base (start + 25) from atAdd) (by omega) .add 0 14
      (BitVec.ofNat 64 arena.size) width ((beforeAdd.lookup 0 (by decide)).trans requested)
      ((beforeAdd.lookup 14 (by decide)).trans oldLen) placed.add
    rw [arithmetic] at added
    have exactOrdinal : lookup f 14 = some (BitVec.ofNat 64 (arena.size + width.toNat)) := by
      have exactWidth : BitVec.ofNat 64 width.toNat = width := by simp
      rwa [← BitVec.ofNat_add_ofNat, exactWidth]
    obtain ⟨after, retained, retainFrame, final, endpoint⟩ := X86PlacedRegisterMove.executes
      (handlers other extra) vector (show At image f base (start + 28) from atRetain) (by omega) 14 0
      (BitVec.ofNat 64 (arena.size + width.toNat)) exactOrdinal placed.retain
    have trace := X86FuelPrefix.fetches_then 7 1 before f after
      (X86FuelPrefix.fetches_then 6 1 before e f (X86FuelPrefix.fetches_then 5 1 before d e firstFive copied) added) retained
    refine ⟨after, 8, trace, (beforeAdd.trans (X86StateFrame.registerOnly (addFrame.trans retainFrame))).mono
      (by decide) (by simp), ?_⟩
    rw [if_pos fits]
    exact ⟨rfl, ((addFrame.trans retainFrame).lookup 3 (by decide)).trans first,
      (retainFrame.lookup 14 (by decide)).trans exactOrdinal, final, endpoint⟩
  · simp only [if_neg fits] at verdict
    refine ⟨d, 5, firstFive, throughCheck.mono (by decide) (by simp), ?_⟩
    rw [if_neg fits]
    exact ⟨rfl, ⟨verdict⟩⟩

def emitPreparation (start exhausted malformed : ℕ) : List ℕ :=
  NativePendingCount.emit start (start + 72) malformed ++ emit (start + 72) exhausted

theorem emitPreparation_size (start exhausted malformed : ℕ) : (emitPreparation start exhausted malformed).length = 103 := by
  simp only [emitPreparation, List.length_append, NativePendingCount.emit_size, emit_size]

structure Preparation (image : NativeImage.View) (start exhausted malformed : ℕ) : Prop where
  count : NativePendingCount.Placed image start (start + 72) malformed
  reserve : Placed image (start + 72) exhausted

theorem preparation_placed (image : NativeImage.View) (start exhausted malformed : ℕ)
    (extent : start + 103 ≤ image.size) (lack : exhausted ≤ image.size) (bad : malformed ≤ image.size)
    (short : image.size < 2 ^ 31) (code : Code image start (emitPreparation start exhausted malformed)) :
    Preparation image start exhausted malformed := by
  obtain ⟨count, reserve⟩ := NativeWords.code_append (show Code image start
    (NativePendingCount.emit start (start + 72) malformed ++ _) from code)
  rw [NativePendingCount.emit_size] at reserve
  exact ⟨NativePendingCount.placed_of_emitted image _ _ malformed (by omega) (by omega) bad short count,
    placed_of_emitted image _ exhausted (by omega) lack short reserve⟩

/-- Plan the whole replacement suffix before its first write.
The same source cursor can start the fill pass; the observed
prefix is unchanged even when the size check fails. -/
theorem fetched_prepare (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start exhausted malformed : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (code : Preparation image start exhausted malformed)
    (root : Word) (pending : List (Word × Word)) (loaded : PackedEquations.readWords arena root = some pending)
    (live : NativeAgendaRecords.Ready layout arena before) (original : lookup before 11 = some root)
    (agenda : lookup before 5 = some layout.words.pointer)
    (zero : lookup before 12 = some 0) (one : lookup before 13 = some 1)
    (limit : Reads before (layout.metadata.cell 2).address (BitVec.ofNat 64 capacity)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame (NativePendingCount.clobbers ∪ clobbers) ∅ before after ∧
      NativeAgendaRecords.Ready layout arena after ∧ lookup after 11 = some root ∧
      if arena.size + pending.length ≤ capacity then
        steps = 13 * pending.length + 14 ∧ lookup after 3 = some (BitVec.ofNat 64 arena.size) ∧
        lookup after 14 = some (BitVec.ofNat 64 (arena.size + pending.length)) ∧
        lookup after 0 = some (BitVec.ofNat 64 (arena.size + pending.length)) ∧
        Nonempty (At image after base (start + 103))
      else steps = 13 * pending.length + 11 ∧ Nonempty (At image after base exhausted) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨a, counted, countFrame, width, actual, rootKept, liveCount, ⟨next⟩⟩ :=
    NativePendingCount.fetched other extra vector point controls code.count root pending loaded live original agenda zero one
  obtain ⟨after, tests, checked, testFrame, decision⟩ := fetched other extra vector next
    (controls.transport countFrame (by decide)) code.reserve (live.preserved countFrame)
    ((countFrame.lookup 5 (by decide)).trans agenda) (limit.preserved countFrame (by simp)) liveCount _ width
  rw [actual] at decision
  have both := (countFrame.trans testFrame).mono (Finset.Subset.refl _) (by simp : (∅ ∪ ∅ : Finset ℕ) ⊆ ∅)
  have executed := X86FuelPrefix.fetches_then (13 * pending.length + 6) tests before a after counted checked
  refine ⟨after, _, executed, both, live.preserved both, (testFrame.lookup 11 (by decide)).trans rootKept, ?_⟩
  by_cases fits : arena.size + pending.length ≤ capacity
  · rw [if_pos fits] at decision ⊢
    exact ⟨by omega, decision.2⟩
  · rw [if_neg fits] at decision ⊢
    exact ⟨by omega, decision.2⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativePendingReserve
