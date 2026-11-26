import Mettapedia.Machines.TIsa.StoreInstructions.NativeEquationReverse

/-!
# Reserving the work agenda for a resolution TEST

The base and the local equation chains are both counted at
their original heads. Reservation charges occurrences, not
distinct pairs. Both sources still exist on the capacity exit.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeResolveReserve

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads)
open X86PlacedScalar (Code registerCode)
open PackedEquations (Arena readWords)
open PackedWorklist (Words)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def keepNewer : List ℕ := registerCode 0x89 11 8
def keepCount : List ℕ := registerCode 0x89 0 9
def baseRoot : List ℕ := registerCode 0x89 7 11
def sumCode : List ℕ := registerCode (X86Arithmetic.opcode .add) 9 0
def restoreNewer : List ℕ := registerCode 0x89 8 11
def stageLength : List ℕ := registerCode 0x89 3 14
def emptyRoot : List ℕ := registerCode 0x89 12 0

def emit (start exhausted malformed : ℕ) : List ℕ :=
  keepNewer ++ (NativePendingCount.emit (start + 3) (start + 75) malformed ++
    (keepCount ++ (baseRoot ++ (NativePendingCount.emit (start + 81) (start + 153) malformed ++
      (sumCode ++ (restoreNewer ++ (NativePendingReserve.emit (start + 159) exhausted ++ (stageLength ++ emptyRoot))))))))

theorem emit_size (start exhausted malformed : ℕ) : (emit start exhausted malformed).length = 196 := by
  simp only [emit, List.length_append, NativePendingCount.emit_size, NativePendingReserve.emit_size, show keepNewer.length = 3 from rfl,
    show keepCount.length = 3 from rfl, show baseRoot.length = 3 from rfl, show sumCode.length = 3 from rfl,
    show restoreNewer.length = 3 from rfl, show stageLength.length = 3 from rfl, show emptyRoot.length = 3 from rfl]

structure Placed (image : NativeImage.View) (start exhausted malformed : ℕ) : Prop where
  extent : start + 196 ≤ image.size
  save : Code image start keepNewer
  newer : NativePendingCount.Placed image (start + 3) (start + 75) malformed
  saveCount : Code image (start + 75) keepCount
  base : Code image (start + 78) baseRoot
  baseCount : NativePendingCount.Placed image (start + 81) (start + 153) malformed
  sum : Code image (start + 153) sumCode
  recover : Code image (start + 156) restoreNewer
  reserve : NativePendingReserve.Placed image (start + 159) exhausted
  stage : Code image (start + 190) stageLength
  empty : Code image (start + 193) emptyRoot

theorem placed_of_emitted (image : NativeImage.View) (start exhausted malformed : ℕ)
    (extent : start + 196 ≤ image.size) (lack : exhausted ≤ image.size)
    (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31) (code : Code image start (emit start exhausted malformed)) :
    Placed image start exhausted malformed := by
  obtain ⟨save, rest⟩ := NativeWords.code_append (show Code image start (keepNewer ++ _) from code)
  obtain ⟨newer, rest⟩ := NativeWords.code_append rest
  rw [NativePendingCount.emit_size] at rest
  obtain ⟨size, rest⟩ := NativeWords.code_append rest
  obtain ⟨base, rest⟩ := NativeWords.code_append rest
  obtain ⟨baseCount, rest⟩ := NativeWords.code_append rest
  rw [NativePendingCount.emit_size] at rest
  obtain ⟨sum, rest⟩ := NativeWords.code_append rest
  obtain ⟨recover, rest⟩ := NativeWords.code_append rest
  obtain ⟨reserve, rest⟩ := NativeWords.code_append rest
  rw [NativePendingReserve.emit_size] at rest
  obtain ⟨stage, empty⟩ := NativeWords.code_append rest
  exact ⟨extent, save, NativePendingCount.placed_of_emitted image _ _ malformed (by omega) (by omega) bad short newer,
    size, base, NativePendingCount.placed_of_emitted image _ _ malformed (by omega) (by omega) bad short baseCount,
    sum, recover, NativePendingReserve.placed_of_emitted image _ exhausted (by omega) lack short reserve, stage, empty⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .r14, .rflags, .rip}
theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {capacity : ℕ} {layout : NativeAgendaRecords.Layout capacity} {arena : Arena}

structure Input (layout : NativeAgendaRecords.Layout capacity) (arena : Arena) (newer older : Word) (before : Native) : Prop where
  current : NativeAgendaRecords.Ready layout arena before
  base : lookup before 5 = some layout.words.pointer
  limit : Reads before (layout.metadata.cell 2).address (BitVec.ofNat 64 capacity)
  newer : lookup before 11 = some newer
  older : lookup before 7 = some older
  zero : lookup before 12 = some 0
  one : lookup before 13 = some 1

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start exhausted malformed : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start exhausted malformed)
    (newerRoot olderRoot : Word) (newer older : Words)
    (input : Input layout arena newerRoot olderRoot before)
    (newerRead : readWords arena newerRoot = some newer) (olderRead : readWords arena olderRoot = some older) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧ X86StateFrame.Frame clobbers ∅ before after ∧
      lookup after 11 = some newerRoot ∧ lookup after 7 = some olderRoot ∧
      if arena.size + (newer.length + older.length) ≤ capacity then
        steps = 13 * (newer.length + older.length) + 27 ∧
        NativeEquationReverse.Input layout arena arena newerRoot 0 after ∧ Nonempty (At image after base (start + 196))
      else steps = 13 * (newer.length + older.length) + 22 ∧ Nonempty (At image after base exhausted) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  obtain ⟨a, saved, save, newerKnown, ⟨atCount⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 11 8 newerRoot input.newer placed.save
  have initial := X86StateFrame.registerOnly save
  obtain ⟨b, counted, count, newerSize, _, _, _, ⟨atSave⟩⟩ := NativePendingCount.fetched other extra vector
    atCount (controls.transport initial (by decide)) placed.newer newerRoot newer newerRead
    (input.current.preserved initial) ((save.lookup 11 (by decide)).trans input.newer)
    ((save.lookup 5 (by decide)).trans input.base) ((save.lookup 12 (by decide)).trans input.zero)
    ((save.lookup 13 (by decide)).trans input.one)
  obtain ⟨c, retained, retain, amount, ⟨atBase⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector atSave (by omega) 0 9 (BitVec.ofNat 64 newer.length) newerSize placed.saveCount
  have throughSave := (initial.trans count).trans (X86StateFrame.registerOnly retain)
  obtain ⟨d, selected, selectFrame, baseCursor, ⟨atSecond⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector (show At image c base (start + 78) from atBase)
    (by omega) 7 11 olderRoot ((throughSave.lookup 7 (by decide)).trans input.older) placed.base
  have beforeSecond : X86StateFrame.Frame
      ( ({key 8, .rip} ∪ NativePendingCount.clobbers) ∪ ({key 9, .rip} ∪ {key 11, .rip}) ) ∅ before d :=
    (throughSave.trans (X86StateFrame.registerOnly selectFrame)).mono (by simp) (by simp)
  obtain ⟨e, countedBase, baseFrame, olderSize, _, _, length, ⟨atAdd⟩⟩ := NativePendingCount.fetched other extra vector
    (show At image d base (start + 81) from atSecond) (controls.transport beforeSecond (by decide)) placed.baseCount
    olderRoot older olderRead (input.current.preserved beforeSecond) baseCursor
    ((beforeSecond.lookup 5 (by decide)).trans input.base) ((beforeSecond.lookup 12 (by decide)).trans input.zero)
    ((beforeSecond.lookup 13 (by decide)).trans input.one)
  have afterSecond := beforeSecond.trans baseFrame
  obtain ⟨f, added, addFrame, result, ⟨atRecover⟩⟩ := X86PlacedArithmetic.executes
    (handlers other extra) vector atAdd (by omega) .add 9 0 (BitVec.ofNat 64 older.length) (BitVec.ofNat 64 newer.length)
    ((baseFrame.lookup 9 (by decide)).trans ((selectFrame.lookup 9 (by decide)).trans amount))
    olderSize placed.sum
  have linked : X86Arithmetic.linkedHandlers (handlers other extra) = handlers other extra := rfl
  rw [linked] at added
  have combined : lookup f 0 = some (BitVec.ofNat 64 (newer.length + older.length)) := by
    change lookup f 0 = some (BitVec.ofNat 64 older.length + BitVec.ofNat 64 newer.length) at result
    rwa [BitVec.ofNat_add_ofNat, Nat.add_comm older.length] at result
  have capSpace := layout.words.positive_room (show 0 < 3 * (capacity + 1) by omega)
  have newerBound := (NativePendingCount.length_le_cursor arena newer newerRoot newerRead).trans
    (PackedEquations.read_bound PackedEquations.wordCodes arena newerRoot newerRead)
  have olderBound := (NativePendingCount.length_le_cursor arena older olderRoot olderRead).trans
    (PackedEquations.read_bound PackedEquations.wordCodes arena olderRoot olderRead)
  have exactWidth : (BitVec.ofNat 64 (newer.length + older.length)).toNat = newer.length + older.length := by
    have bounds := input.current.fits
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have afterAdd := afterSecond.trans (X86StateFrame.registerOnly addFrame)
  have savedRoot := (((((count.trans (X86StateFrame.registerOnly retain)).trans
      (X86StateFrame.registerOnly selectFrame)).trans baseFrame).trans (X86StateFrame.registerOnly addFrame)).lookup 8
    (by decide)).trans newerKnown
  obtain ⟨g, regained, gain, restored, ⟨atReserve⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector (show At image f base (start + 156) from atRecover)
    (by omega) 8 11 newerRoot savedRoot placed.recover
  have checked : X86StateFrame.Frame clobbers ∅ before g := (afterAdd.trans (X86StateFrame.registerOnly gain)).mono (by decide) (by simp)
  obtain ⟨h, reserveSteps, reserved, reserveFrame, decision⟩ := NativePendingReserve.fetched other extra vector
    (show At image g base (start + 159) from atReserve) (controls.transport checked clobbers_data) placed.reserve
    (input.current.preserved checked) ((checked.lookup 5 (by decide)).trans input.base) (input.limit.preserved checked (by simp))
    (((X86StateFrame.registerOnly addFrame).trans (X86StateFrame.registerOnly gain)).lookup 14 (by decide) |>.trans length)
    (BitVec.ofNat 64 (newer.length + older.length)) ((gain.lookup 0 (by decide)).trans combined)
  rw [exactWidth] at decision
  have throughReserve : X86StateFrame.Frame clobbers ∅ before h := (checked.trans reserveFrame).mono (by decide) (by simp)
  have throughNewer := X86FuelPrefix.fetches_then 1 _ before a b saved counted
  have crossed := X86FuelPrefix.fetches_then _ 1 before c d (X86FuelPrefix.fetches_then _ 1 before b c throughNewer retained) selected
  have calculated := X86FuelPrefix.fetches_then _ 1 before f g
    (X86FuelPrefix.fetches_then _ 1 before e f (X86FuelPrefix.fetches_then _ _ before d e crossed countedBase) added) regained
  have ran := X86FuelPrefix.fetches_then _ reserveSteps before g h calculated reserved
  have original := (reserveFrame.lookup 11 (by decide)).trans restored
  by_cases fits : arena.size + (newer.length + older.length) ≤ capacity
  · rw [if_pos fits] at decision
    obtain ⟨rfl, floor, _, _, ⟨atStage⟩⟩ := decision
    obtain ⟨i, recent, recentFrame, oldCount, ⟨atClear⟩⟩ := X86PlacedRegisterMove.executes
      (handlers other extra) vector (show At image h base (start + 190) from atStage)
      (by omega) 3 14 (BitVec.ofNat 64 arena.size) floor placed.stage
    obtain ⟨after, cleared, clearFrame, unset, endpoint⟩ := X86PlacedRegisterMove.executes
      (handlers other extra) vector (show At image i base (start + 193) from atClear)
      (by omega) 12 0 0 ((recentFrame.lookup 12 (by decide)).trans ((throughReserve.lookup 12 (by decide)).trans input.zero)) placed.empty
    have epilogue := X86StateFrame.registerOnly (recentFrame.trans clearFrame)
    have frame : X86StateFrame.Frame clobbers ∅ before after := (throughReserve.trans epilogue).mono (by decide) (by simp)
    have cursor := (epilogue.lookup 11 (by decide)).trans original
    have out : NativeEquationReverse.Input layout arena arena newerRoot 0 after :=
      ⟨input.current.preserved frame, (input.current.preserved frame).records, (frame.lookup 5 (by decide)).trans input.base,
        cursor, (clearFrame.lookup 14 (by decide)).trans oldCount, unset,
        (frame.lookup 12 (by decide)).trans input.zero, (frame.lookup 13 (by decide)).trans input.one⟩
    refine ⟨after, _, X86FuelPrefix.fetches_then _ 1 before i after
      (X86FuelPrefix.fetches_then _ 1 before h i ran recent) cleared, frame, cursor, (frame.lookup 7 (by decide)).trans input.older, ?_⟩
    rw [if_pos fits]
    exact ⟨by omega, out, endpoint⟩
  · rw [if_neg fits] at decision
    obtain ⟨rfl, stop⟩ := decision
    refine ⟨h, _, ran, throughReserve, original, (throughReserve.lookup 7 (by decide)).trans input.older, ?_⟩
    rw [if_neg fits]
    exact ⟨by omega, stop⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeResolveReserve
