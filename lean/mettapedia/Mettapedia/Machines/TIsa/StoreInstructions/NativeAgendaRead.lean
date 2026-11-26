import Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaRecords
import Mettapedia.Machines.TIsa.StoreInstructions.NativeTermDispatch

/-!
# A fetched pop of the native equation agenda

The live root is in r11. Zero exits to the completed path.
Before following a positive handle, the code loads the initialized
length and checks the original handle. At the selected record it
checks that the tail descends before loading either operand or
advancing the live root. No agenda cell is mutated by a pop.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaRead

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads)
open X86PlacedScalar (Code CompareBranch registerCode)
open X86IndexedAddress (Base addressCode)
open X86PreparedLea (Index)
open NativeAgendaRecords (top Top Ready)
open PackedEquations (Arena Node)
open NativeWords (Wiring)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def baseCode : List ℕ := registerCode 0x89 5 6
def countCode : List ℕ := X86DataLoad.code true 8 6 0
def cursorCode : List ℕ := registerCode 0x89 11 1
def indexRegister : Index := ⟨1, by decide⟩
def indexBase : Base := ⟨1, by decide⟩
def agendaBase : Base := ⟨6, by decide⟩
def tripleCode : List ℕ := addressCode 1 indexRegister 1 indexBase
def locateCode : List ℕ := addressCode 6 indexRegister 3 agendaBase
def olderCode : List ℕ := X86DataLoad.code true 9 6 0
def leftCode : List ℕ := X86DataLoad.code true 1 6 8
def rightCode : List ℕ := X86DataLoad.code true 2 6 16
def advanceCode : List ℕ := registerCode 0x89 9 11

def emit (start done malformed : ℕ) : List ℕ :=
  NativeDecisions.compareBytes .lessUnsigned 12 11 start done ++
    (baseCode ++ (countCode ++ (NativeDecisions.compareBytes .lessEqualUnsigned 11 8 (start + 19) malformed ++
      (cursorCode ++ (tripleCode ++ (locateCode ++ (olderCode ++
        (NativeDecisions.compareBytes .lessUnsigned 9 11 (start + 46) malformed ++
          (leftCode ++ (rightCode ++ advanceCode))))))))))

theorem emit_size (start done malformed : ℕ) : (emit start done malformed).length = 72 := rfl

structure Placed (image : NativeImage.View) (start done malformed : ℕ) : Prop where
  extent : start + 72 ≤ image.size
  nonzero : CompareBranch image start done .lessUnsigned 12 11
  base : Code image (start + 9) baseCode
  count : Code image (start + 12) countCode
  inRange : CompareBranch image (start + 19) malformed .lessEqualUnsigned 11 8
  cursor : Code image (start + 28) cursorCode
  triple : Code image (start + 31) tripleCode
  locate : Code image (start + 35) locateCode
  older : Code image (start + 39) olderCode
  descends : CompareBranch image (start + 46) malformed .lessUnsigned 9 11
  left : Code image (start + 55) leftCode
  right : Code image (start + 62) rightCode
  advance : Code image (start + 69) advanceCode

theorem placed_of_emitted (image : NativeImage.View) (start done malformed : ℕ)
    (space : start + 72 ≤ image.size) (finishFits : done ≤ image.size) (badFits : malformed ≤ image.size)
    (short : image.size < 2 ^ 31) (stored : Code image start (emit start done malformed)) :
    Placed image start done malformed := by
  obtain ⟨nonzero, tail⟩ := NativeWords.code_append (show Code image start
    (NativeDecisions.compareBytes .lessUnsigned 12 11 start done ++ _) from stored)
  rw [NativeDecisions.compare_size] at tail
  obtain ⟨base, tail⟩ := NativeWords.code_append tail
  obtain ⟨count, tail⟩ := NativeWords.code_append tail
  change Code image (start + 19) _ at tail
  obtain ⟨bound, tail⟩ := NativeWords.code_append tail
  rw [NativeDecisions.compare_size] at tail
  obtain ⟨cursor, tail⟩ := NativeWords.code_append tail
  obtain ⟨triple, tail⟩ := NativeWords.code_append tail
  obtain ⟨locate, tail⟩ := NativeWords.code_append tail
  obtain ⟨older, tail⟩ := NativeWords.code_append tail
  change Code image (start + 46) _ at tail
  obtain ⟨back, tail⟩ := NativeWords.code_append tail
  rw [NativeDecisions.compare_size] at tail
  obtain ⟨left, tail⟩ := NativeWords.code_append tail
  obtain ⟨right, advance⟩ := NativeWords.code_append tail
  exact ⟨space, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) finishFits short nonzero,
    base, count, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) badFits short bound, cursor,
    triple, locate, older, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) badFits short back,
    left, right, advance⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register := {.rcx, .rdx, .rsi, .r8, .r9, .r11, .rflags, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

def countWire : Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 8, by decide, by decide⟩
def olderWire : Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 9, by decide, by decide⟩
def leftWire : Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 1, by decide, by decide⟩
def rightWire : Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 2, by decide, by decide⟩

def fieldSource {length : ℕ} (bank : WordRegion.Region length) (slot : Fin length) : NativeWords.Source bank.pointer :=
  .copy _ (bank.cell slot)

def cost (arena : Arena) (root : Word) : ℕ :=
  if root.toNat = 0 then 2
  else
    match arena[root.toNat - 1]? with
    | none => 6
    | some node => if node.older.toNat < root.toNat then 15 else 12

theorem cost_pop (arena : Arena) (root : Word) (node : Node) (selected : top arena root = .equation node) :
    cost arena root = 15 := by
  unfold top at selected
  by_cases zero : root.toNat = 0
  · simp [zero] at selected
  · rw [if_neg zero] at selected
    cases read : arena[root.toNat - 1]? with
    | none => simp only [read] at selected; cases selected
    | some record =>
      simp only [read] at selected
      by_cases below : record.older.toNat < root.toNat
      · simp [cost, zero, read, below]
      · simp [below] at selected

theorem empty_cursor (arena : Arena) (root : Word) (selected : top arena root = .empty) : root = 0 := by
  apply BitVec.eq_of_toNat_eq
  change root.toNat = 0
  by_contra nonzero
  rw [top, if_neg nonzero] at selected
  cases loaded : arena[root.toNat - 1]? with
  | none => simp only [loaded] at selected; cases selected
  | some record =>
    simp only [loaded] at selected
    by_cases below : record.older.toNat < root.toNat <;> simp [below] at selected

theorem cost_empty (arena : Arena) (root : Word) (selected : top arena root = .empty) :
    cost arena root = 2 := by
  rw [empty_cursor arena root selected]
  rfl

def Arrival (arena : Arena) (root : Word) (image : NativeImage.View) (base : BitVec 48)
    (start done malformed : ℕ) (after : Native) : Prop :=
  match top arena root with
  | .empty => lookup after 11 = some root ∧ Nonempty (At image after base done)
  | .malformed => lookup after 11 = some root ∧ Nonempty (At image after base malformed)
  | .equation node => lookup after 11 = some node.older ∧
    lookup after 1 = some node.left ∧ lookup after 2 = some node.right ∧ Nonempty (At image after base (start + 72))

private theorem calculate_record (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {base : BitVec 48} {start done malformed : ℕ}
    {before : Native} (point : At image before base (start + 28)) (placed : Placed image start done malformed)
    (arenaPointer root : Word) (location : lookup before 6 = some arenaPointer) (cursor : lookup before 11 = some root) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run before = .ok () after ∧
      X86StateFrame.Frame {.rcx, .rsi, .rip} ∅ before after ∧ lookup after 6 = some (arenaPointer + root * 24) ∧
      Nonempty (At image after base (start + 39)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have room := placed.extent
  obtain ⟨a, copied, copyFrame, known, ⟨atScale⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 11 1 root cursor placed.cursor
  obtain ⟨b, scaled, scaleFrame, tripled, ⟨atLocation⟩⟩ := X86IndexedAddress.forms_address
    other extra vector (show At image a base (start + 31) from atScale) (by omega)
    1 indexRegister 1 indexBase placed.triple root root known known
  have frames := copyFrame.trans scaleFrame
  obtain ⟨after, located, locateFrame, address, endpoint⟩ := X86IndexedAddress.forms_address
    other extra vector (show At image b base (start + 35) from atLocation) (by omega)
    6 indexRegister 3 agendaBase placed.locate arenaPointer _ ((frames.lookup 6 (by decide)).trans location) tripled
  have scale : (root + root * 2) * 8 = root * 24 := by
    calc
      _ = (root * 1 + root * 2) * 8 := congrArg (fun x : Word => (x + root * 2) * 8) (BitVec.mul_one root).symm
      _ = (root * ((1 : Word) + 2)) * 8 := congrArg (fun x : Word => x * 8) (@BitVec.mul_add 64 root 1 2).symm
      _ = root * (((1 : Word) + 2) * 8) := BitVec.mul_assoc _ _ _
      _ = root * 24 := rfl
  change lookup after 6 = some (arenaPointer + (root + root * 2) * 8) at address
  rw [scale] at address
  exact ⟨after, X86FuelPrefix.fetches_then 2 1 before b after
    (X86FuelPrefix.fetches_then 1 1 before a b copied scaled) located,
    (X86StateFrame.registerOnly (frames.trans locateFrame)).mono (by decide) (by simp), address, endpoint⟩

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start done malformed : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start done malformed)
    {capacity : ℕ} {layout : NativeAgendaRecords.Layout capacity} {arena : Arena} (ready : Ready layout arena before)
    (pointer : lookup before 5 = some layout.words.pointer) (root : Word)
    (live : lookup before 11 = some root) (zero : lookup before 12 = some 0) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (cost arena root)).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧ Arrival arena root image base start done malformed after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have room := placed.extent
  have noHandlerChange : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  obtain ⟨a, checkedRoot, rootFrame, ⟨positive⟩⟩ := X86PlacedScalar.compare_branch
    (X86PlacedFrameAddress.nativeBase other) extra vector point .lessUnsigned 12 11 placed.nonzero 0 root zero live
  change At image a base (if decide (0 < root.toNat) then start + 9 else done) at positive
  by_cases occupied : 0 < root.toNat
  · simp only [occupied, decide_true, if_true] at positive
    obtain ⟨b, opened, openFrame, baseRead, ⟨atCount⟩⟩ := X86PlacedRegisterMove.executes
      (handlers other extra) vector positive (by omega) 5 6 layout.words.pointer
      ((rootFrame.lookup 5 (by decide)).trans pointer) placed.base
    have throughBase := (X86StateFrame.registerOnly rootFrame).trans (X86StateFrame.registerOnly openFrame)
    obtain ⟨c, counted, countFrame, boundRead, ⟨atRange⟩⟩ :=
      (fieldSource layout.header 0).fetch (handlers other extra) vector countWire (BitVec.ofNat 64 arena.size)
        (show At image b base (start + 12) from atCount)
        (controls.transport throughBase (by decide)) (layout.header_pointer.symm ▸ baseRead)
        (ready.count.preserved throughBase (by simp)) (show start + 19 ≤ image.size by omega) placed.count
    rw [noHandlerChange] at counted
    have afterCount := throughBase.trans countFrame
    obtain ⟨d, checkedBound, boundFrame, ⟨within⟩⟩ := X86PlacedScalar.compare_branch
      (X86PlacedFrameAddress.nativeBase other) extra vector (show At image c base (start + 19) from atRange)
      .lessEqualUnsigned 11 8 placed.inRange root _ ((afterCount.lookup 11 (by decide)).trans live) boundRead
    change At image d base (if decide (root.toNat ≤ (BitVec.ofNat 64 arena.size).toNat) then start + 19 + 9
      else malformed) at within
    rw [ready.count_word] at within
    have passed := afterCount.trans (X86StateFrame.registerOnly boundFrame)
    have ranBase := X86FuelPrefix.fetches_then 2 1 before a b checkedRoot opened
    have ranCount := X86FuelPrefix.fetches_then 3 1 before b c ranBase counted
    have ranChecks := X86FuelPrefix.fetches_then 4 2 before c d ranCount checkedBound
    by_cases fits : root.toNat ≤ arena.size
    · simp only [fits, decide_true, if_true] at within
      let i : Fin arena.size := ⟨root.toNat - 1, by omega⟩
      let index : Fin capacity := ⟨i.val, i.isLt.trans_le ready.fits⟩
      let node := arena[i]
      let record := layout.record index
      have here : arena[root.toNat - 1]? = some node := Array.getElem?_eq_getElem i.isLt
      have recordPointer := layout.record_pointer root index (by change root.toNat = root.toNat - 1 + 1; omega)
      have existingBase := (((countFrame.trans (X86StateFrame.registerOnly boundFrame))).lookup 6 (by decide)).trans baseRead
      obtain ⟨e, located, placeFrame, address, ⟨atOlder⟩⟩ := calculate_record other extra vector
        (show At image d base (start + 28) from within) placed layout.words.pointer root existingBase
        ((passed.lookup 11 (by decide)).trans live)
      have place := passed.trans placeFrame
      have actual : lookup e 6 = some record.pointer := recordPointer.symm ▸ address
      obtain ⟨f, older, olderFrame, tailRead, ⟨atLink⟩⟩ := (fieldSource record 0).fetch
        (handlers other extra) vector olderWire node.older atOlder (controls.transport place (by decide)) actual
        ((ready.node i 0).preserved place (by simp)) (show start + 46 ≤ image.size by omega) placed.older
      rw [noHandlerChange] at older
      have throughTail := place.trans olderFrame
      obtain ⟨g, checkedLink, linkFrame, ⟨descends⟩⟩ := X86PlacedScalar.compare_branch
        (X86PlacedFrameAddress.nativeBase other) extra vector (show At image f base (start + 46) from atLink)
        .lessUnsigned 9 11 placed.descends _ root tailRead ((throughTail.lookup 11 (by decide)).trans live)
      change At image g base (if decide (node.older.toNat < root.toNat) then start + 46 + 9 else malformed) at descends
      have link := throughTail.trans (X86StateFrame.registerOnly linkFrame)
      have ranPlace := X86FuelPrefix.fetches_then 6 3 before d e ranChecks located
      have ranOlder := X86FuelPrefix.fetches_then 9 1 before e f ranPlace older
      have ranLink := X86FuelPrefix.fetches_then 10 2 before f g ranOlder checkedLink
      have nonzero : root.toNat ≠ 0 := by omega
      by_cases down : node.older.toNat < root.toNat
      · simp only [down, decide_true, if_true] at descends
        obtain ⟨h, leftLoad, leftFrame, left, ⟨forRight⟩⟩ := (fieldSource record 1).fetch
          (handlers other extra) vector leftWire node.left (show At image g base (start + 55) from descends)
          (controls.transport link (by decide)) (((olderFrame.trans (X86StateFrame.registerOnly linkFrame)).lookup 6
            (by decide)).trans actual) ((ready.node i 1).preserved link (by simp))
          (show start + 62 ≤ image.size by omega) placed.left
        rw [noHandlerChange] at leftLoad
        have throughLeft := link.trans leftFrame
        obtain ⟨j, rightLoad, rightFrame, right, ⟨forAdvance⟩⟩ := (fieldSource record 2).fetch
          (handlers other extra) vector rightWire node.right (show At image h base (start + 62) from forRight)
          (controls.transport throughLeft (by decide)) ((((olderFrame.trans (X86StateFrame.registerOnly linkFrame)).trans
            leftFrame).lookup 6 (by decide)).trans actual) ((ready.node i 2).preserved throughLeft (by simp))
          (show start + 69 ≤ image.size by omega) placed.right
        rw [noHandlerChange] at rightLoad
        have keptTail := ((((X86StateFrame.registerOnly linkFrame).trans leftFrame).trans rightFrame).lookup 9
          (by decide)).trans tailRead
        obtain ⟨after, advanced, advanceFrame, newRoot, endpoint⟩ := X86PlacedRegisterMove.executes
          (handlers other extra) vector (show At image j base (start + 69) from forAdvance)
          (by omega) 9 11 node.older keptTail placed.advance
        have ranLeft := X86FuelPrefix.fetches_then 12 1 before g h ranLink leftLoad
        have ranRight := X86FuelPrefix.fetches_then 13 1 before h j ranLeft rightLoad
        have all := ((throughLeft.trans rightFrame).trans (X86StateFrame.registerOnly advanceFrame))
        simp only [cost, if_neg nonzero, here, if_pos down, Arrival, top]
        exact ⟨after, X86FuelPrefix.fetches_then 14 1 before j after ranRight advanced,
          all.mono (by decide) (by simp), newRoot,
          ((rightFrame.trans (X86StateFrame.registerOnly advanceFrame)).lookup 1 (by decide)).trans left,
          (advanceFrame.lookup 2 (by decide)).trans right, endpoint⟩
      · simp only [down, decide_false] at descends
        simp only [cost, if_neg nonzero, here, if_neg down, Arrival, top]
        exact ⟨g, ranLink, link.mono (by decide) (by simp), (link.lookup 11 (by decide)).trans live, ⟨descends⟩⟩
    · simp only [fits, decide_false] at within
      have outside : arena[root.toNat - 1]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
      simp only [cost, if_neg (show root.toNat ≠ 0 by omega), outside, Arrival, top]
      exact ⟨d, ranChecks, passed.mono (by decide) (by simp), (passed.lookup 11 (by decide)).trans live, ⟨within⟩⟩
  · simp only [occupied, decide_false] at positive
    simp only [cost, if_pos (show root.toNat = 0 by omega), Arrival, top]
    exact ⟨a, checkedRoot, (X86StateFrame.registerOnly rootFrame).mono (by decide) (by simp),
      (rootFrame.lookup 11 (by decide)).trans live, ⟨positive⟩⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaRead
