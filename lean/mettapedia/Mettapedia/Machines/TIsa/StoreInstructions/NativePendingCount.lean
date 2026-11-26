import Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaRead
import Mettapedia.Machines.TIsa.X86PlacedArithmetic

/-!
# Counting a pending equation chain without copying it

Only the older-link field is needed to reserve the destination
suffix. This pass leaves the original cursor and pending binding
in their registers and does not load either term of an equation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativePendingCount

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls)
open X86PlacedScalar (Code CompareBranch Jump registerCode jumpDelta)
open NativeAgendaRecords (Ready)
open PackedEquations (Arena readWords)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def cursorIndex : X86PreparedLea.Index := ⟨2, by decide⟩
def cursorBase : X86IndexedAddress.Base := ⟨2, by decide⟩
def offsetIndex : X86PreparedLea.Index := ⟨1, by decide⟩
def arenaBase : X86IndexedAddress.Base := ⟨6, by decide⟩
def tripleCode : List ℕ := X86IndexedAddress.addressCode 1 cursorIndex 1 cursorBase
def locateCode : List ℕ := X86IndexedAddress.addressCode 6 offsetIndex 3 arenaBase
def linkCode : List ℕ := X86DataLoad.code true 10 6 0
def linkWire : NativeWords.Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 10, by decide, by decide⟩
def moveCode : List ℕ := registerCode 0x89 10 2
def addCode : List ℕ := registerCode (X86Arithmetic.opcode .add) 13 0

def emitLoop (start done malformed : ℕ) : List ℕ :=
  NativeDecisions.compareBytes .lessUnsigned 12 2 start done ++
    (NativeDecisions.compareBytes .lessEqualUnsigned 2 14 (start + 9) malformed ++
      (tripleCode ++ (NativeAgendaRead.baseCode ++ (locateCode ++ (linkCode ++
        (NativeDecisions.compareBytes .lessUnsigned 10 2 (start + 36) malformed ++
          (moveCode ++ (addCode ++ X86UnconditionalJump.Block.code (jumpDelta (start + 51) start)))))))))

theorem emitLoop_size (start done malformed : ℕ) : (emitLoop start done malformed).length = 56 := by
  simp only [emitLoop, List.length_append, NativeDecisions.compare_size, X86UnconditionalJump.Block.code_length,
    show tripleCode.length = 4 from rfl, show locateCode.length = 4 from rfl, show linkCode.length = 7 from rfl,
    show NativeAgendaRead.baseCode.length = 3 from rfl, show moveCode.length = 3 from rfl, show addCode.length = 3 from rfl]

structure LoopPlaced (image : NativeImage.View) (start done malformed : ℕ) : Prop where
  extent : start + 56 ≤ image.size
  nonzero : CompareBranch image start done .lessUnsigned 12 2
  bound : CompareBranch image (start + 9) malformed .lessEqualUnsigned 2 14
  triple : Code image (start + 18) tripleCode
  base : Code image (start + 22) NativeAgendaRead.baseCode
  locate : Code image (start + 25) locateCode
  link : Code image (start + 29) linkCode
  descending : CompareBranch image (start + 36) malformed .lessUnsigned 10 2
  move : Code image (start + 45) moveCode
  add : Code image (start + 48) addCode
  again : Jump image (start + 51) start

theorem loop_placed (image : NativeImage.View) (start done malformed : ℕ)
    (extent : start + 56 ≤ image.size) (finish : done ≤ image.size)
    (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31) (code : Code image start (emitLoop start done malformed)) :
    LoopPlaced image start done malformed := by
  obtain ⟨nz, rest⟩ := NativeWords.code_append (show Code image start
    (NativeDecisions.compareBytes .lessUnsigned 12 2 start done ++ _) from code)
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨bound, rest⟩ := NativeWords.code_append rest
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨triple, rest⟩ := NativeWords.code_append rest
  obtain ⟨copy, rest⟩ := NativeWords.code_append rest
  obtain ⟨locate, rest⟩ := NativeWords.code_append rest
  obtain ⟨link, rest⟩ := NativeWords.code_append rest
  change Code image (start + 36) _ at rest
  obtain ⟨down, rest⟩ := NativeWords.code_append rest
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨move, rest⟩ := NativeWords.code_append rest
  obtain ⟨add, again⟩ := NativeWords.code_append rest
  refine ⟨extent, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) finish short nz,
    NativeDecisions.compare_placed image _ _ _ _ _ (by omega) bad short bound, triple, copy, locate, link,
    NativeDecisions.compare_placed image _ _ _ _ _ (by omega) bad short down, move, add,
    ⟨by omega, by omega, ?_, again⟩⟩
  unfold jumpDelta
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
  omega

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev loopClobbers : Finset Register := {.rax, .rcx, .rdx, .rsi, .r10, .rflags, .rip}

variable {capacity : ℕ} {layout : NativeAgendaRecords.Layout capacity} {arena : Arena}

structure Input (layout : NativeAgendaRecords.Layout capacity) (arena : Arena) (cursor : Word) (counted : ℕ)
    (native : Native) : Prop where
  live : Ready layout arena native
  base : lookup native 5 = some layout.words.pointer
  count : lookup native 14 = some (BitVec.ofNat 64 arena.size)
  zero : lookup native 12 = some 0
  one : lookup native 13 = some 1
  cursor : lookup native 2 = some cursor
  result : lookup native 0 = some (BitVec.ofNat 64 counted)

private theorem stride (cursor : Word) : (cursor + cursor * 2) * 8 = cursor * 24 := by
  calc
    _ = (cursor * 1 + cursor * 2) * 8 := congrArg (fun v : Word => (v + cursor * 2) * 8) (BitVec.mul_one cursor).symm
    _ = (cursor * ((1 : Word) + 2)) * 8 := congrArg (fun v : Word => v * 8) (@BitVec.mul_add 64 cursor 1 2).symm
    _ = cursor * 24 := BitVec.mul_assoc _ _ _

theorem older_of_read (arena : Arena) (cursor : Word) (first : Word × Word) (tail : List (Word × Word))
    (loaded : readWords arena cursor = some (first :: tail)) :
    ∃ i : Fin arena.size, cursor.toNat = i.val + 1 ∧ arena[i].older.toNat < cursor.toNat ∧
      readWords arena arena[i].older = some tail := by
  obtain ⟨node, selected, _, older⟩ := NativeAgendaRecords.top_of_read arena cursor (first :: tail) loaded
  unfold NativeAgendaRecords.top at selected
  by_cases nonempty : cursor.toNat = 0
  · simp [nonempty] at selected
  · rw [if_neg nonempty] at selected
    cases atIndex : arena[cursor.toNat - 1]? with
    | none => simp [atIndex] at selected
    | some record =>
      rw [atIndex] at selected
      by_cases down : record.older.toNat < cursor.toNat
      · simp only [if_pos down, NativeAgendaRecords.Top.equation.injEq] at selected
        obtain rfl := selected
        obtain ⟨inside, equality⟩ := Array.getElem?_eq_some_iff.mp atIndex
        refine ⟨⟨cursor.toNat - 1, inside⟩, ?_, ?_, ?_⟩
        · change cursor.toNat = cursor.toNat - 1 + 1
          omega
        change arena[cursor.toNat - 1].older.toNat < cursor.toNat
        rwa [equality]
        change readWords arena arena[cursor.toNat - 1].older = some tail
        rwa [equality]
      · simp [down] at selected

theorem length_le_cursor (arena : Arena) (pending : List (Word × Word)) (cursor : Word)
    (loaded : readWords arena cursor = some pending) : pending.length ≤ cursor.toNat := by
  induction pending generalizing cursor with
  | nil => simp
  | cons first tail ih =>
    obtain ⟨i, _, descends, rest⟩ := older_of_read arena cursor first tail loaded
    have n := ih arena[i].older rest
    simp only [List.length_cons]
    exact Nat.succ_le_of_lt (n.trans_lt descends)

/-- A linked chain of length n takes exactly 13n+2 fetched
instructions after counts and the traversal cursor are loaded. -/
theorem fetched_loop (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start done malformed : ℕ}
    (placed : LoopPlaced image start done malformed) (pending : List (Word × Word)) (cursor : Word) (counted : ℕ)
    (loaded : readWords arena cursor = some pending) {before : Native} (point : At image before base start)
    (controls : Controls before) (input : Input layout arena cursor counted before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (13 * pending.length + 2)).run before = .ok () after ∧
      X86StateFrame.Frame loopClobbers ∅ before after ∧
      lookup after 0 = some (BitVec.ofNat 64 (counted + pending.length)) ∧ Nonempty (At image after base done) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  induction pending generalizing cursor counted before with
  | nil =>
    have empty := NativeAgendaRead.empty_cursor arena cursor (NativeAgendaRecords.top_of_read arena cursor [] loaded)
    subst cursor
    obtain ⟨a, ran, quiet, ⟨stopped⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
      extra vector point .lessUnsigned 12 2 placed.nonzero 0 0 input.zero input.cursor
    exact ⟨a, ran, (X86StateFrame.registerOnly quiet).mono (by decide) (Finset.Subset.refl _),
      (quiet.lookup 0 (by decide)).trans input.result, ⟨stopped⟩⟩
  | cons first tail ih =>
    obtain ⟨i, index, descending, rest⟩ := older_of_read arena cursor first tail loaded
    let node := arena[i]
    let record := layout.record ⟨i.val, i.isLt.trans_le input.live.fits⟩
    obtain ⟨a, tested, testFrame, ⟨atPositive⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
      extra vector point .lessUnsigned 12 2 placed.nonzero 0 cursor input.zero input.cursor
    have pos : 0 < cursor.toNat := by omega
    change At image a base (if decide (0 < cursor.toNat) then start + 9 else done) at atPositive
    have nonempty : At image a base (start + 9) := by simpa [pos] using atPositive
    obtain ⟨b, checked, checkFrame, ⟨atBound⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
      extra vector nonempty .lessEqualUnsigned 2 14 placed.bound cursor _
      ((testFrame.lookup 2 (by decide)).trans input.cursor) ((testFrame.lookup 14 (by decide)).trans input.count)
    change At image b base (if decide (cursor.toNat ≤ (BitVec.ofNat 64 arena.size).toNat) then start + 18 else malformed)
      at atBound
    rw [input.live.count_word] at atBound
    have bounded : cursor.toNat ≤ arena.size := by have := i.isLt; omega
    have tripleAt : At image b base (start + 18) := by simpa [bounded] using atBound
    have headFrame := testFrame.trans checkFrame
    have cur := (headFrame.lookup 2 (by decide)).trans input.cursor
    obtain ⟨c, triple, tripled, offset, ⟨atAddress⟩⟩ := X86IndexedAddress.forms_address
      other extra vector tripleAt (by omega) 1 cursorIndex 1 cursorBase placed.triple cursor cursor cur cur
    obtain ⟨c', copied, copying, baseWord, ⟨atLocate⟩⟩ := X86PlacedRegisterMove.executes
      (handlers other extra) vector (show At image c base (start + 22) from atAddress) (by omega) 5 6
      layout.words.pointer (((headFrame.trans tripled).lookup 5 (by decide)).trans input.base) placed.base
    obtain ⟨d, addr, addressed, pointer, ⟨atLoad⟩⟩ := X86IndexedAddress.forms_address
      other extra vector (show At image c' base (start + 25) from atLocate)
      (by omega) 6 offsetIndex 3 arenaBase placed.locate layout.words.pointer _
      baseWord ((copying.lookup 1 (by decide)).trans offset)
    change lookup d 6 = some (layout.words.pointer + (cursor + cursor * 2) * 8) at pointer
    rw [stride, ← layout.record_pointer cursor ⟨i.val, i.isLt.trans_le input.live.fits⟩ index] at pointer
    have beforeLoad := X86StateFrame.registerOnly (((headFrame.trans tripled).trans copying).trans addressed)
    obtain ⟨e, fetchLink, linkFrame, link, ⟨atCheck⟩⟩ := (NativeAgendaRead.fieldSource record 0).fetch
      (handlers other extra) vector linkWire node.older (show At image d base (start + 29) from atLoad)
      (controls.transport beforeLoad (by decide)) pointer ((input.live.node i 0).preserved beforeLoad (by simp))
      (show start + 36 ≤ image.size by omega) placed.link
    have sameHandlers : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
    rw [sameHandlers] at fetchLink
    have throughLink := beforeLoad.trans linkFrame
    obtain ⟨f, down, downFrame, ⟨atDown⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
      extra vector (show At image e base (start + 36) from atCheck) .lessUnsigned 10 2 placed.descending node.older cursor
      link ((throughLink.lookup 2 (by decide)).trans input.cursor)
    change At image f base (if decide (node.older.toNat < cursor.toNat) then start + 45 else malformed) at atDown
    have atMove : At image f base (start + 45) := by simpa [show node.older.toNat < cursor.toNat from descending] using atDown
    obtain ⟨g, move, moved, atOlder, ⟨atAdd⟩⟩ := X86PlacedRegisterMove.executes
      (handlers other extra) vector atMove (by omega) 10 2 node.older ((downFrame.lookup 10 (by decide)).trans link) placed.move
    have throughMove := throughLink.trans (X86StateFrame.registerOnly (downFrame.trans moved))
    obtain ⟨h, add, added, larger, ⟨backEdge⟩⟩ := X86PlacedArithmetic.executes
      (handlers other extra) vector (show At image g base (start + 48) from atAdd) (by omega) .add 13 0
      (BitVec.ofNat 64 counted) 1 ((throughMove.lookup 13 (by decide)).trans input.one)
      ((throughMove.lookup 0 (by decide)).trans input.result) placed.add
    have addLinked : X86Arithmetic.linkedHandlers (handlers other extra) = handlers other extra := rfl
    rw [addLinked] at add
    obtain ⟨j, jump, jumped, ⟨again⟩⟩ := X86PlacedScalar.jump (X86PlacedFrameAddress.nativeBase other)
      extra vector (show At image h base (start + 51) from backEdge) placed.again
    have entire : X86StateFrame.Frame loopClobbers ∅ before j :=
      (throughMove.trans (X86StateFrame.registerOnly (added.trans jumped))).mono (by decide) (by simp)
    have advanced : Input layout arena node.older (counted + 1) j :=
      ⟨input.live.preserved entire, (entire.lookup 5 (by decide)).trans input.base, (entire.lookup 14 (by decide)).trans input.count,
        (entire.lookup 12 (by decide)).trans input.zero, (entire.lookup 13 (by decide)).trans input.one,
        ((added.trans jumped).lookup 2 (by decide)).trans atOlder, (jumped.lookup 0 (by decide)).trans (by
          change lookup h 0 = some (BitVec.ofNat 64 counted + BitVec.ofNat 64 1) at larger
          rw [← BitVec.ofNat_add_ofNat]; exact larger)⟩
    obtain ⟨after, finished, tailFrame, tally, atDone⟩ := ih node.older (counted + 1) rest again
      (controls.transport entire (by decide)) advanced
    have beforeNode := X86FuelPrefix.fetches_then 2 2 before a b tested checked
    have throughAddress := X86FuelPrefix.fetches_then 6 1 before c' d
      (X86FuelPrefix.fetches_then 5 1 before c c' (X86FuelPrefix.fetches_then 4 1 before b c beforeNode triple) copied) addr
    have throughBounds := X86FuelPrefix.fetches_then 8 2 before e f
      (X86FuelPrefix.fetches_then 7 1 before d e throughAddress fetchLink) down
    have advancedFrom := X86FuelPrefix.fetches_then 12 1 before h j
      (X86FuelPrefix.fetches_then 11 1 before g h (X86FuelPrefix.fetches_then 10 1 before f g throughBounds move) add) jump
    have combined := X86FuelPrefix.fetches_then 13 _ before j after advancedFrom finished
    refine ⟨after, ?_, (entire.trans tailFrame).mono (by simp) (by simp), ?_, atDone⟩
    · have work : 13 * (first :: tail).length + 2 = 13 + (13 * tail.length + 2) := by
        simp only [List.length_cons]
        omega
      rw [work]
      exact combined
    · have size : counted + 1 + tail.length = counted + (first :: tail).length := by simp only [List.length_cons]; omega
      rwa [size] at tally

def copyCursor : List ℕ := registerCode 0x89 11 2
def clearCounter : List ℕ := registerCode 0x89 12 0
def readCount : List ℕ := X86DataLoad.code true 14 6 0
def countWire : NativeWords.Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 14, by decide, by decide⟩

def emit (start done malformed : ℕ) : List ℕ :=
  copyCursor ++ (clearCounter ++ (NativeAgendaRead.baseCode ++ (readCount ++ emitLoop (start + 16) done malformed)))

theorem emit_size (start done malformed : ℕ) : (emit start done malformed).length = 72 := by
  simp only [emit, List.length_append, emitLoop_size, show copyCursor.length = 3 from rfl,
    show clearCounter.length = 3 from rfl, show NativeAgendaRead.baseCode.length = 3 from rfl, show readCount.length = 7 from rfl]

structure Placed (image : NativeImage.View) (start done malformed : ℕ) : Prop where
  extent : start + 72 ≤ image.size
  original : Code image start copyCursor
  clear : Code image (start + 3) clearCounter
  base : Code image (start + 6) NativeAgendaRead.baseCode
  size : Code image (start + 9) readCount
  loop : LoopPlaced image (start + 16) done malformed

theorem placed_of_emitted (image : NativeImage.View) (start done malformed : ℕ)
    (extent : start + 72 ≤ image.size) (finish : done ≤ image.size)
    (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31) (code : Code image start (emit start done malformed)) :
    Placed image start done malformed := by
  obtain ⟨copy, rest⟩ := NativeWords.code_append (show Code image start (copyCursor ++ _) from code)
  obtain ⟨clear, rest⟩ := NativeWords.code_append rest
  obtain ⟨base, rest⟩ := NativeWords.code_append rest
  obtain ⟨size, loop⟩ := NativeWords.code_append rest
  exact ⟨extent, copy, clear, base, size, loop_placed image _ done malformed (by omega) finish bad short loop⟩

abbrev clobbers : Finset Register := insert .r14 loopClobbers

/-- The published count bounds every read, but it is not the
length of the pending suffix. Starting with the true cursor
returns that length and leaves the cursor intact. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start done malformed : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start done malformed)
    (root : Word) (pending : List (Word × Word)) (loaded : readWords arena root = some pending)
    (live : Ready layout arena before) (original : lookup before 11 = some root)
    (agenda : lookup before 5 = some layout.words.pointer)
    (zero : lookup before 12 = some 0) (one : lookup before 13 = some 1) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (13 * pending.length + 6)).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧
      lookup after 0 = some (BitVec.ofNat 64 pending.length) ∧
      (BitVec.ofNat 64 pending.length).toNat = pending.length ∧
      lookup after 11 = some root ∧ lookup after 14 = some (BitVec.ofNat 64 arena.size) ∧
      Nonempty (At image after base done) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  obtain ⟨a, copied, copyFrame, cursor, ⟨atClear⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 11 2 root original placed.original
  obtain ⟨b, cleared, clearFrame, empty, ⟨atBase⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector atClear (by omega) 12 0 0 ((copyFrame.lookup 12 (by decide)).trans zero) placed.clear
  obtain ⟨c, based, baseFrame, pointer, ⟨atSize⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector (show At image b base (start + 6) from atBase) (by omega)
    5 6 layout.words.pointer (((copyFrame.trans clearFrame).lookup 5 (by decide)).trans agenda) placed.base
  have prefixFrame := X86StateFrame.registerOnly ((copyFrame.trans clearFrame).trans baseFrame)
  obtain ⟨d, header, headerFrame, count, ⟨atLoop⟩⟩ := (NativeAgendaRead.fieldSource layout.header 0).fetch
    (handlers other extra) vector countWire (BitVec.ofNat 64 arena.size)
    (show At image c base (start + 9) from atSize) (controls.transport prefixFrame (by decide))
    (layout.header_pointer.symm ▸ pointer) (live.count.preserved prefixFrame (by simp))
    (show start + 16 ≤ image.size by omega) placed.size
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  rw [linked] at header
  have entry := prefixFrame.trans headerFrame
  have unchanged : X86StateFrame.Frame clobbers ∅ before d := entry.mono (by decide) (by simp)
  have input : Input layout arena root 0 d :=
    ⟨live.preserved unchanged, (unchanged.lookup 5 (by decide)).trans agenda, count,
      (unchanged.lookup 12 (by decide)).trans zero, (unchanged.lookup 13 (by decide)).trans one,
      (headerFrame.lookup 2 (by decide)).trans (((clearFrame.trans baseFrame).lookup 2 (by decide)).trans cursor),
      (headerFrame.lookup 0 (by decide)).trans ((baseFrame.lookup 0 (by decide)).trans empty)⟩
  obtain ⟨after, counted, countFrame, exactCount, endpoint⟩ := fetched_loop other extra vector placed.loop pending root 0
    loaded atLoop (controls.transport unchanged (by decide)) input
  have firstFour := X86FuelPrefix.fetches_then 3 1 before c d
    (X86FuelPrefix.fetches_then 2 1 before b c (X86FuelPrefix.fetches_then 1 1 before a b copied cleared) based) header
  have total := X86FuelPrefix.fetches_then 4 _ before d after firstFour counted
  have frame : X86StateFrame.Frame clobbers ∅ before after := (unchanged.trans countFrame).mono (by decide) (by simp)
  have chain := length_le_cursor arena pending root loaded
  have width := root.isLt
  refine ⟨after, ?_, frame, by simpa only [Nat.zero_add] using exactCount, ?_,
    (frame.lookup 11 (by decide)).trans original, (countFrame.lookup 14 (by decide)).trans count, endpoint⟩
  · simpa only [show 4 + (13 * pending.length + 2) = 13 * pending.length + 6 by omega] using total
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (chain.trans_lt width)]

namespace Examples

theorem allocated_records_are_not_pending_length :
    readWords #[⟨0, 1, 2⟩, ⟨0, 4, 5⟩, ⟨1, 6, 7⟩] 3 = some [(6, 7), (1, 2)] := by decide +kernel

theorem cyclic_links_do_not_describe_a_finite_count :
    readWords #[⟨1, 1, 2⟩] 1 = none := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.NativePendingCount
