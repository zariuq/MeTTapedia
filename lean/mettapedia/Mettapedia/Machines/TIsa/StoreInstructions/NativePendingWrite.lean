import Mettapedia.Machines.TIsa.StoreInstructions.NativePendingReserve
import Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaInsert
import Mettapedia.Machines.TIsa.StoreInstructions.PackedAgendaCoordinates

/-!
# Writing one remapped equation at its descending destination

The physical slot lies beyond all published records. Its link
is the previous ordinal, except at the bottom of the new
suffix. The write moves only the private destination cursor;
the reserved extent and the source cursor retain their roles.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativePendingWrite

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads Encoding CodeApart footprint)
open X86PlacedScalar (Code CompareBranch registerCode)
open NativeAgendaRecords (Ready field)
open NativeAgendaRecords renaming Layout → AgendaLayout
open PackedEquations (Arena Node)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def ordinalIndex : X86PreparedLea.Index := ⟨0, by decide⟩
def ordinalBase : X86IndexedAddress.Base := ⟨0, by decide⟩
def writeBase : X86IndexedAddress.Base := ⟨6, by decide⟩
def savedExtent : List ℕ := registerCode 0x89 0 10
def ordinalCode : List ℕ := registerCode 0x89 14 0
def tripleCode : List ℕ := X86IndexedAddress.addressCode 0 ordinalIndex 1 ordinalBase
def locateCode : List ℕ := X86IndexedAddress.addressCode 6 ordinalIndex 3 writeBase
def restoreExtent : List ℕ := registerCode 0x89 10 0
def copyCode : List ℕ := registerCode 0x89 14 10
def predecessorCode : List ℕ := registerCode (X86Arithmetic.opcode .sub) 13 10
def zeroCode : List ℕ := registerCode 0x89 12 10
def decrementCode : List ℕ := registerCode (X86Arithmetic.opcode .sub) 13 14
def encoding : Encoding := .direct 6 (by decide) (by decide)
def stores : List ℕ := encoding.bytes 10 0 ++ (encoding.bytes 1 8 ++ encoding.bytes 2 16)

def emit (start : ℕ) : List ℕ :=
  savedExtent ++ (ordinalCode ++ (tripleCode ++ (NativeAgendaRead.baseCode ++ (locateCode ++
    (restoreExtent ++ (copyCode ++ (predecessorCode ++
      (NativeDecisions.compareBytes .equal 10 3 (start + 26) (start + 38) ++
        (zeroCode ++ (stores ++ decrementCode))))))))))

theorem emit_size (start : ℕ) : (emit start).length = 62 := by
  simp only [emit, List.length_append, NativeDecisions.compare_size, show tripleCode.length = 4 from rfl,
    show NativeAgendaRead.baseCode.length = 3 from rfl, show locateCode.length = 4 from rfl,
    show savedExtent.length = 3 from rfl, show ordinalCode.length = 3 from rfl, show restoreExtent.length = 3 from rfl,
    show copyCode.length = 3 from rfl, show predecessorCode.length = 3 from rfl,
    show zeroCode.length = 3 from rfl, show stores.length = 21 from rfl, show decrementCode.length = 3 from rfl]

structure Placed (image : NativeImage.View) (start : ℕ) : Prop where
  extent : start + 62 ≤ image.size
  save : Code image start savedExtent
  ordinal : Code image (start + 3) ordinalCode
  triple : Code image (start + 6) tripleCode
  base : Code image (start + 10) NativeAgendaRead.baseCode
  locate : Code image (start + 13) locateCode
  restore : Code image (start + 17) restoreExtent
  copy : Code image (start + 20) copyCode
  predecessor : Code image (start + 23) predecessorCode
  bottom : CompareBranch image (start + 26) (start + 38) .equal 10 3
  clear : Code image (start + 35) zeroCode
  words : Code image (start + 38) stores
  decrement : Code image (start + 59) decrementCode

theorem placed_of_emitted (image : NativeImage.View) (start : ℕ) (extent : start + 62 ≤ image.size)
    (short : image.size < 2 ^ 31) (code : Code image start (emit start)) : Placed image start := by
  obtain ⟨save, rest⟩ := NativeWords.code_append (show Code image start (savedExtent ++ _) from code)
  obtain ⟨ordinal, rest⟩ := NativeWords.code_append rest
  obtain ⟨triple, rest⟩ := NativeWords.code_append rest
  obtain ⟨base, rest⟩ := NativeWords.code_append rest
  obtain ⟨locate, rest⟩ := NativeWords.code_append rest
  obtain ⟨restore, rest⟩ := NativeWords.code_append rest
  obtain ⟨copy, rest⟩ := NativeWords.code_append rest
  obtain ⟨sub, rest⟩ := NativeWords.code_append rest
  change Code image (start + 26) _ at rest
  obtain ⟨check, rest⟩ := NativeWords.code_append rest
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨clear, rest⟩ := NativeWords.code_append rest
  obtain ⟨stores, decrement⟩ := NativeWords.code_append rest
  exact ⟨extent, save, ordinal, triple, base, locate, restore, copy, sub,
    NativeDecisions.compare_placed image _ _ _ _ _ (by omega) (by omega) short check, clear, stores, decrement⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rax, .rsi, .r10, .r14, .rflags, .rip}
private abbrev beforeWrite : Finset Register := {.rax, .rsi, .r10, .rflags, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

private def relocate {pointer : Word} (w : NativeStores.Write pointer) : NativeStores.Write pointer :=
  { w with source := if w.source = 11 then 10 else if w.source = 9 then 1 else 2 }

def writeAt (bank : WordRegion.Region 3) (node : Node) (i : Fin 3) : NativeStores.Write bank.pointer :=
  relocate (NativeAgendaInsert.writeAt bank node i)

def writes (bank : WordRegion.Region 3) (node : Node) : List (NativeStores.Write bank.pointer) :=
  (NativeAgendaInsert.writes bank node).map relocate

private theorem member {bank : WordRegion.Region 3} {node : Node} {w : NativeStores.Write bank.pointer}
    (hit : w ∈ writes bank node) : ∃ i : Fin 3, w = writeAt bank node i := by
  obtain ⟨prior, seen, rfl⟩ := List.mem_map.mp hit
  obtain ⟨i, rfl⟩ := NativeAgendaInsert.write_members seen
  exact ⟨i, rfl⟩

private theorem apart (bank : WordRegion.Region 3) (node : Node) : NativeStores.Separate (writes bank node) := by
  unfold NativeStores.Separate writes
  rw [List.pairwise_map]
  exact NativeAgendaInsert.write_apart bank node

private theorem fixed_bytes (bank : WordRegion.Region 3) (node : Node) :
    NativeStores.emitted encoding (writes bank node) = stores := rfl

theorem written_at (bank : WordRegion.Region 3) (node : Node) {byte : ℕ}
    (modified : byte ∈ NativeStores.written (writes bank node)) :
    ∃ j : Fin 3, byte ∈ footprint (bank.cell j).address := by
  change byte ∈ footprint (bank.cell (0 : Fin 3)).address ∪
    (footprint (bank.cell (1 : Fin 3)).address ∪ (footprint (bank.cell (2 : Fin 3)).address ∪ ∅)) at modified
  simp only [Finset.union_empty, Finset.mem_union] at modified
  rcases modified with left | middle | right
  · exact ⟨0, left⟩
  · exact ⟨1, middle⟩
  · exact ⟨2, right⟩

variable {capacity : ℕ} {layout : AgendaLayout capacity} {arena : Arena}

structure Input (layout : AgendaLayout capacity) (arena : Arena) (ordinal : ℕ) (pair : Word × Word) (native : Native) : Prop where
  current : Ready layout arena native
  base : lookup native 5 = some layout.words.pointer
  floor : lookup native 3 = some (BitVec.ofNat 64 arena.size)
  target : lookup native 14 = some (BitVec.ofNat 64 ordinal)
  left : lookup native 1 = some pair.1
  right : lookup native 2 = some pair.2
  zero : lookup native 12 = some 0
  one : lookup native 13 = some 1

private theorem org_word (layout : AgendaLayout capacity) (n : ℕ) (bound : n ≤ capacity) :
    (BitVec.ofNat 64 n).toNat = n := by
  have room := layout.words.positive_room (show 0 < 3 * (capacity + 1) by omega)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem stride (root : Word) : (root + root * 2) * 8 = root * 24 := by
  calc
    _ = (root * 1 + root * 2) * 8 := congrArg (fun v : Word => (v + root * 2) * 8) (BitVec.mul_one root).symm
    _ = (root * ((1 : Word) + 2)) * 8 := congrArg (fun v : Word => v * 8) (@BitVec.mul_add 64 root 1 2).symm
    _ = root * 24 := BitVec.mul_assoc _ _ _

private theorem older (floor ordinal : ℕ) (above : floor < ordinal) (pair : Word × Word) :
    (PackedAgendaCoordinates.recordAt floor 0 (ordinal - 1 - floor) pair).older =
      if ordinal - 1 = floor then 0 else BitVec.ofNat 64 (ordinal - 1) := by
  cases seen : ordinal - 1 - floor with
  | zero =>
    have bottom : ordinal - 1 = floor := by omega
    simp [PackedAgendaCoordinates.recordAt, PackedAgendaCoordinates.headAfter, bottom]
  | succ n =>
    have higher : ordinal - 1 ≠ floor := by omega
    have pos : floor + (n + 1) = ordinal - 1 := by omega
    simp [PackedAgendaCoordinates.recordAt, PackedAgendaCoordinates.headAfter, higher, pos]

/-- Real memory writes fill only the selected future record.
Every previously published record remains readable, and both
source endpoints are copied without any equality test. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start)
    (ordinal : ℕ) (pair : Word × Word) (input : Input layout arena ordinal pair before)
    (reservedEnd : Word) (reserved : lookup before 0 = some reservedEnd)
    (above : arena.size < ordinal) (bounded : ordinal ≤ capacity)
    (clearOfCode : ∀ j : Fin 3, CodeApart image base
      (footprint ((layout.record ⟨ordinal - 1, by omega⟩).cell j).address)) :
    let bank := layout.record ⟨ordinal - 1, by omega⟩
    let node := PackedAgendaCoordinates.recordAt arena.size 0 (ordinal - 1 - arena.size) pair
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      steps = (if ordinal - 1 = arena.size then 15 else 14) ∧
      X86StateFrame.Frame clobbers (NativeStores.written (writes bank node)) before after ∧
      Ready layout arena after ∧ (∀ j : Fin 3, Reads after (bank.cell j).address (field node j)) ∧
      lookup after 14 = some (BitVec.ofNat 64 (ordinal - 1)) ∧
      lookup after 0 = some reservedEnd ∧ Nonempty (At image after base (start + 62)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let raw := BitVec.ofNat 64 ordinal
  let bank := layout.record ⟨ordinal - 1, by omega⟩
  let node := PackedAgendaCoordinates.recordAt arena.size 0 (ordinal - 1 - arena.size) pair
  let prev := BitVec.ofNat 64 (ordinal - 1)
  have rawNat : raw.toNat = ordinal := org_word layout _ bounded
  have prevNat : prev.toNat = ordinal - 1 := org_word layout _ (by omega)
  have floorNat := input.current.count_word
  have extent := placed.extent
  have arithmetic : X86Arithmetic.linkedHandlers (handlers other extra) = handlers other extra := rfl
  have beforeWord : raw - 1 = prev := by
    have h : (1 : Word) ≤ raw := by rw [BitVec.le_def, rawNat]; change 1 ≤ ordinal; omega
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le h, rawNat, prevNat]
    rfl
  have rootAt : raw.toNat = (ordinal - 1) + 1 := by rw [rawNat]; omega
  obtain ⟨s, saved, saveFrame, savedWord, ⟨atOrdinal⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 0 10 reservedEnd reserved placed.save
  obtain ⟨t, selected, selectFrame, addressOrdinal, ⟨atTriple⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector atOrdinal (by omega) 14 0 raw
    ((saveFrame.lookup 14 (by decide)).trans input.target) placed.ordinal
  have beginning := saveFrame.trans selectFrame
  obtain ⟨a, tripled, tripling, index, ⟨atBase⟩⟩ := X86IndexedAddress.forms_address other extra vector
    (show At image t base (start + 6) from atTriple) (by omega)
    0 ordinalIndex 1 ordinalBase placed.triple raw raw addressOrdinal addressOrdinal
  obtain ⟨b, based, moved, address, ⟨atLocate⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector (show At image a base (start + 10) from atBase)
    (by omega) 5 6 layout.words.pointer (((beginning.trans tripling).lookup 5 (by decide)).trans input.base) placed.base
  obtain ⟨c, located, locatedFrame, pointer, ⟨atRestore⟩⟩ := X86IndexedAddress.forms_address other extra vector
    (show At image b base (start + 13) from atLocate) (by omega) 6 ordinalIndex 3 writeBase placed.locate
    layout.words.pointer _ address ((moved.lookup 0 (by decide)).trans index)
  change lookup c 6 = some (layout.words.pointer + (raw + raw * 2) * 8) at pointer
  rw [stride, ← layout.record_pointer raw ⟨ordinal - 1, by omega⟩ rootAt] at pointer
  have throughAddress := ((beginning.trans tripling).trans moved).trans locatedFrame
  obtain ⟨c', restored, restoreFrame, restoredWord, ⟨atCopy⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector (show At image c base (start + 17) from atRestore)
    (by omega) 10 0 reservedEnd
    ((((selectFrame.trans tripling).trans moved).trans locatedFrame).lookup 10 (by decide) |>.trans savedWord) placed.restore
  have throughRestore := throughAddress.trans restoreFrame
  obtain ⟨d, copied, copyFrame, prior, ⟨atSubtract⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector (show At image c' base (start + 20) from atCopy)
    (by omega) 14 10 raw ((throughRestore.lookup 14 (by decide)).trans input.target) placed.copy
  have kept := throughRestore.trans copyFrame
  obtain ⟨e, reduced, sub, new, ⟨atTest⟩⟩ := X86PlacedArithmetic.executes
    (handlers other extra) vector (show At image d base (start + 23) from atSubtract)
    (by omega) .sub 13 10 raw 1 ((kept.lookup 13 (by decide)).trans input.one) prior placed.predecessor
  rw [arithmetic] at reduced
  change lookup e 10 = some (raw - 1) at new
  rw [beforeWord] at new
  have prepared := kept.trans sub
  obtain ⟨f, tested, check, ⟨decision⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
    extra vector (show At image e base (start + 26) from atTest) .equal 10 3 placed.bottom prev _
    new ((prepared.lookup 3 (by decide)).trans input.floor)
  have equality : prev = BitVec.ofNat 64 arena.size ↔ ordinal - 1 = arena.size := by
    constructor
    · intro same
      exact prevNat.symm.trans ((congrArg BitVec.toNat same).trans floorNat)
    · intro same
      exact congrArg (BitVec.ofNat 64) same
  simp only [Comparison.evaluate, beq_iff_eq, equality] at decision
  have readied := prepared.trans check
  have firstThree := X86FuelPrefix.fetches_then 2 1 before t a (X86FuelPrefix.fetches_then 1 1 before s t saved selected) tripled
  have firstSix := X86FuelPrefix.fetches_then 5 1 before c c'
    (X86FuelPrefix.fetches_then 4 1 before b c (X86FuelPrefix.fetches_then 3 1 before a b firstThree based) located) restored
  have firstTen := X86FuelPrefix.fetches_then 8 2 before e f
    (X86FuelPrefix.fetches_then 7 1 before d e (X86FuelPrefix.fetches_then 6 1 before c' d firstSix copied) reduced) tested
  have aroundCheck := (copyFrame.trans sub).trans check
  have retained := (aroundCheck.lookup 0 (by decide)).trans restoredWord
  have link : ∃ selected steps, (X86FuelPrefix.fetches steps).run before = .ok () selected ∧
      steps = (if ordinal - 1 = arena.size then 11 else 10) ∧
      X86StateFrame.Frame beforeWrite ∅ before selected ∧ lookup selected 6 = some bank.pointer ∧
      lookup selected 10 = some node.older ∧ lookup selected 0 = some reservedEnd ∧
      Nonempty (At image selected base (start + 38)) := by
    have reached := restoreFrame.trans aroundCheck
    have bankKnown := (reached.lookup 6 (by decide)).trans pointer
    by_cases final : ordinal - 1 = arena.size
    · simp only [if_pos final] at decision
      obtain ⟨selected, cleared, clearFrame, zero, endpoint⟩ := X86PlacedRegisterMove.executes
        (handlers other extra) vector decision (by omega) 12 10 0 ((readied.lookup 12 (by decide)).trans input.zero) placed.clear
      have actual : node.older = 0 := by rw [older _ _ above, if_pos final]
      exact ⟨selected, 11, X86FuelPrefix.fetches_then 10 1 before f selected firstTen cleared, by simp [final],
        (X86StateFrame.registerOnly (readied.trans clearFrame)).mono (by decide) (Finset.Subset.refl _),
        (clearFrame.lookup 6 (by decide)).trans bankKnown, actual ▸ zero,
        (clearFrame.lookup 0 (by decide)).trans retained, endpoint⟩
    · simp only [if_neg final] at decision
      have actual : node.older = prev := by rw [older _ _ above, if_neg final]
      exact ⟨f, 10, firstTen, by simp [final],
        (X86StateFrame.registerOnly readied).mono (by decide) (Finset.Subset.refl _), bankKnown,
        actual ▸ (check.lookup 10 (by decide)).trans new, retained, ⟨decision⟩⟩
  obtain ⟨selected, setup, got, cost, ready, bankKnown, predecessor, finalLength, ⟨atStore⟩⟩ := link
  have storesCode : Code image (start + 38) (NativeStores.emitted encoding (writes bank node)) :=
    fixed_bytes bank node ▸ placed.words
  have operands (w : NativeStores.Write bank.pointer) (present : w ∈ writes bank node) :
      lookup selected w.source = some w.value := by
    obtain ⟨i, rfl⟩ := member present
    fin_cases i
    · exact predecessor
    · exact (ready.lookup 1 (by decide)).trans input.left
    · exact (ready.lookup 2 (by decide)).trans input.right
  have codeApart : CodeApart image base (NativeStores.written (writes bank node)) := by
    intro i byte present touched
    obtain ⟨j, hit⟩ := written_at bank node touched
    exact clearOfCode j i byte present hit
  obtain ⟨a', populated, storesFrame, fields, ⟨atDecrement⟩⟩ := NativeStores.fetched (handlers other extra)
    vector encoding (writes bank node) atStore (controls.transport ready (by decide))
    (NativeStores.checked_of_emitted encoding image _ _ (by rw [fixed_bytes]; change start + 38 + 21 ≤ image.size; omega) storesCode)
    bankKnown operands (apart bank node) codeApart
  have beforeDec := ready.trans storesFrame
  obtain ⟨after, decreased, decreaseFrame, next, endpoint⟩ := X86PlacedArithmetic.executes (handlers other extra) vector
    (show At image a' base (start + 59) from atDecrement) (by omega) .sub 13 14 raw 1
    ((beforeDec.lookup 13 (by decide)).trans input.one) ((beforeDec.lookup 14 (by decide)).trans input.target) placed.decrement
  rw [arithmetic] at decreased
  change lookup after 14 = some (raw - 1) at next
  rw [beforeWord] at next
  have untouched := X86StateFrame.registerOnly decreaseFrame
  have complete : X86StateFrame.Frame clobbers (NativeStores.written (writes bank node)) before after :=
    (beforeDec.trans untouched).mono (by decide) (by simp)
  have previously : Ready layout arena after := by
    refine ⟨input.current.fits, input.current.count.preserved complete ?_, fun i j => (input.current.node i j).preserved complete ?_⟩
    · apply NativeStores.apart_written
      intro item hit
      obtain ⟨j, rfl⟩ := member hit
      exact layout.header_apart _ j
    · apply NativeStores.apart_written
      intro item hit
      obtain ⟨k, rfl⟩ := member hit
      exact layout.records_apart _ _ (by have bound := i.isLt; change i.val < ordinal - 1; omega) j k
  have stored : (X86FuelPrefix.fetches 3).run selected = .ok () a' := populated
  refine ⟨after, setup + 3 + 1, X86FuelPrefix.fetches_then (setup + 3) 1 before a' after
    (X86FuelPrefix.fetches_then setup 3 before selected a' got stored) decreased, ?_,
    complete, previously, ?_, next, ((storesFrame.trans untouched).lookup 0 (by decide)).trans finalLength, endpoint⟩
  · rw [cost]
    split <;> rfl
  · intro j
    have wrote := fields (writeAt bank node j) (by fin_cases j <;> simp [writes, writeAt, NativeAgendaInsert.writes])
    exact wrote.preserved untouched (by simp)

end Mettapedia.Machines.TIsa.StoreInstructions.NativePendingWrite
