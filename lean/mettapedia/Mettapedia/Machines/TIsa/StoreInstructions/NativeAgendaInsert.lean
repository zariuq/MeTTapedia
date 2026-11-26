import Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaReserve
import Mettapedia.Machines.TIsa.StoreInstructions.NativeStores

/-!
# One fetched insertion into a private agenda extension

The provisional length is in r14 and the provisional root in
r11. The actual child operands are in r9 and r10. The code
derives the new record address from the length, writes the
three words, and then updates the provisional root. The live
length in metadata remains unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaInsert

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads CodeApart footprint Encoding)
open X86PlacedScalar (Code registerCode)
open X86PreparedLea (Index)
open X86IndexedAddress (Base addressCode)
open PackedEquations (Arena Node readWords)
open NativeAgendaRecords (Records field)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def incrementCode : List ℕ := registerCode (X86Arithmetic.opcode .add) 13 14
def copyCode : List ℕ := registerCode 0x89 14 0
def ordinalReg : Index := ⟨0, by decide⟩
def ordinalBase : Base := ⟨0, by decide⟩
def strideCode : List ℕ := addressCode 0 ordinalReg 1 ordinalBase
def baseCode : List ℕ := registerCode 0x89 5 2
def storeBase : Base := ⟨2, by decide⟩
def locateCode : List ℕ := addressCode 2 ordinalReg 3 storeBase
def encoding : Encoding := .direct 2 (by decide) (by decide)
def stores : List ℕ := encoding.bytes 11 0 ++ (encoding.bytes 9 8 ++ encoding.bytes 10 16)
def rootCode : List ℕ := registerCode 0x89 14 11

def emit : List ℕ :=
  incrementCode ++ (copyCode ++ (strideCode ++ (baseCode ++ (locateCode ++ (stores ++ rootCode)))))

theorem emit_size : emit.length = 41 := rfl

structure Placed (image : NativeImage.View) (start : ℕ) : Prop where
  extent : start + 41 ≤ image.size
  increment : Code image start incrementCode
  copy : Code image (start + 3) copyCode
  stride : Code image (start + 6) strideCode
  base : Code image (start + 10) baseCode
  locate : Code image (start + 13) locateCode
  stores : Code image (start + 17) stores
  root : Code image (start + 38) rootCode

theorem placed_of_emitted (image : NativeImage.View) (start : ℕ) (size : start + 41 ≤ image.size)
    (installed : Code image start emit) : Placed image start := by
  obtain ⟨a, tail⟩ := NativeWords.code_append (show Code image start (incrementCode ++ _) from installed)
  obtain ⟨b, tail⟩ := NativeWords.code_append tail
  obtain ⟨c, tail⟩ := NativeWords.code_append tail
  obtain ⟨d, tail⟩ := NativeWords.code_append tail
  obtain ⟨e, tail⟩ := NativeWords.code_append tail
  obtain ⟨f, g⟩ := NativeWords.code_append tail
  exact ⟨size, a, b, c, d, e, f, g⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register := {.rax, .rdx, .r11, .r14, .rflags, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

def source (j : Fin 3) : Fin 16 :=
  match j.val with | 0 => 11 | 1 => 9 | _ => 10

def writeAt (record : WordRegion.Region 3) (node : Node) (j : Fin 3) : NativeStores.Write record.pointer :=
  ⟨source j, _, record.cell j, field node j⟩

def writes (record : WordRegion.Region 3) (node : Node) : List (NativeStores.Write record.pointer) :=
  [writeAt record node 0, writeAt record node 1, writeAt record node 2]

theorem write_members {record : WordRegion.Region 3} {node : Node} {write : NativeStores.Write record.pointer}
    (found : write ∈ writes record node) : ∃ j : Fin 3, write = writeAt record node j := by
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at found
  rcases found with left | center | right
  · exact ⟨0, left⟩
  · exact ⟨1, center⟩
  · exact ⟨2, right⟩

theorem write_apart (record : WordRegion.Region 3) (node : Node) : NativeStores.Separate (writes record node) := by
  apply List.pairwise_cons.mpr
  refine ⟨?_, List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, .nil⟩⟩⟩
  · intro item member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h
    · subst item
      exact record.separate_words (by decide : (0 : Fin 3) ≠ 1)
    · subst item
      exact record.separate_words (by decide : (0 : Fin 3) ≠ 2)
  · intro item member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst item
    exact record.separate_words (by decide : (1 : Fin 3) ≠ 2)
  · intro _ impossible
    cases impossible

theorem stores_independent (record : WordRegion.Region 3) (node : Node) :
    NativeStores.emitted encoding (writes record node) = stores := rfl

private theorem stride (root : Word) : (root + root * 2) * 8 = root * 24 := by
  calc
    _ = (root * 1 + root * 2) * 8 := congrArg (fun x : Word => (x + root * 2) * 8) (BitVec.mul_one root).symm
    _ = (root * ((1 : Word) + 2)) * 8 := congrArg (fun x : Word => x * 8) (@BitVec.mul_add 64 root 1 2).symm
    _ = root * (((1 : Word) + 2) * 8) := BitVec.mul_assoc _ _ _
    _ = root * 24 := rfl

variable {capacity : ℕ} {layout : NativeAgendaRecords.Layout capacity} {arena : Arena}

structure Inputs (layout : NativeAgendaRecords.Layout capacity) (arena : Arena)
    (node : Node) (before : Native) : Prop where
  records : Records layout arena before
  base : lookup before 5 = some layout.words.pointer
  length : lookup before 14 = some (BitVec.ofNat 64 arena.size)
  one : lookup before 13 = some 1
  tail : lookup before 11 = some node.older
  left : lookup before 9 = some node.left
  right : lookup before 10 = some node.right

def footprintOf (layout : NativeAgendaRecords.Layout capacity) (arena : Arena) (room : arena.size < capacity)
    (node : Node) : Finset ℕ :=
  NativeStores.written (writes (layout.record ⟨arena.size, room⟩) node)

theorem footprint_member (layout : NativeAgendaRecords.Layout capacity) (arena : Arena) (room : arena.size < capacity)
    (node : Node) {byte : ℕ} (hit : byte ∈ footprintOf layout arena room node) :
    ∃ j : Fin 3, byte ∈ footprint ((layout.record ⟨arena.size, room⟩).cell j).address := by
  simp only [footprintOf, writes, NativeStores.written, Finset.union_empty, Finset.mem_union] at hit
  rcases hit with h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩

theorem preserves_header (layout : NativeAgendaRecords.Layout capacity) (arena : Arena) (room : arena.size < capacity)
    (node : Node) :
    Disjoint (footprint (layout.header.cell 0).address) (footprintOf layout arena room node) := by
  apply NativeStores.apart_written
  intro item h
  obtain ⟨j, rfl⟩ := write_members h
  exact layout.header_apart ⟨arena.size, room⟩ j

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start)
    (node : Node) (input : Inputs layout arena node before) (room : arena.size < capacity)
    (history : List (Word × Word)) (old : readWords arena node.older = some history)
    (bounded : node.older.toNat ≤ arena.size)
    (apart : CodeApart image base (footprintOf layout arena room node)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 9).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (footprintOf layout arena room node) before after ∧
      Records layout (arena.push node) after ∧
      lookup after 14 = some (PackedEquations.next arena) ∧ lookup after 11 = some (PackedEquations.next arena) ∧
      readWords (arena.push node) (PackedEquations.next arena) = some ((node.left, node.right) :: history) ∧
      Nonempty (At image after base (start + 41)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  have sizeLimit := layout.words.positive_room (show 0 < 3 * (capacity + 1) by omega)
  have fits : PackedEquations.CanAppend arena node.older := ⟨bounded, by omega⟩
  let next := PackedEquations.next arena
  have nextIndex := PackedEquations.next_exact fits
  let index : Fin capacity := ⟨arena.size, room⟩
  let record := layout.record index
  have recordAddress := layout.record_pointer next index nextIndex
  have arithmeticHandler : X86Arithmetic.linkedHandlers (handlers other extra) = handlers other extra := rfl
  obtain ⟨a, incremented, incrFrame, newCount, ⟨atCopy⟩⟩ := X86PlacedArithmetic.executes
    (handlers other extra) vector point (by omega) .add 13 14 _ 1 input.one input.length placed.increment
  rw [arithmeticHandler] at incremented
  have exactCount : lookup a 14 = some next := by
    change lookup a 14 = some (BitVec.ofNat 64 arena.size + BitVec.ofNat 64 1) at newCount
    rw [BitVec.ofNat_add_ofNat] at newCount
    exact newCount
  obtain ⟨b, copied, copyFrame, copiedCount, ⟨atStride⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector atCopy (by omega) 14 0 next exactCount placed.copy
  obtain ⟨c, scaled, scaleFrame, tripled, ⟨atBase⟩⟩ := X86IndexedAddress.forms_address
    other extra vector (show At image b base (start + 6) from atStride) (by omega) 0 ordinalReg 1 ordinalBase
    placed.stride next next copiedCount copiedCount
  have prelude := (incrFrame.trans copyFrame).trans scaleFrame
  obtain ⟨d, based, baseFrame, location, ⟨atLocate⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector (show At image c base (start + 10) from atBase) (by omega) 5 2
    layout.words.pointer ((prelude.lookup 5 (by decide)).trans input.base) placed.base
  obtain ⟨e, located, locateFrame, address, ⟨atStore⟩⟩ := X86IndexedAddress.forms_address
    other extra vector (show At image d base (start + 13) from atLocate) (by omega) 2 ordinalReg 3 storeBase placed.locate
    layout.words.pointer _ location ((baseFrame.lookup 0 (by decide)).trans tripled)
  change lookup e 2 = some (layout.words.pointer + (next + next * 2) * 8) at address
  rw [stride, ← recordAddress] at address
  have beforeStore := X86StateFrame.registerOnly ((prelude.trans baseFrame).trans locateFrame)
  have bytes : Code image (start + 17) (NativeStores.emitted encoding (writes record node)) := by
    rw [stores_independent]
    exact placed.stores
  have bounds : start + 17 + (NativeStores.emitted encoding (writes record node)).length ≤ image.size := by
    rw [stores_independent]
    change start + 17 + 21 ≤ image.size
    omega
  have loads (write : NativeStores.Write record.pointer) (found : write ∈ writes record node) :
      lookup e write.source = some write.value := by
    obtain ⟨j, rfl⟩ := write_members found
    fin_cases j
    · exact (beforeStore.lookup 11 (by decide)).trans input.tail
    · exact (beforeStore.lookup 9 (by decide)).trans input.left
    · exact (beforeStore.lookup 10 (by decide)).trans input.right
  obtain ⟨f, stored, storeFrame, populated, ⟨atRoot⟩⟩ := NativeStores.fetched (handlers other extra) vector
    encoding (writes record node) (show At image e base (start + 17) from atStore)
    (controls.transport beforeStore (by decide)) (NativeStores.checked_of_emitted encoding image _ _ bounds bytes)
    address loads (write_apart record node) apart
  have keptCount := ((((copyFrame.trans scaleFrame).trans baseFrame).trans locateFrame).lookup 14 (by decide)).trans exactCount
  obtain ⟨after, rooted, rootFrame, knownRoot, endpoint⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector (show At image f base (start + 38) from atRoot) (by omega)
    14 11 next ((storeFrame.lookup 14 (by decide)).trans keptCount) placed.root
  have all : X86StateFrame.Frame clobbers (footprintOf layout arena room node) before after :=
    ((beforeStore.trans storeFrame).trans (X86StateFrame.registerOnly rootFrame)).mono (by decide)
      (by
        simp only [Finset.empty_union, Finset.union_empty, footprintOf, record, index]
        exact Finset.Subset.refl _)
  have content : Records layout (arena.push node) after := by
    have fitsRoom : (arena.push node).size ≤ capacity := by simp only [Array.size_push]; omega
    refine ⟨fitsRoom, fun i j => ?_⟩
    by_cases appended : i.val = arena.size
    · have atLast : (arena.push node)[i] = node := by
        change (arena.push node)[i.val] = node
        simp [Array.getElem_push, appended]
      have sameSlot : (⟨i.val, i.isLt.trans_le fitsRoom⟩ : Fin capacity) = index := Fin.ext appended
      have present := populated (writeAt record node j) (by fin_cases j <;> simp [writes])
      rw [atLast, sameSlot]
      exact present.preserved (X86StateFrame.registerOnly rootFrame) (by simp)
    · have earlier : i.val < arena.size := by have goes := i.isLt; simp only [Array.size_push] at goes; omega
      let k : Fin arena.size := ⟨i.val, earlier⟩
      have atEarlier : (arena.push node)[i] = arena[k] := by
        change (arena.push node)[i.val] = arena[i.val]
        simp [Array.getElem_push, earlier]
      have stays := input.records.node k j
      rw [atEarlier]
      apply stays.preserved all
      apply NativeStores.apart_written
      intro item member
      obtain ⟨col, rfl⟩ := write_members member
      exact layout.records_apart ⟨k.val, k.isLt.trans_le input.records.fits⟩ index earlier j col
  have firstTwo := X86FuelPrefix.fetches_then 1 1 before a b incremented copied
  have firstThree := X86FuelPrefix.fetches_then 2 1 before b c firstTwo scaled
  have firstFour := X86FuelPrefix.fetches_then 3 1 before c d firstThree based
  have firstFive := X86FuelPrefix.fetches_then 4 1 before d e firstFour located
  have firstEight := X86FuelPrefix.fetches_then 5 3 before e f firstFive stored
  exact ⟨after, X86FuelPrefix.fetches_then 8 1 before f after firstEight rooted, all, content,
    ((storeFrame.trans (X86StateFrame.registerOnly rootFrame)).lookup 14 (by decide)).trans keptCount,
    knownRoot, PackedEquations.appended_read PackedEquations.wordCodes fits old
      (PackedEquations.word_decode _) (PackedEquations.word_decode _), endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaInsert
