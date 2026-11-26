import Mettapedia.Machines.TIsa.StoreInstructions.NativePendingWrite
import Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaRemapPair
import Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaLoop

/-!
# Filling the staged agenda from the original cursor

The read cursor follows the old links; the write cursor moves
down through the reserved suffix. The old length remains live
while the new records are initialized. Each matching pair of
source and destination cursors advances independently.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativePendingFill

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads CodeApart footprint)
open X86PlacedScalar (Code Jump jumpDelta)
open NativeArenaGeometry (Region)
open NativeAgendaRecords (Ready Records field)
open NativeAgendaLoop (Within)
open NativeSubstLeaf (MapReady)
open PackedEquations (Arena Node readWords)
open PackedWorklist (Words)
open PackedAgendaCoordinates (recordAt)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def emit (start done malformed : ℕ) : List ℕ :=
  NativeAgendaRead.emit start done malformed ++
    (NativeAgendaRemapPair.emit (start + 72) malformed ++
      (NativePendingWrite.emit (start + 112) ++ X86UnconditionalJump.Block.code (jumpDelta (start + 174) start)))

theorem emit_size (start done malformed : ℕ) : (emit start done malformed).length = 179 := by
  simp only [emit, List.length_append, NativeAgendaRead.emit_size, NativeAgendaRemapPair.emit_size,
    NativePendingWrite.emit_size, X86UnconditionalJump.Block.code_length]

structure Placed (image : NativeImage.View) (start done malformed : ℕ) : Prop where
  extent : start + 179 ≤ image.size
  read : NativeAgendaRead.Placed image start done malformed
  pair : NativeAgendaRemapPair.Placed image (start + 72) malformed
  write : NativePendingWrite.Placed image (start + 112)
  again : Jump image (start + 174) start

theorem placed_of_emitted (image : NativeImage.View) (start done malformed : ℕ)
    (extent : start + 179 ≤ image.size) (finish : done ≤ image.size)
    (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31) (code : Code image start (emit start done malformed)) :
    Placed image start done malformed := by
  obtain ⟨read, rest⟩ := NativeWords.code_append (show Code image start (NativeAgendaRead.emit start done malformed ++ _) from code)
  rw [NativeAgendaRead.emit_size] at rest
  obtain ⟨pair, rest⟩ := NativeWords.code_append rest
  rw [NativeAgendaRemapPair.emit_size] at rest
  obtain ⟨write, again⟩ := NativeWords.code_append rest
  rw [NativePendingWrite.emit_size] at again
  refine ⟨extent, NativeAgendaRead.placed_of_emitted image _ done malformed (by omega) finish bad short read,
    NativeAgendaRemapPair.placed_of_emitted image _ malformed (by omega) bad short pair,
    NativePendingWrite.placed_of_emitted image _ (by omega) short write,
    ⟨by omega, by omega, ?_, again⟩⟩
  unfold jumpDelta
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
  omega

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rax, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .r14, .rflags, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {capacity mapCapacity : ℕ}
variable {layout : NativeAgendaRecords.Layout capacity} {table : Region mapCapacity}
variable {arena : Arena} {mapping : Array Word}
variable {image : NativeImage.View} {base : BitVec 48}

structure Geometry (layout : NativeAgendaRecords.Layout capacity) (table : Region mapCapacity)
    (image : NativeImage.View) (base : BitVec 48) : Prop where
  code : ∀ i j, CodeApart image base (footprint ((layout.record i).cell j).address)
  apart : NativeBindingSelection.Separated layout.words table

theorem Geometry.map_apart (space : Geometry layout table image base) (m : Fin mapCapacity)
    (index : Fin capacity) (column : Fin 3) :
    Disjoint (footprint ((table.wordCell m).cell 0).address) (footprint ((layout.record index).cell column).address) :=
  (layout.words.separate_arenas table space.apart (3 * (index.val + 1)) 3 m.val 1
    (by decide) (by decide) (by have bound := index.isLt; omega) m.isLt (by decide) (by decide) column 0).symm

theorem Within.separate {lo hi : ℕ} {writes : Finset ℕ} (inside : Within layout lo hi writes) (held : Finset ℕ)
    (different : ∀ (i : Fin capacity) (j : Fin 3), lo ≤ i.val → i.val < hi →
      Disjoint held (footprint ((layout.record i).cell j).address)) :
    Disjoint held writes := by
  apply Finset.disjoint_left.mpr
  intro byte saved changed
  obtain ⟨i, j, lower, upper, there⟩ := inside byte changed
  exact Finset.disjoint_left.mp (different i j lower upper) saved there

structure Input (layout : NativeAgendaRecords.Layout capacity) (table : Region mapCapacity) (arena : Arena)
    (mapping : Array Word) (root endWord : Word) (remaining : ℕ) (native : Native) : Prop where
  current : Ready layout arena native
  map : MapReady table mapping native
  agendaBase : lookup native 5 = some layout.words.pointer
  mapBase : lookup native 7 = some (table.atWord 0)
  mapCount : lookup native 15 = some (BitVec.ofNat 64 mapping.size)
  floor : lookup native 3 = some (BitVec.ofNat 64 arena.size)
  cursor : lookup native 11 = some root
  ordinal : lookup native 14 = some (BitVec.ofNat 64 (arena.size + remaining))
  reserved : lookup native 0 = some endWord
  zero : lookup native 12 = some 0
  one : lookup native 13 = some 1

structure Staged (layout : NativeAgendaRecords.Layout capacity) (floor : ℕ) (pairs : Words) (native : Native) : Prop where
  fits : floor + pairs.length ≤ capacity
  record : ∀ (i : Fin pairs.length) (j : Fin 3),
    Reads native ((layout.record ⟨floor + (pairs.length - 1 - i.val), by have bound := i.isLt; omega⟩).cell j).address
      (field (recordAt floor 0 (pairs.length - 1 - i.val) pairs[i.val]) j)

private theorem Staged.cons {floor : ℕ} {pairs : Words} {before : Native} (later : Staged layout floor pairs before)
    (first : Word × Word) (room : floor + (first :: pairs).length ≤ capacity)
    (head : ∀ j : Fin 3, Reads before ((layout.record ⟨floor + pairs.length, by simp only [List.length_cons] at room; omega⟩).cell j).address
      (field (recordAt floor 0 pairs.length first) j)) :
    Staged layout floor (first :: pairs) before := by
  refine ⟨room, fun i j => ?_⟩
  rcases i with ⟨i, ilt⟩
  cases i with
  | zero =>
    have index : (first :: pairs).length - 1 - 0 = pairs.length := by simp
    have slot : (⟨floor + ((first :: pairs).length - 1 - 0), by omega⟩ : Fin capacity) =
        ⟨floor + pairs.length, by omega⟩ := Fin.ext (congrArg (floor + ·) index)
    rw [slot, index]
    exact head j
  | succ n =>
    have inside : n < pairs.length := by simp only [List.length_cons] at ilt; omega
    have index : (first :: pairs).length - 1 - (n + 1) = pairs.length - 1 - n := by simp only [List.length_cons]; omega
    have slot : (⟨floor + ((first :: pairs).length - 1 - (n + 1)), by omega⟩ : Fin capacity) =
        ⟨floor + (pairs.length - 1 - n), by omega⟩ := Fin.ext (congrArg (floor + ·) index)
    rw [slot, index]
    exact later.record ⟨n, inside⟩ j

/-- One actual iteration translates one pending occurrence and
leaves an initialized record at the reserved destination. -/
theorem fetched_one (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start done malformed : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start done malformed)
    (space : Geometry layout table image base) (root endWord : Word) (first rewritten : Word × Word) (pending : Words)
    (input : Input layout table arena mapping root endWord (pending.length + 1) before)
    (known : readWords arena root = some (first :: pending))
    (matched : PackedSubstitution.mappedPair mapping first = some rewritten)
    (fits : arena.size + pending.length + 1 ≤ capacity) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps bytes older, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      steps = 38 + (if pending = [] then 1 else 0) ∧
      X86StateFrame.Frame clobbers bytes before after ∧
      Within layout (arena.size + pending.length) (arena.size + pending.length + 1) bytes ∧
      Input layout table arena mapping older endWord pending.length after ∧ readWords arena older = some pending ∧
      (∀ j : Fin 3, Reads after ((layout.record ⟨arena.size + pending.length, by omega⟩).cell j).address
        (field (recordAt arena.size 0 pending.length rewritten) j)) ∧
      Nonempty (At image after base start) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨node, shape, pair, tail⟩ := NativeAgendaRecords.top_of_read arena root (first :: pending) known
  obtain ⟨a, scanned, readFrame, arrival⟩ := NativeAgendaRead.fetched other extra vector
    point controls placed.read input.current input.agendaBase root input.cursor input.zero
  rw [NativeAgendaRead.cost_pop arena root node shape] at scanned
  simp only [NativeAgendaRead.Arrival, shape] at arrival
  obtain ⟨older, left, right, ⟨atPair⟩⟩ := arrival
  have remap : NativeAgendaRemapPair.Input table mapping node.left node.right a :=
    ⟨input.map.preserved readFrame, (readFrame.lookup 7 (by decide)).trans input.mapBase,
      (readFrame.lookup 15 (by decide)).trans input.mapCount, left, right⟩
  obtain ⟨b, translated, computed, pairFrame, selected⟩ := NativeAgendaRemapPair.fetched other extra vector
    atPair (controls.transport readFrame NativeAgendaRead.clobbers_data) placed.pair node.left node.right remap
  rw [pair, matched] at selected
  obtain ⟨rfl, newLeft, newRight, ⟨atWrite⟩⟩ := selected
  have throughPair : X86StateFrame.Frame clobbers ∅ before b :=
    (readFrame.trans pairFrame).mono (by decide) (by simp)
  have target := ((readFrame.trans pairFrame).lookup 14 (by decide)).trans input.ordinal
  let ordinal := arena.size + (pending.length + 1)
  have positive : arena.size < ordinal := by dsimp [ordinal]; omega
  have spaceFits : ordinal ≤ capacity := by dsimp [ordinal]; omega
  let i : Fin capacity := ⟨arena.size + pending.length, by omega⟩
  have coord : ordinal - 1 = i.val := by change arena.size + (pending.length + 1) - 1 = arena.size + pending.length; omega
  have slot : (⟨ordinal - 1, by omega⟩ : Fin capacity) = i := Fin.ext coord
  have offset : ordinal - 1 - arena.size = pending.length := by dsimp [ordinal]; omega
  have writeInput : NativePendingWrite.Input layout arena ordinal rewritten b :=
    ⟨input.current.preserved throughPair, (throughPair.lookup 5 (by decide)).trans input.agendaBase,
      (throughPair.lookup 3 (by decide)).trans input.floor, target, newLeft, newRight,
      (throughPair.lookup 12 (by decide)).trans input.zero, (throughPair.lookup 13 (by decide)).trans input.one⟩
  obtain ⟨c, work, wrote, count, writeFrame, current, ready, nextOrdinal, reserved, ⟨atJump⟩⟩ :=
    NativePendingWrite.fetched other extra vector atWrite (controls.transport throughPair clobbers_data) placed.write
      ordinal rewritten writeInput endWord ((readFrame.trans pairFrame).lookup 0 (by decide) |>.trans input.reserved)
      positive spaceFits (fun j => slot ▸ space.code i j)
  obtain ⟨after, jumped, jumpedFrame, endpoint⟩ := X86PlacedScalar.jump (X86PlacedFrameAddress.nativeBase other)
    extra vector (show At image c base (start + 174) from atJump) placed.again
  have jumpFrame := X86StateFrame.registerOnly jumpedFrame
  let words := NativeStores.written (NativePendingWrite.writes (layout.record ⟨ordinal - 1, by omega⟩)
    (recordAt arena.size 0 (ordinal - 1 - arena.size) rewritten))
  have localWrites : Within layout (arena.size + pending.length) (arena.size + pending.length + 1) words := by
    intro byte modified
    obtain ⟨j, localByte⟩ := NativePendingWrite.written_at _ _ modified
    rw [slot] at localByte
    exact ⟨i, j, Nat.le_refl _, by change arena.size + pending.length < arena.size + pending.length + 1; omega, localByte⟩
  have all : X86StateFrame.Frame clobbers words before after :=
    ((throughPair.trans writeFrame).trans jumpFrame).mono (by decide) (by
      simp only [Finset.empty_union, Finset.union_empty, words]
      exact Finset.Subset.refl _)
  have output : Input layout table arena mapping node.older endWord pending.length after :=
    ⟨current.preserved jumpFrame, input.map.kept all (fun index =>
      Within.separate localWrites _ (fun d j _ _ => space.map_apart index d j)),
      (all.lookup 5 (by decide)).trans input.agendaBase, (all.lookup 7 (by decide)).trans input.mapBase,
      (all.lookup 15 (by decide)).trans input.mapCount, (all.lookup 3 (by decide)).trans input.floor,
      (((pairFrame.trans writeFrame).trans jumpFrame).lookup 11 (by decide)).trans older,
      (jumpedFrame.lookup 14 (by decide)).trans (by simpa only [coord, i] using nextOrdinal),
      (jumpedFrame.lookup 0 (by decide)).trans reserved,
      (all.lookup 12 (by decide)).trans input.zero, (all.lookup 13 (by decide)).trans input.one⟩
  have ran := X86FuelPrefix.fetches_then (23 + work) 1 before c after
    (X86FuelPrefix.fetches_then 23 work before b c (X86FuelPrefix.fetches_then 15 8 before a b scanned computed) wrote) jumped
  refine ⟨after, _, words, node.older, ran, ?_, all, localWrites, output, tail, ?_, endpoint⟩
  · have bottom : ordinal - 1 = arena.size ↔ pending = [] := by
      rw [show ordinal - 1 = arena.size + pending.length from coord]
      simp
    rw [count, if_congr bottom rfl rfl]
    split <;> rfl
  · intro j
    have saved := (ready j).preserved jumpFrame (by simp)
    rwa [slot, offset] at saved

/-- The staged suffix and the old prefix initialize exactly
the arena returned by the existing ordered prepend operation.
This does not change the live length. -/
theorem Staged.records {pending : Words} {updated : Arena} {head : Word} {native : Native}
    (staged : Staged layout arena.size pending native) (old : Ready layout arena native)
    (built : PackedEquations.prependWords arena 0 pending = some (updated, head)) :
    Records layout updated native := by
  have coordinates := PackedAgendaCoordinates.coordinates arena 0 pending built
  have size := coordinates.size
  have fits : updated.size ≤ capacity := size ▸ staged.fits
  refine ⟨fits, fun index col => ?_⟩
  have present := index.isLt
  change Reads native ((layout.record ⟨index.val, present.trans_le fits⟩).cell col).address
    (field updated[index.val] col)
  by_cases prior : index.val < arena.size
  · have unchanged := coordinates.preserved index.val prior
    rw [Array.getElem?_eq_getElem present, Array.getElem?_eq_getElem prior] at unchanged
    rw [Option.some.inj unchanged]
    exact old.node ⟨index.val, prior⟩ col
  · let offset := index.val - arena.size
    have enough : offset < pending.length := by dsimp [offset]; omega
    let source : Fin pending.length := ⟨pending.length - 1 - offset, by omega⟩
    have offsetExact : pending.length - 1 - source.val = offset := by dsimp [source]; omega
    have correctAt : arena.size + offset = index.val := by dsimp [offset]; omega
    have slot : (⟨arena.size + (pending.length - 1 - source.val), by omega⟩ : Fin capacity) =
        ⟨index.val, present.trans_le fits⟩ := Fin.ext ((congrArg (arena.size + ·) offsetExact).trans correctAt)
    have identity := coordinates.descending source.val pending[source.val] (List.getElem?_eq_getElem source.isLt)
    dsimp only at identity
    rw [offsetExact, correctAt, Array.getElem?_eq_getElem present] at identity
    have reads := staged.record source col
    rw [slot, offsetExact] at reads
    rw [Option.some.inj identity]
    exact reads

/-- The fill pass realizes every remapped occurrence. Its
only stores belong to the future suffix, and the original
agenda and initialized map remain readable at the exit. -/
theorem fetched_all (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start done malformed : ℕ} (placed : Placed image start done malformed)
    (space : Geometry layout table image base) (endWord : Word)
    (pending remapped : Words) (mapped : PackedSubstitution.remapPending mapping pending = some remapped)
    (fits : arena.size + pending.length ≤ capacity) (root : Word) (known : readWords arena root = some pending)
    {before : Native} (point : At image before base start) (controls : Controls before)
    (input : Input layout table arena mapping root endWord pending.length before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after writes, (X86FuelPrefix.fetches (38 * pending.length + 2 + (if pending = [] then 0 else 1))).run before = .ok () after ∧
      X86StateFrame.Frame clobbers writes before after ∧ Within layout arena.size (arena.size + pending.length) writes ∧
      Input layout table arena mapping 0 endWord 0 after ∧ Staged layout arena.size remapped after ∧
      Nonempty (At image after base done) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  induction pending generalizing before remapped root with
  | nil =>
    obtain rfl := Option.some.inj mapped
    have selected := NativeAgendaRecords.top_of_read arena root [] known
    have isEmpty := NativeAgendaRead.empty_cursor arena root selected
    subst root
    obtain ⟨after, ran, frame, exit⟩ := NativeAgendaRead.fetched other extra vector point controls placed.read
      input.current input.agendaBase 0 input.cursor input.zero
    rw [NativeAgendaRead.cost_empty arena 0 selected] at ran
    simp only [NativeAgendaRead.Arrival, selected] at exit
    have out : Input layout table arena mapping 0 endWord 0 after :=
      ⟨input.current.preserved frame, input.map.preserved frame,
        (frame.lookup 5 (by decide)).trans input.agendaBase, (frame.lookup 7 (by decide)).trans input.mapBase,
        (frame.lookup 15 (by decide)).trans input.mapCount, (frame.lookup 3 (by decide)).trans input.floor, exit.1,
        (frame.lookup 14 (by decide)).trans input.ordinal, (frame.lookup 0 (by decide)).trans input.reserved,
        (frame.lookup 12 (by decide)).trans input.zero, (frame.lookup 13 (by decide)).trans input.one⟩
    exact ⟨after, ∅, ran, frame.mono (by decide) (Finset.Subset.refl _), by simp [Within], out,
      ⟨fits, fun i => Fin.elim0 i⟩, exit.2⟩
  | cons first pending ih =>
    unfold PackedSubstitution.remapPending at mapped
    rw [List.mapM_cons] at mapped
    obtain ⟨item, matched, later⟩ := Option.bind_eq_some_iff.mp mapped
    obtain ⟨restored, tailMap, form⟩ := Option.bind_eq_some_iff.mp later
    obtain rfl := Option.some.inj (show some (item :: restored) = some remapped from form)
    have size := PackedAgendaCoordinates.remap_length mapping pending restored tailMap
    have capacityFits : arena.size + pending.length + 1 ≤ capacity := fits
    obtain ⟨middle, used, wrote, cursor, ran, work, firstFrame, firstWrites, advance, tail, initialized, ⟨again⟩⟩ :=
      fetched_one other extra vector point controls placed space root endWord first item pending input known matched capacityFits
    obtain ⟨after, more, finished, tailFrame, tailWrites, out, staged, doneAt⟩ :=
      ih restored tailMap (by omega) cursor tail again (controls.transport firstFrame clobbers_data) advance
    have headReads (j : Fin 3) : Reads after ((layout.record ⟨arena.size + restored.length, by omega⟩).cell j).address
          (field (recordAt arena.size 0 restored.length item) j) := by
      let high : Fin capacity := ⟨arena.size + pending.length, by omega⟩
      have kept := (initialized j).preserved tailFrame
        (Within.separate tailWrites _ (fun i col _ low =>
          (layout.records_apart i high (show i.val < high.val from low) col j).symm))
      have sameSlot : (⟨arena.size + restored.length, by omega⟩ : Fin capacity) = high :=
        Fin.ext (congrArg (arena.size + ·) size)
      rw [sameSlot, size]
      exact kept
    have stagedAll := staged.cons item (by simp only [List.length_cons, size]; omega) headReads
    have confined : Within layout arena.size (arena.size + (first :: pending).length) (wrote ∪ more) := by
      intro byte changed
      rcases Finset.mem_union.mp changed with top | rest
      · obtain ⟨i, j, lower, upper, live⟩ := firstWrites byte top
        exact ⟨i, j, by omega, upper, live⟩
      · obtain ⟨i, j, lower, upper, live⟩ := tailWrites byte rest
        exact ⟨i, j, lower, by simp only [List.length_cons]; omega, live⟩
    have trace := X86FuelPrefix.fetches_then used _ before middle after ran finished
    refine ⟨after, wrote ∪ more, ?_, (firstFrame.trans tailFrame).mono (by simp) (Finset.Subset.refl _),
      confined, out, stagedAll, doneAt⟩
    have total : used + (38 * pending.length + 2 + (if pending = [] then 0 else 1)) =
        38 * (first :: pending).length + 2 + (if first :: pending = [] then 0 else 1) := by
      simp only [work, List.length_cons, List.cons_ne_nil, if_false]
      split_ifs <;> omega
    rwa [total] at trace

end Mettapedia.Machines.TIsa.StoreInstructions.NativePendingFill
