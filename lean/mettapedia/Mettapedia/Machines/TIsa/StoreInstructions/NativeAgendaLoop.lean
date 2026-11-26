import Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaInsert

/-!
# The descending native loop for a reserved child prefix

The loop starts from an exact pair of spans and a reserved group
of agenda slots. The counter is the number of children not yet
visited. It reads from right to left and pushes onto the root so
the pending equations are finally in the original left-to-right
order. The live count word is not published by this loop.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaLoop

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls CodeApart Reads footprint)
open X86PlacedScalar (Code CompareBranch Jump registerCode jumpDelta)
open NativeChildPair (Spans spanPointer)
open PackedEquations (Arena Node readWords)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def decrementCode : List ℕ := registerCode (X86Arithmetic.opcode .sub) 13 1

def emit (start finished malformed : ℕ) : List ℕ :=
  NativeDecisions.compareBytes .lessUnsigned 12 1 start finished ++
    (decrementCode ++ (NativeChildPair.emit (start + 12) malformed ++ (NativeAgendaInsert.emit ++
      X86UnconditionalJump.Block.code (jumpDelta (start + 84) start))))

theorem emit_size (start finished malformed : ℕ) : (emit start finished malformed).length = 89 := rfl

structure Placed (image : NativeImage.View) (start finished malformed : ℕ) : Prop where
  extent : start + 89 ≤ image.size
  check : CompareBranch image start finished .lessUnsigned 12 1
  decrement : Code image (start + 9) decrementCode
  pair : NativeChildPair.Placed image (start + 12) malformed
  insert : NativeAgendaInsert.Placed image (start + 43)
  again : Jump image (start + 84) start

theorem placed_of_emitted (image : NativeImage.View) (start finished malformed : ℕ)
    (size : start + 89 ≤ image.size) (ends : finished ≤ image.size) (bad : malformed ≤ image.size)
    (short : image.size < 2 ^ 31) (bytes : Code image start (emit start finished malformed)) :
    Placed image start finished malformed := by
  obtain ⟨test, rest⟩ := NativeWords.code_append (show Code image start
    (NativeDecisions.compareBytes .lessUnsigned 12 1 start finished ++ _) from bytes)
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨decrement, rest⟩ := NativeWords.code_append rest
  change Code image (start + 12) _ at rest
  obtain ⟨pair, rest⟩ := NativeWords.code_append rest
  rw [NativeChildPair.emit_size] at rest
  obtain ⟨insert, jump⟩ := NativeWords.code_append rest
  rw [NativeAgendaInsert.emit_size] at jump
  refine ⟨size, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) ends short test, decrement,
    NativeChildPair.placed_of_emitted image (start + 12) malformed (by omega) bad short pair,
    NativeAgendaInsert.placed_of_emitted image (start + 43) (by omega) insert,
    ⟨by omega, by omega, ?_, jump⟩⟩
  unfold jumpDelta
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
  omega

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register := {.rax, .rcx, .rdx, .r9, .r10, .r11, .r14, .rflags, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {capacity nodeCapacity edgeCapacity : ℕ}
variable {agendaLayout : NativeAgendaRecords.Layout capacity}
variable {termLayout : NativeTermArena.Layout nodeCapacity edgeCapacity} {terms : PackedTerms.Arena}
variable {left right : PackedTerms.Node} {spans : Spans terms left right}

structure Geometry (agendaLayout : NativeAgendaRecords.Layout capacity)
    (termLayout : NativeTermArena.Layout nodeCapacity edgeCapacity) (image : NativeImage.View) (base : BitVec 48) : Prop where
  code : ∀ (index : Fin capacity) (field : Fin 3), CodeApart image base
    (footprint ((agendaLayout.record index).cell field).address)
  nodes : ∀ (term : Fin nodeCapacity) (part : Fin 4) (index : Fin capacity) (field : Fin 3),
    Disjoint (footprint ((termLayout.record term).cell part).address)
      (footprint ((agendaLayout.record index).cell field).address)
  children : ∀ (child : Fin edgeCapacity) (index : Fin capacity) (field : Fin 3),
    Disjoint (footprint ((termLayout.child child).cell 0).address)
      (footprint ((agendaLayout.record index).cell field).address)

def Within (layout : NativeAgendaRecords.Layout capacity) (lo hi : ℕ) (bytes : Finset ℕ) : Prop :=
  ∀ byte ∈ bytes, ∃ (index : Fin capacity) (field : Fin 3), lo ≤ index.val ∧ index.val < hi ∧
    byte ∈ footprint ((layout.record index).cell field).address

theorem Within.preserves_count {lo hi : ℕ} {bytes : Finset ℕ}
    (fresh : Within agendaLayout lo hi bytes) :
    Disjoint (footprint (agendaLayout.header.cell 0).address) bytes := by
  apply Finset.disjoint_left.mpr
  intro byte atCount changed
  obtain ⟨index, field, _, _, written⟩ := fresh byte changed
  exact Finset.disjoint_left.mp (agendaLayout.header_apart index field) atCount written

private theorem Geometry.code_for {image : NativeImage.View} {base : BitVec 48}
    (geometry : Geometry agendaLayout termLayout image base) {lo hi : ℕ} {bytes : Finset ℕ}
    (writes : Within agendaLayout lo hi bytes) : CodeApart image base bytes := by
  intro index byte known changed
  obtain ⟨i, col, _, _, record⟩ := writes _ changed
  exact geometry.code i col index byte known record

private theorem Geometry.keep_terms {image : NativeImage.View} {base : BitVec 48}
    (geometry : Geometry agendaLayout termLayout image base) {lo hi : ℕ} {bytes : Finset ℕ}
    (writes : Within agendaLayout lo hi bytes) {before after : Native} {regs : Finset Register}
    (ready : NativeTermArena.Ready termLayout terms before) (frame : X86StateFrame.Frame regs bytes before after) :
    NativeTermArena.Ready termLayout terms after := by
  apply ready.kept frame
  · intro term part
    apply Finset.disjoint_left.mpr
    intro byte seen changed
    obtain ⟨index, field, _, _, written⟩ := writes byte changed
    exact Finset.disjoint_left.mp (geometry.nodes term part index field) seen written
  · intro child
    apply Finset.disjoint_left.mpr
    intro byte seen changed
    obtain ⟨index, field, _, _, written⟩ := writes byte changed
    exact Finset.disjoint_left.mp (geometry.children child index field) seen written

structure Inputs (agendaLayout : NativeAgendaRecords.Layout capacity)
    (termLayout : NativeTermArena.Layout nodeCapacity edgeCapacity) {terms : PackedTerms.Arena}
    {left right : PackedTerms.Node} (spans : Spans terms left right) (agenda : Arena)
    (root : Word) (remaining : ℕ) (before : Native) : Prop where
  records : NativeAgendaRecords.Records agendaLayout agenda before
  terms : NativeTermArena.Ready termLayout terms before
  agendaBase : lookup before 5 = some agendaLayout.words.pointer
  length : lookup before 14 = some (BitVec.ofNat 64 agenda.size)
  root : lookup before 11 = some root
  one : lookup before 13 = some 1
  zero : lookup before 12 = some 0
  counter : lookup before 1 = some (BitVec.ofNat 64 remaining)
  total : lookup before 8 = some (BitVec.ofNat 64 spans.leftWords.size)
  left : lookup before 6 = some (spanPointer termLayout left)
  right : lookup before 7 = some (spanPointer termLayout right)

private theorem index_nat (spans : Spans terms left right) (remaining : ℕ)
    (bound : remaining ≤ spans.leftWords.size) : (BitVec.ofNat 64 remaining).toNat = remaining := by
  have size := (PackedTerms.segment_width terms.children left spans.leftWords spans.left).1
  have word := left.childrenCount.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem decremented (n : ℕ) : BitVec.ofNat 64 (n + 1) - 1 = BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_add, show BitVec.ofNat 64 1 = (1 : Word) from rfl]
  exact BitVec.add_sub_cancel _ _

/-- Nineteen fetched instructions perform one real iteration and
return to the installed loop. The exact selected pair is then
the new head of the agenda; no metadata was published. -/
theorem fetched_iteration (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {base : BitVec 48}
    {start finished malformed : ℕ} {before : Native} (point : At image before base start)
    (controls : Controls before) (placed : Placed image start finished malformed)
    (geometry : Geometry agendaLayout termLayout image base) (spans : Spans terms left right)
    (agenda : Arena) (root : Word) (remaining : ℕ) (width : remaining + 1 ≤ spans.leftWords.size)
    (room : agenda.size < capacity) (rootBound : root.toNat ≤ agenda.size)
    (input : Inputs agendaLayout termLayout spans agenda root (remaining + 1) before)
    (history : List (Word × Word)) (held : readWords agenda root = some history) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after pair, spans.pairs[remaining]? = some pair ∧
      let node : Node := ⟨root, pair.1, pair.2⟩
      (X86FuelPrefix.fetches 19).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (NativeAgendaInsert.footprintOf agendaLayout agenda room node) before after ∧
      readWords (agenda.push node) (PackedEquations.next agenda) = some (pair :: history) ∧
      Inputs agendaLayout termLayout spans (agenda.push node) (PackedEquations.next agenda) remaining after ∧
      Nonempty (At image after base start) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  obtain ⟨a, checked, checkFrame, ⟨inside⟩⟩ := X86PlacedScalar.compare_branch
    (X86PlacedFrameAddress.nativeBase other) extra vector point .lessUnsigned 12 1 placed.check
    0 (BitVec.ofNat 64 (remaining + 1)) input.zero input.counter
  change At image a base (if decide (0 < (BitVec.ofNat 64 (remaining + 1)).toNat) then start + 9 else finished) at inside
  rw [index_nat spans (remaining + 1) width] at inside
  simp only [show 0 < remaining + 1 by omega, decide_true, if_true] at inside
  obtain ⟨b, reduced, reduceFrame, index, ⟨atPair⟩⟩ := X86PlacedArithmetic.executes (handlers other extra) vector
    inside (by omega) .sub 13 1 (BitVec.ofNat 64 (remaining + 1)) 1
    ((checkFrame.lookup 13 (by decide)).trans input.one) ((checkFrame.lookup 1 (by decide)).trans input.counter)
    placed.decrement
  have ordinary : X86Arithmetic.linkedHandlers (handlers other extra) = handlers other extra := rfl
  rw [ordinary] at reduced
  change lookup b 1 = some (BitVec.ofNat 64 (remaining + 1) - 1) at index
  rw [decremented] at index
  have beforePair := X86StateFrame.registerOnly (checkFrame.trans reduceFrame)
  obtain ⟨c, count, loaded, loadFrame, selected⟩ := NativeChildPair.fetched other extra vector
    (show At image b base (start + 12) from atPair) (controls.transport beforePair (by decide)) placed.pair
    (input.terms.preserved beforePair) left right spans (BitVec.ofNat 64 remaining) index
    ((beforePair.lookup 8 (by decide)).trans input.total) ((beforePair.lookup 6 (by decide)).trans input.left)
    ((beforePair.lookup 7 (by decide)).trans input.right)
  rw [index_nat spans remaining (by omega), if_pos (show remaining < spans.leftWords.size by omega)] at selected
  obtain ⟨pair, rfl, chosen, first, second, ⟨atInsert⟩⟩ := selected
  let node : Node := ⟨root, pair.1, pair.2⟩
  have beforeStore := beforePair.trans loadFrame
  have entries : NativeAgendaRecords.Records agendaLayout agenda c := by
    refine ⟨input.records.fits, fun i j => (input.records.node i j).preserved beforeStore (by simp)⟩
  have operands : NativeAgendaInsert.Inputs agendaLayout agenda node c :=
    ⟨entries, (beforeStore.lookup 5 (by decide)).trans input.agendaBase, (beforeStore.lookup 14 (by decide)).trans input.length,
      (beforeStore.lookup 13 (by decide)).trans input.one, (beforeStore.lookup 11 (by decide)).trans input.root, first, second⟩
  have fresh : Within agendaLayout agenda.size (agenda.size + 1) (NativeAgendaInsert.footprintOf agendaLayout agenda room node) := by
    intro byte changed
    obtain ⟨col, changed⟩ := NativeAgendaInsert.footprint_member _ _ _ _ changed
    exact ⟨⟨agenda.size, room⟩, col, by simp, by simp, changed⟩
  obtain ⟨d, inserted, insertFrame, records, length, tail, meaning, ⟨atJump⟩⟩ := NativeAgendaInsert.fetched
    other extra vector (show At image c base (start + 43) from atInsert) (controls.transport beforeStore (by decide))
    placed.insert node operands room history held rootBound (geometry.code_for fresh)
  obtain ⟨after, jumped, jumpFrame, endpoint⟩ := X86PlacedScalar.jump (X86PlacedFrameAddress.nativeBase other)
    extra vector (show At image d base (start + 84) from atJump) placed.again
  have later := insertFrame.trans (X86StateFrame.registerOnly jumpFrame)
  have frame : X86StateFrame.Frame clobbers (NativeAgendaInsert.footprintOf agendaLayout agenda room node) before after :=
    (beforeStore.trans later).mono (by decide) (by simp)
  have firstThree := X86FuelPrefix.fetches_then 2 1 before a b checked reduced
  have firstNine := X86FuelPrefix.fetches_then 3 6 before b c firstThree loaded
  have firstEighteen := X86FuelPrefix.fetches_then 9 9 before c d firstNine inserted
  refine ⟨after, pair, chosen, X86FuelPrefix.fetches_then 18 1 before d after firstEighteen jumped,
    frame, meaning, ?_, endpoint⟩
  refine ⟨⟨records.fits, fun i j => (records.node i j).preserved (X86StateFrame.registerOnly jumpFrame) (by simp)⟩,
    geometry.keep_terms fresh input.terms frame, (frame.lookup 5 (by decide)).trans input.agendaBase, ?_,
    (jumpFrame.lookup 11 (by decide)).trans tail, (frame.lookup 13 (by decide)).trans input.one,
    (frame.lookup 12 (by decide)).trans input.zero, ?_, (frame.lookup 8 (by decide)).trans input.total,
    (frame.lookup 6 (by decide)).trans input.left, (frame.lookup 7 (by decide)).trans input.right⟩
  · simp only [Array.size_push]
    exact (jumpFrame.lookup 14 (by decide)).trans length
  · exact ((loadFrame.trans later).lookup 1 (by decide)).trans index

/-- Finite, complete execution of the native descending loop. The
result is the ordered prepend, with no writes outside the reserved
suffix. In particular duplicate child equations are not merged. -/
theorem fetched_all (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {base : BitVec 48}
    {start finished malformed : ℕ} (placed : Placed image start finished malformed)
    (geometry : Geometry agendaLayout termLayout image base) (spans : Spans terms left right)
    (remaining : ℕ) (width : remaining ≤ spans.leftWords.size)
    (agenda : Arena) (root : Word) (reserved : agenda.size + remaining ≤ capacity)
    (rootBound : root.toNat ≤ agenda.size) (history : List (Word × Word)) (held : readWords agenda root = some history)
    {before : Native} (point : At image before base start) (controls : Controls before)
    (input : Inputs agendaLayout termLayout spans agenda root remaining before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after updated newRoot writes,
      (X86FuelPrefix.fetches (19 * remaining + 2)).run before = .ok () after ∧
      X86StateFrame.Frame clobbers writes before after ∧ Within agendaLayout agenda.size updated.size writes ∧
      PackedEquations.prependWords agenda root (spans.pairs.take remaining) = some (updated, newRoot) ∧
      updated.size = agenda.size + remaining ∧ readWords updated newRoot = some (spans.pairs.take remaining ++ history) ∧
      Inputs agendaLayout termLayout spans updated newRoot 0 after ∧ Nonempty (At image after base finished) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  induction remaining generalizing agenda root history before with
  | zero =>
    obtain ⟨after, ran, registers, ⟨endpoint⟩⟩ := X86PlacedScalar.compare_branch
      (X86PlacedFrameAddress.nativeBase other) extra vector point .lessUnsigned 12 1 placed.check 0 0
      input.zero input.counter
    have frame := X86StateFrame.registerOnly registers
    have records : NativeAgendaRecords.Records agendaLayout agenda after :=
      ⟨input.records.fits, fun i j => (input.records.node i j).preserved frame (by simp)⟩
    have unchanged : Inputs agendaLayout termLayout spans agenda root 0 after :=
      ⟨records, input.terms.preserved frame, (frame.lookup 5 (by decide)).trans input.agendaBase,
        (frame.lookup 14 (by decide)).trans input.length, (frame.lookup 11 (by decide)).trans input.root,
        (frame.lookup 13 (by decide)).trans input.one, (frame.lookup 12 (by decide)).trans input.zero,
        (frame.lookup 1 (by decide)).trans input.counter, (frame.lookup 8 (by decide)).trans input.total,
        (frame.lookup 6 (by decide)).trans input.left, (frame.lookup 7 (by decide)).trans input.right⟩
    exact ⟨after, agenda, root, ∅, ran, frame.mono (by decide) (by simp), by simp [Within],
      rfl, by simp, held, unchanged, ⟨endpoint⟩⟩
  | succ remaining ih =>
    have room : agenda.size < capacity := by omega
    obtain ⟨middle, pair, picked, ran, frame, seen, nextInputs, ⟨back⟩⟩ :=
      fetched_iteration other extra vector point controls placed geometry spans agenda root remaining width
        room rootBound input history held
    let node : Node := ⟨root, pair.1, pair.2⟩
    let updated := agenda.push node
    let head := PackedEquations.next agenda
    have updatedSize : updated.size = agenda.size + 1 := Array.size_push node
    have limit := agendaLayout.words.positive_room (show 0 < 3 * (capacity + 1) by omega)
    have allocation : PackedEquations.CanAppend agenda node.older := ⟨rootBound, by omega⟩
    have headValid : head.toNat ≤ updated.size := by
      rw [show head = PackedEquations.next agenda from rfl, PackedEquations.next_exact allocation, updatedSize]
    obtain ⟨after, last, newRoot, bytes, done, kept, onlyFresh, prepended, size, readback, newState, endpoint⟩ :=
      ih (by omega) updated head (by omega) headValid (pair :: history) seen back
        (controls.transport frame clobbers_data) nextInputs
    have ordering : spans.pairs.take (remaining + 1) = spans.pairs.take remaining ++ [pair] := by
      rw [List.take_add_one, picked]
      rfl
    have inserted : PackedEquations.prependWords agenda root [pair] = some (updated, head) := by
      rcases pair with ⟨l, r⟩
      change PackedEquations.append agenda node = some (updated, head)
      exact if_pos allocation
    let just := NativeAgendaInsert.footprintOf agendaLayout agenda room node
    have total : X86StateFrame.Frame clobbers (just ∪ bytes) before after :=
      (frame.trans kept).mono (by simp) (Finset.Subset.refl _)
    have footprint : Within agendaLayout agenda.size last.size (just ∪ bytes) := by
      intro b written
      rcases Finset.mem_union.mp written with now | further
      · obtain ⟨j, present⟩ := NativeAgendaInsert.footprint_member agendaLayout agenda room node now
        have increased : agenda.size < last.size := by omega
        exact ⟨⟨agenda.size, room⟩, j, by simp, increased, present⟩
      · obtain ⟨i, j, within, upper, present⟩ := onlyFresh b further
        exact ⟨i, j, by omega, upper, present⟩
    have expected : PackedEquations.prependWords agenda root (spans.pairs.take (remaining + 1)) =
        some (last, newRoot) := by
      rw [ordering, PackedEquations.prepend_words_append, inserted, Option.bind_some]
      exact prepended
    have completed := X86FuelPrefix.fetches_then 19 (19 * remaining + 2) before middle after ran done
    rw [show 19 + (19 * remaining + 2) = 19 * (remaining + 1) + 2 by omega] at completed
    refine ⟨after, last, newRoot, just ∪ bytes, completed, total, footprint, expected, by omega, ?_, newState, endpoint⟩
    rw [ordering]
    simpa only [List.append_assoc, List.singleton_append] using readback

end Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaLoop
