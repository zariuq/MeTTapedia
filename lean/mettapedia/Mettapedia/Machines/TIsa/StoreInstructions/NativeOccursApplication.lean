import Mettapedia.Machines.TIsa.StoreInstructions.NativeChildMarkLoop
import Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaRead

/-!
# Native occurrence of one application

Both coordinates come from the selected node. The child pool
pointer comes from the agenda metadata. The code then reads only
the needed child marks with the generic loop; the instruction
stream contains no embedded span positions or arity.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeOccursApplication

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads)
open X86PlacedScalar (Code registerCode)
open X86IndexedAddress (Base addressCode)
open X86PreparedLea (Index)
open NativeArenaGeometry (Region)
open NativeAgendaRead (fieldSource)
open NativeOccurs (word)
open NativeWords (Wiring)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def countCode : List ℕ := X86DataLoad.code true 2 6 24
def startCode : List ℕ := X86DataLoad.code true 0 6 16
def contextCode : List ℕ := registerCode 0x89 5 10
def poolCode : List ℕ := X86DataLoad.code true 6 10 8
def poolReg : Base := ⟨6, by decide⟩
def spanIndex : Index := ⟨0, by decide⟩
def spanCode : List ℕ := addressCode 6 spanIndex 3 poolReg

def prepareCode : List ℕ := countCode ++ (startCode ++ (contextCode ++ (poolCode ++ spanCode)))

theorem prepare_size : prepareCode.length = 28 := by
  simp only [prepareCode, List.length_append,
    show countCode.length = 7 from rfl, show startCode.length = 7 from rfl, show contextCode.length = 3 from rfl,
    show poolCode.length = 7 from rfl, show spanCode.length = 4 from rfl]

def emit (start malformed : ℕ) : List ℕ :=
  prepareCode ++ NativeChildMarkLoop.emit (start + 28) malformed

theorem emit_size (start malformed : ℕ) : (emit start malformed).length = 88 := by
  simp only [emit, List.length_append, prepare_size, NativeChildMarkLoop.emit_size]

structure PreparePlaced (image : NativeImage.View) (start : ℕ) : Prop where
  extent : start + 28 ≤ image.size
  count : Code image start countCode
  first : Code image (start + 7) startCode
  context : Code image (start + 14) contextCode
  pool : Code image (start + 17) poolCode
  span : Code image (start + 24) spanCode

theorem prepare_placed (image : NativeImage.View) (start : ℕ)
    (extent : start + 28 ≤ image.size) (bytes : Code image start prepareCode) : PreparePlaced image start := by
  obtain ⟨count, rest⟩ := NativeWords.code_append (show Code image start (countCode ++ _) from bytes)
  obtain ⟨first, rest⟩ := NativeWords.code_append rest
  obtain ⟨context, rest⟩ := NativeWords.code_append rest
  obtain ⟨pool, span⟩ := NativeWords.code_append rest
  exact ⟨extent, count, first, context, pool, span⟩

structure Placed (image : NativeImage.View) (start malformed : ℕ) : Prop where
  prepare : PreparePlaced image start
  loop : NativeChildMarkLoop.Placed image (start + 28) malformed

theorem placed_of_emitted (image : NativeImage.View) (start malformed : ℕ)
    (extent : start + 88 ≤ image.size) (target : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (bytes : Code image start (emit start malformed)) : Placed image start malformed := by
  obtain ⟨prepare, loopBytes⟩ := NativeWords.code_append (show Code image start (prepareCode ++ _) from bytes)
  rw [prepare_size] at loopBytes
  exact ⟨prepare_placed image start (by omega) prepare,
    NativeChildMarkLoop.placed_of_emitted image (start + 28) malformed (by omega) target short loopBytes⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register := insert .rsi NativeChildMarkLoop.clobbers

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

def countWire : Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 2, by decide, by decide⟩
def startWire : Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 0, by decide, by decide⟩
def poolWire : Wiring := ⟨10, by decide, by decide, NativeIndexedWord.storeEncoding, 6, by decide, by decide⟩

variable {nodeCapacity edgeCapacity markCapacity agendaCapacity : ℕ}
variable {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {arena : PackedTerms.Arena}
variable {agendaLayout : NativeAgendaRecords.Layout agendaCapacity}
variable {table : Region markCapacity} {marks : Array Bool}

structure Input (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (arena : PackedTerms.Arena)
    (agendaLayout : NativeAgendaRecords.Layout agendaCapacity) (table : Region markCapacity) (marks : Array Bool)
    (i : Fin arena.nodes.size) (before : Native) : Prop where
  source : NativeTermArena.Ready layout arena before
  marked : NativeMarkTable.Ready table marks before
  record : lookup before 6 = some (source.bank i).pointer
  work : lookup before 5 = some agendaLayout.words.pointer
  pool : Reads before (agendaLayout.metadata.cell 1).address layout.edges.pointer
  tableBase : lookup before 7 = some (table.atWord 0)
  parent : lookup before 1 = some (BitVec.ofNat 64 marks.size)
  zero : lookup before 12 = some 0
  one : lookup before 13 = some 1

theorem fetched_span (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : PreparePlaced image start)
    (i : Fin arena.nodes.size) (source : NativeTermArena.Ready layout arena before)
    (selected : lookup before 6 = some (source.bank i).pointer)
    (work : lookup before 5 = some agendaLayout.words.pointer)
    (pool : Reads before (agendaLayout.metadata.cell 1).address layout.edges.pointer) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 5).run before = .ok () after ∧ X86StateFrame.Frame clobbers ∅ before after ∧
      lookup after 6 = some (layout.edges.atWord arena.nodes[i].childrenAt.toNat) ∧
      lookup after 2 = some arena.nodes[i].childrenCount ∧ Nonempty (At image after base (start + 28)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  let node := arena.nodes[i]
  let record := layout.record ⟨i.val, i.isLt.trans_le source.nodesFit⟩
  obtain ⟨a, loadedCount, countFrame, count, ⟨atStart⟩⟩ := (fieldSource record 3).fetch
    (handlers other extra) vector countWire node.childrenCount point controls selected (source.node i 3)
    (show start + 7 ≤ image.size by omega) placed.count
  obtain ⟨b, loadedStart, startFrame, first, ⟨atContext⟩⟩ := (fieldSource record 2).fetch
    (handlers other extra) vector startWire node.childrenAt atStart (controls.transport countFrame (by decide))
    ((countFrame.lookup 6 (by decide)).trans selected) ((source.node i 2).preserved countFrame (by simp))
    (show start + 14 ≤ image.size by omega) placed.first
  rw [linked] at loadedCount loadedStart
  have fetchedCoords := countFrame.trans startFrame
  obtain ⟨c, moved, moveFrame, context, ⟨atPool⟩⟩ := X86PlacedRegisterMove.executes (handlers other extra) vector
    (show At image b base (start + 14) from atContext) (by omega) 5 10 agendaLayout.words.pointer
    ((fetchedCoords.lookup 5 (by decide)).trans work) placed.context
  have pastCoords := fetchedCoords.trans (X86StateFrame.registerOnly moveFrame)
  have headerBase : agendaLayout.metadata.pointer = agendaLayout.words.pointer := BitVec.add_zero _
  obtain ⟨d, loadedPool, poolFrame, pointer, ⟨atSpan⟩⟩ := (fieldSource agendaLayout.metadata 1).fetch
    (handlers other extra) vector poolWire layout.edges.pointer (show At image c base (start + 17) from atPool)
    (controls.transport pastCoords (by decide)) (headerBase.symm ▸ context) (pool.preserved pastCoords (by simp))
    (show start + 24 ≤ image.size by omega) placed.pool
  rw [linked] at loadedPool
  obtain ⟨e, located, locateFrame, span, ⟨atLoop⟩⟩ := X86IndexedAddress.forms_address other extra vector
    (show At image d base (start + 24) from atSpan) (by omega) 6 spanIndex 3 poolReg placed.span
    layout.edges.pointer node.childrenAt pointer
    ((poolFrame.lookup 0 (by decide)).trans ((moveFrame.lookup 0 (by decide)).trans first))
  have beforeLoop := (pastCoords.trans poolFrame).trans (X86StateFrame.registerOnly locateFrame)
  have spanBase : lookup e 6 = some (layout.edges.atWord node.childrenAt.toNat) := by
    unfold Region.atWord
    rw [NativeArenaGeometry.word_scale8]
    exact span
  have retainedCount := ((((startFrame.trans (X86StateFrame.registerOnly moveFrame)).trans poolFrame).trans
    (X86StateFrame.registerOnly locateFrame)).lookup 2 (by decide)).trans count
  have firstTwo := X86FuelPrefix.fetches_then 1 1 before a b loadedCount loadedStart
  have firstThree := X86FuelPrefix.fetches_then 2 1 before b c firstTwo moved
  have firstFour := X86FuelPrefix.fetches_then 3 1 before c d firstThree loadedPool
  exact ⟨e, X86FuelPrefix.fetches_then 4 1 before d e firstFour located, beforeLoop.mono (by decide) (by simp),
    spanBase, retainedCount, ⟨atLoop⟩⟩

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start malformed : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start malformed)
    (i : Fin arena.nodes.size) (input : Input layout arena agendaLayout table marks i before)
    (children : Array Word) (segment : PackedTerms.segment arena.children arena.nodes[i] = some children)
    (bits : List Bool) (ordered : PackedOccurs.childrenBits marks children = some bits) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧ steps ≤ 12 * children.size + 8 ∧
      X86StateFrame.Frame clobbers ∅ before after ∧ lookup after 0 = some (word (bits.any id)) ∧
      Nonempty (At image after base (start + 88)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let node := arena.nodes[i]
  obtain ⟨e, firstFive, beforeLoop, spanBase, count, ⟨atLoop⟩⟩ := fetched_span other extra vector point controls
    placed.prepare i input.source input.record input.work input.pool
  have width := (PackedTerms.segment_width arena.children node children segment).1
  have physicalCount : BitVec.ofNat 64 children.size = node.childrenCount := by
    rw [width, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have inputLoop : NativeChildMarkLoop.Input layout arena table marks node children.size e :=
    ⟨input.source.preserved beforeLoop, input.marked.preserved beforeLoop, spanBase,
      (beforeLoop.lookup 7 (by decide)).trans input.tableBase, (beforeLoop.lookup 1 (by decide)).trans input.parent,
      physicalCount.symm ▸ count,
      (beforeLoop.lookup 12 (by decide)).trans input.zero, (beforeLoop.lookup 13 (by decide)).trans input.one⟩
  obtain ⟨after, steps, looped, cost, frame, result, endpoint⟩ := NativeChildMarkLoop.fetched other extra vector
    placed.loop children bits segment ordered children.size (Nat.le_refl _)
    (show At image e base (start + 28) from atLoop) (controls.transport beforeLoop (by decide)) inputLoop
  have exactBits := (PackedOccursPrefix.child_coordinates marks children bits ordered).1
  rw [← exactBits, List.take_length] at result
  exact ⟨after, 5 + steps, X86FuelPrefix.fetches_then 5 steps before e after firstFive looped,
    by omega, (beforeLoop.trans frame).mono (by decide) (by simp), result, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeOccursApplication
