import Mettapedia.Machines.TIsa.StoreInstructions.NativeOccursNode

/-!
# A native occurrence scan up to a target handle

Every iteration selects one node, computes its bit, and appends
that bit to the initialized scratch prefix. The emitted back
edge increments the loop index only if the target is still
ahead. Term records and the agenda are not rewritten by marking.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeOccursLoop

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls CodeApart Reads footprint)
open X86PlacedScalar (Code CompareBranch Jump registerCode jumpDelta)
open NativeArenaGeometry (Region)
open NativeOccurs (word)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def cursorIndex : X86PreparedLea.Index := ⟨1, by decide⟩
def storeCode : List ℕ := NativeIndexedWord.storeCode NativeChildMarkLoop.markBase cursorIndex
def incrementCode : List ℕ := registerCode (X86Arithmetic.opcode .add) 13 1

def emit (start done malformed : ℕ) : List ℕ :=
  NativeOccursNode.emit start malformed ++ (storeCode ++
    (NativeDecisions.compareBytes .notEqual 1 9 (start + 213) done ++
      (incrementCode ++ X86UnconditionalJump.Block.code (jumpDelta (start + 225) start))))

theorem emit_size (start done malformed : ℕ) : (emit start done malformed).length = 230 := by
  simp only [emit, List.length_append, NativeOccursNode.emit_size, NativeDecisions.compare_size,
    X86UnconditionalJump.Block.code_length, show storeCode.length = 11 from rfl,
    show incrementCode.length = 3 from rfl]

structure Placed (image : NativeImage.View) (start done malformed : ℕ) : Prop where
  extent : start + 230 ≤ image.size
  node : NativeOccursNode.Placed image start malformed
  store : Code image (start + 202) storeCode
  check : CompareBranch image (start + 213) done .notEqual 1 9
  increment : Code image (start + 222) incrementCode
  again : Jump image (start + 225) start

theorem placed_of_emitted (image : NativeImage.View) (start done malformed : ℕ) (size : start + 230 ≤ image.size)
    (finished : done ≤ image.size) (target : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (bytes : Code image start (emit start done malformed)) : Placed image start done malformed := by
  obtain ⟨node, rest⟩ := NativeWords.code_append (show Code image start (NativeOccursNode.emit start malformed ++ _) from bytes)
  rw [NativeOccursNode.emit_size] at rest
  obtain ⟨store, rest⟩ := NativeWords.code_append rest
  change Code image (start + 213) _ at rest
  obtain ⟨check, rest⟩ := NativeWords.code_append rest
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨increment, again⟩ := NativeWords.code_append rest
  refine ⟨size, NativeOccursNode.placed_of_emitted image start malformed (by omega) target short node, store,
    NativeDecisions.compare_placed image _ _ _ _ _ (by omega) finished short check, increment,
    ⟨by omega, by omega, ?_, again⟩⟩
  unfold jumpDelta
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
  omega

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register := insert .rcx NativeOccursNode.clobbers

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {nodeCapacity edgeCapacity markCapacity agendaCapacity : ℕ}
variable {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {arena : PackedTerms.Arena}
variable {agendaLayout : NativeAgendaRecords.Layout agendaCapacity}
variable {table : Region markCapacity} {marks : Array Bool}

def cellBytes (table : Region markCapacity) (slot : Fin markCapacity) : Finset ℕ :=
  footprint ((table.wordCell slot).cell 0).address

structure Geometry (layout : NativeTermArena.Layout nodeCapacity edgeCapacity)
    (agendaLayout : NativeAgendaRecords.Layout agendaCapacity) (table : Region markCapacity)
    (image : NativeImage.View) (base : BitVec 48) : Prop where
  code : ∀ slot : Fin markCapacity, CodeApart image base (cellBytes table slot)
  nodes : ∀ (i : Fin nodeCapacity) (j : Fin 4) (slot : Fin markCapacity),
    Disjoint (footprint ((layout.record i).cell j).address) (cellBytes table slot)
  edges : ∀ (i : Fin edgeCapacity) (slot : Fin markCapacity),
    Disjoint (footprint ((layout.child i).cell 0).address) (cellBytes table slot)
  pool : ∀ slot : Fin markCapacity, Disjoint (footprint (agendaLayout.metadata.cell 1).address) (cellBytes table slot)

structure Input (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (arena : PackedTerms.Arena)
    (agendaLayout : NativeAgendaRecords.Layout agendaCapacity) (table : Region markCapacity) (marks : Array Bool)
    (query target : Word) (before : Native) : Prop where
  node : NativeOccursNode.Input layout arena agendaLayout table marks query before
  target : lookup before 9 = some target

def Next (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (arena : PackedTerms.Arena)
    (agendaLayout : NativeAgendaRecords.Layout agendaCapacity) (table : Region markCapacity)
    (marks : Array Bool) (query target : Word) (bit : Bool)
    (image : NativeImage.View) (base : BitVec 48) (start done : ℕ) (after : Native) : Prop :=
  if marks.size = target.toNat then lookup after 0 = some (word bit) ∧ Nonempty (At image after base done)
  else Input layout arena agendaLayout table (marks.push bit) query target after ∧
    Nonempty (At image after base start)

private theorem slot_nat (table : Region markCapacity) (n : ℕ) (below : n < markCapacity) :
    (BitVec.ofNat 64 n).toNat = n := by
  have room := table.positive_room (show 0 < markCapacity by omega)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem fetched_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start done malformed : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start done malformed)
    (geometry : Geometry layout agendaLayout table image base) (query target : Word)
    (input : Input layout arena agendaLayout table marks query target before) (room : marks.size < markCapacity)
    (i : Fin arena.nodes.size) (current : i.val = marks.size) (children : Array Word)
    (segment : PackedTerms.segment arena.children arena.nodes[i] = some children)
    (bit : Bool) (marked : PackedOccurs.mark query marks arena.nodes[i].header children = some bit) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      steps ≤ 12 * children.size + 25 ∧
      X86StateFrame.Frame clobbers (cellBytes table ⟨marks.size, room⟩) before after ∧
      NativeMarkTable.Ready table (marks.push bit) after ∧
      Next layout arena agendaLayout table marks query target bit image base start done after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  obtain ⟨a, steps, calculated, cost, calcFrame, result, ⟨atStore⟩⟩ :=
    NativeOccursNode.fetched other extra vector point controls placed.node query input.node
      i current children segment bit marked
  let slot : Fin markCapacity := ⟨marks.size, room⟩
  let ordinal := BitVec.ofNat 64 marks.size
  have exactOrdinal : ordinal.toNat = marks.size := slot_nat table _ room
  have physical : 0 + ordinal.toNat < markCapacity := by rw [Nat.zero_add, exactOrdinal]; exact room
  have same : (⟨0 + ordinal.toNat, physical⟩ : Fin markCapacity) = slot := Fin.ext ((Nat.zero_add _).trans exactOrdinal)
  have apart : CodeApart image base (footprint ((table.wordCell ⟨0 + ordinal.toNat, physical⟩).cell 0).address) := by
    rw [same]
    exact geometry.code slot
  obtain ⟨b, stored, storeFrame, written, ⟨atCheck⟩⟩ := NativeIndexedWord.fetched_store other extra vector
    atStore (controls.transport calcFrame NativeOccursNode.clobbers_data) (by omega)
    NativeChildMarkLoop.markBase cursorIndex table 0 ordinal (word bit) physical
    ((calcFrame.lookup 7 (by decide)).trans input.node.tableBase) ((calcFrame.lookup 1 (by decide)).trans input.node.current)
    result placed.store apart
  rw [same] at storeFrame written
  have beforeCheck := calcFrame.trans storeFrame
  have currentRead := (beforeCheck.lookup 1 (by decide)).trans input.node.current
  obtain ⟨c, checked, checkFrame, ⟨destination⟩⟩ := X86PlacedScalar.compare_branch
    (X86PlacedFrameAddress.nativeBase other) extra vector (show At image b base (start + 213) from atCheck)
    .notEqual 1 9 placed.check ordinal target currentRead ((beforeCheck.lookup 9 (by decide)).trans input.target)
  have expected : ordinal = target ↔ marks.size = target.toNat := by
    constructor
    · intro equal
      exact exactOrdinal.symm.trans (congrArg BitVec.toNat equal)
    · intro equal
      exact BitVec.eq_of_toNat_eq (exactOrdinal.trans equal)
  simp only [Comparison.evaluate, bne_iff_ne, ne_eq, expected] at destination
  have checkTrace := X86FuelPrefix.fetches_then (steps + 2) 2 before b c
    (X86FuelPrefix.fetches_then steps 2 before a b calculated stored) checked
  have finished := beforeCheck.trans (X86StateFrame.registerOnly checkFrame)
  by_cases stop : marks.size = target.toNat
  · have atDone : At image c base done := by simpa [stop] using destination
    have frame : X86StateFrame.Frame clobbers (cellBytes table slot) before c :=
      finished.mono (by decide) (by simp [cellBytes])
    have known : lookup c 0 = some (word bit) :=
      ((storeFrame.trans (X86StateFrame.registerOnly checkFrame)).lookup 0 (by decide)).trans result
    refine ⟨c, steps + 2 + 2, checkTrace, by omega, frame,
      input.node.marked.extend room bit frame (written.preserved (X86StateFrame.registerOnly checkFrame) (by simp)), ?_⟩
    simp only [Next, if_pos stop]
    exact ⟨known, ⟨atDone⟩⟩
  · have atIncrement : At image c base (start + 222) := by simpa [stop] using destination
    obtain ⟨d, increased, increaseFrame, newCount, ⟨atJump⟩⟩ := X86PlacedArithmetic.executes
      (handlers other extra) vector atIncrement (by omega) .add 13 1 ordinal 1
      ((finished.lookup 13 (by decide)).trans input.node.one)
      ((checkFrame.lookup 1 (by decide)).trans currentRead) placed.increment
    have ordinary : X86Arithmetic.linkedHandlers (handlers other extra) = handlers other extra := rfl
    rw [ordinary] at increased
    have cursor : lookup d 1 = some (BitVec.ofNat 64 (marks.push bit).size) := by
      change lookup d 1 = some (BitVec.ofNat 64 marks.size + BitVec.ofNat 64 1) at newCount
      rw [Array.size_push, ← BitVec.ofNat_add_ofNat]
      exact newCount
    obtain ⟨after, jumped, jumpFrame, endpoint⟩ := X86PlacedScalar.jump (X86PlacedFrameAddress.nativeBase other)
      extra vector (show At image d base (start + 225) from atJump) placed.again
    have tail := X86StateFrame.registerOnly ((checkFrame.trans increaseFrame).trans jumpFrame)
    have frame : X86StateFrame.Frame clobbers (cellBytes table slot) before after :=
      (beforeCheck.trans tail).mono (by decide) (by simp [cellBytes])
    have newMarks := input.node.marked.extend room bit frame (written.preserved tail (by simp))
    have next : Input layout arena agendaLayout table (marks.push bit) query target after :=
      ⟨⟨input.node.source.kept frame (fun i j => geometry.nodes i j slot) (fun i => geometry.edges i slot),
        newMarks, (frame.lookup 3 (by decide)).trans input.node.terms, (frame.lookup 5 (by decide)).trans input.node.work,
        input.node.pool.preserved frame (geometry.pool slot), (frame.lookup 7 (by decide)).trans input.node.tableBase,
        (jumpFrame.lookup 1 (by decide)).trans cursor, (frame.lookup 8 (by decide)).trans input.node.name,
        (frame.lookup 12 (by decide)).trans input.node.zero, (frame.lookup 13 (by decide)).trans input.node.one,
        (frame.lookup 14 (by decide)).trans input.node.two⟩, (frame.lookup 9 (by decide)).trans input.target⟩
    have ran := X86FuelPrefix.fetches_then (steps + 2 + 2 + 1) 1 before d after
      (X86FuelPrefix.fetches_then (steps + 2 + 2) 1 before c d checkTrace increased) jumped
    refine ⟨after, _, ran, by omega, frame, newMarks, ?_⟩
    simp only [Next, if_neg stop]
    exact ⟨next, endpoint⟩

def Aligned (arena : PackedTerms.Arena) (start : ℕ) (nodes : List PackedTerms.Node) : Prop :=
  ∀ i : Fin nodes.length, arena.nodes[start + i.val]? = some nodes[i]

theorem aligned_prefix (arena : PackedTerms.Arena) (count : ℕ) (inside : count ≤ arena.nodes.size) :
    Aligned arena 0 (arena.nodes.toList.take count) := by
  intro i
  have width : (arena.nodes.toList.take count).length = count := by simp [List.length_take, Nat.min_eq_left inside]
  have reads := List.getElem?_eq_getElem i.isLt
  change (arena.nodes.toList.take count)[i.val]? = some (arena.nodes.toList.take count)[i] at reads
  rw [List.getElem?_take_of_lt (i.isLt.trans_le (by rw [width])), Array.getElem?_toList] at reads
  simpa only [Nat.zero_add] using reads

def workBound : List PackedTerms.Node → ℕ
  | [] => 0
  | node :: tail => (12 * node.childrenCount.toNat + 25) + workBound tail

/-- A successful packed scan gives a complete fetched execution
through its target. The execution stores exactly the initialized
prefix, and later nodes are not needed to answer the question. -/
theorem fetched_scan (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start done malformed : ℕ}
    (placed : Placed image start done malformed) (geometry : Geometry layout agendaLayout table image base)
    (query target : Word) (nodes : List PackedTerms.Node) (initial final : Array Bool) (bit : Bool)
    (aligned : Aligned arena initial.size nodes) (extent : initial.size + nodes.length = target.toNat + 1)
    (notPast : initial.size ≤ target.toNat) (room : target.toNat < markCapacity)
    (computed : PackedOccurs.scan query arena.children nodes initial = some final)
    (observed : final[target.toNat]? = some bit)
    {before : Native} (point : At image before base start) (controls : Controls before)
    (input : Input layout arena agendaLayout table initial query target before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps bytes, (X86FuelPrefix.fetches steps).run before = .ok () after ∧ steps ≤ workBound nodes ∧
      X86StateFrame.Frame clobbers bytes before after ∧ NativeMarkTable.Within table initial.size final.size bytes ∧
      NativeMarkTable.Ready table final after ∧ lookup after 0 = some (word bit) ∧ Nonempty (At image after base done) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  induction nodes generalizing before initial with
  | nil => simp only [List.length_nil, Nat.add_zero] at extent; omega
  | cons node tail ih =>
    have head : arena.nodes[initial.size]? = some node := by
      have same := aligned ⟨0, by simp⟩
      change arena.nodes[initial.size]? = some node at same
      exact same
    obtain ⟨indexWithin, indexed⟩ := Array.getElem?_eq_some_iff.mp head
    let i : Fin arena.nodes.size := ⟨initial.size, indexWithin⟩
    have inArena : arena.nodes[i] = node := indexed
    cases segment : PackedTerms.segment arena.children node with
    | none => simp [PackedOccurs.scan, segment] at computed
    | some children =>
      cases result : PackedOccurs.mark query initial node.header children with
      | none => simp [PackedOccurs.scan, segment, result] at computed
      | some value =>
        have scannedTail : PackedOccurs.scan query arena.children tail (initial.push value) = some final := by
          simpa only [PackedOccurs.scan, segment, result] using computed
        have available : initial.size < markCapacity := notPast.trans_lt room
        obtain ⟨middle, steps, ran, bound, frame, ready, next⟩ := fetched_step other extra vector point controls
          placed geometry query target input available i rfl children
          (by simpa only [inArena] using segment) value (by simpa only [inArena] using result)
        have childCount := (PackedTerms.segment_width arena.children node children segment).1
        rw [childCount] at bound
        let changed := cellBytes table ⟨initial.size, available⟩
        by_cases finished : initial.size = target.toNat
        · rw [Next, if_pos finished] at next
          have noTail : tail = [] := by
            apply List.eq_nil_of_length_eq_zero
            simp only [List.length_cons] at extent
            omega
          subst tail
          have eqFinal : initial.push value = final := Option.some.inj scannedTail
          subst final
          have bitAt : value = bit := by
            rw [← finished, Array.getElem?_push_size] at observed
            exact Option.some.inj observed
          have confined : NativeMarkTable.Within table initial.size (initial.push value).size changed := by
            intro byte touched
            exact ⟨⟨initial.size, available⟩, Nat.le_refl _, by simp, touched⟩
          exact ⟨middle, steps, changed, ran, by simpa only [workBound, Nat.add_zero] using bound,
            frame, confined, ready, bitAt ▸ next.1, next.2⟩
        · rw [Next, if_neg finished] at next
          have nextAligned : Aligned arena (initial.push value).size tail := by
            intro j
            have read := aligned ⟨j.val + 1, by simpa only [List.length_cons] using Nat.succ_lt_succ j.isLt⟩
            change arena.nodes[initial.size + (j.val + 1)]? = some tail[j] at read
            rw [Array.size_push, Nat.add_right_comm _ 1 _]
            exact read
          have width : (initial.push value).size + tail.length = target.toNat + 1 := by
            simp only [List.length_cons] at extent
            rw [Array.size_push]
            omega
          obtain ⟨after, laterSteps, bytes, later, laterBound, laterFrame, confined, finalReady, exactBit, doneAt⟩ :=
            ih (initial.push value) nextAligned width (by rw [Array.size_push]; omega) scannedTail
              next.2.some (controls.transport frame clobbers_data) next.1
          have total : X86StateFrame.Frame clobbers (changed ∪ bytes) before after :=
            (frame.trans laterFrame).mono (by simp) (Finset.Subset.refl _)
          have endWidth := PackedOccursPrefix.scan_size query arena.children tail (initial.push value) final scannedTail
          have allConfined : NativeMarkTable.Within table initial.size final.size (changed ∪ bytes) := by
            intro byte touched
            rcases Finset.mem_union.mp touched with first | rest
            · have grows : initial.size < final.size := by rw [Array.size_push] at endWidth; omega
              exact ⟨⟨initial.size, available⟩, Nat.le_refl _, grows, first⟩
            · obtain ⟨slot, lower, upper, inBytes⟩ := confined byte rest
              exact ⟨slot, by rw [Array.size_push] at lower; omega, upper, inBytes⟩
          exact ⟨after, steps + laterSteps, changed ∪ bytes,
            X86FuelPrefix.fetches_then steps laterSteps before middle after ran later,
            by simp only [workBound]; omega, total, allConfined, finalReady, exactBit, doneAt⟩

open Mettapedia.Logic.LP

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars]

theorem fetched_target (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start done malformed : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start done malformed)
    (geometry : Geometry layout agendaLayout table image base) (symbols : UnifierHeaders.Symbols σ)
    (name : σ.vars) (query target : Word) (registered : symbols.vars.encode name = some query)
    (term : Term σ) (resolved : PackedTerms.lookup symbols arena target = some term)
    (room : target.toNat < markCapacity) (input : Input layout arena agendaLayout table #[] query target before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps bytes, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      steps ≤ workBound (arena.nodes.toList.take (target.toNat + 1)) ∧
      X86StateFrame.Frame clobbers bytes before after ∧ NativeMarkTable.Within table 0 (target.toNat + 1) bytes ∧
      lookup after 0 = some (word (term.occursIn name)) ∧ Nonempty (At image after base done) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨terms, decoded, read⟩ := Option.bind_eq_some_iff.mp resolved
  have inside := (Array.getElem?_eq_some_iff.mp read).choose
  rw [PackedTerms.decode_size symbols arena decoded] at inside
  have marks := PackedOccurs.scan_exact symbols name query registered arena.children arena.nodes.toList #[] terms decoded
  simp only [Array.map_empty] at marks
  have take : target.toNat + 1 ≤ arena.nodes.size := by omega
  obtain ⟨first, scanned, size, exactBit⟩ := PackedOccursPrefix.prefix_marks query arena _ take _ marks
  have answer : first[target.toNat]? = some (term.occursIn name) := by
    rw [exactBit _ (by omega), Array.getElem?_map, read, Option.map_some]
  obtain ⟨after, steps, bytes, ran, cost, frame, confined, _, result, endpoint⟩ :=
    fetched_scan other extra vector placed geometry query target (arena.nodes.toList.take (target.toNat + 1)) #[] first
      (term.occursIn name) (aligned_prefix arena _ take) (by simp [List.length_take, Nat.min_eq_left take])
      (by simp) room scanned answer point controls input
  exact ⟨after, steps, bytes, ran, cost, frame, by simpa only [size, Array.size_empty] using confined, result, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeOccursLoop
