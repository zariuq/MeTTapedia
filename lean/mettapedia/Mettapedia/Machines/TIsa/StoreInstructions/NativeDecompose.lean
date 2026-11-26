import Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaPublish
import Mettapedia.Machines.TIsa.StoreInstructions.PackedWorklist

/-!
# Native decomposition with one publication

From the two selected term records, the block loads their spans,
reserves the entire extension, pairs their children and publishes
the new agenda once. Capacity refusal happens before any store.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeDecompose

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads CodeApart footprint)
open X86PlacedScalar (Code registerCode)
open PackedEquations (Arena readWords)
open NativeChildPair (Spans)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def lengthCode : List ℕ := registerCode 0x89 9 14
def counterCode : List ℕ := registerCode 0x89 8 1

def emit (start retry malformed exhausted : ℕ) : List ℕ :=
  NativeSpanPrepare.emit start malformed ++ (NativeAgendaReserve.emit (start + 55) exhausted ++
    (lengthCode ++ (counterCode ++ (NativeAgendaLoop.emit (start + 90) (start + 179) malformed ++
      NativeAgendaPublish.emit (start + 179) retry))))

theorem emit_size (start retry malformed exhausted : ℕ) : (emit start retry malformed exhausted).length = 200 := by
  simp only [emit, List.length_append, NativeSpanPrepare.emit_size, NativeAgendaReserve.emit_size,
    NativeAgendaLoop.emit_size, NativeAgendaPublish.emit_size,
    show lengthCode.length = 3 from rfl, show counterCode.length = 3 from rfl]

structure Placed (image : NativeImage.View) (start retry malformed exhausted : ℕ) : Prop where
  extent : start + 200 ≤ image.size
  spans : NativeSpanPrepare.Placed image start malformed
  reserve : NativeAgendaReserve.Placed image (start + 55) exhausted
  length : Code image (start + 84) lengthCode
  counter : Code image (start + 87) counterCode
  loop : NativeAgendaLoop.Placed image (start + 90) (start + 179) malformed
  publish : NativeAgendaPublish.Placed image (start + 179) retry

theorem placed_of_emitted (image : NativeImage.View) (start retry malformed exhausted : ℕ)
    (extent : start + 200 ≤ image.size) (again : retry ≤ image.size) (bad : malformed ≤ image.size)
    (lack : exhausted ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit start retry malformed exhausted)) :
    Placed image start retry malformed exhausted := by
  obtain ⟨spans, tail⟩ := NativeWords.code_append (show Code image start (NativeSpanPrepare.emit start malformed ++ _) from code)
  rw [NativeSpanPrepare.emit_size] at tail
  obtain ⟨reserve, tail⟩ := NativeWords.code_append tail
  rw [NativeAgendaReserve.emit_size] at tail
  obtain ⟨length, tail⟩ := NativeWords.code_append tail
  obtain ⟨counter, tail⟩ := NativeWords.code_append tail
  change Code image (start + 90) _ at tail
  obtain ⟨looped, publish⟩ := NativeWords.code_append tail
  rw [NativeAgendaLoop.emit_size] at publish
  exact ⟨extent, NativeSpanPrepare.placed_of_emitted image start malformed (by omega) bad short spans,
    NativeAgendaReserve.placed_of_emitted image _ exhausted (by omega) lack short reserve,
    length, counter, NativeAgendaLoop.placed_of_emitted image _ _ malformed (by omega) (by omega) bad short looped,
    NativeAgendaPublish.placed_of_emitted image _ retry (by omega) again short publish⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register :=
  NativeSpanPrepare.clobbers ∪ NativeAgendaReserve.clobbers ∪ NativeAgendaLoop.clobbers ∪ NativeAgendaPublish.clobbers

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {capacity nodeCapacity edgeCapacity : ℕ}
variable {agendaLayout : NativeAgendaRecords.Layout capacity}
variable {termLayout : NativeTermArena.Layout nodeCapacity edgeCapacity} {terms : PackedTerms.Arena}

def countCell (layout : NativeAgendaRecords.Layout capacity) : Finset ℕ := footprint (layout.header.cell 0).address

structure Geometry (agendaLayout : NativeAgendaRecords.Layout capacity)
    (termLayout : NativeTermArena.Layout nodeCapacity edgeCapacity) (image : NativeImage.View) (base : BitVec 48) : Prop where
  loop : NativeAgendaLoop.Geometry agendaLayout termLayout image base
  count : CodeApart image base (countCell agendaLayout)
  nodes : ∀ (i : Fin nodeCapacity) (field : Fin 4),
    Disjoint (footprint ((termLayout.record i).cell field).address) (countCell agendaLayout)
  edges : ∀ i : Fin edgeCapacity,
    Disjoint (footprint ((termLayout.child i).cell 0).address) (countCell agendaLayout)

/-- The packed source transition for the branch whose child
spans the native block is about to read. -/
theorem packed_expands (terms : PackedTerms.Arena) (left right : Word)
    (l : left.toNat < terms.nodes.size) (r : right.toNat < terms.nodes.size)
    (spans : Spans terms terms.nodes[left.toNat] terms.nodes[right.toNat])
    (choose : NativeTermDispatch.choose terms left right = .expand) (history trail : PackedWorklist.Words) :
    PackedWorklist.advance ⟨terms, (left, right) :: history, trail⟩ =
      some (.working ⟨terms, spans.pairs ++ history, trail⟩) := by
  have branch : UnifierHeaders.dispatch terms.nodes[left.toNat].header terms.nodes[right.toNat].header = .expand := by
    simpa only [NativeTermDispatch.choose, Array.getElem?_eq_getElem l, Array.getElem?_eq_getElem r] using choose
  simp [PackedWorklist.advance, PackedUnifierAction.inspect, Array.getElem?_eq_getElem l, Array.getElem?_eq_getElem r,
    branch, spans.left, spans.right, spans.width, NativeChildPair.Spans.pairs]

private theorem binding_not_decomposition (terms : PackedTerms.Arena) (name handle : Word)
    (pairs : List (Word × Word)) :
    PackedUnifierAction.binding terms name handle ≠ some (.decompose pairs) := by
  unfold PackedUnifierAction.binding
  cases test : PackedOccurs.find name terms handle with
  | none => simp
  | some bit => cases bit <;> simp

theorem spans_of_inspect (terms : PackedTerms.Arena) (left right : Word) (pairs : List (Word × Word))
    (inspected : PackedUnifierAction.inspect terms left right = some (.decompose pairs)) :
    ∃ (l : left.toNat < terms.nodes.size) (r : right.toNat < terms.nodes.size)
      (spans : Spans terms terms.nodes[left.toNat] terms.nodes[right.toNat]),
      NativeTermDispatch.choose terms left right = .expand ∧ spans.pairs = pairs := by
  cases locatedL : terms.nodes[left.toNat]? with
  | none => simp [PackedUnifierAction.inspect, locatedL] at inspected
  | some lhs =>
    cases locatedR : terms.nodes[right.toNat]? with
    | none => simp [PackedUnifierAction.inspect, locatedL, locatedR] at inspected
    | some rhs =>
      simp only [PackedUnifierAction.inspect, locatedL, locatedR, bind, Option.bind_some] at inspected
      cases output : UnifierHeaders.dispatch lhs.header rhs.header with
      | malformed => simp [output] at inspected
      | discard => simp [output] at inspected
      | clash => simp [output] at inspected
      | bindLeft => exact (binding_not_decomposition terms lhs.header.symbol right pairs (by simpa only [output] using inspected)).elim
      | bindRight => exact (binding_not_decomposition terms rhs.header.symbol left pairs (by simpa only [output] using inspected)).elim
      | expand =>
        rw [output] at inspected
        cases leftSpan : PackedTerms.segment terms.children lhs with
        | none => simp [leftSpan] at inspected
        | some leftWords =>
          cases rightSpan : PackedTerms.segment terms.children rhs with
          | none => simp [leftSpan, rightSpan] at inspected
          | some rightWords =>
            by_cases width : leftWords.size = rightWords.size
            · simp only [leftSpan, rightSpan, Option.bind_some, if_pos width, Option.some.injEq,
                PackedUnifierAction.Encoded.decompose.injEq] at inspected
              have l := (Array.getElem?_eq_some_iff.mp locatedL).choose
              have r := (Array.getElem?_eq_some_iff.mp locatedR).choose
              have lnode := (Array.getElem?_eq_some_iff.mp locatedL).choose_spec
              have rnode := (Array.getElem?_eq_some_iff.mp locatedR).choose_spec
              let spans : Spans terms terms.nodes[left.toNat] terms.nodes[right.toNat] :=
                ⟨leftWords, rightWords, lnode.symm ▸ leftSpan, rnode.symm ▸ rightSpan, width⟩
              exact ⟨l, r, spans, by simp [NativeTermDispatch.choose, locatedL, locatedR, output], inspected⟩
            · simp [leftSpan, rightSpan, width] at inspected

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start retry malformed exhausted : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start retry malformed exhausted)
    (geometry : Geometry agendaLayout termLayout image base) (left right : Fin terms.nodes.size)
    (spans : Spans terms terms.nodes[left] terms.nodes[right]) (agenda : Arena) (root : Word)
    (context : NativeAgendaDispatch.Context agendaLayout termLayout agenda terms root before)
    (selected : NativeSpanPrepare.Inputs agendaLayout termLayout terms left right before)
    (limit : Reads before (agendaLayout.metadata.cell 2).address (BitVec.ofNat 64 capacity))
    (history : PackedWorklist.Words) (held : readWords agenda root = some history) (rootBound : root.toNat ≤ agenda.size) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      if agenda.size + spans.leftWords.size ≤ capacity then
        ∃ updated next writes,
          steps = 24 + 19 * spans.leftWords.size ∧
          X86StateFrame.Frame clobbers (writes ∪ countCell agendaLayout) before after ∧
          NativeAgendaLoop.Within agendaLayout agenda.size updated.size writes ∧
          PackedEquations.prependWords agenda root spans.pairs = some (updated, next) ∧
          updated.size = agenda.size + spans.leftWords.size ∧
          readWords updated next = some (spans.pairs ++ history) ∧
          NativeAgendaDispatch.Context agendaLayout termLayout updated terms next after ∧
          Nonempty (At image after base retry)
      else steps = 16 ∧ X86StateFrame.Frame clobbers ∅ before after ∧
        lookup after 11 = some root ∧ Nonempty (At image after base exhausted) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  have leftSize := (PackedTerms.segment_width terms.children terms.nodes[left] spans.leftWords spans.left).1
  have rightSize := (PackedTerms.segment_width terms.children terms.nodes[right] spans.rightWords spans.right).1
  have counts : terms.nodes[left].childrenCount = terms.nodes[right].childrenCount :=
    BitVec.eq_of_toNat_eq (leftSize.symm.trans (spans.width.trans rightSize))
  have widthWord : BitVec.ofNat 64 spans.leftWords.size = terms.nodes[left].childrenCount := by
    rw [leftSize, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have widthNat : (BitVec.ofNat 64 spans.leftWords.size).toNat = spans.leftWords.size :=
    (congrArg BitVec.toNat widthWord).trans leftSize.symm
  obtain ⟨prepared, steps, readSpans, spanFrame, shapes⟩ :=
    NativeSpanPrepare.fetched other extra vector point controls placed.spans left right selected
  rw [if_pos counts] at shapes
  obtain ⟨rfl, width, lPtr, rPtr, ⟨atReserve⟩⟩ := shapes
  rw [← widthWord] at width
  obtain ⟨reserved, reservation, reserveFrame, initializedLength, _, ⟨afterReserve⟩⟩ := NativeAgendaReserve.fetched
    other extra vector atReserve (controls.transport spanFrame NativeSpanPrepare.clobbers_data) placed.reserve
    (context.agendaReady.preserved spanFrame) ((spanFrame.lookup 5 (by decide)).trans context.agendaBase)
    (limit.preserved spanFrame (by simp)) (BitVec.ofNat 64 spans.leftWords.size) width
  rw [widthNat] at afterReserve
  have tested := spanFrame.trans reserveFrame
  have throughReserve := X86FuelPrefix.fetches_then 10 6 before prepared reserved readSpans reservation
  by_cases fits : agenda.size + spans.leftWords.size ≤ capacity
  · simp only [if_pos fits] at afterReserve
    obtain ⟨a, initialLength, lengthFrame, used, ⟨atCounter⟩⟩ := X86PlacedRegisterMove.executes
      (handlers other extra) vector (show At image reserved base (start + 84) from afterReserve) (by omega)
      9 14 (BitVec.ofNat 64 agenda.size) initializedLength placed.length
    have loopWidth := ((reserveFrame.trans (X86StateFrame.registerOnly lengthFrame)).lookup 8 (by decide)).trans width
    obtain ⟨b, initialIndex, indexFrame, index, ⟨atLoop⟩⟩ := X86PlacedRegisterMove.executes
      (handlers other extra) vector (show At image a base (start + 87) from atCounter) (by omega)
      8 1 (BitVec.ofNat 64 spans.leftWords.size) loopWidth placed.counter
    have postSpan := (reserveFrame.trans (X86StateFrame.registerOnly lengthFrame)).trans (X86StateFrame.registerOnly indexFrame)
    have initialized := spanFrame.trans postSpan
    have inputs : NativeAgendaLoop.Inputs agendaLayout termLayout spans agenda root spans.leftWords.size b :=
      ⟨(context.agendaReady.preserved initialized).records, context.termReady.preserved initialized,
        (initialized.lookup 5 (by decide)).trans context.agendaBase, (indexFrame.lookup 14 (by decide)).trans used,
        (initialized.lookup 11 (by decide)).trans context.cursor, (initialized.lookup 13 (by decide)).trans context.one,
        (initialized.lookup 12 (by decide)).trans context.zero, index, (indexFrame.lookup 8 (by decide)).trans loopWidth,
        (postSpan.lookup 6 (by decide)).trans lPtr, (postSpan.lookup 7 (by decide)).trans rPtr⟩
    obtain ⟨staged, updated, next, writes, looped, loopFrame, fresh, prepended, size, exactHistory, stagedState, ⟨atPublish⟩⟩ :=
      NativeAgendaLoop.fetched_all other extra vector placed.loop geometry.loop spans spans.leftWords.size (Nat.le_refl _)
        agenda root fits rootBound history held (show At image b base (start + 90) from atLoop)
        (controls.transport initialized (by decide)) inputs
    have privateFrame := initialized.trans loopFrame
    obtain ⟨after, published, publishFrame, ready, application, endpoint⟩ := NativeAgendaPublish.fetched
      other extra vector atPublish (controls.transport privateFrame (by decide)) placed.publish stagedState.records
      stagedState.agendaBase stagedState.length geometry.count
    have resulting : X86StateFrame.Frame clobbers (writes ∪ countCell agendaLayout) before after :=
      (privateFrame.trans publishFrame).mono (by decide) (by simp [countCell])
    have newState : NativeAgendaDispatch.Context agendaLayout termLayout updated terms next after :=
      ⟨ready, stagedState.terms.kept publishFrame geometry.nodes geometry.edges,
        (resulting.lookup 5 (by decide)).trans context.agendaBase, (resulting.lookup 3 (by decide)).trans context.termBase,
        (publishFrame.lookup 11 (by decide)).trans stagedState.root, (resulting.lookup 15 (by decide)).trans context.termCount,
        (resulting.lookup 12 (by decide)).trans context.zero, (resulting.lookup 13 (by decide)).trans context.one, application⟩
    have throughLength := X86FuelPrefix.fetches_then 16 1 before reserved a throughReserve initialLength
    have throughSetup := X86FuelPrefix.fetches_then 17 1 before a b throughLength initialIndex
    have throughLoop := X86FuelPrefix.fetches_then 18 _ before b staged throughSetup looped
    have completed := X86FuelPrefix.fetches_then _ 4 before staged after throughLoop published
    rw [show 18 + (19 * spans.leftWords.size + 2) + 4 = 24 + 19 * spans.leftWords.size by omega] at completed
    have whole : spans.pairs.take spans.leftWords.size = spans.pairs := by rw [← spans.length, List.take_length]
    rw [whole] at prepended exactHistory
    refine ⟨after, _, completed, ?_⟩
    rw [if_pos fits]
    exact ⟨updated, next, writes, rfl, resulting, fresh, prepended, size, exactHistory, newState, endpoint⟩
  · simp only [if_neg fits] at afterReserve
    refine ⟨reserved, 16, throughReserve, ?_⟩
    rw [if_neg fits]
    exact ⟨rfl, tested.mono (by decide) (by simp), (tested.lookup 11 (by decide)).trans context.cursor, ⟨afterReserve⟩⟩

/-- Starting at the actual agenda entry, one native expansion
has the packed work-list effect, or leaves the published memory
unchanged on the capacity exit. No span positions are passed
to the generated code. -/
theorem fetched_expansion (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {entry done exhausted : ℕ}
    {target : NativeTermDispatch.Targets} {before : Native}
    (point : At image before base entry) (controls : Controls before)
    (agendaCode : NativeAgendaDispatch.Placed image entry done target)
    (decomposition : Placed image target.expand entry target.malformed exhausted)
    (geometry : Geometry agendaLayout termLayout image base) (agenda : Arena) (root left right : Word)
    (context : NativeAgendaDispatch.Context agendaLayout termLayout agenda terms root before)
    (childBase : Reads before (agendaLayout.metadata.cell 1).address termLayout.edges.pointer)
    (limit : Reads before (agendaLayout.metadata.cell 2).address (BitVec.ofNat 64 capacity))
    (history trail pairs : PackedWorklist.Words) (held : readWords agenda root = some ((left, right) :: history))
    (inspected : PackedUnifierAction.inspect terms left right = some (.decompose pairs)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      if agenda.size + pairs.length ≤ capacity then
        ∃ updated next writes,
          steps = NativeAgendaDispatch.cost agenda terms root + (24 + 19 * pairs.length) ∧
          X86StateFrame.Frame (NativeAgendaDispatch.clobbers ∪ clobbers) (writes ∪ countCell agendaLayout) before after ∧
          NativeAgendaLoop.Within agendaLayout agenda.size updated.size writes ∧
          updated.size = agenda.size + pairs.length ∧
          readWords updated next = some (pairs ++ history) ∧
          PackedWorklist.advance ⟨terms, (left, right) :: history, trail⟩ = some (.working ⟨terms, pairs ++ history, trail⟩) ∧
          NativeAgendaDispatch.Context agendaLayout termLayout updated terms next after ∧
          Nonempty (At image after base entry)
      else steps = NativeAgendaDispatch.cost agenda terms root + 16 ∧
        X86StateFrame.Frame (NativeAgendaDispatch.clobbers ∪ clobbers) ∅ before after ∧
        Nonempty (At image after base exhausted) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨l, r, spans, choose, pairsEq⟩ := spans_of_inspect terms left right pairs inspected
  obtain ⟨node, top, operands, later⟩ :=
    NativeAgendaRecords.top_of_read agenda root ((left, right) :: history) held
  obtain ⟨leftEq, rightEq⟩ := Prod.mk.inj operands
  obtain ⟨selected, allocated, selectedFrame, position⟩ :=
    NativeAgendaDispatch.fetched other extra vector point controls agendaCode context
  simp only [NativeAgendaDispatch.Arrival, top] at position
  rw [leftEq, rightEq] at position
  obtain ⟨older, _, _, inputSpans, ⟨atExpand⟩⟩ := position
  have expansion : At image selected base target.expand := by simpa only [choose, NativeTermDispatch.Targets.at] using atExpand
  have shape := NativeSpanPrepare.Inputs.from_dispatch context.termReady inputSpans selectedFrame context.agendaBase childBase l r
  have nextState := context.next selectedFrame older
  have bound := PackedEquations.read_bound PackedEquations.wordCodes agenda node.older later
  obtain ⟨after, count, ran, result⟩ := fetched other extra vector expansion
    (controls.transport selectedFrame NativeAgendaDispatch.clobbers_data) decomposition geometry
    ⟨left.toNat, l⟩ ⟨right.toNat, r⟩ spans agenda node.older nextState shape
    (limit.preserved selectedFrame (by simp)) history later bound
  have width : spans.leftWords.size = pairs.length := spans.length.symm.trans (congrArg List.length pairsEq)
  rw [width] at result
  refine ⟨after, _, X86FuelPrefix.fetches_then _ _ before selected after allocated ran, ?_⟩
  by_cases fits : agenda.size + pairs.length ≤ capacity
  · rw [if_pos fits] at result ⊢
    obtain ⟨updated, next, writes, steps, frame, fresh, _, size, understood, newState, endpoint⟩ := result
    refine ⟨updated, next, writes, by rw [steps],
      (selectedFrame.trans frame).mono (Finset.Subset.refl _) (by simp), fresh, size, ?_, ?_, newState, endpoint⟩
    · rwa [pairsEq] at understood
    · have exact := packed_expands terms left right l r spans choose history trail
      rwa [pairsEq] at exact
  · rw [if_neg fits] at result ⊢
    obtain ⟨steps, frame, _, endpoint⟩ := result
    exact ⟨by rw [steps], (selectedFrame.trans frame).mono (Finset.Subset.refl _) (by simp), endpoint⟩

namespace Examples

private def graph : PackedTerms.Arena :=
  ⟨#[⟨⟨0, 7⟩, 0, 0⟩, ⟨⟨1, 42⟩, 0, 0⟩, ⟨⟨2, 3⟩, 0, 3⟩, ⟨⟨2, 3⟩, 3, 3⟩],
    #[0, 0, 1, 1, 1, 0]⟩

theorem ordered_decomposition_keeps_both_copies :
    PackedUnifierAction.inspect graph 2 3 = some (.decompose [(0, 1), (0, 1), (1, 0)]) := by decide +kernel

theorem pushing_backwards_presents_source_order :
    (PackedEquations.prependWords #[⟨0, 1, 1⟩] 1 [(0, 1), (0, 1), (1, 0)]).bind
      (fun (arena, root) => PackedEquations.readWords arena root) = some [(0, 1), (0, 1), (1, 0), (1, 1)] := by
  decide +kernel

theorem unequal_child_counts_do_not_truncate_the_work :
    PackedUnifierAction.inspect
      { graph with nodes := graph.nodes.set! 3 ⟨⟨2, 3⟩, 3, 2⟩ } 2 3 = none := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.NativeDecompose
