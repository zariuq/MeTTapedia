import Mettapedia.Machines.TIsa.StoreInstructions.NativeOccursApplication
import Mettapedia.Machines.TIsa.StoreInstructions.NativeTermSelection
import Mettapedia.Machines.TIsa.StoreInstructions.NativeDecisionTargets

/-!
# The native mark for whichever term is currently selected

The loop index selects the record. Its actual tag dispatches to
variable equality, constant zero, or a child-mark scan. All
successful paths join with the computed Boolean in RAX.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeOccursNode

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads)
open X86PlacedScalar (Code registerCode)
open NativeAgendaRead (fieldSource)
open NativeArenaGeometry (Region)
open NativeDecisions (Tree)
open NativeOccurs (word)
open NativeWords (Wiring)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def zeroCode : List ℕ := registerCode 0x89 12 0
def tagCode : List ℕ := X86DataLoad.code true 10 6 0
def symbolCode : List ℕ := X86DataLoad.code true 10 6 8
def tagWire : Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 10, by decide, by decide⟩

def tags : Tree :=
  .test .equal 10 12 (.leaf 0) (.test .equal 10 13 (.leaf 1) (.test .equal 10 14 (.leaf 2) (.leaf 3)))

def tagSite (start malformed : ℕ) (code : BitVec 32) : ℕ :=
  match code.toNat with
  | 0 => start + 65
  | 1 => start + 103
  | 2 => start + 114
  | _ => malformed

def tagRegisters (tag : Word) (r : Fin 16) : Word :=
  match r.val with
  | 10 => tag
  | 13 => 1
  | 14 => 2
  | _ => 0

theorem tag_reads : tags.reads = ({10, 12, 13, 14} : Finset (Fin 16)) := by decide +kernel

theorem tag_target (start malformed : ℕ) (tag : Word) :
    tagSite start malformed (tags.answer (tagRegisters tag)) =
      if tag = 0 then start + 65
      else if tag = 1 then start + 103
      else if tag = 2 then start + 114
      else malformed := by
  change tagSite start malformed
    (if (tag == 0) = true then 0 else if (tag == 1) = true then 1 else if (tag == 2) = true then 2 else 3) = _
  simp only [beq_iff_eq]
  split_ifs <;> rfl

theorem tag_cost (tag : Word) : NativeDecisionTargets.cost (tagRegisters tag) tags ≤ 7 := by
  simp only [tags, NativeDecisionTargets.cost]
  split_ifs <;> decide

def compareVariable : Tree := .test .equal 8 10 (.leaf 1) (.leaf 0)

def variableRegisters (query symbol : Word) (r : Fin 16) : Word :=
  if r = 8 then query else symbol

theorem variable_reads : compareVariable.reads = ({8, 10} : Finset (Fin 16)) := by decide +kernel

theorem variable_result (query symbol : Word) :
    (compareVariable.answer (variableRegisters query symbol)).zeroExtend 64 = word (query == symbol) := by
  change (if (query == symbol) = true then (1 : BitVec 32) else 0).zeroExtend 64 = _
  cases query == symbol <;> rfl

theorem variable_cost (query symbol : Word) :
    compareVariable.cost (variableRegisters query symbol) = 4 := by
  unfold compareVariable Tree.cost
  split <;> rfl

def variableCode (start : ℕ) : List ℕ :=
  symbolCode ++ NativeDecisions.emit 0 (start + 202) compareVariable (start + 72)

def constantCode (start : ℕ) : List ℕ := NativeDecisions.emit 0 (start + 202) (.leaf 0) (start + 103)

def emit (start malformed : ℕ) : List ℕ :=
  zeroCode ++ (NativeTermSelection.scaleCode .left ++ (tagCode ++
    (NativeDecisionTargets.emit (tagSite start malformed) tags (start + 18) ++
      (variableCode start ++ (constantCode start ++ NativeOccursApplication.emit (start + 114) malformed)))))

theorem emit_size (start malformed : ℕ) : (emit start malformed).length = 202 := by
  simp only [emit, List.length_append, NativeTermSelection.scale_size, NativeDecisionTargets.emit_size, variableCode,
    NativeDecisions.size, constantCode, NativeOccursApplication.emit_size, tags, compareVariable,
    Tree.width, NativeDecisionTargets.width, show zeroCode.length = 3 from rfl, show tagCode.length = 7 from rfl,
    show symbolCode.length = 7 from rfl]

structure Placed (image : NativeImage.View) (start malformed : ℕ) : Prop where
  extent : start + 202 ≤ image.size
  zero : Code image start zeroCode
  scale : Code image (start + 3) (NativeTermSelection.scaleCode .left)
  tag : Code image (start + 11) tagCode
  branch : NativeDecisionTargets.Placed image (tagSite start malformed) (start + 18) tags
  symbol : Code image (start + 65) symbolCode
  varCase : NativeDecisions.Placed image 0 (start + 202) (start + 72) compareVariable
  constant : NativeDecisions.Placed image 0 (start + 202) (start + 103) (.leaf 0)
  app : NativeOccursApplication.Placed image (start + 114) malformed

theorem placed_of_emitted (image : NativeImage.View) (start malformed : ℕ)
    (extent : start + 202 ≤ image.size) (target : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (bytes : Code image start (emit start malformed)) : Placed image start malformed := by
  obtain ⟨zero, rest⟩ := NativeWords.code_append (show Code image start (zeroCode ++ _) from bytes)
  obtain ⟨scale, rest⟩ := NativeWords.code_append rest
  rw [NativeTermSelection.scale_size] at rest
  obtain ⟨tag, rest⟩ := NativeWords.code_append rest
  change Code image (start + 18) _ at rest
  obtain ⟨route, rest⟩ := NativeWords.code_append rest
  rw [NativeDecisionTargets.emit_size] at rest
  change Code image (start + 65) _ at rest
  obtain ⟨varCode, rest⟩ := NativeWords.code_append rest
  have varWidth : (variableCode start).length = 38 := by
    simp only [variableCode, List.length_append, NativeDecisions.size, compareVariable, Tree.width]
    rfl
  rw [varWidth] at rest
  obtain ⟨constant, app⟩ := NativeWords.code_append rest
  rw [show (constantCode start).length = 11 from NativeDecisions.size _ _ _ _] at app
  obtain ⟨symbol, varCase⟩ := NativeWords.code_append (show Code image (start + 65)
    (symbolCode ++ NativeDecisions.emit 0 (start + 202) compareVariable (start + 72)) from varCode)
  have targets (tag : BitVec 32) : tagSite start malformed tag ≤ image.size := by
    unfold tagSite
    split <;> omega
  refine ⟨extent, zero, scale, tag, NativeDecisionTargets.placed_of_emitted image _ _ _
      (show start + 65 ≤ image.size by omega) targets short route,
    symbol, NativeDecisions.placed_of_emitted image 0 (start + 202) compareVariable (start + 72)
      (show start + 103 ≤ image.size by omega) extent short varCase,
    NativeDecisions.placed_of_emitted image 0 (start + 202) (.leaf 0) (start + 103)
      (show start + 114 ≤ image.size by omega) extent short constant,
    NativeOccursApplication.placed_of_emitted image (start + 114) malformed
      (show start + 202 ≤ image.size from extent) target short app⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register := NativeOccursApplication.clobbers

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {nodeCapacity edgeCapacity markCapacity agendaCapacity : ℕ}
variable {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {arena : PackedTerms.Arena}
variable {agendaLayout : NativeAgendaRecords.Layout agendaCapacity}
variable {table : Region markCapacity} {marks : Array Bool}

structure Input (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (arena : PackedTerms.Arena)
    (agendaLayout : NativeAgendaRecords.Layout agendaCapacity) (table : Region markCapacity) (marks : Array Bool)
    (query : Word) (before : Native) : Prop where
  source : NativeTermArena.Ready layout arena before
  marked : NativeMarkTable.Ready table marks before
  terms : lookup before 3 = some layout.nodes.pointer
  work : lookup before 5 = some agendaLayout.words.pointer
  pool : Reads before (agendaLayout.metadata.cell 1).address layout.edges.pointer
  tableBase : lookup before 7 = some (table.atWord 0)
  current : lookup before 1 = some (BitVec.ofNat 64 marks.size)
  name : lookup before 8 = some query
  zero : lookup before 12 = some 0
  one : lookup before 13 = some 1
  two : lookup before 14 = some 2

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start malformed : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start malformed)
    (query : Word) (input : Input layout arena agendaLayout table marks query before)
    (i : Fin arena.nodes.size) (current : i.val = marks.size)
    (children : Array Word) (segment : PackedTerms.segment arena.children arena.nodes[i] = some children)
    (bit : Bool) (marked : PackedOccurs.mark query marks arena.nodes[i].header children = some bit) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧ steps ≤ 12 * children.size + 19 ∧
      X86StateFrame.Frame clobbers ∅ before after ∧ lookup after 0 = some (word bit) ∧
      Nonempty (At image after base (start + 202)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  let node := arena.nodes[i]
  change PackedOccurs.mark query marks node.header children = some bit at marked
  let ordinal := BitVec.ofNat 64 marks.size
  let record := layout.record ⟨i.val, i.isLt.trans_le input.source.nodesFit⟩
  have iNat : ordinal.toNat = i.val := by
    have cap := (BitVec.ofNat 64 arena.nodes.size).isLt
    rw [input.source.count_word] at cap
    have present := i.isLt
    change (BitVec.ofNat 64 marks.size).toNat = i.val
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact current.symm
  have selectedPointer : record.pointer = layout.nodes.pointer + ordinal * 32 := by
    have eq : (⟨ordinal.toNat, by rw [iNat]; exact i.isLt.trans_le input.source.nodesFit⟩ : Fin nodeCapacity) =
        ⟨i.val, i.isLt.trans_le input.source.nodesFit⟩ := Fin.ext iNat
    have address := layout.record_word ordinal (by rw [iNat]; exact i.isLt.trans_le input.source.nodesFit)
    rw [eq] at address
    exact address
  obtain ⟨a, zeroed, zeroFrame, zero, ⟨atSelect⟩⟩ := X86PlacedRegisterMove.executes (handlers other extra) vector
    point (by omega) 12 0 0 input.zero placed.zero
  obtain ⟨b, scaled, scaledFrame, selected, ⟨atTag⟩⟩ := NativeTermSelection.scale_fetched other extra vector
    atSelect (by omega) .left layout.nodes.pointer ordinal ((zeroFrame.lookup 3 (by decide)).trans input.terms)
    zero ((zeroFrame.lookup 1 (by decide)).trans input.current) placed.scale
  have throughScale := (X86StateFrame.registerOnly zeroFrame).trans scaledFrame
  have heldPointer : lookup b 6 = some record.pointer := selectedPointer.symm ▸ selected
  obtain ⟨c, loadedTag, tagFrame, actualTag, ⟨atBranch⟩⟩ := (fieldSource record 0).fetch
    (handlers other extra) vector tagWire node.header.tag (show At image b base (start + 11) from atTag)
    (controls.transport throughScale (by decide)) heldPointer ((input.source.node i 0).preserved throughScale (by simp))
    (show start + 18 ≤ image.size by omega) placed.tag
  rw [linked] at loadedTag
  have ready := throughScale.trans tagFrame
  have tests (r : Fin 16) (read : r ∈ tags.reads) : lookup c r = some (tagRegisters node.header.tag r) := by
    simp only [tag_reads, Finset.mem_insert, Finset.mem_singleton] at read
    rcases read with rfl | rfl | rfl | rfl
    · exact actualTag
    · exact (ready.lookup 12 (by decide)).trans input.zero
    · exact (ready.lookup 13 (by decide)).trans input.one
    · exact (ready.lookup 14 (by decide)).trans input.two
  obtain ⟨d, routed, routeFrame, ⟨position⟩⟩ := NativeDecisionTargets.fetched (X86PlacedFrameAddress.nativeBase other)
    extra vector (tagSite start malformed) tags (tagRegisters node.header.tag)
    (show At image c base (start + 18) from atBranch) placed.branch tests
  rw [tag_target] at position
  let cost := NativeDecisionTargets.cost (tagRegisters node.header.tag) tags
  have costBound := tag_cost node.header.tag
  have spent := X86FuelPrefix.fetches_then 1 2 before a b zeroed scaled
  have throughTag := X86FuelPrefix.fetches_then 3 1 before b c spent loadedTag
  have dispatch := X86FuelPrefix.fetches_then 4 cost before c d throughTag routed
  have prelude := ready.trans routeFrame
  have keptPointer := ((tagFrame.trans routeFrame).lookup 6 (by decide)).trans heldPointer
  by_cases isVar : node.header.tag = 0
  · simp only [if_pos isVar] at position
    have bitIs : (query == node.header.symbol) = bit := by
      simpa only [PackedOccurs.mark, if_pos isVar, Option.some.injEq] using marked
    obtain ⟨e, read, symbolFrame, actual, ⟨atTest⟩⟩ := (fieldSource record 1).fetch (handlers other extra) vector
      tagWire node.header.symbol position (controls.transport prelude (by decide)) keptPointer
      ((input.source.node i 1).preserved prelude (by simp)) (show start + 72 ≤ image.size by omega) placed.symbol
    rw [linked] at read
    have registers := prelude.trans symbolFrame
    have inputs (r : Fin 16) (register : r ∈ compareVariable.reads) : lookup e r = some (variableRegisters query node.header.symbol r) := by
      simp only [variable_reads, Finset.mem_insert, Finset.mem_singleton] at register
      rcases register with rfl | rfl
      · exact (registers.lookup 8 (by decide)).trans input.name
      · exact actual
    obtain ⟨after, ran, frame, value, endpoint⟩ := NativeDecisions.fetched (X86PlacedFrameAddress.nativeBase other)
      extra vector 0 compareVariable (variableRegisters query node.header.symbol)
      (show At image e base (start + 72) from atTest) placed.varCase inputs
    rw [variable_cost] at ran
    rw [variable_result, bitIs] at value
    refine ⟨after, 4 + cost + 1 + 4, X86FuelPrefix.fetches_then _ 4 before e after
      (X86FuelPrefix.fetches_then _ 1 before d e dispatch read) ran, ?_,
      (registers.trans frame).mono (by decide) (by simp), value, endpoint⟩
    change cost ≤ 7 at costBound
    omega
  · by_cases isConst : node.header.tag = 1
    · simp only [if_neg isVar, if_pos isConst] at position
      have unmarked : false = bit := by
        simpa only [PackedOccurs.mark, if_neg isVar, if_pos isConst, Option.some.injEq] using marked
      obtain ⟨after, ran, frame, value, endpoint⟩ := NativeDecisions.fetched (X86PlacedFrameAddress.nativeBase other)
        extra vector 0 (.leaf 0) (fun _ => 0) position placed.constant (fun _ h => (Finset.notMem_empty _ h).elim)
      refine ⟨after, 4 + cost + 2, X86FuelPrefix.fetches_then _ 2 before d after dispatch ran,
        ?_, (prelude.trans frame).mono (by decide) (by simp), unmarked ▸ value, endpoint⟩
      change cost ≤ 7 at costBound
      omega
    · have isApp : node.header.tag = 2 := by
        by_contra otherTag
        simp only [PackedOccurs.mark, if_neg isVar, if_neg isConst, if_neg otherTag] at marked
        cases marked
      simp only [if_neg isVar, if_neg isConst, if_pos isApp] at position
      have markedChildren : (PackedOccurs.childrenBits marks children).map (List.any · id) = some bit := by
        simpa only [PackedOccurs.mark, if_neg isVar, if_neg isConst, if_pos isApp] using marked
      obtain ⟨bits, ordered, equal⟩ := Option.map_eq_some_iff.mp markedChildren
      have inputApp : NativeOccursApplication.Input layout arena agendaLayout table marks i d :=
        ⟨input.source.preserved prelude, input.marked.preserved prelude, keptPointer,
          (prelude.lookup 5 (by decide)).trans input.work, input.pool.preserved prelude (by simp),
          (prelude.lookup 7 (by decide)).trans input.tableBase, (prelude.lookup 1 (by decide)).trans input.current,
          (prelude.lookup 12 (by decide)).trans input.zero, (prelude.lookup 13 (by decide)).trans input.one⟩
      obtain ⟨after, steps, ran, bound, frame, value, endpoint⟩ := NativeOccursApplication.fetched other extra vector
        position (controls.transport prelude (by decide)) placed.app i inputApp children segment bits ordered
      refine ⟨after, 4 + cost + steps, X86FuelPrefix.fetches_then _ steps before d after dispatch ran,
        ?_, (prelude.trans frame).mono (by decide) (by simp), equal ▸ value, endpoint⟩
      change cost ≤ 7 at costBound
      omega

end Mettapedia.Machines.TIsa.StoreInstructions.NativeOccursNode
