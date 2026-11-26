import Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingSelection
import Mettapedia.Machines.TIsa.StoreInstructions.PackedRemapCoordinates

/-!
# Native remapping for variable and constant nodes

The occurrence workspace can subsequently hold the handle map;
the map starts with an empty initialized prefix. A leaf reuses
its original node, except for a variable with the selected
symbol. The bytes load its actual tag and symbol and write
exactly one new map word. Applications take a separate exit.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstLeaf

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls CodeApart footprint)
open X86PlacedScalar (Code CompareBranch Jump registerCode jumpDelta)
open NativeArenaGeometry (Region)
open NativeAgendaRead (fieldSource)
open MemoryBinding (Native)
open PackedTerms (Arena)
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev MapReady {capacity : ℕ} (table : Region capacity) (mapping : Array Word) (native : Native) : Prop :=
  NativeMarkTable.PrefixReady id table mapping native

theorem empty_on_reuse {capacity : ℕ} (table : Region capacity) (native : Native) :
    MapReady table #[] native :=
  NativeMarkTable.PrefixReady.empty id table native

def targets (start application malformed : ℕ) (word : BitVec 32) : ℕ :=
  match word.toNat with
  | 0 => start + 54
  | 1 => start + 78
  | 2 => application
  | _ => malformed

def tagBytes : List ℕ := X86DataLoad.code true 10 6 0
def symbolBytes : List ℕ := X86DataLoad.code true 10 6 8
def replaceCode : List ℕ := registerCode 0x89 9 0
def keepCode : List ℕ := registerCode 0x89 1 0
def mapStore : List ℕ := NativeIndexedWord.storeCode NativeChildMarkLoop.markBase NativeOccursLoop.cursorIndex

def emit (start application malformed : ℕ) : List ℕ :=
  tagBytes ++ (NativeDecisionTargets.emit (targets start application malformed) NativeOccursNode.tags (start + 7) ++
    (symbolBytes ++ (NativeDecisions.compareBytes .equal 8 10 (start + 61) (start + 78) ++
      (replaceCode ++ (X86UnconditionalJump.Block.code (jumpDelta (start + 73) (start + 81)) ++
        (keepCode ++ mapStore))))))

theorem emit_size (start application malformed : ℕ) : (emit start application malformed).length = 92 := by
  simp only [emit, List.length_append, NativeDecisionTargets.emit_size, NativeDecisions.compare_size,
    NativeOccursNode.tags, NativeDecisionTargets.width, X86UnconditionalJump.Block.code_length,
    show tagBytes.length = 7 from rfl, show symbolBytes.length = 7 from rfl, show replaceCode.length = 3 from rfl,
    show keepCode.length = 3 from rfl, show mapStore.length = 11 from rfl]

structure Placed (image : NativeImage.View) (start application malformed : ℕ) : Prop where
  extent : start + 92 ≤ image.size
  tag : Code image start tagBytes
  route : NativeDecisionTargets.Placed image (targets start application malformed) (start + 7) NativeOccursNode.tags
  symbol : Code image (start + 54) symbolBytes
  compare : CompareBranch image (start + 61) (start + 78) .equal 8 10
  replace : Code image (start + 70) replaceCode
  jump : Jump image (start + 73) (start + 81)
  keep : Code image (start + 78) keepCode
  store : Code image (start + 81) mapStore

theorem placed_of_emitted (image : NativeImage.View) (start application malformed : ℕ)
    (extent : start + 92 ≤ image.size) (app : application ≤ image.size) (bad : malformed ≤ image.size)
    (short : image.size < 2 ^ 31) (installed : Code image start (emit start application malformed)) :
    Placed image start application malformed := by
  obtain ⟨tag, rest⟩ := NativeWords.code_append (show Code image start (tagBytes ++ _) from installed)
  obtain ⟨route, rest⟩ := NativeWords.code_append rest
  rw [NativeDecisionTargets.emit_size] at rest
  change Code image (start + 54) _ at rest
  obtain ⟨symbol, rest⟩ := NativeWords.code_append rest
  change Code image (start + 61) _ at rest
  obtain ⟨compare, rest⟩ := NativeWords.code_append rest
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨replace, rest⟩ := NativeWords.code_append rest
  obtain ⟨jump, rest⟩ := NativeWords.code_append rest
  obtain ⟨keep, store⟩ := NativeWords.code_append rest
  have target (word : BitVec 32) : targets start application malformed word ≤ image.size := by
    unfold targets
    split <;> omega
  refine ⟨extent, tag, NativeDecisionTargets.placed_of_emitted image _ _ _ (show start + 54 ≤ image.size by omega)
    target short route, symbol, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) (by omega) short compare, replace,
    ⟨by omega, by omega, ?_, jump⟩, keep, store⟩
  unfold jumpDelta
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
  omega

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register := {.rax, .r10, .rflags, .rip}

variable {capacity nodeCapacity edgeCapacity : ℕ}
variable {table : Region capacity} {layout : NativeTermArena.Layout nodeCapacity edgeCapacity}
variable {arena : Arena} {mapping : Array Word}

structure Inputs (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (arena : Arena)
    (table : Region capacity) (mapping : Array Word) (i : Fin arena.nodes.size)
    (original query replacement : Word) (before : Native) : Prop where
  ready : NativeTermArena.Ready layout arena before
  physical : MapReady table mapping before
  record : lookup before 6 = some (ready.bank i).pointer
  tableBase : lookup before 7 = some (table.atWord 0)
  current : lookup before 1 = some original
  query : lookup before 8 = some query
  replacement : lookup before 9 = some replacement
  zero : lookup before 12 = some 0
  one : lookup before 13 = some 1
  two : lookup before 14 = some 2

private theorem route_target (start application malformed : ℕ) (tag : Word) :
    targets start application malformed (NativeOccursNode.tags.answer (NativeOccursNode.tagRegisters tag)) =
      if tag = 0 then start + 54 else if tag = 1 then start + 78 else if tag = 2 then application else malformed := by
  change targets start application malformed
    (if (tag == 0) = true then 0 else if (tag == 1) = true then 1 else if (tag == 2) = true then 2 else 3) = _
  simp only [beq_iff_eq]
  split_ifs <;> rfl

private theorem keep_word (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start application malformed : ℕ} {before : Native}
    (point : At image before base (start + 78)) (placed : Placed image start application malformed)
    (original : Word) (current : lookup before 1 = some original) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧ lookup after 0 = some original ∧
      Nonempty (At image after base (start + 81)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  obtain ⟨after, moved, frame, known, endpoint⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 1 0 original current placed.keep
  exact ⟨after, moved, (X86StateFrame.registerOnly frame).mono (by decide) (by simp), known, endpoint⟩

/-- Fetched classification and leaf remapping, without tree
expansion or any reconstructed term record. On the other
paths the map and the selected record are retained. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start application malformed : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start application malformed)
    (i : Fin arena.nodes.size) (original query replacement : Word) (ordinal : original.toNat = i.val)
    (cursor : i.val = mapping.size) (input : Inputs layout arena table mapping i original query replacement before)
    (room : mapping.size < capacity) (apart : CodeApart image base
      (footprint ((table.wordCell ⟨mapping.size, room⟩).cell 0).address)) (target : Arena) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      if arena.nodes[i].header.tag = 0 ∨ arena.nodes[i].header.tag = 1 then
        ∃ handle, X86StateFrame.Frame clobbers (footprint ((table.wordCell ⟨mapping.size, room⟩).cell 0).address) before after ∧
          MapReady table (mapping.push handle) after ∧
          PackedSubstitution.rewrite arena target mapping query replacement original = some (target, handle) ∧
          lookup after 0 = some handle ∧ Nonempty (At image after base (start + 92))
      else X86StateFrame.Frame clobbers ∅ before after ∧
        lookup after 6 = some (input.ready.bank i).pointer ∧
        Nonempty (At image after base (if arena.nodes[i].header.tag = 2 then application else malformed)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  let node := arena.nodes[i]
  let record := layout.record ⟨i.val, i.isLt.trans_le input.ready.nodesFit⟩
  obtain ⟨a, tag, tagFrame, value, ⟨atRoute⟩⟩ := (fieldSource record 0).fetch (handlers other extra)
    vector NativeOccursNode.tagWire node.header.tag point controls input.record (input.ready.node i 0)
    (show start + 7 ≤ image.size by omega) placed.tag
  rw [linked] at tag
  have regs (r : Fin 16) (read : r ∈ NativeOccursNode.tags.reads) :
      lookup a r = some (NativeOccursNode.tagRegisters node.header.tag r) := by
    simp only [NativeOccursNode.tag_reads, Finset.mem_insert, Finset.mem_singleton] at read
    rcases read with rfl | rfl | rfl | rfl
    · exact value
    · exact (tagFrame.lookup 12 (by decide)).trans input.zero
    · exact (tagFrame.lookup 13 (by decide)).trans input.one
    · exact (tagFrame.lookup 14 (by decide)).trans input.two
  obtain ⟨b, routed, routeFrame, ⟨atCase⟩⟩ := NativeDecisionTargets.fetched (X86PlacedFrameAddress.nativeBase other)
    extra vector (targets start application malformed) NativeOccursNode.tags (NativeOccursNode.tagRegisters node.header.tag)
    (show At image a base (start + 7) from atRoute) placed.route regs
  rw [route_target] at atCase
  let dispatchCost := 1 + NativeDecisionTargets.cost (NativeOccursNode.tagRegisters node.header.tag) NativeOccursNode.tags
  have dispatch := X86FuelPrefix.fetches_then 1 _ before a b tag routed
  have beforeCase : X86StateFrame.Frame clobbers ∅ before b := (tagFrame.trans routeFrame).mono (by decide) (by simp)
  have readNode : arena.nodes[original.toNat]? = some node := by
    rw [ordinal, Array.getElem?_eq_getElem i.isLt]
    rfl
  by_cases leaf : node.header.tag = 0 ∨ node.header.tag = 1
  · have choose : ∃ selected steps handle, (X86FuelPrefix.fetches steps).run b = .ok () selected ∧
        X86StateFrame.Frame clobbers ∅ b selected ∧ lookup selected 0 = some handle ∧
        PackedSubstitution.rewrite arena target mapping query replacement original = some (target, handle) ∧
        Nonempty (At image selected base (start + 81)) := by
      rcases leaf with isVar | isConstant
      · simp only [if_pos isVar] at atCase
        obtain ⟨c, symbol, symbolFrame, selectedName, ⟨atCompare⟩⟩ := (fieldSource record 1).fetch
          (handlers other extra) vector NativeOccursNode.tagWire node.header.symbol atCase
          (controls.transport beforeCase (by decide)) ((beforeCase.lookup 6 (by decide)).trans input.record)
          ((input.ready.node i 1).preserved beforeCase (by simp)) (show start + 61 ≤ image.size by omega) placed.symbol
        rw [linked] at symbol
        obtain ⟨d, compared, compareFrame, ⟨decision⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
          extra vector (show At image c base (start + 61) from atCompare) .equal 8 10 placed.compare query node.header.symbol
          (((beforeCase.trans symbolFrame).lookup 8 (by decide)).trans input.query) selectedName
        simp only [Comparison.evaluate, beq_iff_eq] at decision
        have solid := symbolFrame.trans (X86StateFrame.registerOnly compareFrame)
        have prefixRun := X86FuelPrefix.fetches_then 1 2 b c d symbol compared
        by_cases same : query = node.header.symbol
        · simp only [if_pos same] at decision
          obtain ⟨e, moved, movedFrame, handle, ⟨atJump⟩⟩ := X86PlacedRegisterMove.executes (handlers other extra) vector
            (show At image d base (start + 70) from decision) (by omega) 9 0 replacement
            (((beforeCase.trans solid).lookup 9 (by decide)).trans input.replacement) placed.replace
          obtain ⟨after, jumped, jumpedFrame, endpoint⟩ := X86PlacedScalar.jump (X86PlacedFrameAddress.nativeBase other)
            extra vector (show At image e base (start + 73) from atJump) placed.jump
          exact ⟨after, 5, replacement, X86FuelPrefix.fetches_then 4 1 b e after
            (X86FuelPrefix.fetches_then 3 1 b d e prefixRun moved) jumped,
            (solid.trans (X86StateFrame.registerOnly (movedFrame.trans jumpedFrame))).mono (by decide) (by simp),
            (jumpedFrame.lookup 0 (by decide)).trans handle,
            by simp [PackedSubstitution.rewrite, readNode, isVar, same.symm], endpoint⟩
        · simp only [if_neg same] at decision
          obtain ⟨after, moved, movedFrame, handle, endpoint⟩ := keep_word other extra vector decision placed original
            (((beforeCase.trans solid).lookup 1 (by decide)).trans input.current)
          exact ⟨after, 4, original, X86FuelPrefix.fetches_then 3 1 b d after prefixRun moved,
            (solid.trans movedFrame).mono (by decide) (by simp), handle,
            by simp [PackedSubstitution.rewrite, readNode, isVar, Ne.symm same], endpoint⟩
      · have notVar : node.header.tag ≠ 0 := by rw [isConstant]; decide
        simp only [if_neg notVar, if_pos isConstant] at atCase
        obtain ⟨after, moved, frame, known, endpoint⟩ := keep_word other extra vector atCase placed original
          ((beforeCase.lookup 1 (by decide)).trans input.current)
        exact ⟨after, 1, original, moved, frame, known, by simp [PackedSubstitution.rewrite, readNode, isConstant], endpoint⟩
    obtain ⟨c, steps, handle, ran, selectFrame, chosen, law, ⟨beforeStore⟩⟩ := choose
    have prelude := beforeCase.trans selectFrame
    let slot : Fin capacity := ⟨mapping.size, room⟩
    have physical : 0 + original.toNat < capacity := by rw [Nat.zero_add, ordinal, cursor]; exact room
    have coord : (⟨0 + original.toNat, physical⟩ : Fin capacity) = slot := Fin.ext ((Nat.zero_add _).trans (ordinal.trans cursor))
    have separated : CodeApart image base (footprint ((table.wordCell ⟨0 + original.toNat, physical⟩).cell 0).address) := by
      rw [coord]; exact apart
    obtain ⟨after, stored, storeFrame, written, endpoint⟩ := NativeIndexedWord.fetched_store other extra vector beforeStore
      (controls.transport prelude (by decide)) (by omega) NativeChildMarkLoop.markBase NativeOccursLoop.cursorIndex table 0
      original handle physical ((prelude.lookup 7 (by decide)).trans input.tableBase)
      ((prelude.lookup 1 (by decide)).trans input.current) chosen placed.store separated
    rw [coord] at storeFrame written
    have frame : X86StateFrame.Frame clobbers (footprint ((table.wordCell slot).cell 0).address) before after :=
      (prelude.trans storeFrame).mono (by decide) (by simp)
    refine ⟨after, dispatchCost + steps + 2, X86FuelPrefix.fetches_then _ 2 before c after
      (X86FuelPrefix.fetches_then dispatchCost steps before b c dispatch ran) stored, ?_⟩
    rw [if_pos leaf]
    exact ⟨handle, frame, input.physical.extend room handle frame written, law,
      (storeFrame.lookup 0 (by decide)).trans chosen, endpoint⟩
  · have notVar : node.header.tag ≠ 0 := fun h => leaf (Or.inl h)
    have notConst : node.header.tag ≠ 1 := fun h => leaf (Or.inr h)
    simp only [if_neg notVar, if_neg notConst] at atCase
    refine ⟨b, dispatchCost, dispatch, ?_⟩
    rw [if_neg leaf]
    exact ⟨beforeCase, (beforeCase.lookup 6 (by decide)).trans input.record, ⟨atCase⟩⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstLeaf
