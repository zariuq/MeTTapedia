import Mettapedia.Machines.TIsa.StoreInstructions.NativeRemapChildren

/-!
# Reusing an unchanged native application

The code starts from the selected record, reads its child span
and checks the initialized remap. If no child moves it restores
the tag constant and writes the original handle to the map.
The changed continuation is reached with no stores.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstCompound

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads CodeApart footprint)
open X86PlacedScalar (Code)
open NativeArenaGeometry (Region)
open NativeSubstLeaf (MapReady keepCode mapStore)
open MemoryBinding (Native)
open PackedTerms (Arena)
local instance : MemoryPrimitives := X86Memory.ordinary

def restoreCode : List ℕ := X86Immediate32.code 14 2

def emit (start changed malformed : ℕ) : List ℕ :=
  NativeOccursApplication.prepareCode ++
    (NativeRemapChildren.emit (start + 28) (start + 85) changed malformed ++ (restoreCode ++ (keepCode ++ mapStore)))

theorem emit_size (start changed malformed : ℕ) : (emit start changed malformed).length = 105 := by
  simp only [emit, List.length_append, NativeOccursApplication.prepare_size, NativeRemapChildren.emit_size,
    show restoreCode.length = 6 from rfl, show keepCode.length = 3 from rfl, show mapStore.length = 11 from rfl]

structure Placed (image : NativeImage.View) (start changed malformed : ℕ) : Prop where
  extent : start + 105 ≤ image.size
  span : NativeOccursApplication.PreparePlaced image start
  test : NativeRemapChildren.Placed image (start + 28) (start + 85) changed malformed
  restore : Code image (start + 85) restoreCode
  keep : Code image (start + 91) keepCode
  store : Code image (start + 94) mapStore

theorem placed_of_emitted (image : NativeImage.View) (start changed malformed : ℕ)
    (extent : start + 105 ≤ image.size) (different : changed ≤ image.size) (bad : malformed ≤ image.size)
    (short : image.size < 2 ^ 31) (installed : Code image start (emit start changed malformed)) :
    Placed image start changed malformed := by
  obtain ⟨span, rest⟩ := NativeWords.code_append (show Code image start (NativeOccursApplication.prepareCode ++ _) from installed)
  rw [NativeOccursApplication.prepare_size] at rest
  obtain ⟨test, rest⟩ := NativeWords.code_append rest
  rw [NativeRemapChildren.emit_size] at rest
  obtain ⟨restore, rest⟩ := NativeWords.code_append rest
  obtain ⟨keep, store⟩ := NativeWords.code_append rest
  exact ⟨extent, NativeOccursApplication.prepare_placed image start (by omega) span,
    NativeRemapChildren.placed_of_emitted image (start + 28) (start + 85) changed malformed
      (by omega) (by omega) different bad short test, restore, keep, store⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register := NativeOccursApplication.clobbers ∪ NativeRemapChildren.clobbers

variable {mapCapacity nodeCapacity edgeCapacity agendaCapacity : ℕ}
variable {table : Region mapCapacity} {layout : NativeTermArena.Layout nodeCapacity edgeCapacity}
variable {agendaLayout : NativeAgendaRecords.Layout agendaCapacity}
variable {arena : Arena} {mapping : Array Word}

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start changed malformed : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start changed malformed)
    (i : Fin arena.nodes.size) (original query replacement : Word) (ordinal : original.toNat = i.val)
    (cursor : i.val = mapping.size) (input : NativeSubstLeaf.Inputs layout arena table mapping i original query replacement before)
    (work : lookup before 5 = some agendaLayout.words.pointer)
    (pool : Reads before (agendaLayout.metadata.cell 1).address layout.edges.pointer)
    (application : arena.nodes[i].header.tag = 2)
    (children newer : Array Word) (segment : PackedTerms.segment arena.children arena.nodes[i] = some children)
    (translated : PackedSubstitution.translate mapping children = some newer)
    (room : mapping.size < mapCapacity) (apart : CodeApart image base
      (footprint ((table.wordCell ⟨mapping.size, room⟩).cell 0).address)) (target : Arena) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      if newer = children then
        X86StateFrame.Frame clobbers (footprint ((table.wordCell ⟨mapping.size, room⟩).cell 0).address) before after ∧
        MapReady table (mapping.push original) after ∧ lookup after 14 = some 2 ∧
        PackedSubstitution.rewrite arena target mapping query replacement original = some (target, original) ∧
        Nonempty (At image after base (start + 105))
      else X86StateFrame.Frame clobbers ∅ before after ∧ Nonempty (At image after base changed) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  let node := arena.nodes[i]
  obtain ⟨a, loaded, spanFrame, pointer, count, ⟨testAt⟩⟩ := NativeOccursApplication.fetched_span other extra vector
    point controls placed.span i input.ready input.record work pool
  have width := (PackedTerms.segment_width arena.children node children segment).1
  have widthWord : BitVec.ofNat 64 children.size = node.childrenCount := by
    rw [width, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have originalWord : original = BitVec.ofNat 64 mapping.size := by
    rw [← cursor, ← ordinal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have ready : NativeRemapChildren.Input layout arena table mapping node children.size a :=
    ⟨input.ready.preserved spanFrame, input.physical.preserved spanFrame, pointer,
      (spanFrame.lookup 7 (by decide)).trans input.tableBase,
      originalWord ▸ (spanFrame.lookup 1 (by decide)).trans input.current,
      widthWord.symm ▸ count, (spanFrame.lookup 12 (by decide)).trans input.zero, (spanFrame.lookup 13 (by decide)).trans input.one⟩
  obtain ⟨b, steps, tested, _, testFrame, ⟨destination⟩⟩ := NativeRemapChildren.fetched other extra vector placed.test
    children newer segment translated children.size (Nat.le_refl _) testAt
    (controls.transport spanFrame NativeOccursApplication.clobbers_data) ready
  have width' := (PackedRemapCoordinates.coordinates mapping children newer translated).1
  have condition : children.toList.take children.size = newer.toList.take children.size ↔ newer = children := by
    have l := List.take_length (l := children.toList)
    have r := List.take_length (l := newer.toList)
    simp only [Array.length_toList, width'] at l r
    rw [l, r]
    exact ⟨fun same => Array.toList_inj.mp same.symm, fun h => by rw [h]⟩
  have passed := spanFrame.trans testFrame
  have testedSpan := X86FuelPrefix.fetches_then 5 steps before a b loaded tested
  by_cases same : newer = children
  · simp only [if_pos (condition.mpr same)] at destination
    obtain ⟨c, reset, resetFrame, two, ⟨atKeep⟩⟩ := X86PlacedScalar.rex_immediate
      (X86PlacedFrameAddress.nativeBase other) extra vector destination (by omega) 14 2 placed.restore
    have throughReset := passed.trans (X86StateFrame.registerOnly resetFrame)
    obtain ⟨d, retained, retainFrame, keep, ⟨atStore⟩⟩ := X86PlacedRegisterMove.executes
      (handlers other extra) vector (show At image c base (start + 91) from atKeep)
      (by omega) 1 0 original ((throughReset.lookup 1 (by decide)).trans input.current) placed.keep
    have prepared := throughReset.trans (X86StateFrame.registerOnly retainFrame)
    let slot : Fin mapCapacity := ⟨mapping.size, room⟩
    have fits : 0 + original.toNat < mapCapacity := by rw [Nat.zero_add, ordinal, cursor]; exact room
    have sameSlot : (⟨0 + original.toNat, fits⟩ : Fin mapCapacity) = slot :=
      Fin.ext ((Nat.zero_add _).trans (ordinal.trans cursor))
    have codeAside : CodeApart image base (footprint ((table.wordCell ⟨0 + original.toNat, fits⟩).cell 0).address) := by
      rw [sameSlot]; exact apart
    obtain ⟨after, stored, storeFrame, wrote, endpoint⟩ := NativeIndexedWord.fetched_store other extra vector
      (show At image d base (start + 94) from atStore) (controls.transport prepared (by decide)) (by omega)
      NativeChildMarkLoop.markBase NativeOccursLoop.cursorIndex table 0 original original fits
      ((prepared.lookup 7 (by decide)).trans input.tableBase) ((prepared.lookup 1 (by decide)).trans input.current)
      keep placed.store codeAside
    rw [sameSlot] at storeFrame wrote
    have frame : X86StateFrame.Frame clobbers (footprint ((table.wordCell slot).cell 0).address) before after :=
      (prepared.trans storeFrame).mono (by decide) (by simp)
    have index : arena.nodes[original.toNat]? = some node := by rw [ordinal, Array.getElem?_eq_getElem i.isLt]; rfl
    have rule : PackedSubstitution.rewrite arena target mapping query replacement original = some (target, original) := by
      have app : node.header.tag = 2 := application
      have neither₀ : node.header.tag ≠ 0 := by rw [app]; decide
      have neither₁ : node.header.tag ≠ 1 := by rw [app]; decide
      change PackedTerms.segment arena.children node = some children at segment
      simp only [PackedSubstitution.rewrite, index, bind, Option.bind_some, if_neg neither₀, if_neg neither₁,
        if_pos app, segment, translated, if_pos same]
    have executed := X86FuelPrefix.fetches_then (5 + steps + 1 + 1) 2 before d after
      (X86FuelPrefix.fetches_then (5 + steps + 1) 1 before c d
        (X86FuelPrefix.fetches_then (5 + steps) 1 before b c testedSpan reset) retained) stored
    refine ⟨after, _, executed, ?_⟩
    rw [if_pos same]
    exact ⟨frame, input.physical.extend room original frame wrote,
      ((X86StateFrame.registerOnly retainFrame).trans storeFrame).lookup 14 (by decide) |>.trans two, rule, endpoint⟩
  · simp only [if_neg (fun h => same (condition.mp h))] at destination
    refine ⟨b, _, testedSpan, ?_⟩
    rw [if_neg same]
    exact ⟨passed.mono (Finset.Subset.refl _) (by simp), ⟨destination⟩⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstCompound
