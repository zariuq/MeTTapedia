import Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionChanged
import Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstCompound

/-!
# One native iteration of term-graph substitution

The original node decides whether to reuse a leaf, retain an
application, or append a changed application. Each branch
initializes exactly the next map entry. In particular, testing
a child does not unfold the subgraph reachable from it.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionBody

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls)
open X86PlacedScalar (Code Jump jumpDelta)
open NativeArenaGeometry (Region)
open NativeSubstitutionFrame (Table mutableBytes)
open NativeSubstitutionMemory (Geometry Includes mapBytes)
open NativeSubstitutionChanged renaming State → RemapState
open NativeSubstLeaf (MapReady)
open PackedTerms (Arena)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def emit (start exhausted malformed : ℕ) : List ℕ :=
  NativeSubstitutionSelect.emit ++
    (NativeSubstLeaf.emit (start + 11) (start + 108) malformed ++
      (X86UnconditionalJump.Block.code (jumpDelta (start + 103) (start + 538)) ++
        (NativeSubstCompound.emit (start + 108) (start + 218) malformed ++
          (X86UnconditionalJump.Block.code (jumpDelta (start + 213) (start + 538)) ++
            NativeSubstitutionChanged.emit (start + 218) exhausted malformed))))

theorem emit_size (start exhausted malformed : ℕ) : (emit start exhausted malformed).length = 538 := by
  simp only [emit, List.length_append, NativeSubstitutionSelect.emit_size, NativeSubstLeaf.emit_size,
    X86UnconditionalJump.Block.code_length, NativeSubstCompound.emit_size, NativeSubstitutionChanged.emit_size]

structure Placed (image : NativeImage.View) (start exhausted malformed : ℕ) : Prop where
  extent : start + 538 ≤ image.size
  select : Code image start NativeSubstitutionSelect.emit
  leaf : NativeSubstLeaf.Placed image (start + 11) (start + 108) malformed
  afterLeaf : Jump image (start + 103) (start + 538)
  application : NativeSubstCompound.Placed image (start + 108) (start + 218) malformed
  afterApplication : Jump image (start + 213) (start + 538)
  different : NativeSubstitutionChanged.Placed image (start + 218) exhausted malformed

theorem placed_of_emitted (image : NativeImage.View) (start exhausted malformed : ℕ)
    (extent : start + 538 ≤ image.size) (lack : exhausted ≤ image.size) (bad : malformed ≤ image.size)
    (short : image.size < 2 ^ 31) (code : Code image start (emit start exhausted malformed)) :
    Placed image start exhausted malformed := by
  obtain ⟨select, rest⟩ := NativeWords.code_append (show Code image start (NativeSubstitutionSelect.emit ++ _) from code)
  rw [NativeSubstitutionSelect.emit_size] at rest
  obtain ⟨leaf, rest⟩ := NativeWords.code_append rest
  rw [NativeSubstLeaf.emit_size] at rest
  obtain ⟨leafEnd, rest⟩ := NativeWords.code_append rest
  rw [X86UnconditionalJump.Block.code_length] at rest
  obtain ⟨application, rest⟩ := NativeWords.code_append rest
  rw [NativeSubstCompound.emit_size] at rest
  obtain ⟨applicationEnd, different⟩ := NativeWords.code_append rest
  rw [X86UnconditionalJump.Block.code_length] at different
  refine ⟨extent, select,
    NativeSubstLeaf.placed_of_emitted image _ _ malformed (by omega) (by omega) bad short leaf,
    ⟨by omega, by omega, ?_, leafEnd⟩,
    NativeSubstCompound.placed_of_emitted image _ _ malformed (by omega) (by omega) bad short application,
    ⟨by omega, by omega, ?_, applicationEnd⟩,
    NativeSubstitutionChanged.placed_of_emitted image _ exhausted malformed (by omega) lack bad short different⟩
  all_goals
    unfold jumpDelta
    rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
    omega

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register := NativeSubstitutionChanged.clobbers
private abbrev quiet : Finset Register := {.rax, .rdx, .rsi, .r10, .r14, .rflags, .rip}

variable {nodeCapacity edgeCapacity mapCapacity agendaCapacity : ℕ}
variable {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {map : Region mapCapacity}
variable {frame : Table} {agenda : NativeAgendaRecords.Layout agendaCapacity}
variable {source target : Arena} {mapping : Array Word} {original query replacement : Word}
variable {before after : Native} {image : NativeImage.View} {base : BitVec 48}

private theorem with_map (ready : RemapState layout map frame agenda source target mapping original query replacement before)
    {writes : Finset ℕ} {newMapping : Array Word} (run : X86StateFrame.Frame quiet writes before after)
    (mapped : MapReady map newMapping after)
    (nodes : ∀ i j, Disjoint (NativeSubstitutionMemory.nodeBytes layout i j) writes)
    (edges : ∀ i, Disjoint (NativeSubstitutionMemory.edgeBytes layout i) writes)
    (staged : ∀ j, Disjoint (NativeSubstitutionMemory.frameBytes frame j) writes)
    (pool : Disjoint (NativeSubstitutionMemory.poolBytes agenda) writes) :
    RemapState layout map frame agenda source target newMapping original query replacement after :=
  ⟨ready.extension, ready.terms.kept run nodes edges, ready.staged.kept run (by decide) staged, mapped,
    (run.lookup 3 (by decide)).trans ready.nodes, (run.lookup 5 (by decide)).trans ready.agendaBase,
    ready.pool.preserved run pool, (run.lookup 7 (by decide)).trans ready.tableBase,
    (run.lookup 1 (by decide)).trans ready.cursor, (run.lookup 8 (by decide)).trans ready.query,
    (run.lookup 9 (by decide)).trans ready.replacement, (run.lookup 12 (by decide)).trans ready.zero,
    (run.lookup 13 (by decide)).trans ready.one⟩

private theorem retain (geometry : Geometry layout map frame agenda image base)
    (ready : RemapState layout map frame agenda source target mapping original query replacement before)
    {newMapping : Array Word} (slot : Fin mapCapacity)
    (run : X86StateFrame.Frame quiet (mapBytes map slot) before after) (mapped : MapReady map newMapping after) :
    RemapState layout map frame agenda source target newMapping original query replacement after :=
  with_map ready run mapped (fun i j => geometry.node_map i j slot) (fun i => geometry.edge_map i slot)
    (fun j => (geometry.map_frame slot j).symm) (geometry.pool_map slot)

/-- The installed code realizes a successful packed rewrite,
including its exact handle and any newly initialized records.
The only effects are private to the remap. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start exhausted malformed : ℕ}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start exhausted malformed)
    (geometry : Geometry layout map frame agenda image base)
    (ready : RemapState layout map frame agenda source target mapping original query replacement before)
    (two : lookup before 14 = some 2)
    (inside : original.toNat < source.nodes.size) (cursor : original.toNat = mapping.size)
    (mapRoom : mapping.size < mapCapacity) (updated : Arena) (handle : Word)
    (rewritten : PackedSubstitution.rewrite source target mapping query replacement original = some (updated, handle))
    (fitsNodes : updated.nodes.size ≤ nodeCapacity) (fitsEdges : updated.children.size ≤ edgeCapacity) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps writes, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers writes before after ∧ Includes layout map frame writes ∧
      RemapState layout map frame agenda source updated (mapping.push handle) original query replacement after ∧
      lookup after 14 = some 2 ∧ Nonempty (At image after base (start + 538)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  let i : Fin source.nodes.size := ⟨original.toNat, inside⟩
  let slot : Fin mapCapacity := ⟨mapping.size, mapRoom⟩
  have sourceReady := NativeRemapSnapshot.ready_restrict ready.extension ready.terms
  have indexed : source.nodes[original.toNat]? = some source.nodes[i] := Array.getElem?_eq_getElem inside
  have shape := NativeRemapSnapshot.rewrite_case source target mapping query replacement original indexed rewritten
  obtain ⟨a, selected, selectFrame, pointed, ⟨atLeaf⟩⟩ := NativeSubstitutionSelect.fetched
    other extra vector point (by omega) placed.select sourceReady original inside ready.cursor ready.nodes ready.zero
  have input : NativeSubstLeaf.Inputs layout source map mapping i original query replacement a :=
    ⟨sourceReady.preserved selectFrame, ready.mapped.preserved selectFrame, pointed,
      (selectFrame.lookup 7 (by decide)).trans ready.tableBase, (selectFrame.lookup 1 (by decide)).trans ready.cursor,
      (selectFrame.lookup 8 (by decide)).trans ready.query, (selectFrame.lookup 9 (by decide)).trans ready.replacement,
      (selectFrame.lookup 12 (by decide)).trans ready.zero, (selectFrame.lookup 13 (by decide)).trans ready.one,
      (selectFrame.lookup 14 (by decide)).trans two⟩
  obtain ⟨b, leafSteps, checked, leafResult⟩ := NativeSubstLeaf.fetched other extra vector
    atLeaf (controls.transport selectFrame NativeSubstitutionSelect.clobbers_data) placed.leaf
    i original query replacement rfl cursor input mapRoom (geometry.mapCode slot) target
  have throughLeaf := X86FuelPrefix.fetches_then 3 leafSteps before a b selected checked
  by_cases isLeaf : source.nodes[i].header.tag = 0 ∨ source.nodes[i].header.tag = 1
  · rw [if_pos isLeaf] at leafResult
    obtain ⟨actual, stored, mapped, law, _, ⟨atJump⟩⟩ := leafResult
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (law.symm.trans rewritten))
    obtain ⟨c, jumped, jumpFrame, endpoint⟩ := X86PlacedScalar.jump
      (X86PlacedFrameAddress.nativeBase other) extra vector
      (show At image b base (start + 103) from atJump) placed.afterLeaf
    have frame : X86StateFrame.Frame quiet (mapBytes map slot) before c :=
      ((selectFrame.trans stored).trans (X86StateFrame.registerOnly jumpFrame)).mono (by decide) (by
        simp only [Finset.empty_union, Finset.union_empty, mapBytes, slot]
        exact Finset.Subset.refl _)
    have tag := ((selectFrame.trans stored).trans (X86StateFrame.registerOnly jumpFrame)).lookup 14 (by decide)
    exact ⟨c, _, _, X86FuelPrefix.fetches_then _ 1 before b c throughLeaf jumped,
      frame.mono (by decide) (Finset.Subset.refl _), Includes.map_only layout map _ slot,
      retain geometry ready slot frame (mapped.preserved (X86StateFrame.registerOnly jumpFrame)), tag.trans two, endpoint⟩
  · rw [if_neg isLeaf] at leafResult
    have decomposition : ∃ children newer : Array Word, source.nodes[i].header.tag = 2 ∧
        PackedTerms.segment source.children source.nodes[i] = some children ∧
        PackedSubstitution.translate mapping children = some newer := by
      cases shape with
      | leaf tag _ => exact (isLeaf tag).elim
      | unchanged children tag span mapped => exact ⟨children, children, tag, span, mapped⟩
      | changed children newer tag span mapped _ => exact ⟨children, newer, tag, span, mapped⟩
    obtain ⟨children, newer, tag, span, translated⟩ := decomposition
    obtain ⟨tested, pointed, ⟨atApplication⟩⟩ := leafResult
    simp only [if_pos tag] at atApplication
    have leafFrame : X86StateFrame.Frame quiet ∅ before b :=
      (selectFrame.trans tested).mono (by decide) (by simp)
    have compoundInput : NativeSubstLeaf.Inputs layout source map mapping i original query replacement b :=
      ⟨sourceReady.preserved leafFrame, ready.mapped.preserved leafFrame, pointed,
        (leafFrame.lookup 7 (by decide)).trans ready.tableBase, (leafFrame.lookup 1 (by decide)).trans ready.cursor,
        (leafFrame.lookup 8 (by decide)).trans ready.query, (leafFrame.lookup 9 (by decide)).trans ready.replacement,
        (leafFrame.lookup 12 (by decide)).trans ready.zero, (leafFrame.lookup 13 (by decide)).trans ready.one,
        ((selectFrame.trans tested).lookup 14 (by decide)).trans two⟩
    obtain ⟨c, cmpSteps, compared, cmpResult⟩ := NativeSubstCompound.fetched other extra vector
      atApplication (controls.transport leafFrame (by decide)) placed.application i original query replacement rfl cursor
      compoundInput ((leafFrame.lookup 5 (by decide)).trans ready.agendaBase) (ready.pool.preserved leafFrame (by simp))
      tag children newer span translated mapRoom (geometry.mapCode slot) target
    have throughCompare := X86FuelPrefix.fetches_then (3 + leafSteps) cmpSteps before b c throughLeaf compared
    by_cases same : newer = children
    · rw [if_pos same] at cmpResult
      obtain ⟨stored, mapped, restored, law, ⟨atJump⟩⟩ := cmpResult
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (law.symm.trans rewritten))
      obtain ⟨d, jumped, jumpFrame, endpoint⟩ := X86PlacedScalar.jump
        (X86PlacedFrameAddress.nativeBase other) extra vector
        (show At image c base (start + 213) from atJump) placed.afterApplication
      have frame : X86StateFrame.Frame quiet (mapBytes map slot) before d :=
        ((leafFrame.trans stored).trans (X86StateFrame.registerOnly jumpFrame)).mono (by decide) (by
          simp only [Finset.empty_union, Finset.union_empty, mapBytes, slot]
          exact Finset.Subset.refl _)
      exact ⟨d, _, _, X86FuelPrefix.fetches_then _ 1 before c d throughCompare jumped,
        frame.mono (by decide) (Finset.Subset.refl _), Includes.map_only layout map _ slot,
        retain geometry ready slot frame (mapped.preserved (X86StateFrame.registerOnly jumpFrame)),
        (jumpFrame.lookup 14 (by decide)).trans restored, endpoint⟩
    · rw [if_neg same] at cmpResult
      obtain ⟨tested, ⟨atChanged⟩⟩ := cmpResult
      have comparedFrame : X86StateFrame.Frame quiet ∅ before c :=
        (leafFrame.trans tested).mono (by decide) (by simp)
      have changedInput := with_map ready comparedFrame (ready.mapped.preserved comparedFrame)
        (fun _ _ => by simp) (fun _ => by simp) (fun _ => by simp) (by simp)
      have sized : PackedTerms.place target source.nodes[i].header newer = updated := by
        have v : source.nodes[i].header.tag ≠ 0 := fun h => isLeaf (Or.inl h)
        have k : source.nodes[i].header.tag ≠ 1 := fun h => isLeaf (Or.inr h)
        simp only [PackedSubstitution.rewrite, indexed, bind, Option.bind_some,
          if_neg v, if_neg k, if_pos tag, span, translated, if_neg same] at rewritten
        unfold PackedTerms.append at rewritten
        split at rewritten
        · exact (Prod.mk.inj (Option.some.inj rewritten)).1
        · cases rewritten
      have room : target.nodes.size < nodeCapacity ∧ target.children.size + newer.size ≤ edgeCapacity := by
        rw [← sized] at fitsNodes fitsEdges
        simp only [PackedTerms.place, Array.size_push, Array.size_append] at fitsNodes fitsEdges
        exact ⟨by omega, fitsEdges⟩
      obtain ⟨d, changeSteps, changed, changeResult⟩ := NativeSubstitutionChanged.fetched other extra vector
        atChanged (controls.transport comparedFrame (by decide)) placed.different geometry source target mapping original query replacement
        changedInput inside cursor mapRoom children newer tag span translated same
      rw [dif_pos room] at changeResult
      obtain ⟨bytes, _, wrote, edgeWrites, law, next, restored, endpoint⟩ := changeResult
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (law.symm.trans rewritten))
      have privateWrites := (Includes.edges (layout := layout) (map := map) (frame := frame) edgeWrites).union
        (Includes.appending layout map frame target room.1 (PackedTerms.newNode target source.nodes[i].header newer))
      refine ⟨d, _, NativeSubstitutionChanged.written bytes layout map frame target room.1
          (PackedTerms.newNode target source.nodes[i].header newer) slot,
        X86FuelPrefix.fetches_then _ changeSteps before c d throughCompare changed,
        (comparedFrame.trans wrote).mono (by decide) (by
          simp only [Finset.empty_union, slot, i]
          exact Finset.Subset.refl _), ?_, next, restored, endpoint⟩
      exact privateWrites.union ((Includes.map_only layout map frame slot).union (Includes.lengths layout map frame))

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionBody
