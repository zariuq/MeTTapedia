import Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionMemory

/-!
# A complete native changed-application step

Reselect from the source snapshot, reserve against staged
lengths, copy the translated edge span, fill the term record,
and restore a usable remap cursor. Exhaustion precedes all writes
by this step. The published agenda and lengths are external to it.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionChanged

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads footprint)
open X86PlacedScalar (Code)
open NativeArenaGeometry (Region)
open NativeSubstitutionFrame (Table mutableBytes)
open NativeSubstitutionMemory (Geometry nodeBytes edgeBytes mapBytes frameBytes poolBytes)
open NativeSubstLeaf (MapReady)
open NativeTermAppend (remapRegisters)
open PackedTerms (Arena)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def emit (start exhausted malformed : ℕ) : List ℕ :=
  NativeSubstitutionSelect.emit ++
    (NativeOccursApplication.prepareCode ++
      (NativeSubstitutionReserve.emit (start + 39) exhausted ++
        (NativeSubstitutionCopyEntry.emit ++
          (NativeRemapCopy.emit (start + 108) (start + 170) malformed ++
            (NativeSubstitutionAppendPrep.emit ++ (NativeTermAppend.emit remapRegisters ++ NativeSubstitutionCommit.emit))))))

theorem emit_size (start exhausted malformed : ℕ) : (emit start exhausted malformed).length = 320 := by
  simp only [emit, List.length_append, NativeSubstitutionSelect.emit_size, NativeOccursApplication.prepare_size,
    NativeSubstitutionReserve.emit_size, NativeSubstitutionCopyEntry.emit_size, NativeRemapCopy.emit_size,
    NativeSubstitutionAppendPrep.emit_size, NativeTermAppend.emit_size, NativeSubstitutionCommit.emit_size]

structure Placed (image : NativeImage.View) (start exhausted malformed : ℕ) : Prop where
  extent : start + 320 ≤ image.size
  select : Code image start NativeSubstitutionSelect.emit
  span : NativeOccursApplication.PreparePlaced image (start + 11)
  reserve : NativeSubstitutionReserve.Placed image (start + 39) exhausted
  destination : Code image (start + 91) NativeSubstitutionCopyEntry.emit
  copy : NativeRemapCopy.Placed image (start + 108) (start + 170) malformed
  prep : Code image (start + 170) NativeSubstitutionAppendPrep.emit
  append : NativeTermAppend.Placed remapRegisters image (start + 228)
  commit : NativeSubstitutionCommit.Placed image (start + 267)

theorem placed_of_emitted (image : NativeImage.View) (start exhausted malformed : ℕ)
    (extent : start + 320 ≤ image.size) (lack : exhausted ≤ image.size) (bad : malformed ≤ image.size)
    (short : image.size < 2 ^ 31) (code : Code image start (emit start exhausted malformed)) :
    Placed image start exhausted malformed := by
  obtain ⟨select, rest⟩ := NativeWords.code_append (show Code image start (NativeSubstitutionSelect.emit ++ _) from code)
  rw [NativeSubstitutionSelect.emit_size] at rest
  obtain ⟨span, rest⟩ := NativeWords.code_append rest
  rw [NativeOccursApplication.prepare_size] at rest
  obtain ⟨reserve, rest⟩ := NativeWords.code_append rest
  rw [NativeSubstitutionReserve.emit_size] at rest
  obtain ⟨destination, rest⟩ := NativeWords.code_append rest
  rw [NativeSubstitutionCopyEntry.emit_size] at rest
  obtain ⟨copy, rest⟩ := NativeWords.code_append rest
  rw [NativeRemapCopy.emit_size] at rest
  obtain ⟨prep, rest⟩ := NativeWords.code_append rest
  rw [NativeSubstitutionAppendPrep.emit_size] at rest
  obtain ⟨append, commit⟩ := NativeWords.code_append rest
  rw [NativeTermAppend.emit_size] at commit
  exact ⟨extent, select, NativeOccursApplication.prepare_placed image _ (by omega) span,
    NativeSubstitutionReserve.placed_of_emitted image _ exhausted (by omega) lack short reserve, destination,
    NativeRemapCopy.placed_of_emitted image _ _ malformed (by omega) (by omega) bad short copy, prep,
    NativeTermAppend.placed_of_emitted _ _ _ (by omega) append,
    NativeSubstitutionCommit.placed_of_emitted _ _ (by omega) commit⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rax, .rbx, .rdx, .rsi, .rdi, .r10, .r13, .r14, .rflags, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {nodeCapacity edgeCapacity mapCapacity agendaCapacity : ℕ}
variable {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {map : Region mapCapacity}
variable {frame : Table} {agenda : NativeAgendaRecords.Layout agendaCapacity}

structure State (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (map : Region mapCapacity)
    (frame : Table) (agenda : NativeAgendaRecords.Layout agendaCapacity) (source target : Arena)
    (mapping : Array Word) (original query replacement : Word) (native : Native) : Prop where
  extension : NativeRemapSnapshot.Extension source target
  terms : NativeTermArena.Ready layout target native
  staged : NativeSubstitutionFrame.Ready layout map frame target native
  mapped : MapReady map mapping native
  nodes : lookup native 3 = some layout.nodes.pointer
  agendaBase : lookup native 5 = some agenda.words.pointer
  pool : Reads native (agenda.metadata.cell 1).address layout.edges.pointer
  tableBase : lookup native 7 = some (map.atWord 0)
  cursor : lookup native 1 = some original
  query : lookup native 8 = some query
  replacement : lookup native 9 = some replacement
  zero : lookup native 12 = some 0
  one : lookup native 13 = some 1

def written (edgeWrites : Finset ℕ) (layout : NativeTermArena.Layout nodeCapacity edgeCapacity)
    (map : Region mapCapacity) (frame : Table) (target : Arena) (nodeRoom : target.nodes.size < nodeCapacity)
    (newNode : PackedTerms.Node) (slot : Fin mapCapacity) : Finset ℕ :=
  (edgeWrites ∪ NativeTermAppend.bytesOf remapRegisters layout target nodeRoom newNode) ∪
    (mapBytes map slot ∪ mutableBytes frame)

/-- Native success has the exact packed rewrite and initialized
map extension. Either capacity failure is read-only. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start exhausted malformed : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start exhausted malformed)
    (geometry : Geometry layout map frame agenda image base)
    (source target : Arena) (mapping : Array Word) (original query replacement : Word)
    (ready : State layout map frame agenda source target mapping original query replacement before)
    (inside : original.toNat < source.nodes.size) (cursor : original.toNat = mapping.size)
    (mapRoom : mapping.size < mapCapacity) (children newer : Array Word)
    (application : (source.nodes[original.toNat]'inside).header.tag = 2)
    (segment : PackedTerms.segment source.children (source.nodes[original.toNat]'inside) = some children)
    (translated : PackedSubstitution.translate mapping children = some newer) (changed : newer ≠ children) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      if room : target.nodes.size < nodeCapacity ∧ target.children.size + newer.size ≤ edgeCapacity then
        let header := (source.nodes[original.toNat]'inside).header
        let arena := PackedTerms.place target header newer
        let handle := PackedTerms.root target
        ∃ bytes, steps = 53 + 13 * newer.size ∧
          X86StateFrame.Frame clobbers
            (written bytes layout map frame target room.1 (PackedTerms.newNode target header newer) ⟨mapping.size, mapRoom⟩)
            before after ∧
          NativeMarkTable.Within layout.edges target.children.size (target.children.size + newer.size) bytes ∧
          PackedSubstitution.rewrite source target mapping query replacement original = some (arena, handle) ∧
          State layout map frame agenda source arena (mapping.push handle) original query replacement after ∧
          lookup after 14 = some 2 ∧ Nonempty (At image after base (start + 320))
      else X86StateFrame.Frame clobbers ∅ before after ∧ Nonempty (At image after base exhausted) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  let i : Fin source.nodes.size := ⟨original.toNat, inside⟩
  let node := source.nodes[i]
  have sourceReady := NativeRemapSnapshot.ready_restrict ready.extension ready.terms
  obtain ⟨a, selected, selectFrame, pointed, ⟨atSpan⟩⟩ := NativeSubstitutionSelect.fetched
    other extra vector point (by omega) placed.select sourceReady original inside ready.cursor ready.nodes ready.zero
  obtain ⟨b, loaded, spanFrame, span, width, ⟨atReserve⟩⟩ := NativeOccursApplication.fetched_span other extra vector
    atSpan (controls.transport selectFrame NativeSubstitutionSelect.clobbers_data) placed.span i (sourceReady.preserved selectFrame)
    pointed ((selectFrame.lookup 5 (by decide)).trans ready.agendaBase) (ready.pool.preserved selectFrame (by simp))
  have beforeReserve := selectFrame.trans spanFrame
  obtain ⟨c, testSteps, checked, reserveFrame, decision⟩ := NativeSubstitutionReserve.fetched other extra vector
    (show At image b base (start + 39) from atReserve) (controls.transport beforeReserve (by decide)) placed.reserve
    (ready.staged.preserved beforeReserve (by decide)) (ready.terms.preserved beforeReserve) node.childrenCount width
  have originalWidth := (PackedTerms.segment_width source.children node children segment).1
  have translatedWidth := (PackedRemapCoordinates.coordinates mapping children newer translated).1
  have sameWidth : node.childrenCount.toNat = newer.size := originalWidth.symm.trans translatedWidth.symm
  rw [sameWidth] at decision
  have firstEight := X86FuelPrefix.fetches_then 3 5 before a b selected loaded
  have throughReserve := X86FuelPrefix.fetches_then 8 testSteps before b c firstEight checked
  have reserved := beforeReserve.trans reserveFrame
  by_cases room : target.nodes.size < nodeCapacity ∧ target.children.size + newer.size ≤ edgeCapacity
  · rw [if_pos room.1, if_pos room.2] at decision
    obtain ⟨rfl, ordinal, ⟨atDestination⟩⟩ := decision
    obtain ⟨d, gathered, destinationFrame, pointer, ⟨atCopy⟩⟩ := NativeSubstitutionCopyEntry.fetched other extra vector
      (show At image c base (start + 91) from atDestination) (controls.transport reserved (by decide))
      (by omega) placed.destination agenda layout.edges target.children.size (by omega)
      ((reserved.lookup 5 (by decide)).trans ready.agendaBase) (ready.pool.preserved reserved (by simp)) ordinal
    have gatheredState := reserved.trans destinationFrame
    have tail := (reserveFrame.trans destinationFrame)
    have parent : original = BitVec.ofNat 64 mapping.size := by
      rw [← cursor, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have countWord : node.childrenCount = BitVec.ofNat 64 newer.size := by
      rw [← sameWidth, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have inputCopy : NativeRemapCopy.Input layout source map mapping node target.children.size newer.size d :=
      ⟨⟨sourceReady.preserved gatheredState, ready.mapped.preserved gatheredState,
        (tail.lookup 6 (by decide)).trans span, (gatheredState.lookup 7 (by decide)).trans ready.tableBase,
        parent ▸ (gatheredState.lookup 1 (by decide)).trans ready.cursor,
        countWord ▸ (tail.lookup 2 (by decide)).trans width, (gatheredState.lookup 12 (by decide)).trans ready.zero,
        (gatheredState.lookup 13 (by decide)).trans ready.one⟩, pointer⟩
    obtain ⟨e, bytes, copied, copyFrame, fresh, storedEdges, ⟨atPrep⟩⟩ := NativeRemapCopy.fetched other extra vector
      placed.copy geometry.copy children newer segment translated target.children.size newer.size
      (by omega) (Nat.le_refl _) ready.extension.edge_size room.2 (show At image d base (start + 108) from atCopy)
      (controls.transport gatheredState (by decide)) inputCopy
    have throughCopy : X86StateFrame.Frame clobbers bytes before e :=
      (gatheredState.trans copyFrame).mono (by decide) (by simp)
    have stagedInput := ready.staged.kept throughCopy (by decide)
      (fun j => fresh.apart _ (fun slot => (geometry.edge_frame slot j).symm))
    have graph := NativeSubstitutionCopyEntry.target_kept ready.terms throughCopy fresh (Nat.le_refl _) geometry.node_edge
    obtain ⟨f, prepared, prepFrame, fields, ⟨atAppend⟩⟩ := NativeSubstitutionAppendPrep.fetched other extra vector
      atPrep (controls.transport throughCopy (by decide)) (by omega) placed.prep ready.extension stagedInput graph
      original inside ((throughCopy.lookup 1 (by decide)).trans ready.cursor)
      ((throughCopy.lookup 12 (by decide)).trans ready.zero) newer application countWord
    have savedEdges : NativeRemapCopy.Stored layout target.children.size newer.size newer room.2 (Nat.le_refl _) f :=
      fun j => (storedEdges j).preserved prepFrame (by simp)
    let newNode := PackedTerms.newNode target node.header newer
    have readNode : source.nodes[original.toNat]? = some node := Array.getElem?_eq_getElem inside
    obtain ⟨g, appended, appendFrame, bigger, rewritten, newHandle, ⟨atCommit⟩⟩ :=
      NativeTermAppend.fetched_rewrite other extra vector (show At image f base (start + 228) from atAppend)
        ((controls.transport throughCopy (by decide)).transport prepFrame NativeSubstitutionAppendPrep.clobbers_data)
        remapRegisters placed.append
        source original query replacement mapping node readNode application children newer segment translated changed
        room.1 room.2 fields savedEdges (NativeSubstitutionMemory.append_code geometry target room.1 newNode)
        (fun i j => (geometry.node_edge _ j i).symm)
    have afterCopy := prepFrame.trans appendFrame
    have throughAppend := throughCopy.trans afterCopy
    have descriptor : NativeSubstitutionFrame.Ready layout map frame target g :=
      stagedInput.kept afterCopy (by decide) (fun j => by
        simp only [Finset.empty_union]
        exact NativeSubstitutionMemory.append_apart layout target room.1 newNode _
          (fun c => (geometry.node_frame _ c j).symm))
    have mapKept : MapReady map mapping g :=
      (ready.mapped.kept throughCopy (fun j =>
        fresh.apart _ (fun e => (geometry.edge_map e j).symm))).kept afterCopy (fun j => by
          simp only [Finset.empty_union]
          exact NativeSubstitutionMemory.append_apart layout target room.1 newNode _ (fun c => (geometry.node_map _ c j).symm))
    have commitInput : NativeSubstitutionCommit.Input layout map frame target mapping original newer.size g :=
      ⟨descriptor, mapKept, (throughAppend.lookup 1 (by decide)).trans ready.cursor, newHandle,
        (appendFrame.lookup 13 (by decide)).trans (fields.fields 2),
        (appendFrame.lookup 6 (by decide)).trans (fields.fields 3)⟩
    obtain ⟨after, committed, commitFrame, staged, mapped, mapBase, one, endpoint⟩ :=
      NativeSubstitutionCommit.fetched other extra vector atCommit (controls.transport throughAppend (by decide)) placed.commit
        geometry.commit original cursor mapRoom node.header newer commitInput
    let arena := PackedTerms.place target node.header newer
    let slot : Fin mapCapacity := ⟨mapping.size, mapRoom⟩
    let book := poolBytes agenda
    have poolProtection : Disjoint book (written bytes layout map frame target room.1 newNode slot) := by
      apply Finset.disjoint_union_right.mpr
      refine ⟨Finset.disjoint_union_right.mpr ⟨fresh.apart _ (fun i => geometry.pool_edge i),
        NativeSubstitutionMemory.append_apart layout target room.1 newNode _ (geometry.pool_node ⟨target.nodes.size, room.1⟩)⟩, ?_⟩
      exact Finset.disjoint_union_right.mpr ⟨geometry.pool_map slot,
        Finset.disjoint_union_right.mpr
          ⟨geometry.pool_frame NativeSubstitutionFrame.nodeCount, geometry.pool_frame NativeSubstitutionFrame.edgeCount⟩⟩
    have all : X86StateFrame.Frame clobbers (written bytes layout map frame target room.1 newNode slot) before after :=
      (throughAppend.trans commitFrame).mono (by decide) (by
        simpa only [Finset.empty_union, written, NativeSubstitutionCommit.slotBytes, mapBytes] using
          (Finset.Subset.refl (written bytes layout map frame target room.1 newNode slot)))
    have termReady : NativeTermArena.Ready layout arena after :=
      bigger.kept commitFrame
        (fun i j => Finset.disjoint_union_right.mpr ⟨geometry.node_map i j slot,
          Finset.disjoint_union_right.mpr ⟨geometry.node_frame i j _, geometry.node_frame i j _⟩⟩)
        (fun e => Finset.disjoint_union_right.mpr ⟨geometry.edge_map e slot,
          Finset.disjoint_union_right.mpr ⟨geometry.edge_frame e _, geometry.edge_frame e _⟩⟩)
    have next : State layout map frame agenda source arena (mapping.push (PackedTerms.root target))
        original query replacement after :=
      ⟨ready.extension.trans (NativeRemapSnapshot.place_extends _ _ _), termReady, staged, mapped,
        ((appendFrame.trans commitFrame).lookup 3 (by decide)).trans fields.pointer,
        (all.lookup 5 (by decide)).trans ready.agendaBase, ready.pool.preserved all poolProtection, mapBase,
        (all.lookup 1 (by decide)).trans ready.cursor, (all.lookup 8 (by decide)).trans ready.query,
        (all.lookup 9 (by decide)).trans ready.replacement, (all.lookup 12 (by decide)).trans ready.zero, one⟩
    have first := X86FuelPrefix.fetches_then 18 4 before c d throughReserve gathered
    have second := X86FuelPrefix.fetches_then 22 _ before d e first copied
    have third := X86FuelPrefix.fetches_then _ 11 before e f second prepared
    have fourth := X86FuelPrefix.fetches_then _ 7 before f g third appended
    refine ⟨after, _, X86FuelPrefix.fetches_then _ 11 before g after fourth committed, ?_⟩
    rw [dif_pos room]
    exact ⟨bytes, by omega, all, fresh, rewritten, next,
      ((appendFrame.trans commitFrame).lookup 14 (by decide)).trans (by rw [← application]; exact fields.fields 0),
      endpoint⟩
  · have refused : Nonempty (At image c base exhausted) := by
      by_cases n : target.nodes.size < nodeCapacity
      · have e : ¬ target.children.size + newer.size ≤ edgeCapacity := fun e => room ⟨n, e⟩
        rw [if_pos n, if_neg e] at decision
        exact decision.2
      · rw [if_neg n] at decision
        exact decision.2
    refine ⟨c, _, throughReserve, ?_⟩
    rw [dif_neg room]
    exact ⟨reserved.mono (by decide) (by simp), refused⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionChanged
