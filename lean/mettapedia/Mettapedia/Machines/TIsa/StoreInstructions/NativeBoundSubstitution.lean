import Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionLoop

/-!
# From an accepted binding to the staged substitution

The occurrence pass owns scratch only until it has answered.
The remap reuses those bytes, starting with no initialized map
entries. A successful run retains the original agenda and the
cursor of its unconsumed suffix; committing the rewritten suffix
and extending the substitution trail are separate operations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeBoundSubstitution

open Mettapedia.Logic.LP
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads)
open X86PlacedScalar (Code)
open NativeArenaGeometry (Region)
open NativeSubstitutionFrame (Table scratchDescriptor)
open NativeSubstitutionMemory (Geometry Includes)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def emit (start done exhausted malformed : ℕ) : List ℕ :=
  NativeRemapReserve.emit start exhausted ++ NativeSubstitutionLoop.emit (start + 29) done exhausted malformed

theorem emit_size (start done exhausted malformed : ℕ) : (emit start done exhausted malformed).length = 584 := by
  simp only [emit, List.length_append, NativeRemapReserve.emit_size, NativeSubstitutionLoop.emit_size]

structure Placed (image : NativeImage.View) (start done exhausted malformed : ℕ) : Prop where
  extent : start + 584 ≤ image.size
  reserve : NativeRemapReserve.Placed image start exhausted
  scan : NativeSubstitutionLoop.Placed image (start + 29) done exhausted malformed

theorem placed_of_emitted (image : NativeImage.View) (start done exhausted malformed : ℕ)
    (extent : start + 584 ≤ image.size) (finished : done ≤ image.size)
    (lack : exhausted ≤ image.size) (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit start done exhausted malformed)) : Placed image start done exhausted malformed := by
  obtain ⟨reserve, scan⟩ := NativeWords.code_append
    (show Code image start (NativeRemapReserve.emit start exhausted ++ _) from code)
  rw [NativeRemapReserve.emit_size] at scan
  exact ⟨extent, NativeRemapReserve.placed_of_emitted image _ exhausted (by omega) lack short reserve,
    NativeSubstitutionLoop.placed_of_emitted image _ done exhausted malformed (by omega) finished lack bad short scan⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register :=
  (NativeBindingSelection.clobbers ∪ NativeRemapReserve.clobbers) ∪ NativeSubstitutionLoop.clobbers

variable {nodeCapacity edgeCapacity mapCapacity agendaCapacity : ℕ}
variable {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {map : Region mapCapacity}
variable {frame : Table} {agenda : NativeAgendaRecords.Layout agendaCapacity}
variable {image : NativeImage.View} {base : BitVec 48}

theorem Geometry.occurs (space : Geometry layout map frame agenda image base) :
    NativeOccursLoop.Geometry layout agenda map image base :=
  ⟨space.mapCode, space.node_map, space.edge_map, space.pool_map⟩

theorem Geometry.descriptor (space : Geometry layout map frame agenda image base) :
    NativeBindingSelection.Separated (NativeBindingSelection.descriptorRegion (scratchDescriptor frame)) map := by
  have apart := space.mapFrame
  unfold NativeBindingSelection.Separated at apart ⊢
  change map.pointer.toNat + 8 * mapCapacity ≤ frame.pointer.toNat ∨
    frame.pointer.toNat + 8 * 7 ≤ map.pointer.toNat at apart
  change (scratchDescriptor frame).pointer.toNat + 8 * 2 ≤ map.pointer.toNat ∨
    map.pointer.toNat + 8 * mapCapacity ≤ (scratchDescriptor frame).pointer.toNat
  rw [NativeSubstitutionFrame.scratch_pointer]
  omega

private theorem mark_writes_are_private {lo hi : ℕ} {writes : Finset ℕ}
    (marked : NativeMarkTable.Within map lo hi writes) : Includes layout map frame writes := by
  intro byte touched
  obtain ⟨slot, _, _, markWord⟩ := marked byte touched
  exact Or.inr (Or.inr (Or.inl ⟨slot, markWord⟩))

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- An ordinary fetched agenda dispatch, acyclicity decision,
scratch reservation and graph traversal realize the staged
portion of a finite packed binding without consuming any other
pending equation. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {entry done shared cycle exhausted rewrittenAt : ℕ}
    {targets : NativeTermDispatch.Targets} {before : Native}
    (point : At image before base entry) (controls : Controls before) (side : NativeBindEntry.Side)
    (agendaCode : NativeAgendaDispatch.Placed image entry done targets)
    (entryCode : NativeBindEntry.EntryPlaced image side (targets.at side.exiting) shared)
    (gateCode : NativeBindingGate.Placed image shared cycle exhausted targets.malformed)
    (remapCode : Placed image (shared + 273) rewrittenAt exhausted targets.malformed)
    (geometry : Geometry layout map frame agenda image base)
    (equations : PackedEquations.Arena) (source : PackedTerms.Arena) (root left right : Word) (pending : PackedWorklist.Words)
    (context : NativeAgendaDispatch.Context agenda layout equations source root before)
    (staged : NativeSubstitutionFrame.Ready layout map frame source before)
    (pool : Reads before (agenda.metadata.cell 1).address layout.edges.pointer)
    (held : PackedEquations.readWords equations root = some ((left, right) :: pending))
    (symbols : UnifierHeaders.Symbols σ) (lTerm rTerm : Term σ)
    (leftRead : PackedTerms.lookup symbols source left = some lTerm) (rightRead : PackedTerms.lookup symbols source right = some rTerm)
    (routed : NativeTermDispatch.choose source left right = side.exiting)
    (query replacement : Word) (accepted : PackedUnifierAction.inspect source left right = some (.bindVar query replacement))
    (result : PackedSubstitution.State) (substituted : PackedSubstitution.substitute source query replacement = some result)
    (mapFit : source.nodes.size ≤ mapCapacity)
    (nodesFit : result.target.nodes.size ≤ nodeCapacity) (edgesFit : result.target.children.size ≤ edgeCapacity) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps writes cursor, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers writes before after ∧ Includes layout map frame writes ∧
      NativeSubstitutionLoop.Ready layout map frame agenda source result query replacement after ∧
      result.mapped.size = source.nodes.size ∧ NativeAgendaRecords.Ready agenda equations after ∧
      lookup after 11 = some cursor ∧ PackedEquations.readWords equations cursor = some pending ∧
      Nonempty (At image after base rewrittenAt) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have input : NativeBindEntry.Environment layout source agenda map (scratchDescriptor frame) before :=
    ⟨context.termReady, context.termBase, context.agendaBase, pool,
      (NativeSubstitutionFrame.scratch_pointer frame).symm ▸ staged.pointer,
      staged.scratch_base, staged.scratch_size, context.zero, context.one, context.two⟩
  obtain ⟨a, first, marked, cursor, ran, marksFrame, confined, cut, tail, zero, tableBase, name, value, empty, ⟨atLoop⟩⟩ :=
    NativeRemapReserve.fetched_enter_remap other extra vector point controls side agendaCode entryCode gateCode remapCode.reserve
      (Geometry.occurs geometry) geometry.agendaMap (Geometry.descriptor geometry) equations root left right pending context
      input held symbols lTerm rTerm leftRead rightRead routed query replacement accepted mapFit
  have stage := staged.kept marksFrame (by decide) (fun j => confined.apart _ (fun i => (geometry.map_frame i j).symm))
  have poolKept := pool.preserved marksFrame (confined.apart _ geometry.pool_map)
  have startMap : NativeSubstitutionLoop.Ready layout map frame agenda source ⟨source, #[]⟩ query replacement a :=
    ⟨⟨NativeRemapSnapshot.Extension.refl source, cut.termReady, stage, empty, cut.termBase,
      cut.agendaBase, poolKept, tableBase, zero, name, value, cut.zero, cut.one⟩, cut.termCount, cut.two⟩
  obtain ⟨after, second, writes, scanned, scanFrame, privateWrites, final, complete, oldAgenda, finish⟩ :=
    NativeSubstitutionLoop.fetched_substitute other extra vector atLoop (controls.transport marksFrame (by decide))
      remapCode.scan geometry source query replacement result substituted mapFit nodesFit edgesFit
      startMap equations cut.agendaReady
  exact ⟨after, first + second, marked ∪ writes, cursor,
    X86FuelPrefix.fetches_then first second before a after ran scanned, marksFrame.trans scanFrame,
    (mark_writes_are_private confined).union privateWrites, final, complete, oldAgenda,
    (scanFrame.lookup 11 (by decide)).trans cut.cursor, tail, finish⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeBoundSubstitution
