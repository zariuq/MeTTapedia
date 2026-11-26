import Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingMemory

/-!
# A fetched finite-tree binding step

The ordinary agenda dispatch selects a binding. The term
graph, trail entry, and new agenda are staged in that order.
After the last stage the native block re-enters dispatch with
exactly the working state of the packed finite unifier.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingStep

open Mettapedia.Logic.LP
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads footprint)
open X86PlacedScalar (Code)
open NativeArenaGeometry (Region)
open NativeTrailReserve (Descriptor)
open NativeAgendaRecords (Ready Records)
open NativeAgendaLoop (Within)
open NativeBindingMemory (Geometry)
open NativeSubstitutionMemory (Includes)
open PackedEquations (Arena readWords)
open PackedWorklist (Words)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

namespace Tail

def emit (start next exhausted malformed : ℕ) : List ℕ :=
  NativeBindingTrail.emit start exhausted ++
    (NativePendingReserve.emitPreparation (start + 108) exhausted malformed ++
      (NativePendingFill.emit (start + 211) (start + 390) malformed ++ NativeBindingPublish.emit (start + 390) next))

theorem emit_size (start next exhausted malformed : ℕ) : (emit start next exhausted malformed).length = 467 := by
  simp only [emit, List.length_append, NativeBindingTrail.emit_size,
    NativePendingReserve.emitPreparation_size, NativePendingFill.emit_size, NativeBindingPublish.emit_size]

structure Placed (image : NativeImage.View) (start next exhausted malformed : ℕ) : Prop where
  extent : start + 467 ≤ image.size
  trail : NativeBindingTrail.Placed image start exhausted
  plan : NativePendingReserve.Preparation image (start + 108) exhausted malformed
  fill : NativePendingFill.Placed image (start + 211) (start + 390) malformed
  publish : NativeBindingPublish.Placed image (start + 390) next

theorem placed_of_emitted (image : NativeImage.View) (start next exhausted malformed : ℕ)
    (extent : start + 467 ≤ image.size) (continues : next ≤ image.size)
    (lack : exhausted ≤ image.size) (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit start next exhausted malformed)) : Placed image start next exhausted malformed := by
  obtain ⟨trail, rest⟩ := NativeWords.code_append (show Code image start
    (NativeBindingTrail.emit start exhausted ++ _) from code)
  rw [NativeBindingTrail.emit_size] at rest
  obtain ⟨plan, rest⟩ := NativeWords.code_append rest
  rw [NativePendingReserve.emitPreparation_size] at rest
  obtain ⟨fill, commit⟩ := NativeWords.code_append rest
  rw [NativePendingFill.emit_size] at commit
  exact ⟨extent, NativeBindingTrail.placed_of_emitted image _ exhausted (by omega) lack short trail,
    NativePendingReserve.preparation_placed image _ exhausted malformed (by omega) lack bad short plan,
    NativePendingFill.placed_of_emitted image _ _ malformed (by omega) (by omega) bad short fill,
    NativeBindingPublish.placed_of_emitted image _ next (by omega) continues short commit⟩

abbrev clobbers : Finset Register :=
  NativeBindingTrail.clobbers ∪ (NativePendingCount.clobbers ∪ NativePendingReserve.clobbers) ∪
    NativePendingFill.clobbers ∪ NativeBindingPublish.clobbers

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

end Tail

def emit (start next exhausted malformed : ℕ) : List ℕ :=
  NativeBoundSubstitution.emit start (start + 584) exhausted malformed ++
    Tail.emit (start + 584) next exhausted malformed

theorem emit_size (start next exhausted malformed : ℕ) : (emit start next exhausted malformed).length = 1051 := by
  simp only [emit, List.length_append, NativeBoundSubstitution.emit_size, Tail.emit_size]

structure Placed (image : NativeImage.View) (start next exhausted malformed : ℕ) : Prop where
  extent : start + 1051 ≤ image.size
  graph : NativeBoundSubstitution.Placed image start (start + 584) exhausted malformed
  tail : Tail.Placed image (start + 584) next exhausted malformed

theorem placed_of_emitted (image : NativeImage.View) (start next exhausted malformed : ℕ)
    (extent : start + 1051 ≤ image.size) (continues : next ≤ image.size)
    (lack : exhausted ≤ image.size) (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit start next exhausted malformed)) : Placed image start next exhausted malformed := by
  obtain ⟨graph, rest⟩ := NativeWords.code_append (show Code image start
    (NativeBoundSubstitution.emit start (start + 584) exhausted malformed ++ _) from code)
  rw [NativeBoundSubstitution.emit_size] at rest
  exact ⟨extent, NativeBoundSubstitution.placed_of_emitted image _ _ exhausted malformed (by omega) (by omega) lack bad short graph,
    Tail.placed_of_emitted image _ _ _ _ (by omega) continues lack bad short rest⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := NativeBoundSubstitution.clobbers ∪ Tail.clobbers

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {nc ec mc ac tc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {frame : Descriptor}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}
variable {image : NativeImage.View} {base : BitVec 48}

structure Aux (term : NativeTermArena.Layout nc ec) (frame : Descriptor)
    (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc) (native : Native) : Prop where
  pool : Reads native (agenda.metadata.cell 1).address term.edges.pointer
  agendaLimit : Reads native (agenda.metadata.cell 2).address (BitVec.ofNat 64 ac)
  trailLimit : Reads native (trail.metadata.cell 2).address (BitVec.ofNat 64 tc)
  trailPtr : Reads native (frame.cell 7).address trail.words.pointer

structure Live (term : NativeTermArena.Layout nc ec) (map : Region mc) (frame : Descriptor)
    (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc)
    (terms : PackedTerms.Arena) (equations : Arena) (root : Word) (bindings : Arena) (native : Native) : Prop where
  dispatch : NativeAgendaDispatch.Context agenda term equations terms root native
  staged : NativeSubstitutionFrame.Ready term map frame.substitution terms native
  trailReady : Ready trail bindings native
  aux : Aux term frame agenda trail native

variable {before after : Native} {regs : Finset Register} {bytes : Finset ℕ} {lo hi : ℕ}

theorem Aux.preserved (aux : Aux term frame agenda trail before)
    (run : X86StateFrame.Frame regs ∅ before after) : Aux term frame agenda trail after :=
  ⟨aux.pool.preserved run (by simp), aux.agendaLimit.preserved run (by simp),
    aux.trailLimit.preserved run (by simp), aux.trailPtr.preserved run (by simp)⟩

private theorem Aux.graph (aux : Aux term frame agenda trail before)
    (space : Geometry term map frame agenda trail image base) (run : X86StateFrame.Frame regs bytes before after)
    (effects : Includes term map frame.substitution bytes) : Aux term frame agenda trail after :=
  ⟨aux.pool.preserved run (space.substitute.agenda_slice_apart 0 3 (by decide) (by omega) (by decide) 1 effects),
    aux.agendaLimit.preserved run (space.substitute.agenda_slice_apart 0 3 (by decide) (by omega) (by decide) 2 effects),
    aux.trailLimit.preserved run (space.forTrail.agenda_slice_apart 0 3 (by decide) (by omega) (by decide) 2 effects),
    aux.trailPtr.preserved run (space.trailPointer_apart effects)⟩

private theorem Aux.throughTrail (aux : Aux term frame agenda trail before)
    (space : Geometry term map frame agenda trail image base) (run : X86StateFrame.Frame regs bytes before after)
    (effects : Within trail lo hi bytes) : Aux term frame agenda trail after :=
  ⟨aux.pool.preserved run (NativeBindingMemory.meta_apart space.trailAgenda.symm 1 effects),
    aux.agendaLimit.preserved run (NativeBindingMemory.meta_apart space.trailAgenda.symm 2 effects),
    aux.trailLimit.preserved run (NativeBindingMemory.meta_kept 2 effects),
    aux.trailPtr.preserved run (NativePendingFill.Within.separate effects _
      (fun i j _ _ => NativeBindingMemory.frame_record space.trailFrame 7 i j))⟩

theorem Aux.throughAgenda (aux : Aux term frame agenda trail before)
    (space : Geometry term map frame agenda trail image base) (run : X86StateFrame.Frame regs bytes before after)
    (effects : Within agenda lo hi bytes) : Aux term frame agenda trail after :=
  ⟨aux.pool.preserved run (NativeBindingMemory.meta_kept 1 effects),
    aux.agendaLimit.preserved run (NativeBindingMemory.meta_kept 2 effects),
    aux.trailLimit.preserved run (NativeBindingMemory.meta_apart space.trailAgenda 2 effects),
    aux.trailPtr.preserved run (NativePendingFill.Within.separate effects _
      (fun i j _ _ => NativeBindingMemory.frame_record space.agendaFrame 7 i j))⟩

theorem Aux.publishAgenda (aux : Aux term frame agenda trail before)
    (space : Geometry term map frame agenda trail image base)
    (run : X86StateFrame.Frame regs (NativeBindingPublish.header agenda) before after) :
    Aux term frame agenda trail after :=
  ⟨aux.pool.preserved run (NativeBindingMemory.meta_immutable agenda 1 (by decide)),
    aux.agendaLimit.preserved run (NativeBindingMemory.meta_immutable agenda 2 (by decide)),
    aux.trailLimit.preserved run (NativeBindingMemory.meta_header_apart space.trailAgenda 2),
    aux.trailPtr.preserved run (NativeBindingMemory.frame_header space.agendaFrame 7)⟩

private theorem Aux.commit (aux : Aux term frame agenda trail before)
    (space : Geometry term map frame agenda trail image base)
    (run : X86StateFrame.Frame regs (NativeBindingPublish.written agenda trail) before after) : Aux term frame agenda trail after :=
  ⟨aux.pool.preserved run (Finset.disjoint_union_right.mpr ⟨NativeBindingMemory.meta_header_apart space.trailAgenda.symm 1,
      NativeBindingMemory.meta_immutable agenda 1 (by decide)⟩),
    aux.agendaLimit.preserved run (Finset.disjoint_union_right.mpr ⟨NativeBindingMemory.meta_header_apart space.trailAgenda.symm 2,
      NativeBindingMemory.meta_immutable agenda 2 (by decide)⟩),
    aux.trailLimit.preserved run (Finset.disjoint_union_right.mpr ⟨NativeBindingMemory.meta_immutable trail 2 (by decide),
      NativeBindingMemory.meta_header_apart space.trailAgenda 2⟩),
    aux.trailPtr.preserved run (space.publishGeometry.frame 7)⟩

private theorem published_head (prior updated : Arena) (pending : Words) (head : Word)
    (built : PackedEquations.prependWords prior 0 pending = some (updated, head)) :
    head = NativeBindingPublish.newRoot prior updated := by
  have places := PackedAgendaCoordinates.coordinates prior 0 pending built
  rw [places.root, NativeBindingPublish.newRoot, places.size]
  cases pending <;> simp [PackedAgendaCoordinates.headAfter]

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- The graph-to-trail boundary doesn't need the graph
cursor or the register containing two. Those registers are
free for a pass over held roots. -/
structure Staged (term : NativeTermArena.Layout nc ec) (map : Region mc) (frame : Descriptor)
    (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc)
    (source : PackedTerms.Arena) (equations oldTrail : Arena) (result : PackedSubstitution.State)
    (cursor name replacement : Word) (native : Native) : Prop where
  extension : NativeRemapSnapshot.Extension source result.target
  terms : NativeTermArena.Ready term result.target native
  table : NativeSubstitutionFrame.Ready term map frame.substitution result.target native
  mapping : NativeSubstLeaf.MapReady map result.mapped native
  agendaReady : Ready agenda equations native
  trailReady : Ready trail oldTrail native
  aux : Aux term frame agenda trail native
  agendaBase : lookup native 5 = some agenda.words.pointer
  mapBase : lookup native 7 = some (map.atWord 0)
  query : lookup native 8 = some name
  value : lookup native 9 = some replacement
  suffix : lookup native 11 = some cursor
  zero : lookup native 12 = some 0
  one : lookup native 13 = some 1
  mapLimit : lookup native 15 = some (BitVec.ofNat 64 result.mapped.size)

theorem fetched_graph (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {entry done shared cycle exhausted stagedAt : ℕ} {targets : NativeTermDispatch.Targets}
    (point : At image before base entry) (controls : Controls before) (side : NativeBindEntry.Side)
    (agendaCode : NativeAgendaDispatch.Placed image entry done targets)
    (entryCode : NativeBindEntry.EntryPlaced image side (targets.at side.exiting) shared)
    (gateCode : NativeBindingGate.Placed image shared cycle exhausted targets.malformed)
    (code : NativeBoundSubstitution.Placed image (shared + 273) stagedAt exhausted targets.malformed)
    (space : Geometry term map frame agenda trail image base)
    (source : PackedTerms.Arena) (equations oldTrail : Arena) (root left right : Word) (pending : Words)
    (live : Live term map frame agenda trail source equations root oldTrail before)
    (held : readWords equations root = some ((left, right) :: pending))
    (symbols : UnifierHeaders.Symbols σ) (lTerm rTerm : Term σ)
    (leftRead : PackedTerms.lookup symbols source left = some lTerm) (rightRead : PackedTerms.lookup symbols source right = some rTerm)
    (routed : NativeTermDispatch.choose source left right = side.exiting)
    (name replacement : Word) (accepted : PackedUnifierAction.inspect source left right = some (.bindVar name replacement))
    (result : PackedSubstitution.State) (substituted : PackedSubstitution.substitute source name replacement = some result)
    (mapFit : source.nodes.size ≤ mc) (nodesFit : result.target.nodes.size ≤ nc) (edgesFit : result.target.children.size ≤ ec) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps bytes cursor, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame NativeBoundSubstitution.clobbers bytes before after ∧ Includes term map frame.substitution bytes ∧
      Staged term map frame agenda trail source equations oldTrail result cursor name replacement after ∧
      readWords equations cursor = some pending ∧ Nonempty (At image after base stagedAt) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, steps, bytes, cursor, ran, graphFrame, privateGraph, graph, complete, oldAgenda, oldCursor, tail, endpoint⟩ :=
    NativeBoundSubstitution.fetched other extra vector point controls side agendaCode entryCode gateCode code space.substitute
      equations source root left right pending live.dispatch live.staged live.aux.pool held symbols lTerm rTerm leftRead rightRead
      routed name replacement accepted result substituted mapFit nodesFit edgesFit
  have aux := live.aux.graph space graphFrame privateGraph
  have priorTrail := space.forTrail.agenda_kept live.trailReady graphFrame privateGraph
  exact ⟨after, steps, bytes, cursor, ran, graphFrame, privateGraph,
    ⟨graph.stage.extension, graph.stage.terms, graph.stage.staged, graph.stage.mapped, oldAgenda, priorTrail, aux,
      graph.stage.agendaBase, graph.stage.tableBase, graph.stage.query, graph.stage.replacement, oldCursor, graph.stage.zero,
      graph.stage.one, by rw [complete]; exact graph.endCount⟩, tail, endpoint⟩

/-- Continue from a completed map without repeating the term
traversal or changing the order of the pending equations. -/
theorem fetched_tail (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start entry exhausted malformed : ℕ}
    (point : At image before base start) (controls : Controls before) (code : Tail.Placed image start entry exhausted malformed)
    (space : Geometry term map frame agenda trail image base) (source : PackedTerms.Arena)
    (equations oldTrail : Arena) (cursor name replacement : Word) (pending history : Words)
    (result : PackedSubstitution.State) (graph : Staged term map frame agenda trail source equations oldTrail result cursor name replacement before)
    (tail : readWords equations cursor = some pending)
    (traced : readWords oldTrail (NativeBindingTrail.root oldTrail) = some history)
    (remapped : Words) (mapped : PackedSubstitution.remapPending result.mapped pending = some remapped)
    (agendaFit : equations.size + pending.length ≤ ac) (trailFit : oldTrail.size < tc) :
    let newTrail := oldTrail.push (NativeBindingTrail.binding oldTrail name replacement)
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps updated nextRoot trailWrites agendaWrites,
      (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame Tail.clobbers
        (trailWrites ∪ agendaWrites ∪ NativeBindingPublish.written agenda trail) before after ∧
      Within trail oldTrail.size (oldTrail.size + 1) trailWrites ∧
      Within agenda equations.size (equations.size + pending.length) agendaWrites ∧
      Live term map frame agenda trail result.target updated nextRoot newTrail after ∧
      updated.size = equations.size + pending.length ∧
      readWords updated nextRoot = some remapped ∧
      readWords newTrail (NativeBindingTrail.root newTrail) = some ((name, replacement) :: history) ∧
      Nonempty (At image after base entry) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let newTrail := oldTrail.push (NativeBindingTrail.binding oldTrail name replacement)
  have sameLength := PackedAgendaCoordinates.remap_length result.mapped pending remapped mapped
  have bound := agenda.words.positive_room (show 0 < 3 * (ac + 1) by omega)
  obtain ⟨updated, head, built, updatedSize, _, headRead, _⟩ :=
    PackedEquations.prepend_words_exact equations 0 remapped [] rfl (by simp)
      (by rw [sameLength]; omega)
  have finalHead := published_head equations updated remapped head built
  have exactCount : updated.size = equations.size + pending.length := updatedSize.trans (congrArg (equations.size + ·) sameLength)
  have stack : lookup before 4 = some frame.pointer := frame.substitution_pointer ▸ graph.table.pointer
  have mapWord : Reads before (frame.cell 0).address (map.atWord 0) := by
    have slot := graph.table.word 0
    rw [frame.substitution_cell] at slot
    exact slot
  have writeTrail : NativeBindingTrail.Input trail frame oldTrail agenda.words.pointer cursor (map.atWord 0) name replacement before :=
    ⟨graph.trailReady, graph.aux.trailPtr, graph.aux.trailLimit, stack, mapWord, graph.agendaBase, graph.suffix, graph.query,
      graph.value, graph.one⟩
  obtain ⟨b, second, trailBytes, trailRun, trailFrame, trailResult⟩ :=
    NativeBindingTrail.fetched other extra vector point controls code.trail space.trailGeometry
      agenda.words.pointer cursor (map.atWord 0) name replacement writeTrail history traced
  rw [if_pos trailFit] at trailResult
  obtain ⟨_, privateTrail, trailBefore, readyTrail, trailRead, agendaPtr, agendaCursor, mapPtr, ⟨atPlan⟩⟩ := trailResult
  have controlsB := controls.transport trailFrame (by decide)
  have auxB := graph.aux.throughTrail space trailFrame privateTrail
  have readyAgenda := NativeBindingMemory.keep_ready space.trailAgenda.symm privateTrail trailFrame graph.agendaReady
  have zero := (trailFrame.lookup 12 (by decide)).trans graph.zero
  have one := (trailFrame.lookup 13 (by decide)).trans graph.one
  obtain ⟨c, third, planRun, planFrame, agendaBefore, sourceCursor, planned⟩ :=
    NativePendingReserve.fetched_prepare other extra vector atPlan controlsB code.plan cursor pending tail readyAgenda agendaCursor
      agendaPtr zero one auxB.agendaLimit
  rw [if_pos agendaFit] at planned
  obtain ⟨_, floor, ordinal, keptExtent, ⟨atFill⟩⟩ := planned
  have afterPlan := trailFrame.trans planFrame
  have throughPlan := afterPlan
  have auxC := auxB.preserved planFrame
  have nativeMap := (graph.mapping.kept trailFrame (fun i =>
    NativePendingFill.Within.separate privateTrail _ (fun index col _ _ =>
      (show NativePendingFill.Geometry trail map image base from ⟨space.trailCode, space.trailMap⟩).map_apart i index col))).preserved planFrame
  let endWord := BitVec.ofNat 64 (equations.size + pending.length)
  have fillIn : NativePendingFill.Input agenda map equations result.mapped cursor endWord pending.length c :=
    ⟨agendaBefore, nativeMap, (planFrame.lookup 5 (by decide)).trans agendaPtr, (planFrame.lookup 7 (by decide)).trans mapPtr,
      (afterPlan.lookup 15 (by decide)).trans graph.mapLimit,
      floor, sourceCursor, ordinal, keptExtent, (planFrame.lookup 12 (by decide)).trans zero, (planFrame.lookup 13 (by decide)).trans one⟩
  obtain ⟨d, agendaBytes, filled, fillFrame, privateAgenda, empty, stagedAgenda, ⟨atCommit⟩⟩ :=
    NativePendingFill.fetched_all other extra vector code.fill space.fillGeometry endWord pending remapped mapped agendaFit
      cursor tail atFill (controls.transport throughPlan (by decide)) fillIn
  have throughFill := throughPlan.trans fillFrame
  have auxD := auxC.throughAgenda space fillFrame privateAgenda
  have bigTerms := NativeBindingMemory.keep_terms space.substitute.agendaNode space.substitute.agendaEdge privateAgenda fillFrame
    ((NativeBindingMemory.keep_terms space.trailNode space.trailEdge privateTrail trailFrame graph.terms).preserved planFrame)
  have keptStack := NativeBindingMemory.keep_staged space.agendaFrame privateAgenda fillFrame (by decide)
    ((NativeBindingMemory.keep_staged space.trailFrame privateTrail trailFrame (by decide) graph.table).preserved planFrame (by decide))
  have oldTrace := NativeBindingMemory.keep_ready space.trailAgenda privateAgenda fillFrame (trailBefore.preserved planFrame)
  have pendingTrace : Records trail newTrail d :=
    NativeBindingMemory.keep_records space.trailAgenda privateAgenda fillFrame
      ⟨readyTrail.fits, fun i j => (readyTrail.node i j).preserved planFrame (by simp)⟩
  have publishIn : NativeBindingPublish.Input term map agenda trail frame result.target equations updated oldTrail newTrail d :=
    ⟨keptStack, bigTerms, empty.current, stagedAgenda.records empty.current built, oldTrace, pendingTrace,
      auxD.trailPtr, empty.agendaBase, empty.floor, by rw [exactCount]; exact empty.reserved, empty.cursor, empty.one, empty.zero⟩
  obtain ⟨after, last, published, _, committed, nextState, nextTrail, nextFrame, endpoint⟩ :=
    NativeBindingPublish.fetched other extra vector atCommit (controls.transport throughFill (by decide)) code.publish
      space.publishGeometry result.target equations updated oldTrail newTrail (Array.size_push _) publishIn
  have joined : X86StateFrame.Frame Tail.clobbers
      (trailBytes ∪ agendaBytes ∪ NativeBindingPublish.written agenda trail) before after :=
    (throughFill.trans committed).mono (by decide) (by
      simp only [Finset.union_empty]
      exact Finset.Subset.refl _)
  have continued := X86FuelPrefix.fetches_then _ last before d after
    (X86FuelPrefix.fetches_then (second + third) _ before c d
      (X86FuelPrefix.fetches_then second third before b c trailRun planRun) filled) published
  have next : Live term map frame agenda trail result.target updated head newTrail after :=
    ⟨finalHead.symm ▸ nextState, nextFrame, nextTrail, auxD.commit space committed⟩
  exact ⟨after, _, updated, head, trailBytes, agendaBytes, continued, joined, privateTrail, privateAgenda, next, exactCount,
    by simpa only [List.append_nil] using headRead, trailRead, endpoint⟩

/-- A complete binding has one graph traversal and one
continuation that stages and publishes the pending equations. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {entry done shared cycle exhausted : ℕ} {targets : NativeTermDispatch.Targets}
    (point : At image before base entry) (controls : Controls before) (side : NativeBindEntry.Side)
    (agendaCode : NativeAgendaDispatch.Placed image entry done targets)
    (entryCode : NativeBindEntry.EntryPlaced image side (targets.at side.exiting) shared)
    (gateCode : NativeBindingGate.Placed image shared cycle exhausted targets.malformed)
    (code : Placed image (shared + 273) entry exhausted targets.malformed)
    (space : Geometry term map frame agenda trail image base)
    (source : PackedTerms.Arena) (equations oldTrail : Arena) (root left right : Word) (pending history : Words)
    (live : Live term map frame agenda trail source equations root oldTrail before)
    (held : readWords equations root = some ((left, right) :: pending))
    (traced : readWords oldTrail (NativeBindingTrail.root oldTrail) = some history)
    (symbols : UnifierHeaders.Symbols σ) (lTerm rTerm : Term σ)
    (leftRead : PackedTerms.lookup symbols source left = some lTerm) (rightRead : PackedTerms.lookup symbols source right = some rTerm)
    (routed : NativeTermDispatch.choose source left right = side.exiting)
    (name replacement : Word) (accepted : PackedUnifierAction.inspect source left right = some (.bindVar name replacement))
    (result : PackedSubstitution.State) (substituted : PackedSubstitution.substitute source name replacement = some result)
    (remapped : Words) (mapped : PackedSubstitution.remapPending result.mapped pending = some remapped)
    (mapFit : source.nodes.size ≤ mc) (nodesFit : result.target.nodes.size ≤ nc) (edgesFit : result.target.children.size ≤ ec)
    (agendaFit : equations.size + pending.length ≤ ac) (trailFit : oldTrail.size < tc) :
    let newTrail := oldTrail.push (NativeBindingTrail.binding oldTrail name replacement)
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps updated nextRoot graphWrites trailWrites agendaWrites,
      (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers
        (graphWrites ∪ trailWrites ∪ agendaWrites ∪ NativeBindingPublish.written agenda trail) before after ∧
      Includes term map frame.substitution graphWrites ∧ Within trail oldTrail.size (oldTrail.size + 1) trailWrites ∧
      Within agenda equations.size (equations.size + pending.length) agendaWrites ∧
      Live term map frame agenda trail result.target updated nextRoot newTrail after ∧
      updated.size = equations.size + pending.length ∧
      readWords updated nextRoot = some remapped ∧
      readWords newTrail (NativeBindingTrail.root newTrail) = some ((name, replacement) :: history) ∧
      PackedWorklist.advance ⟨source, (left, right) :: pending, history⟩ =
        some (.working ⟨result.target, remapped, (name, replacement) :: history⟩) ∧
      NativeRemapSnapshot.Extension source result.target ∧
      Nonempty (At image after base entry) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨a, first, graphBytes, cursor, remap, graphFrame, privateGraph, graph, suffix, ⟨atTail⟩⟩ :=
    fetched_graph other extra vector point controls side agendaCode entryCode gateCode code.graph space source equations oldTrail
      root left right pending live held symbols lTerm rTerm leftRead rightRead routed name replacement accepted result substituted
      mapFit nodesFit edgesFit
  obtain ⟨after, second, updated, nextRoot, trailBytes, agendaBytes, ran, staged, trailPrivate, agendaPrivate, next,
    count, equationsRead, trace, endpoint⟩ := fetched_tail other extra vector atTail
      (controls.transport graphFrame (by decide)) code.tail space source equations oldTrail cursor name replacement pending history
      result graph suffix traced remapped mapped agendaFit trailFit
  have all : X86StateFrame.Frame clobbers
      (graphBytes ∪ trailBytes ∪ agendaBytes ∪ NativeBindingPublish.written agenda trail) before after := by
    exact (graphFrame.trans staged).mono (Finset.Subset.refl _) (by rw [← Finset.union_assoc, ← Finset.union_assoc])
  refine ⟨after, first + second, updated, nextRoot, graphBytes, trailBytes, agendaBytes,
    X86FuelPrefix.fetches_then first second before a after remap ran, all, privateGraph, trailPrivate, agendaPrivate,
    next, count, equationsRead, trace, ?_, graph.extension, endpoint⟩
  simp [PackedWorklist.advance, accepted, substituted, mapped]

end Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingStep
