import Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingRootMemory

/-!
# A binding with retained roots

Run the ordinary graph block and the ordinary agenda/trail
continuation, with a pass over the private root vector
between them. The pass shares the completed map; it does
not solve another equation or copy the graph.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingRoots

open Mettapedia.Logic.LP
open _root_.X86Registers X86Execution X86RegisterRefinement
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls)
open X86PlacedScalar (Code)
open NativeArenaGeometry (Region)
open NativeLiveRootEntry (Descriptor Held)
open NativeBindingStep (Live Staged)
open NativeBindingRootMemory (Geometry Covered)
open NativeSubstitutionMemory (Includes)
open NativeAgendaLoop (Within)
open PackedEquations (Arena readWords)
open PackedWorklist (Words)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def atRoots (start : ℕ) : ℕ := start + 584
def atLoop (start : ℕ) : ℕ := atRoots start + 20
def atTail (start : ℕ) : ℕ := atLoop start + 59
def endAt (start : ℕ) : ℕ := atTail start + 467

def emit (start next exhausted malformed : ℕ) : List ℕ :=
  NativeBoundSubstitution.emit start (atRoots start) exhausted malformed ++
    (NativeLiveRootEntry.emit ++ (NativeLiveRootLoop.emit (atLoop start) (atTail start) malformed ++
      NativeBindingStep.Tail.emit (atTail start) next exhausted malformed))

theorem emit_size (start next exhausted malformed : ℕ) : start + (emit start next exhausted malformed).length = endAt start := by
  simp only [emit, List.length_append, NativeBoundSubstitution.emit_size, NativeLiveRootEntry.emit_size,
    NativeLiveRootLoop.emit_size, NativeBindingStep.Tail.emit_size, endAt, atTail, atLoop, atRoots, ← Nat.add_assoc]

structure Placed (image : NativeImage.View) (start next exhausted malformed : ℕ) : Prop where
  graph : NativeBoundSubstitution.Placed image start (atRoots start) exhausted malformed
  roots : NativeLiveRootEntry.Placed image (atRoots start)
  loop : NativeLiveRootLoop.Placed image (atLoop start) (atTail start) malformed
  tail : NativeBindingStep.Tail.Placed image (atTail start) next exhausted malformed

theorem placed_of_emitted (image : NativeImage.View) (start next exhausted malformed : ℕ)
    (extent : endAt start ≤ image.size) (continues : next ≤ image.size)
    (lack : exhausted ≤ image.size) (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit start next exhausted malformed)) : Placed image start next exhausted malformed := by
  obtain ⟨graph, rest⟩ := NativeWords.code_append (show Code image start
    (NativeBoundSubstitution.emit start (atRoots start) exhausted malformed ++ _) from code)
  rw [NativeBoundSubstitution.emit_size] at rest
  obtain ⟨setup, rest⟩ := NativeWords.code_append rest
  rw [NativeLiveRootEntry.emit_size] at rest
  obtain ⟨loop, tail⟩ := NativeWords.code_append rest
  rw [NativeLiveRootLoop.emit_size] at tail
  have room := extent
  unfold endAt atTail atLoop atRoots at room
  exact ⟨NativeBoundSubstitution.placed_of_emitted image _ _ _ _ (by omega) (by unfold atRoots; omega) lack bad short graph,
    NativeLiveRootEntry.placed_of_emitted image _ (by unfold atRoots; omega) setup,
    NativeLiveRootLoop.placed_of_emitted image _ _ _ (by unfold atLoop atRoots; omega)
      (by unfold atTail atLoop atRoots; omega) bad short loop,
    NativeBindingStep.Tail.placed_of_emitted image _ _ _ _ extent continues lack bad short tail⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev rootClobbers : Finset Register := NativeLiveRootEntry.clobbers ∪ NativeLiveRootLoop.clobbers
abbrev clobbers : Finset Register := NativeBoundSubstitution.clobbers ∪ rootClobbers ∪ NativeBindingStep.Tail.clobbers
theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {nc ec mc ac tc rc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {d : Descriptor} {roots : Region rc}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}
variable {image : NativeImage.View} {base : BitVec 48}

private theorem moved_roots (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start next exhausted malformed : ℕ} {before : Native} (code : Placed image start next exhausted malformed)
    (point : At image before base (atRoots start)) (controls : Controls before)
    (space : Geometry roots d term map agenda trail image base)
    {source : PackedTerms.Arena} {equations oldTrail : Arena} {result : PackedSubstitution.State} {cursor name value : Word}
    (stage : Staged term map d.solver agenda trail source equations oldTrail result cursor name value before)
    (old new : Array Word) (held : Held d roots old before)
    (moved : PackedSubstitution.translate result.mapped old = some new) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after writes, (X86FuelPrefix.fetches (4 + (12 * old.size + 2))).run before = .ok () after ∧
      X86StateFrame.Frame rootClobbers writes before after ∧ NativeMarkTable.Within roots 0 old.size writes ∧
      Held d roots new after ∧ Staged term map d.solver agenda trail source equations oldTrail result cursor name value after ∧
      Nonempty (At image after base (atTail start)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have stack : lookup before 4 = some d.pointer :=
    ((NativeTrailReserve.Descriptor.substitution_pointer d.solver).trans d.solver_pointer) ▸ stage.table.pointer
  obtain ⟨ready, prepared, prepFrame, input, ⟨loop⟩⟩ := NativeLiveRootEntry.fetched other extra vector
    point controls code.roots d held stage.mapping stack stage.mapBase stage.mapLimit stage.zero stage.one
  obtain ⟨after, writes, movedAll, movedFrame, confined, remapped, endpoint⟩ := NativeLiveRootLoop.fetched
    other extra vector code.loop space.rootSpace.map.symm space.code old new old moved 0 old.size (Nat.zero_add _)
    (NativeLiveRootLoop.Cursor.start _ _) loop (controls.transport prepFrame NativeLiveRootEntry.clobbers_data) input
  have all : X86StateFrame.Frame rootClobbers writes before after :=
    (prepFrame.trans movedFrame).mono (Finset.Subset.refl _) (by rw [Finset.empty_union])
  have written := Covered.rootWrites confined
  have size := (PackedRemapCoordinates.coordinates result.mapped old new moved).1
  have metadata := held.descriptor.kept all
    (Covered.separate space.rootFrame.symm (Covered.field d 16) written)
    (Covered.separate space.rootFrame.symm (Covered.field d 17) written)
  exact ⟨after, writes, X86FuelPrefix.fetches_then 4 _ before ready after prepared movedAll, all, confined,
    ⟨size.symm ▸ metadata, remapped.slot.operands⟩, space.keep_stage stage all written, endpoint⟩

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- The rooted binding is one complete fetched transition
of the same packed solver, now also transporting the
caller's ordered vector. No store occurrence is consumed. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {entry done shared cycle exhausted : ℕ} {targets : NativeTermDispatch.Targets} {before : Native}
    (point : At image before base entry) (controls : Controls before) (side : NativeBindEntry.Side)
    (agendaCode : NativeAgendaDispatch.Placed image entry done targets)
    (entryCode : NativeBindEntry.EntryPlaced image side (targets.at side.exiting) shared)
    (gateCode : NativeBindingGate.Placed image shared cycle exhausted targets.malformed)
    (code : Placed image (shared + 273) entry exhausted targets.malformed)
    (space : NativeBindingMemory.Geometry term map d.solver agenda trail image base)
    (rootSpace : Geometry roots d term map agenda trail image base)
    (source : PackedTerms.Arena) (equations oldTrail : Arena) (root left right : Word) (pending history : Words)
    (live : Live term map d.solver agenda trail source equations root oldTrail before)
    (held : readWords equations root = some ((left, right) :: pending))
    (traced : readWords oldTrail (NativeBindingTrail.root oldTrail) = some history)
    (symbols : UnifierHeaders.Symbols σ) (lTerm rTerm : Term σ)
    (leftRead : PackedTerms.lookup symbols source left = some lTerm) (rightRead : PackedTerms.lookup symbols source right = some rTerm)
    (routed : NativeTermDispatch.choose source left right = side.exiting)
    (name value : Word) (accepted : PackedUnifierAction.inspect source left right = some (.bindVar name value))
    (result : PackedSubstitution.State) (substituted : PackedSubstitution.substitute source name value = some result)
    (remapped : Words) (mapped : PackedSubstitution.remapPending result.mapped pending = some remapped)
    (mapFit : source.nodes.size ≤ mc) (nodesFit : result.target.nodes.size ≤ nc) (edgesFit : result.target.children.size ≤ ec)
    (agendaFit : equations.size + pending.length ≤ ac) (trailFit : oldTrail.size < tc)
    (old new : Array Word) (retained : Held d roots old before)
    (translated : PackedSubstitution.translate result.mapped old = some new) :
    let newTrail := oldTrail.push (NativeBindingTrail.binding oldTrail name value)
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps updated nextRoot graphWrites rootWrites trailWrites agendaWrites,
      (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers
        ((graphWrites ∪ rootWrites) ∪ (trailWrites ∪ agendaWrites ∪ NativeBindingPublish.written agenda trail)) before after ∧
      Includes term map d.solver.substitution graphWrites ∧ NativeMarkTable.Within roots 0 old.size rootWrites ∧
      Within trail oldTrail.size (oldTrail.size + 1) trailWrites ∧
      Within agenda equations.size (equations.size + pending.length) agendaWrites ∧
      Live term map d.solver agenda trail result.target updated nextRoot newTrail after ∧
      Held d roots new after ∧
      updated.size = equations.size + pending.length ∧
      readWords updated nextRoot = some remapped ∧
      readWords newTrail (NativeBindingTrail.root newTrail) = some ((name, value) :: history) ∧
      PackedWorklist.advance ⟨source, (left, right) :: pending, history⟩ =
        some (.working ⟨result.target, remapped, (name, value) :: history⟩) ∧
      NativeRemapSnapshot.Extension source result.target ∧ Nonempty (At image after base entry) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨a, first, graphBytes, cursor, graphRun, graphFrame, privateGraph, graph, suffix, ⟨atRoots⟩⟩ :=
    NativeBindingStep.fetched_graph other extra vector point controls side agendaCode entryCode gateCode code.graph space
      source equations oldTrail root left right pending live held symbols lTerm rTerm leftRead rightRead routed name value
      accepted result substituted mapFit nodesFit edgesFit
  obtain ⟨b, rootBytes, carried, rootFrame, privateRoots, nextHeld, nextStage, ⟨atTail⟩⟩ :=
    moved_roots other extra vector code atRoots (controls.transport graphFrame (by decide)) rootSpace graph
      old new (rootSpace.held_after_graph retained graphFrame privateGraph) translated
  have prep := graphFrame.trans rootFrame
  obtain ⟨after, second, updated, nextRoot, trailBytes, agendaBytes, staged, tailFrame, privateTrail, privateAgenda, next,
    count, equationsRead, trace, endpoint⟩ := NativeBindingStep.fetched_tail other extra vector atTail
      (controls.transport prep (by decide)) code.tail space source equations oldTrail cursor name value pending history result
      nextStage suffix traced remapped mapped agendaFit trailFit
  have prefixRun := X86FuelPrefix.fetches_then first (4 + (12 * old.size + 2)) before a b graphRun carried
  exact ⟨after, _, updated, nextRoot, graphBytes, rootBytes, trailBytes, agendaBytes,
    X86FuelPrefix.fetches_then _ second before b after prefixRun staged, prep.trans tailFrame, privateGraph, privateRoots,
    privateTrail, privateAgenda, next, rootSpace.held_after_tail nextHeld tailFrame privateAgenda privateTrail, count,
    equationsRead, trace, by simp [PackedWorklist.advance, accepted, substituted, mapped], graph.extension, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingRoots
