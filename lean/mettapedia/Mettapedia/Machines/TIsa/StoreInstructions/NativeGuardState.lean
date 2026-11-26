import Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardCursor

/-!
# The stable part of a native guard scan

The term prefix and occurrence directory outlive all trials.
Solver writes are confined to their arenas and staged lengths;
the two scan counters have separate cells in the frame.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardState

open _root_.X86Registers X86RegisterRefinement
open X86PlacedMemory (Reads CodeApart footprint)
open NativeArenaGeometry (Region)
open NativeGuardWorkspace (Frame Avoids)
open NativeGuardOperands (Directory)
open NativeSolverStep (Writes)
open NativeGuardCursor (ordinalBytes)
open NativeGuardPolicy (counterBytes)
open MemoryBinding (Native)

def counters (frame : Frame) : Finset ℕ := ordinalBytes frame ∪ counterBytes frame

theorem counters_apart {frame : Frame} {i : Fin 16} (ordinal : i ≠ 14) (count : i ≠ 15) :
    Disjoint (footprint (frame.cell i).address) (counters frame) :=
  Finset.disjoint_union_right.mpr ⟨frame.separate_words ordinal, frame.separate_words count⟩

variable {nc ec mc ac tc occ : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {frame : Frame}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc} {table : Region occ}
variable {image : NativeImage.View} {base : BitVec 48}

structure Geometry (term : NativeTermArena.Layout nc ec) (map : Region mc) (frame : Frame)
    (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc) (table : Region occ)
    (image : NativeImage.View) (base : BitVec 48) : Prop where
  workspace : NativeGuardWorkspace.Geometry term map frame agenda trail image base
  directory : ∀ i : Fin occ, Avoids term map frame agenda trail (footprint ((table.wordCell i).cell 0).address)
  cursorApart : ∀ i : Fin occ, Disjoint (footprint ((table.wordCell i).cell 0).address) (counters frame)
  ordinalCode : CodeApart image base (ordinalBytes frame)
  countCode : CodeApart image base (counterBytes frame)

structure Stable (term : NativeTermArena.Layout nc ec) (map : Region mc) (frame : Frame)
    (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc) (table : Region occ)
    (terms : PackedTerms.Arena) (needle : Word) (handles : Array Word) (native : Native) : Prop where
  scratch : NativeGuardWorkspace.Ready term map frame agenda trail terms native
  directory : Directory table frame needle handles native

structure State (term : NativeTermArena.Layout nc ec) (map : Region mc) (frame : Frame)
    (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc) (table : Region occ)
    (terms : PackedTerms.Arena) (needle : Word) (handles : Array Word) (ordinal count : ℕ) (native : Native) : Prop where
  stable : Stable term map frame agenda trail table terms needle handles native
  ordinalWord : Reads native (frame.cell 14).address (BitVec.ofNat 64 ordinal)
  counterWord : Reads native (frame.cell 15).address (BitVec.ofNat 64 count)

variable {before after : Native} {terms : PackedTerms.Arena} {needle : Word} {handles : Array Word}
variable {regs : Finset Register} {bytes : Finset ℕ}

theorem Stable.preserved (state : Stable term map frame agenda trail table terms needle handles before)
    (run : X86StateFrame.Frame regs ∅ before after) (stack : key (4 : Fin 16) ∉ regs)
    (zero : key (12 : Fin 16) ∉ regs) (one : key (13 : Fin 16) ∉ regs) :
    Stable term map frame agenda trail table terms needle handles after :=
  ⟨state.scratch.preserved run stack zero one,
    ⟨state.directory.pattern.preserved run (by simp), state.directory.pointer.preserved run (by simp),
      state.directory.count.preserved run (by simp), state.directory.occurrences.preserved run⟩⟩

theorem Stable.afterSolver (state : Stable term map frame agenda trail table terms needle handles before)
    (space : Geometry term map frame agenda trail table image base)
    (run : X86StateFrame.Frame regs bytes before after) (effects : Writes term map frame.solver agenda trail bytes)
    (original : NativeTermArena.Ready term terms after)
    (stack : key (4 : Fin 16) ∉ regs) (zero : key (12 : Fin 16) ∉ regs) (one : lookup after 13 = some 1) :
    Stable term map frame agenda trail table terms needle handles after :=
  ⟨state.scratch.afterTrial space.workspace run effects original stack zero one,
    ⟨state.directory.pattern.preserved run ((space.workspace.saved 11 (by decide) (by decide)).kept effects),
      state.directory.pointer.preserved run ((space.workspace.saved 12 (by decide) (by decide)).kept effects),
      state.directory.count.preserved run ((space.workspace.saved 13 (by decide) (by decide)).kept effects),
      state.directory.occurrences.kept run (fun i => (space.directory i).kept effects)⟩⟩

private theorem meta_counter {n : ℕ} {layout : NativeAgendaRecords.Layout n}
    (apart : NativeBindingSelection.Separated frame.region layout.words) (field : Fin 3) :
    Disjoint (footprint (layout.metadata.cell field).address) (counters frame) := by
  have one (k : Fin 16) : Disjoint (footprint (layout.metadata.cell field).address) (footprint (frame.cell k).address) := by
    rw [← frame.as_slice]
    exact (frame.region.separate_arenas layout.words apart 0 16 0 3
      (by decide) (by decide) (by decide) (by omega) (by decide) (by decide) k field).symm
  exact Finset.disjoint_union_right.mpr ⟨one 14, one 15⟩

theorem Stable.afterCounters (state : Stable term map frame agenda trail table terms needle handles before)
    (space : Geometry term map frame agenda trail table image base)
    (run : X86StateFrame.Frame regs (counters frame) before after)
    (stack : key (4 : Fin 16) ∉ regs) (zero : key (12 : Fin 16) ∉ regs) (one : key (13 : Fin 16) ∉ regs) :
    Stable term map frame agenda trail table terms needle handles after := by
  have disjoint (i : Fin 11) :
      Disjoint (footprint (frame.cell ⟨i.val, by have := i.isLt; omega⟩).address) (counters frame) := by
    apply counters_apart
    · intro equal
      have val := congrArg (fun s : Fin 16 => s.val) equal
      change i.val = 14 at val
      have bound := i.isLt
      omega
    · intro equal
      have val := congrArg (fun s : Fin 16 => s.val) equal
      change i.val = 15 at val
      have bound := i.isLt
      omega
  have slot14 := space.workspace.saved 14 (by decide) (by decide)
  have slot15 := space.workspace.saved 15 (by decide) (by decide)
  have graph : NativeTermArena.Ready term terms after := state.scratch.sourceReady.kept run
    (fun i j => Finset.disjoint_union_right.mpr ⟨(slot14.nodes i j).symm, (slot15.nodes i j).symm⟩)
    (fun i => Finset.disjoint_union_right.mpr ⟨(slot14.edges i).symm, (slot15.edges i).symm⟩)
  exact ⟨⟨graph, (run.lookup 4 stack).trans state.scratch.stack,
      fun i n e => (state.scratch.saved i n e).preserved run (disjoint i),
      state.scratch.pool.preserved run (meta_counter space.workspace.frameAgenda 1),
      state.scratch.agendaLimit.preserved run (meta_counter space.workspace.frameAgenda 2),
      state.scratch.trailLimit.preserved run (meta_counter space.workspace.frameTrail 2),
      (run.lookup 12 zero).trans state.scratch.zero, (run.lookup 13 one).trans state.scratch.one⟩,
    ⟨state.directory.pattern.preserved run (counters_apart (by decide) (by decide)),
      state.directory.pointer.preserved run (counters_apart (by decide) (by decide)),
      state.directory.count.preserved run (counters_apart (by decide) (by decide)),
      state.directory.occurrences.kept run space.cursorApart⟩⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardState
