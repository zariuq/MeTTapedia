import Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardDecision

/-!
# A fixed term prefix and a reusable guard workspace

The solver's descriptor is a prefix of the guard frame.
Two saved lengths describe the original normalized graph;
trial lengths may advance independently. Neither a successful
trial nor a refutation can destroy the original term prefix.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardWorkspace

open _root_.X86Registers X86RegisterRefinement
open X86PlacedMemory (Reads footprint CodeApart)
open NativeArenaGeometry (Region)
open NativeBindingSelection (Separated)
open NativeSubstitutionMemory (nodeBytes edgeBytes mapBytes Includes)
open NativeSolverStep (Writes)
open MemoryBinding (Native)

abbrev Frame := WordRegion.Region 16

def Frame.region (frame : Frame) : Region 16 := ⟨frame.pointer, frame.aligned, frame.area⟩

def Frame.solver (frame : Frame) : NativeTrailReserve.Descriptor :=
  frame.region.slice 0 8 (by decide) (by decide) (by decide)

theorem Frame.solver_pointer (frame : Frame) : frame.solver.pointer = frame.pointer := BitVec.add_zero _

theorem Frame.solver_cell (frame : Frame) (i : Fin 8) :
    (frame.solver.cell i).address = (frame.cell ⟨i.val, by have := i.isLt; omega⟩).address := by
  simp only [Frame.solver, Region.slice_address, Nat.zero_add]
  rfl

theorem Frame.staged_cell (frame : Frame) (i : Fin 7) :
    (frame.solver.substitution.cell i).address = (frame.cell ⟨i.val, by have := i.isLt; omega⟩).address := by
  rw [frame.solver.substitution_cell, frame.solver_cell]

theorem Frame.as_slice (frame : Frame) (i : Fin 16) :
    ((frame.region.slice 0 16 (by decide) (by decide) (by decide)).cell i).address = (frame.cell i).address := by
  rw [Region.slice_address, Nat.zero_add]
  rfl

def activeLengths (frame : Frame) : Finset ℕ := footprint (frame.cell 3).address ∪ footprint (frame.cell 4).address

theorem activeLengths_eq (frame : Frame) :
    activeLengths frame = NativeSubstitutionFrame.mutableBytes frame.solver.substitution := by
  unfold activeLengths NativeSubstitutionFrame.mutableBytes
  rw [frame.staged_cell, frame.staged_cell]
  rfl

variable {nc ec mc ac tc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {frame : Frame}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}
variable {image : NativeImage.View} {base : BitVec 48}

structure Geometry (term : NativeTermArena.Layout nc ec) (map : Region mc) (frame : Frame)
    (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc)
    (image : NativeImage.View) (base : BitVec 48) : Prop where
  solver : NativeBindingMemory.Geometry term map frame.solver agenda trail image base
  frameNode : Separated frame.region term.nodes
  frameEdge : Separated frame.region term.edges
  frameMap : Separated frame.region map
  frameAgenda : Separated frame.region agenda.words
  frameTrail : Separated frame.region trail.words

structure Avoids (term : NativeTermArena.Layout nc ec) (map : Region mc) (frame : Frame)
    (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc) (held : Finset ℕ) : Prop where
  nodes : ∀ i j, Disjoint held (nodeBytes term i j)
  edges : ∀ i, Disjoint held (edgeBytes term i)
  scratch : ∀ i, Disjoint held (mapBytes map i)
  lengths : Disjoint held (activeLengths frame)
  agendaRecord : ∀ i j, Disjoint held (footprint ((agenda.record i).cell j).address)
  trailRecord : ∀ i j, Disjoint held (footprint ((trail.record i).cell j).address)
  agendaCount : Disjoint held (NativeBindingPublish.header agenda)
  trailCount : Disjoint held (NativeBindingPublish.header trail)

theorem Avoids.graph {held bytes : Finset ℕ} (apart : Avoids term map frame agenda trail held)
    (effects : Includes term map frame.solver.substitution bytes) : Disjoint held bytes := by
  apply Finset.disjoint_left.mpr
  intro b kept wrote
  rcases effects b wrote with ⟨i, j, hit⟩ | ⟨i, hit⟩ | ⟨i, hit⟩ | hit
  · exact Finset.disjoint_left.mp (apart.nodes i j) kept hit
  · exact Finset.disjoint_left.mp (apart.edges i) kept hit
  · exact Finset.disjoint_left.mp (apart.scratch i) kept hit
  · exact Finset.disjoint_left.mp apart.lengths kept (activeLengths_eq frame ▸ hit)

theorem Avoids.kept {held bytes : Finset ℕ} (apart : Avoids term map frame agenda trail held)
    (effects : Writes term map frame.solver agenda trail bytes) : Disjoint held bytes := by
  induction effects with
  | idle => simp
  | graph effect => exact apart.graph effect
  | pending effect => exact NativePendingFill.Within.separate effect _ (fun i j _ _ => apart.agendaRecord i j)
  | binding effect => exact NativePendingFill.Within.separate effect _ (fun i j _ _ => apart.trailRecord i j)
  | header => exact apart.agendaCount
  | trailHeader => exact apart.trailCount
  | headers => exact Finset.disjoint_union_right.mpr ⟨apart.trailCount, apart.agendaCount⟩
  | union _ _ left right => exact Finset.disjoint_union_right.mpr ⟨left, right⟩

theorem Geometry.frame_record {capacity : ℕ} {packed : NativeAgendaRecords.Layout capacity}
    (apart : Separated frame.region packed.words) (slot : Fin 16) (i : Fin capacity) (j : Fin 3) :
    Disjoint (footprint (frame.cell slot).address) (footprint ((packed.record i).cell j).address) := by
  rw [← frame.as_slice]
  exact frame.region.separate_arenas packed.words apart 0 16 (3 * (i.val + 1)) 3 (by decide) (by decide)
    (by decide) (by have bound := i.isLt; omega) (by decide) (by decide) slot j

theorem Geometry.frame_header {capacity : ℕ} {packed : NativeAgendaRecords.Layout capacity}
    (apart : Separated frame.region packed.words) (slot : Fin 16) :
    Disjoint (footprint (frame.cell slot).address) (NativeBindingPublish.header packed) := by
  rw [← frame.as_slice]
  exact frame.region.separate_arenas packed.words apart 0 16 0 1 (by decide) (by decide)
    (by decide) (by omega) (by decide) (by decide) slot 0

theorem Geometry.saved (space : Geometry term map frame agenda trail image base) (slot : Fin 16)
    (notNodes : slot ≠ 3) (notEdges : slot ≠ 4) :
    Avoids term map frame agenda trail (footprint (frame.cell slot).address) := by
  refine ⟨?_, ?_, ?_, Finset.disjoint_union_right.mpr ⟨frame.separate_words notNodes, frame.separate_words notEdges⟩,
    frame_record space.frameAgenda slot, frame_record space.frameTrail slot, frame_header space.frameAgenda slot,
    frame_header space.frameTrail slot⟩
  · intro i j
    rw [← frame.as_slice]
    exact frame.region.separate_arenas term.nodes space.frameNode 0 16 (4 * i.val) 4
      (by decide) (by decide) (by decide) (by have bound := i.isLt; omega) (by decide) (by decide) slot j
  · intro i
    rw [← frame.as_slice]
    exact frame.region.separate_arenas term.edges space.frameEdge 0 16 i.val 1
      (by decide) (by decide) (by decide) i.isLt (by decide) (by decide) slot 0
  · intro i
    rw [← frame.as_slice]
    exact frame.region.separate_arenas map space.frameMap 0 16 i.val 1
      (by decide) (by decide) (by decide) i.isLt (by decide) (by decide) slot 0

theorem Geometry.agenda_metadata (space : Geometry term map frame agenda trail image base) (j : Fin 3) (static : j ≠ 0)
    {bytes : Finset ℕ} (effects : Writes term map frame.solver agenda trail bytes) :
    Disjoint (footprint (agenda.metadata.cell j).address) bytes := by
  induction effects with
  | idle => simp
  | graph effect => exact space.solver.substitute.agenda_slice_apart 0 3 (by decide) (by omega) (by decide) j effect
  | pending effect => exact NativeBindingMemory.meta_kept j effect
  | binding effect => exact NativeBindingMemory.meta_apart space.solver.trailAgenda.symm j effect
  | header => exact NativeBindingMemory.meta_immutable agenda j static
  | trailHeader => exact NativeBindingMemory.meta_header_apart space.solver.trailAgenda.symm j
  | headers => exact Finset.disjoint_union_right.mpr ⟨NativeBindingMemory.meta_header_apart space.solver.trailAgenda.symm j,
      NativeBindingMemory.meta_immutable agenda j static⟩
  | union _ _ left right => exact Finset.disjoint_union_right.mpr ⟨left, right⟩

theorem Geometry.trail_metadata (space : Geometry term map frame agenda trail image base) (j : Fin 3) (static : j ≠ 0)
    {bytes : Finset ℕ} (effects : Writes term map frame.solver agenda trail bytes) :
    Disjoint (footprint (trail.metadata.cell j).address) bytes := by
  induction effects with
  | idle => simp
  | graph effect => exact space.solver.forTrail.agenda_slice_apart 0 3 (by decide) (by omega) (by decide) j effect
  | pending effect => exact NativeBindingMemory.meta_apart space.solver.trailAgenda j effect
  | binding effect => exact NativeBindingMemory.meta_kept j effect
  | header => exact NativeBindingMemory.meta_header_apart space.solver.trailAgenda j
  | trailHeader => exact NativeBindingMemory.meta_immutable trail j static
  | headers => exact Finset.disjoint_union_right.mpr ⟨NativeBindingMemory.meta_immutable trail j static,
      NativeBindingMemory.meta_header_apart space.solver.trailAgenda j⟩
  | union _ _ left right => exact Finset.disjoint_union_right.mpr ⟨left, right⟩

def values (term : NativeTermArena.Layout nc ec) (map : Region mc) (agenda : NativeAgendaRecords.Layout ac)
    (trail : NativeAgendaRecords.Layout tc) (source : PackedTerms.Arena) (slot : Fin 11) : Word :=
  match slot.val with
  | 7 => trail.words.pointer
  | 8 => BitVec.ofNat 64 source.nodes.size
  | 9 => BitVec.ofNat 64 source.children.size
  | 10 => agenda.words.pointer
  | _ => NativeSubstitutionFrame.values term map source ⟨slot.val % 7, Nat.mod_lt _ (by decide)⟩

structure Ready (term : NativeTermArena.Layout nc ec) (map : Region mc) (frame : Frame)
    (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc)
    (source : PackedTerms.Arena) (native : Native) : Prop where
  sourceReady : NativeTermArena.Ready term source native
  stack : lookup native 4 = some frame.pointer
  saved : ∀ (i : Fin 11), i ≠ 3 → i ≠ 4 → Reads native (frame.cell ⟨i.val, by have := i.isLt; omega⟩).address
    (values term map agenda trail source i)
  pool : Reads native (agenda.metadata.cell 1).address term.edges.pointer
  agendaLimit : Reads native (agenda.metadata.cell 2).address (BitVec.ofNat 64 ac)
  trailLimit : Reads native (trail.metadata.cell 2).address (BitVec.ofNat 64 tc)
  zero : lookup native 12 = some 0
  one : lookup native 13 = some 1

variable {before after : Native} {source : PackedTerms.Arena} {regs : Finset Register} {bytes : Finset ℕ}

theorem Ready.preserved (ready : Ready term map frame agenda trail source before)
    (run : X86StateFrame.Frame regs ∅ before after)
    (stack : key (4 : Fin 16) ∉ regs) (zero : key (12 : Fin 16) ∉ regs) (one : key (13 : Fin 16) ∉ regs) :
    Ready term map frame agenda trail source after :=
  ⟨ready.sourceReady.preserved run, (run.lookup 4 stack).trans ready.stack,
    fun i n e => (ready.saved i n e).preserved run (by simp),
    ready.pool.preserved run (by simp), ready.agendaLimit.preserved run (by simp), ready.trailLimit.preserved run (by simp),
    (run.lookup 12 zero).trans ready.zero, (run.lookup 13 one).trans ready.one⟩

theorem Ready.afterTrial (ready : Ready term map frame agenda trail source before)
    (space : Geometry term map frame agenda trail image base) (run : X86StateFrame.Frame regs bytes before after)
    (effects : Writes term map frame.solver agenda trail bytes)
    (sourceReady : NativeTermArena.Ready term source after)
    (stack : key (4 : Fin 16) ∉ regs) (zero : key (12 : Fin 16) ∉ regs) (one : lookup after 13 = some 1) :
    Ready term map frame agenda trail source after :=
  ⟨sourceReady, (run.lookup 4 stack).trans ready.stack,
    fun i n e => (ready.saved i n e).preserved run ((space.saved ⟨i.val, by have := i.isLt; omega⟩
      (fun bad => n (Fin.ext (congrArg (fun k : Fin 16 => k.val) bad)))
      (fun bad => e (Fin.ext (congrArg (fun k : Fin 16 => k.val) bad)))).kept effects),
    ready.pool.preserved run (space.agenda_metadata 1 (by decide) effects),
    ready.agendaLimit.preserved run (space.agenda_metadata 2 (by decide) effects),
    ready.trailLimit.preserved run (space.trail_metadata 2 (by decide) effects),
    (run.lookup 12 zero).trans ready.zero, one⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardWorkspace
