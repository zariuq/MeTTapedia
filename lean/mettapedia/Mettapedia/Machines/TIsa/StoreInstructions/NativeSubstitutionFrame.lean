import Mettapedia.Machines.TIsa.StoreInstructions.NativeLoads
import Mettapedia.Machines.TIsa.StoreInstructions.NativeRemapReserve

/-!
# The private lengths of an in-progress native substitution

The caller's initialized lengths remain separate. The frame
shares its first two qwords with occurrence scratch. The
staged lengths advance only after fresh records are ready.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionFrame

open _root_.X86Registers X86RegisterRefinement
open X86PlacedMemory (Reads footprint)
open NativeArenaGeometry (Region)
open MemoryBinding (Native)

abbrev Table := WordRegion.Region 7

def region (frame : Table) : Region 7 := ⟨frame.pointer, frame.aligned, frame.area⟩

def scratchDescriptor (frame : Table) : WordRegion.Region 2 :=
  (region frame).slice 0 2 (by decide) (by decide) (by decide)

theorem scratch_pointer (frame : Table) : (scratchDescriptor frame).pointer = frame.pointer := BitVec.add_zero _

theorem scratch_cell (frame : Table) (slot : Fin 2) :
    ((scratchDescriptor frame).cell slot).address = (frame.cell ⟨slot.val, by omega⟩).address := by
  simp only [scratchDescriptor, Region.slice_address, Nat.zero_add]
  rfl

def nodeCount : Fin 7 := 3
def edgeCount : Fin 7 := 4

def values {nodeCapacity edgeCapacity mapCapacity : ℕ}
    (layout : NativeTermArena.Layout nodeCapacity edgeCapacity)
    (map : Region mapCapacity) (target : PackedTerms.Arena) (slot : Fin 7) : Word :=
  match slot.val with
  | 0 => map.atWord 0
  | 1 => BitVec.ofNat 64 mapCapacity
  | 2 => layout.nodes.pointer
  | 3 => BitVec.ofNat 64 target.nodes.size
  | 4 => BitVec.ofNat 64 target.children.size
  | 5 => BitVec.ofNat 64 nodeCapacity
  | _ => BitVec.ofNat 64 edgeCapacity

structure Ready {nodeCapacity edgeCapacity mapCapacity : ℕ}
    (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (map : Region mapCapacity)
    (frame : Table) (target : PackedTerms.Arena) (native : Native) : Prop where
  pointer : lookup native 4 = some frame.pointer
  word : ∀ slot : Fin 7, Reads native (frame.cell slot).address (values layout map target slot)

variable {nodeCapacity edgeCapacity mapCapacity : ℕ}
variable {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {map : Region mapCapacity}
variable {frame : Table} {arena : PackedTerms.Arena}

theorem Ready.kept {before after : Native} {regs : Finset Register} {bytes : Finset ℕ}
    (ready : Ready layout map frame arena before) (run : X86StateFrame.Frame regs bytes before after)
    (stack : key (4 : Fin 16) ∉ regs)
    (apart : ∀ slot : Fin 7, Disjoint (footprint (frame.cell slot).address) bytes) :
    Ready layout map frame arena after :=
  ⟨(run.lookup 4 stack).trans ready.pointer, fun slot => (ready.word slot).preserved run (apart slot)⟩

theorem Ready.preserved {before after : Native} {regs : Finset Register}
    (ready : Ready layout map frame arena before) (run : X86StateFrame.Frame regs ∅ before after)
    (stack : key (4 : Fin 16) ∉ regs) : Ready layout map frame arena after :=
  ready.kept run stack (by intro _; simp)

theorem Ready.scratch_base {before : Native} (ready : Ready layout map frame arena before) :
    Reads before ((scratchDescriptor frame).cell 0).address (map.atWord 0) := by
  rw [scratch_cell]
  exact ready.word 0

theorem Ready.scratch_size {before : Native} (ready : Ready layout map frame arena before) :
    Reads before ((scratchDescriptor frame).cell 1).address (BitVec.ofNat 64 mapCapacity) := by
  rw [scratch_cell]
  exact ready.word 1

def mutableBytes (frame : Table) : Finset ℕ :=
  footprint (frame.cell nodeCount).address ∪ footprint (frame.cell edgeCount).address

theorem unchanged_field {i : Fin 7} (notNode : i ≠ nodeCount) (notEdge : i ≠ edgeCount)
    (new : PackedTerms.Arena) : values layout map new i = values layout map arena i := by
  fin_cases i <;> try rfl
  · exact (notNode rfl).elim
  · exact (notEdge rfl).elim

theorem immutable_disjoint (frame : Table) {i : Fin 7} (notNode : i ≠ nodeCount) (notEdge : i ≠ edgeCount) :
    Disjoint (footprint (frame.cell i).address) (mutableBytes frame) :=
  Finset.disjoint_union_right.mpr ⟨frame.separate_words notNode, frame.separate_words notEdge⟩

/-- A completed update of just the two staged lengths realizes
the new view without changing any descriptor field. -/
theorem Ready.lengths_updated {before after : Native} {regs : Finset Register}
    (ready : Ready layout map frame arena before) (run : X86StateFrame.Frame regs (mutableBytes frame) before after)
    (stack : key (4 : Fin 16) ∉ regs) (new : PackedTerms.Arena)
    (nodes : Reads after (frame.cell nodeCount).address (BitVec.ofNat 64 new.nodes.size))
    (edges : Reads after (frame.cell edgeCount).address (BitVec.ofNat 64 new.children.size)) :
    Ready layout map frame new after := by
  refine ⟨(run.lookup 4 stack).trans ready.pointer, fun i => ?_⟩
  by_cases n : i = nodeCount
  · subst i
    exact nodes
  · by_cases e : i = edgeCount
    · subst i
      exact edges
    · rw [unchanged_field n e new]
      exact (ready.word i).preserved run (immutable_disjoint _ n e)

def load (base : NativeLoads.Base) (frame : Table) (register : Fin 16)
    (separate : base.register ≠ register) (slot : Fin 7) (value : Word) : NativeLoads.Load base frame.pointer :=
  ⟨register, separate, _, frame.cell slot, value⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionFrame
