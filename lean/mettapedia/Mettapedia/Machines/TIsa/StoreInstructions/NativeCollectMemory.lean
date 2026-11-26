import Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardInstall
import Mettapedia.Machines.TIsa.StoreInstructions.OccurrenceMask

/-!
# The private occurrence mask

The candidate and mask use the same ordinal, so writing a
mark needs no lookup or copying of an occurrence identity.
A mask prefix is separate from the source graph, equations,
trail, and occurrence directory. The output pointer lies
after the solver, guard, and retained-root metadata.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeCollectMemory

open _root_.X86Registers X86RegisterRefinement
open X86PlacedMemory (Reads Cell CodeApart footprint)
open NativeArenaGeometry (Region)
open NativeBindingSelection (Separated)
open NativeBindingRootMemory (External Covered)
open NativeGuardWorkspace (Frame Avoids)
open NativeGuardState (Stable counters)
open NativeSolverStep (Writes)
open NativeSubstLeaf (MapReady)
open MemoryBinding (Native)

/-- Reuse the classifier's certain and impossible word
codes; there is no conversion on the hot append path. -/
def mark (selected : Bool) : Word := if selected then 2 else 0

def slotBytes {q : ℕ} (output : Region q) (i : Fin q) : Finset ℕ :=
  footprint ((output.wordCell i).cell 0).address

variable {nc ec mc ac tc oc cap : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {frame : Frame}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}
variable {table : Region oc} {output : Region cap} {pointer : Cell frame.pointer 144}
variable {image : NativeImage.View} {base : BitVec 48}

structure Geometry (term : NativeTermArena.Layout nc ec) (map : Region mc) (frame : Frame)
    (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc)
    (table : Region oc) (output : Region cap) (pointer : Cell frame.pointer 144)
    (image : NativeImage.View) (base : BitVec 48) : Prop where
  guard : NativeGuardState.Geometry term map frame agenda trail table image base
  outside : External output term map agenda trail
  frameApart : Separated output frame.region
  tableApart : Separated output table
  pointerTrial : Avoids term map frame agenda trail (footprint pointer.address)
  pointerScan : Disjoint (footprint pointer.address) (counters frame)
  pointerMarks : ∀ i : Fin cap, Disjoint (footprint pointer.address) (slotBytes output i)
  code : ∀ i : Fin cap, CodeApart image base (slotBytes output i)

structure Prefix (frame : Frame) (output : Region cap) (pointer : Cell frame.pointer 144)
    (bits : Array Bool) (native : Native) : Prop where
  base : Reads native pointer.address (output.atWord 0)
  bits : NativeMarkTable.PrefixReady mark output bits native

variable {terms : PackedTerms.Arena} {needle : Word} {handles : Array Word}
variable {R : Finset Register} {bytes : Finset ℕ} {before after : Native} {bits : Array Bool}

theorem Geometry.mask_avoids (space : Geometry term map frame agenda trail table output pointer image base) (i : Fin cap) :
    Avoids term map frame agenda trail (slotBytes output i) := by
  have held := Covered.word output i
  refine ⟨fun j k => Covered.separate space.outside.nodes held (Covered.node term j k),
    fun edge => Covered.separate space.outside.edges held (Covered.edge term edge),
    fun slot => Covered.separate space.outside.map held (Covered.word map slot), ?_,
    fun row col => Covered.separate space.outside.agenda held (Covered.record agenda row col),
    fun row col => Covered.separate space.outside.trail held (Covered.record trail row col),
    Covered.separate space.outside.agenda held (Covered.header agenda),
    Covered.separate space.outside.trail held (Covered.header trail)⟩
  unfold NativeGuardWorkspace.activeLengths
  exact Covered.separate space.frameApart held ((NativeGuardInstall.slots_cover frame 3).union (NativeGuardInstall.slots_cover frame 4))

theorem Geometry.slot_counters (space : Geometry term map frame agenda trail table output pointer image base) (i : Fin cap) :
    Disjoint (slotBytes output i) (counters frame) :=
  Covered.separate space.frameApart (Covered.word output i)
    ((NativeGuardInstall.slots_cover frame 14).union (NativeGuardInstall.slots_cover frame 15))

theorem Prefix.preserved (resident : Prefix frame output pointer bits before) (run : X86StateFrame.Frame R ∅ before after) :
    Prefix frame output pointer bits after :=
  ⟨resident.base.preserved run (by simp), resident.bits.preserved run⟩

theorem Prefix.afterProbe (resident : Prefix frame output pointer bits before)
    (space : Geometry term map frame agenda trail table output pointer image base)
    (run : X86StateFrame.Frame R bytes before after) (writes : Writes term map frame.solver agenda trail bytes) :
    Prefix frame output pointer bits after :=
  ⟨resident.base.preserved run (space.pointerTrial.kept writes),
    resident.bits.kept run (fun i => (space.mask_avoids i).kept writes)⟩

theorem Prefix.afterCounters (resident : Prefix frame output pointer bits before)
    (space : Geometry term map frame agenda trail table output pointer image base)
    (run : X86StateFrame.Frame R (counters frame) before after) : Prefix frame output pointer bits after :=
  ⟨resident.base.preserved run space.pointerScan, resident.bits.kept run space.slot_counters⟩

theorem Geometry.stable_after_marks (space : Geometry term map frame agenda trail table output pointer image base)
    (stable : Stable term map frame agenda trail table terms needle handles before)
    (run : X86StateFrame.Frame R bytes before after) (wrote : Covered output bytes)
    (stack : key (4 : Fin 16) ∉ R) (zero : key (12 : Fin 16) ∉ R) (one : key (13 : Fin 16) ∉ R) :
    Stable term map frame agenda trail table terms needle handles after := by
  have disjoint (slot : Fin 16) : Disjoint (footprint (frame.cell slot).address) bytes :=
    Covered.separate space.frameApart.symm (NativeGuardInstall.slots_cover frame slot) wrote
  have graph := stable.scratch.sourceReady.kept run
    (fun i j => Covered.separate space.outside.nodes.symm (Covered.node term i j) wrote)
    (fun i => Covered.separate space.outside.edges.symm (Covered.edge term i) wrote)
  exact ⟨⟨graph, (run.lookup 4 stack).trans stable.scratch.stack,
      fun i n e => (stable.scratch.saved i n e).preserved run (disjoint _),
      stable.scratch.pool.preserved run (Covered.separate space.outside.agenda.symm (Covered.metadata agenda 1) wrote),
      stable.scratch.agendaLimit.preserved run (Covered.separate space.outside.agenda.symm (Covered.metadata agenda 2) wrote),
      stable.scratch.trailLimit.preserved run (Covered.separate space.outside.trail.symm (Covered.metadata trail 2) wrote),
      (run.lookup 12 zero).trans stable.scratch.zero, (run.lookup 13 one).trans stable.scratch.one⟩,
    ⟨stable.directory.pattern.preserved run (disjoint 11), stable.directory.pointer.preserved run (disjoint 12),
      stable.directory.count.preserved run (disjoint 13),
      stable.directory.occurrences.kept run (fun i => Covered.separate space.tableApart.symm (Covered.word table i) wrote)⟩⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeCollectMemory
