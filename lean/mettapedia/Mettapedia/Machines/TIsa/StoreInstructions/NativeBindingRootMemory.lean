import Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingStep
import Mettapedia.Machines.TIsa.StoreInstructions.NativeLiveRootEntry

/-!
# Regions retained across the native binding continuation

A rooted value has a private slot, independent of both its
term record and any occurrence that owns it. The root pass
writes only that vector. The graph, agenda and trail phases
leave the vector and its descriptor alone.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingRootMemory

open _root_.X86Registers X86RegisterRefinement
open X86PlacedMemory (Reads footprint CodeApart)
open NativeArenaGeometry (Region)
open NativeBindingSelection (Separated)
open NativeLiveRootEntry (Descriptor Held Metadata)
open NativeSubstitutionMemory (Includes nodeBytes edgeBytes mapBytes)
open NativeBindingStep (Staged)
open NativeAgendaLoop (Within)
open MemoryBinding (Native)

variable {n m : ℕ}

/-- A set of accessed bytes sits inside an actual word arena
if each byte belongs to one of its aligned cells. -/
def Covered (region : Region n) (bytes : Finset ℕ) : Prop :=
  ∀ byte ∈ bytes, ∃ i : Fin n, byte ∈ footprint ((region.wordCell i).cell 0).address

theorem Covered.cell (region : Region n) (start width : ℕ)
    (positive : 0 < width) (inside : start + width ≤ n) (short : 8 * width ≤ 2 ^ 31)
    (field : Fin width) : Covered region (footprint ((region.slice start width positive inside short).cell field).address) := by
  intro byte hit
  refine ⟨⟨start + field.val, by have := field.isLt; omega⟩, ?_⟩
  rw [Region.slice_address] at hit
  simpa only [Region.wordCell, Region.slice_address, Fin.val_zero, Nat.add_zero] using hit

theorem Covered.word (region : Region n) (i : Fin n) : Covered region (footprint ((region.wordCell i).cell 0).address) :=
  fun _ hit => ⟨i, hit⟩

theorem Covered.empty (region : Region n) : Covered region ∅ := fun _ h => (Finset.notMem_empty _ h).elim

theorem Covered.union {region : Region n} {left right : Finset ℕ}
    (first : Covered region left) (second : Covered region right) : Covered region (left ∪ right) :=
  fun b hit => (Finset.mem_union.mp hit).elim (first b) (second b)

theorem Covered.separate {left : Region n} {right : Region m} {reads writes : Finset ℕ}
    (apart : Separated left right) (kept : Covered left reads) (saved : Covered right writes) :
    Disjoint reads writes := by
  apply Finset.disjoint_left.mpr
  intro byte two first
  obtain ⟨l, read⟩ := kept byte two
  obtain ⟨r, wrote⟩ := saved byte first
  exact Finset.disjoint_left.mp (left.separate_arenas right apart l.val 1 r.val 1
    (by decide) (by decide) l.isLt r.isLt (by decide) (by decide) 0 0) read wrote

variable {rc nc ec mc ac tc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {d : Descriptor} {roots : Region rc}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}
variable {image : NativeImage.View} {base : BitVec 48}

theorem Covered.node (term : NativeTermArena.Layout nc ec) (i : Fin nc) (j : Fin 4) :
    Covered term.nodes (nodeBytes term i j) :=
  .cell term.nodes (4 * i.val) 4 (by decide) (by have := i.isLt; omega) (by decide) j

theorem Covered.edge (term : NativeTermArena.Layout nc ec) (i : Fin ec) : Covered term.edges (edgeBytes term i) :=
  .word term.edges i

theorem Covered.field (d : Descriptor) (i : Fin 18) : Covered d.region (footprint (d.cell i).address) := by
  have agree : ((d.region.slice 0 18 (by decide) (by decide) (by decide)).cell i).address = (d.cell i).address := by
    rw [Region.slice_address, Nat.zero_add]
    rfl
  rw [← agree]
  exact .cell d.region 0 18 (by decide) (by decide) (by decide) i

theorem Covered.solver (d : Descriptor) (i : Fin 8) : Covered d.region (footprint (d.solver.cell i).address) :=
  d.cell_of_solver i ▸ Covered.field d ⟨i.val, i.isLt.trans (by decide)⟩

theorem Covered.table (d : Descriptor) (i : Fin 7) :
    Covered d.region (footprint (d.solver.substitution.cell i).address) :=
  d.solver.substitution_cell i ▸ Covered.solver d ⟨i.val, i.isLt.trans (by decide)⟩

theorem Covered.record {c : ℕ} (bank : NativeAgendaRecords.Layout c) (i : Fin c) (j : Fin 3) :
    Covered bank.words (footprint ((bank.record i).cell j).address) :=
  .cell bank.words (3 * (i.val + 1)) 3 (by decide) (by have := i.isLt; omega) (by decide) j

theorem Covered.metadata {c : ℕ} (bank : NativeAgendaRecords.Layout c) (j : Fin 3) :
    Covered bank.words (footprint (bank.metadata.cell j).address) :=
  .cell bank.words 0 3 (by decide) (by omega) (by decide) j

theorem Covered.header {c : ℕ} (bank : NativeAgendaRecords.Layout c) :
    Covered bank.words (NativeBindingPublish.header bank) :=
  .cell bank.words 0 1 (by decide) (by omega) (by decide) 0

theorem Covered.agendaWrites {c lo hi : ℕ} {bank : NativeAgendaRecords.Layout c} {bytes : Finset ℕ}
    (touched : Within bank lo hi bytes) : Covered bank.words bytes := by
  intro byte hit
  obtain ⟨i, j, _, _, written⟩ := touched byte hit
  exact (Covered.record bank i j) byte written

theorem Covered.rootWrites {lo hi : ℕ} {bytes : Finset ℕ}
    (touched : NativeMarkTable.Within roots lo hi bytes) : Covered roots bytes := by
  intro byte hit
  obtain ⟨i, _, _, wrote⟩ := touched byte hit
  exact ⟨i, wrote⟩

structure External (outside : Region n) (term : NativeTermArena.Layout nc ec) (map : Region mc)
    (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc) : Prop where
  nodes : Separated outside term.nodes
  edges : Separated outside term.edges
  map : Separated outside map
  agenda : Separated outside agenda.words
  trail : Separated outside trail.words

structure Geometry (roots : Region rc) (d : Descriptor) (term : NativeTermArena.Layout nc ec) (map : Region mc)
    (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc)
    (image : NativeImage.View) (base : BitVec 48) : Prop where
  rootSpace : External roots term map agenda trail
  descriptor : External d.region term map agenda trail
  rootFrame : Separated roots d.region
  code : ∀ i : Fin rc, CodeApart image base (NativeLiveRoots.slotBytes roots i)

theorem External.kept_graph {outside : Region n} {seen words : Finset ℕ}
    (external : External outside term map agenda trail) (read : Covered outside seen)
    (lengths : Disjoint seen (NativeSubstitutionFrame.mutableBytes d.solver.substitution))
    (graph : Includes term map d.solver.substitution words) : Disjoint seen words := by
  apply Finset.disjoint_left.mpr
  intro byte held wrote
  rcases graph byte wrote with ⟨i, j, node⟩ | ⟨i, child⟩ | ⟨i, entry⟩ | length
  · exact Finset.disjoint_left.mp (Covered.separate external.nodes read (Covered.node term i j)) held node
  · exact Finset.disjoint_left.mp (Covered.separate external.edges read (Covered.edge term i)) held child
  · exact Finset.disjoint_left.mp (Covered.separate external.map read (Covered.word map i)) held entry
  · exact Finset.disjoint_left.mp lengths held length

theorem External.kept_tail {outside : Region n} {seen agendaBytes trailBytes : Finset ℕ} {loA hiA loT hiT : ℕ}
    (external : External outside term map agenda trail) (read : Covered outside seen)
    (agendaWrites : Within agenda loA hiA agendaBytes) (trailWrites : Within trail loT hiT trailBytes) :
    Disjoint seen (trailBytes ∪ agendaBytes ∪ NativeBindingPublish.written agenda trail) :=
  Finset.disjoint_union_right.mpr ⟨
    Finset.disjoint_union_right.mpr ⟨Covered.separate external.trail read (Covered.agendaWrites trailWrites),
      Covered.separate external.agenda read (Covered.agendaWrites agendaWrites)⟩,
    Finset.disjoint_union_right.mpr ⟨Covered.separate external.trail read (Covered.header trail),
      Covered.separate external.agenda read (Covered.header agenda)⟩⟩

theorem descriptor_lengths (d : Descriptor) (i : Fin 18) (nodes : i ≠ 3) (edges : i ≠ 4) :
    Disjoint (footprint (d.cell i).address) (NativeSubstitutionFrame.mutableBytes d.solver.substitution) := by
  unfold NativeSubstitutionFrame.mutableBytes
  rw [d.solver.substitution_cell, d.solver.substitution_cell, d.cell_of_solver, d.cell_of_solver]
  exact Finset.disjoint_union_right.mpr ⟨d.separate_words nodes, d.separate_words edges⟩

theorem root_lengths (d : Descriptor) (apart : Separated roots d.region) (i : Fin rc) :
    Disjoint (footprint ((roots.wordCell i).cell 0).address) (NativeSubstitutionFrame.mutableBytes d.solver.substitution) :=
  Covered.separate apart (Covered.word roots i) ((Covered.table d 3).union (Covered.table d 4))

variable {R : Finset Register} {bytes : Finset ℕ} {before after : Native} {words : Array Word}

theorem Geometry.held_after_graph (space : Geometry roots d term map agenda trail image base)
    (held : Held d roots words before) (run : X86StateFrame.Frame R bytes before after)
    (effects : Includes term map d.solver.substitution bytes) : Held d roots words after :=
  ⟨held.descriptor.kept run
    (space.descriptor.kept_graph (Covered.field d 16) (descriptor_lengths d 16 (by decide) (by decide)) effects)
    (space.descriptor.kept_graph (Covered.field d 17) (descriptor_lengths d 17 (by decide) (by decide)) effects),
    held.words.kept run (fun i => space.rootSpace.kept_graph (Covered.word roots i) (root_lengths d space.rootFrame i) effects)⟩

theorem Geometry.held_after_tail (space : Geometry roots d term map agenda trail image base) {tr ag : Finset ℕ}
    {loA hiA loT hiT : ℕ} (held : Held d roots words before)
    (run : X86StateFrame.Frame R (tr ∪ ag ∪ NativeBindingPublish.written agenda trail) before after)
    (agWrites : Within agenda loA hiA ag) (trWrites : Within trail loT hiT tr) : Held d roots words after :=
  ⟨held.descriptor.kept run (space.descriptor.kept_tail (Covered.field d 16) agWrites trWrites)
    (space.descriptor.kept_tail (Covered.field d 17) agWrites trWrites),
    held.words.kept run (fun i => space.rootSpace.kept_tail (Covered.word roots i) agWrites trWrites)⟩

private theorem keepAgenda {c : ℕ} {layout : NativeAgendaRecords.Layout c} {packed : PackedEquations.Arena}
    (space : Separated layout.words roots) (rootWrites : Covered roots bytes) (run : X86StateFrame.Frame R bytes before after)
    (ready : NativeAgendaRecords.Ready layout packed before) : NativeAgendaRecords.Ready layout packed after :=
  ⟨ready.fits, ready.count.preserved run (Covered.separate space (Covered.header layout) rootWrites),
    fun i j => (ready.node i j).preserved run
      (Covered.separate space (Covered.record layout ⟨i.val, i.isLt.trans_le ready.fits⟩ j) rootWrites)⟩

theorem Geometry.keep_stage (space : Geometry roots d term map agenda trail image base)
    {source : PackedTerms.Arena} {eqs bindings : PackedEquations.Arena} {result : PackedSubstitution.State}
    {cursor name value : Word}
    (stage : Staged term map d.solver agenda trail source eqs bindings result cursor name value before)
    (run : X86StateFrame.Frame (NativeLiveRootEntry.clobbers ∪ NativeLiveRootLoop.clobbers) bytes before after)
    (writes : Covered roots bytes) : Staged term map d.solver agenda trail source eqs bindings result cursor name value after :=
  ⟨stage.extension,
    stage.terms.kept run (fun i j => Covered.separate space.rootSpace.nodes.symm (Covered.node term i j) writes)
      (fun i => Covered.separate space.rootSpace.edges.symm (Covered.edge term i) writes),
    stage.table.kept run (by decide) (fun j => Covered.separate space.rootFrame.symm (Covered.table d j) writes),
    stage.mapping.kept run (fun i => Covered.separate space.rootSpace.map.symm (Covered.word map i) writes),
    keepAgenda space.rootSpace.agenda.symm writes run stage.agendaReady, keepAgenda space.rootSpace.trail.symm writes run stage.trailReady,
    ⟨stage.aux.pool.preserved run (Covered.separate space.rootSpace.agenda.symm (Covered.metadata agenda 1) writes),
      stage.aux.agendaLimit.preserved run (Covered.separate space.rootSpace.agenda.symm (Covered.metadata agenda 2) writes),
      stage.aux.trailLimit.preserved run (Covered.separate space.rootSpace.trail.symm (Covered.metadata trail 2) writes),
      stage.aux.trailPtr.preserved run (Covered.separate space.rootFrame.symm (Covered.solver d 7) writes)⟩,
    (run.lookup 5 (by decide)).trans stage.agendaBase, (run.lookup 7 (by decide)).trans stage.mapBase,
    (run.lookup 8 (by decide)).trans stage.query, (run.lookup 9 (by decide)).trans stage.value,
    (run.lookup 11 (by decide)).trans stage.suffix, (run.lookup 12 (by decide)).trans stage.zero,
    (run.lookup 13 (by decide)).trans stage.one, (run.lookup 15 (by decide)).trans stage.mapLimit⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingRootMemory
