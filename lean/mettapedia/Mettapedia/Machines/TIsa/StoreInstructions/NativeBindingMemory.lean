import Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingPublish
import Mettapedia.Machines.TIsa.StoreInstructions.NativeBoundSubstitution

/-!
# Separation of the native binding regions

Term records, their edge array, scratch, the stack descriptor,
the agenda and the trail occupy different canonical arenas.
Framing a write needs only its destination interval, even
when the interval was filled in descending order.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingMemory

open _root_.X86Registers (Register)
open NativeTrailReserve (Descriptor)
open NativeArenaGeometry (Region)
open NativeBindingSelection (Separated)
open NativeSubstitutionMemory (nodeBytes edgeBytes mapBytes Includes)
open NativeAgendaRecords (Ready Records)
open NativeAgendaRecords renaming Layout → PackedLayout
open NativeAgendaLoop (Within)
open X86PlacedMemory (footprint CodeApart)
open MemoryBinding (Native)

variable {nc ec mc ac tc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {frame : Descriptor}
variable {agenda : PackedLayout ac} {trail : PackedLayout tc} {image : NativeImage.View} {base : BitVec 48}

structure Geometry (term : NativeTermArena.Layout nc ec) (map : Region mc) (frame : Descriptor)
    (agenda : PackedLayout ac) (trail : PackedLayout tc) (image : NativeImage.View) (base : BitVec 48) : Prop where
  substitute : NativeSubstitutionMemory.Geometry term map frame.substitution agenda image base
  agendaCode : ∀ i j, CodeApart image base (footprint ((agenda.record i).cell j).address)
  trailCode : ∀ i j, CodeApart image base (footprint ((trail.record i).cell j).address)
  agendaHeader : CodeApart image base (NativeBindingPublish.header agenda)
  trailHeader : CodeApart image base (NativeBindingPublish.header trail)
  trailAgenda : Separated trail.words agenda.words
  trailNode : Separated trail.words term.nodes
  trailEdge : Separated trail.words term.edges
  trailMap : Separated trail.words map
  trailFrame : Separated trail.words frame.region
  agendaFrame : Separated agenda.words frame.region
  frameNode : Separated frame.region term.nodes
  frameEdge : Separated frame.region term.edges
  frameMap : Separated frame.region map

theorem Geometry.fillGeometry (geometry : Geometry term map frame agenda trail image base) :
    NativePendingFill.Geometry agenda map image base := ⟨geometry.agendaCode, geometry.substitute.agendaMap⟩

theorem Geometry.trailGeometry (geometry : Geometry term map frame agenda trail image base) :
    NativeBindingTrail.Geometry trail frame image base := ⟨geometry.trailCode, geometry.trailFrame⟩

theorem Geometry.forTrail (geometry : Geometry term map frame agenda trail image base) :
    NativeSubstitutionMemory.Geometry term map frame.substitution trail image base := by
  have physical := geometry.trailFrame
  unfold Separated at physical
  change trail.words.pointer.toNat + 8 * (3 * (tc + 1)) ≤ frame.pointer.toNat ∨
    frame.pointer.toNat + 8 * 8 ≤ trail.words.pointer.toNat at physical
  have reduced : Separated trail.words (NativeSubstitutionFrame.region frame.substitution) := by
    unfold Separated
    change trail.words.pointer.toNat + 8 * (3 * (tc + 1)) ≤ frame.substitution.pointer.toNat ∨
      frame.substitution.pointer.toNat + 8 * 7 ≤ trail.words.pointer.toNat
    rw [frame.substitution_pointer]
    omega
  have support := geometry.substitute
  exact ⟨support.nodeCode, support.edgeCode, support.mapCode, support.lengthCode, support.nodeEdge, support.nodeMap,
    support.nodeFrame, support.edgeMap, support.edgeFrame, support.mapFrame, geometry.trailNode, geometry.trailEdge,
    geometry.trailMap, reduced⟩

theorem frame_as_slice (frame : Descriptor) (i : Fin 8) :
    ((frame.region.slice 0 8 (by decide) (by decide) (by decide)).cell i).address = (frame.cell i).address := by
  rw [Region.slice_address, Nat.zero_add]
  rfl

theorem Geometry.trailPointer_apart (geometry : Geometry term map frame agenda trail image base)
    {bytes : Finset ℕ} (privateWrites : Includes term map frame.substitution bytes) :
    Disjoint (footprint (frame.cell 7).address) bytes := by
  apply Finset.disjoint_left.mpr
  intro byte held written
  rcases privateWrites byte written with ⟨i, j, node⟩ | ⟨i, child⟩ | ⟨i, mapped⟩ | length
  · rw [← frame_as_slice] at held
    exact Finset.disjoint_left.mp
      (frame.region.separate_arenas term.nodes geometry.frameNode 0 8 (4 * i.val) 4
        (by decide) (by decide) (by decide) (by have bound := i.isLt; omega) (by decide) (by decide) 7 j) held node
  · rw [← frame_as_slice] at held
    exact Finset.disjoint_left.mp
      (frame.region.separate_arenas term.edges geometry.frameEdge 0 8 i.val 1
        (by decide) (by decide) (by decide) i.isLt (by decide) (by decide) 7 0) held child
  · rw [← frame_as_slice] at held
    exact Finset.disjoint_left.mp
      (frame.region.separate_arenas map geometry.frameMap 0 8 i.val 1
        (by decide) (by decide) (by decide) i.isLt (by decide) (by decide) 7 0) held mapped
  · simp only [NativeSubstitutionFrame.mutableBytes, Finset.mem_union] at length
    rcases length with nodes | edges
    · rw [frame.substitution_cell] at nodes
      exact Finset.disjoint_left.mp (frame.separate_words (by decide : (7 : Fin 8) ≠ 3)) held nodes
    · rw [frame.substitution_cell] at edges
      exact Finset.disjoint_left.mp (frame.separate_words (by decide : (7 : Fin 8) ≠ 4)) held edges

section TwoPacked

variable {a b : ℕ} {first : PackedLayout a} {second : PackedLayout b}
variable {left right : Native} {registers : Finset Register} {writes : Finset ℕ} {lo hi : ℕ}

theorem header_apart (privateAreas : Separated first.words second.words) :
    Disjoint (NativeBindingPublish.header first) (NativeBindingPublish.header second) :=
  first.words.separate_arenas second.words privateAreas 0 1 0 1 (by decide) (by decide) (by omega) (by omega)
    (by decide) (by decide) 0 0

theorem record_header_apart (privateAreas : Separated first.words second.words) (i : Fin a) (j : Fin 3) :
    Disjoint (footprint ((first.record i).cell j).address) (NativeBindingPublish.header second) :=
  first.words.separate_arenas second.words privateAreas (3 * (i.val + 1)) 3 0 1
    (by decide) (by decide) (by have bound := i.isLt; omega) (by omega) (by decide) (by decide) j 0

theorem meta_header_apart (privateAreas : Separated first.words second.words) (j : Fin 3) :
    Disjoint (footprint (first.metadata.cell j).address) (NativeBindingPublish.header second) :=
  first.words.separate_arenas second.words privateAreas 0 3 0 1 (by decide) (by decide) (by omega) (by omega)
    (by decide) (by decide) j 0

theorem meta_apart (privateAreas : Separated first.words second.words)
    (j : Fin 3) (effects : Within second lo hi writes) :
    Disjoint (footprint (first.metadata.cell j).address) writes :=
  NativePendingFill.Within.separate effects _ (fun i col _ _ => first.words.separate_arenas second.words privateAreas
    0 3 (3 * (i.val + 1)) 3 (by decide) (by decide) (by omega) (by have bound := i.isLt; omega)
    (by decide) (by decide) j col)

theorem meta_kept (j : Fin 3) (effects : Within first lo hi writes) :
    Disjoint (footprint (first.metadata.cell j).address) writes :=
  NativePendingFill.Within.separate effects _ (fun i col _ _ => first.words.slices_disjoint
    0 3 (3 * (i.val + 1)) 3 (by decide) (by decide) (by omega) (by have bound := i.isLt; omega)
    (by decide) (by decide) (by omega) j col)

theorem meta_immutable (layout : PackedLayout a) (j : Fin 3) (away : j ≠ 0) :
    Disjoint (footprint (layout.metadata.cell j).address) (NativeBindingPublish.header layout) := by
  have header : (layout.header.cell 0).address = (layout.metadata.cell 0).address := by
    simp only [NativeAgendaRecords.Layout.header, NativeAgendaRecords.Layout.metadata, Region.slice_address]
    rfl
  unfold NativeBindingPublish.header
  rw [header]
  exact layout.metadata.separate_words away

theorem keep_records (privateAreas : Separated first.words second.words) (effects : Within second lo hi writes)
    (execution : X86StateFrame.Frame registers writes left right) {arena : PackedEquations.Arena}
    (ready : Records first arena left) : Records first arena right := by
  refine ⟨ready.fits, fun i j => (ready.node i j).preserved execution ?_⟩
  apply NativePendingFill.Within.separate effects
  intro k col _ _
  have hi := i.isLt.trans_le ready.fits
  exact first.words.separate_arenas second.words privateAreas (3 * (i.val + 1)) 3 (3 * (k.val + 1)) 3
    (by decide) (by decide) (by omega) (by have bound := k.isLt; omega) (by decide) (by decide) j col

theorem keep_ready (privateAreas : Separated first.words second.words) (effects : Within second lo hi writes)
    (execution : X86StateFrame.Frame registers writes left right) {arena : PackedEquations.Arena}
    (ready : Ready first arena left) : Ready first arena right := by
  have records := keep_records privateAreas effects execution ready.records
  refine ⟨ready.fits, ready.count.preserved execution ?_, records.node⟩
  apply NativePendingFill.Within.separate effects
  intro i j _ _
  exact first.words.separate_arenas second.words privateAreas 0 1 (3 * (i.val + 1)) 3
    (by decide) (by decide) (by omega) (by have bound := i.isLt; omega) (by decide) (by decide) 0 j

end TwoPacked

section Regions

variable {a : ℕ} {writtenArena : PackedLayout a} {lo hi : ℕ} {writes : Finset ℕ}
variable {left right : Native} {registers : Finset Register}

theorem frame_record (apart : Separated writtenArena.words frame.region) (j : Fin 8) (i : Fin a) (col : Fin 3) :
    Disjoint (footprint (frame.cell j).address) (footprint ((writtenArena.record i).cell col).address) := by
  rw [← frame_as_slice]
  exact (writtenArena.words.separate_arenas frame.region apart (3 * (i.val + 1)) 3 0 8 (by decide) (by decide)
    (by have bound := i.isLt; omega) (by decide) (by decide) (by decide) col j).symm

theorem frame_header (apart : Separated writtenArena.words frame.region) (j : Fin 8) :
    Disjoint (footprint (frame.cell j).address) (NativeBindingPublish.header writtenArena) := by
  rw [← frame_as_slice]
  exact (writtenArena.words.separate_arenas frame.region apart 0 1 0 8 (by decide) (by decide)
    (by omega) (by decide) (by decide) (by decide) 0 j).symm

theorem keep_staged (apart : Separated writtenArena.words frame.region) (fresh : Within writtenArena lo hi writes)
    (run : X86StateFrame.Frame registers writes left right) (stack : X86RegisterRefinement.key (4 : Fin 16) ∉ registers)
    {terms : PackedTerms.Arena} (held : NativeSubstitutionFrame.Ready term map frame.substitution terms left) :
    NativeSubstitutionFrame.Ready term map frame.substitution terms right :=
  held.kept run stack (fun j => by rw [frame.substitution_cell]; exact
    NativePendingFill.Within.separate fresh _ (fun i col _ _ => frame_record apart _ i col))

theorem keep_terms (nodes : Separated writtenArena.words term.nodes) (edges : Separated writtenArena.words term.edges)
    (fresh : Within writtenArena lo hi writes) (run : X86StateFrame.Frame registers writes left right)
    {terms : PackedTerms.Arena} (ready : NativeTermArena.Ready term terms left) : NativeTermArena.Ready term terms right :=
  ready.kept run (fun i j => NativePendingFill.Within.separate fresh _ (fun d col _ _ =>
    (writtenArena.words.separate_arenas term.nodes nodes (3 * (d.val + 1)) 3 (4 * i.val) 4
      (by decide) (by decide) (by have bound := d.isLt; omega) (by have bound := i.isLt; omega)
      (by decide) (by decide) col j).symm))
    (fun i => NativePendingFill.Within.separate fresh _ (fun d col _ _ =>
      (writtenArena.words.separate_arenas term.edges edges (3 * (d.val + 1)) 3 i.val 1
        (by decide) (by decide) (by have bound := d.isLt; omega) i.isLt (by decide) (by decide) col 0).symm))

private theorem nodes_header (apart : Separated writtenArena.words term.nodes) (i : Fin nc) (j : Fin 4) :
    Disjoint (nodeBytes term i j) (NativeBindingPublish.header writtenArena) :=
  (writtenArena.words.separate_arenas term.nodes apart 0 1 (4 * i.val) 4 (by decide) (by decide)
    (by omega) (by have bound := i.isLt; omega) (by decide) (by decide) 0 j).symm

private theorem edges_header (apart : Separated writtenArena.words term.edges) (i : Fin ec) :
    Disjoint (edgeBytes term i) (NativeBindingPublish.header writtenArena) :=
  (writtenArena.words.separate_arenas term.edges apart 0 1 i.val 1 (by decide) (by decide)
    (by omega) i.isLt (by decide) (by decide) 0 0).symm

end Regions

theorem Geometry.publishGeometry (geometry : Geometry term map frame agenda trail image base) :
    NativeBindingPublish.Geometry term agenda trail frame image base :=
  ⟨geometry.agendaHeader, geometry.trailHeader, header_apart geometry.trailAgenda,
    record_header_apart geometry.trailAgenda.symm, record_header_apart geometry.trailAgenda,
    fun i j => Finset.disjoint_union_right.mpr ⟨nodes_header geometry.trailNode i j, nodes_header geometry.substitute.agendaNode i j⟩,
    fun i => Finset.disjoint_union_right.mpr ⟨edges_header geometry.trailEdge i, edges_header geometry.substitute.agendaEdge i⟩,
    fun j => Finset.disjoint_union_right.mpr ⟨frame_header geometry.trailFrame j, frame_header geometry.agendaFrame j⟩⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingMemory
