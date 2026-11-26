import Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionCommit

/-!
# Physical separation for staging one native remap

Disjoint canonical ranges, rather than assumed effects of a
rewrite, justify retaining the other initialized views.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionMemory

open X86PlacedMemory (footprint CodeApart)
open NativeArenaGeometry (Region)
open NativeBindingSelection (Separated)
open NativeSubstitutionFrame (Table region mutableBytes)
open NativeTermAppend (remapRegisters)

variable {nodeCapacity edgeCapacity mapCapacity agendaCapacity : ℕ}
variable {layout : NativeTermArena.Layout nodeCapacity edgeCapacity}
variable {map : Region mapCapacity} {frame : Table} {agenda : NativeAgendaRecords.Layout agendaCapacity}

def nodeBytes (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (i : Fin nodeCapacity) (j : Fin 4) : Finset ℕ :=
  footprint ((layout.record i).cell j).address

def edgeBytes (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (i : Fin edgeCapacity) : Finset ℕ :=
  footprint ((layout.child i).cell 0).address

def mapBytes (map : Region mapCapacity) (i : Fin mapCapacity) : Finset ℕ :=
  footprint ((map.wordCell i).cell 0).address

def frameBytes (frame : Table) (i : Fin 7) : Finset ℕ := footprint (frame.cell i).address

def poolBytes (agenda : NativeAgendaRecords.Layout agendaCapacity) : Finset ℕ :=
  footprint (agenda.metadata.cell 1).address

structure Geometry (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (map : Region mapCapacity)
    (frame : Table) (agenda : NativeAgendaRecords.Layout agendaCapacity) (image : NativeImage.View) (base : BitVec 48) : Prop where
  nodeCode : ∀ i j, CodeApart image base (nodeBytes layout i j)
  edgeCode : ∀ i, CodeApart image base (edgeBytes layout i)
  mapCode : ∀ i, CodeApart image base (mapBytes map i)
  lengthCode : CodeApart image base (mutableBytes frame)
  nodeEdge : Separated layout.nodes layout.edges
  nodeMap : Separated layout.nodes map
  nodeFrame : Separated layout.nodes (region frame)
  edgeMap : Separated layout.edges map
  edgeFrame : Separated layout.edges (region frame)
  mapFrame : Separated map (region frame)
  agendaNode : Separated agenda.words layout.nodes
  agendaEdge : Separated agenda.words layout.edges
  agendaMap : Separated agenda.words map
  agendaFrame : Separated agenda.words (region frame)

private theorem frameAddress (frame : Table) (i : Fin 7) :
    (((region frame).slice 0 7 (by decide) (by decide) (by decide)).cell i).address = (frame.cell i).address := by
  rw [Region.slice_address]
  change X86CanonicalSpan.narrow (frame.pointer + BitVec.ofNat 64 (8 * (0 + i.val))) = _
  rw [Nat.zero_add]
  rfl

variable {image : NativeImage.View} {base : BitVec 48}

theorem Geometry.node_edge (h : Geometry layout map frame agenda image base)
    (i : Fin nodeCapacity) (j : Fin 4) (e : Fin edgeCapacity) :
    Disjoint (nodeBytes layout i j) (edgeBytes layout e) :=
  layout.nodes.separate_arenas layout.edges h.nodeEdge (4 * i.val) 4 e.val 1
    (by decide) (by decide) (by have bound := i.isLt; omega) e.isLt (by decide) (by decide) j 0

theorem Geometry.node_map (h : Geometry layout map frame agenda image base)
    (i : Fin nodeCapacity) (j : Fin 4) (m : Fin mapCapacity) :
    Disjoint (nodeBytes layout i j) (mapBytes map m) :=
  layout.nodes.separate_arenas map h.nodeMap (4 * i.val) 4 m.val 1
    (by decide) (by decide) (by have bound := i.isLt; omega) m.isLt (by decide) (by decide) j 0

theorem Geometry.node_frame (h : Geometry layout map frame agenda image base)
    (i : Fin nodeCapacity) (j : Fin 4) (f : Fin 7) :
    Disjoint (nodeBytes layout i j) (frameBytes frame f) := by
  unfold frameBytes
  rw [← frameAddress frame f]
  exact layout.nodes.separate_arenas (region frame) h.nodeFrame (4 * i.val) 4 0 7
    (by decide) (by decide) (by have bound := i.isLt; omega) (by decide) (by decide) (by decide) j f

theorem Geometry.edge_map (h : Geometry layout map frame agenda image base) (e : Fin edgeCapacity) (m : Fin mapCapacity) :
    Disjoint (edgeBytes layout e) (mapBytes map m) :=
  layout.edges.separate_arenas map h.edgeMap e.val 1 m.val 1 (by decide) (by decide) e.isLt m.isLt (by decide) (by decide) 0 0

theorem Geometry.edge_frame (h : Geometry layout map frame agenda image base) (e : Fin edgeCapacity) (f : Fin 7) :
    Disjoint (edgeBytes layout e) (frameBytes frame f) := by
  unfold frameBytes
  rw [← frameAddress frame f]
  exact layout.edges.separate_arenas (region frame) h.edgeFrame e.val 1 0 7 (by decide) (by decide)
    e.isLt (by decide) (by decide) (by decide) 0 f

theorem Geometry.map_frame (h : Geometry layout map frame agenda image base) (m : Fin mapCapacity) (f : Fin 7) :
    Disjoint (mapBytes map m) (frameBytes frame f) := by
  unfold frameBytes
  rw [← frameAddress frame f]
  exact map.separate_arenas (region frame) h.mapFrame m.val 1 0 7 (by decide) (by decide)
    m.isLt (by decide) (by decide) (by decide) 0 f

theorem Geometry.pool_node (h : Geometry layout map frame agenda image base) (i : Fin nodeCapacity) (j : Fin 4) :
    Disjoint (poolBytes agenda) (nodeBytes layout i j) :=
  agenda.words.separate_arenas layout.nodes h.agendaNode 0 3 (4 * i.val) 4 (by decide) (by decide)
    (by omega) (by have bound := i.isLt; omega) (by decide) (by decide) 1 j

theorem Geometry.pool_edge (h : Geometry layout map frame agenda image base) (e : Fin edgeCapacity) :
    Disjoint (poolBytes agenda) (edgeBytes layout e) :=
  agenda.words.separate_arenas layout.edges h.agendaEdge 0 3 e.val 1 (by decide) (by decide)
    (by omega) e.isLt (by decide) (by decide) 1 0

theorem Geometry.pool_map (h : Geometry layout map frame agenda image base) (m : Fin mapCapacity) :
    Disjoint (poolBytes agenda) (mapBytes map m) :=
  agenda.words.separate_arenas map h.agendaMap 0 3 m.val 1 (by decide) (by decide)
    (by omega) m.isLt (by decide) (by decide) 1 0

theorem Geometry.pool_frame (h : Geometry layout map frame agenda image base) (f : Fin 7) :
    Disjoint (poolBytes agenda) (frameBytes frame f) := by
  unfold frameBytes
  rw [← frameAddress frame f]
  exact agenda.words.separate_arenas (region frame) h.agendaFrame 0 3 0 7 (by decide) (by decide)
    (by omega) (by decide) (by decide) (by decide) 1 f

theorem Geometry.copy (h : Geometry layout map frame agenda image base) : NativeRemapCopy.Geometry layout map image base :=
  ⟨h.edgeCode, h.node_edge, fun m e => (h.edge_map e m).symm⟩

theorem Geometry.commit (h : Geometry layout map frame agenda image base) :
    NativeSubstitutionCommit.Geometry map frame image base :=
  ⟨h.mapCode, h.lengthCode, h.map_frame⟩

theorem append_apart (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (target : PackedTerms.Arena)
    (room : target.nodes.size < nodeCapacity) (node : PackedTerms.Node) (held : Finset ℕ)
    (separate : ∀ col, Disjoint held (nodeBytes layout ⟨target.nodes.size, room⟩ col)) :
    Disjoint held (NativeTermAppend.bytesOf remapRegisters layout target room node) := by
  apply NativeStores.apart_written
  intro w member
  obtain ⟨j, rfl⟩ := NativeTermAppend.field_members member
  exact separate j

theorem append_code (h : Geometry layout map frame agenda image base) (target : PackedTerms.Arena)
    (room : target.nodes.size < nodeCapacity) (node : PackedTerms.Node) :
    CodeApart image base (NativeTermAppend.bytesOf remapRegisters layout target room node) := by
  intro i byte present
  have every (j : Fin 4) : Disjoint {((Mettapedia.Machines.TIsa.X86Execution.address base.toInt i).signExtend 52).toNat}
      (nodeBytes layout ⟨target.nodes.size, room⟩ j) :=
    Finset.disjoint_singleton_left.mpr (h.nodeCode _ j i byte present)
  exact Finset.disjoint_singleton_left.mp (append_apart layout target room node _ every)

def Includes (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (map : Region mapCapacity)
    (frame : Table) (changed : Finset ℕ) : Prop :=
  ∀ byte ∈ changed,
    (∃ i j, byte ∈ nodeBytes layout i j) ∨
      (∃ e, byte ∈ edgeBytes layout e) ∨ (∃ i, byte ∈ mapBytes map i) ∨ byte ∈ mutableBytes frame

theorem Includes.empty (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (map : Region mapCapacity) (frame : Table) :
    Includes layout map frame ∅ := by simp [Includes]

theorem Includes.union {first second : Finset ℕ} (left : Includes layout map frame first)
    (right : Includes layout map frame second) : Includes layout map frame (first ∪ second) := by
  intro b touched
  exact (Finset.mem_union.mp touched).elim (left b) (right b)

theorem Includes.map_only (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (map : Region mapCapacity)
    (frame : Table) (slot : Fin mapCapacity) : Includes layout map frame (mapBytes map slot) :=
  fun _ hit => Or.inr (Or.inr (Or.inl ⟨slot, hit⟩))

private theorem one_of_stores {pointer : Word} (stores : List (NativeStores.Write pointer)) (byte : ℕ)
    (touched : byte ∈ NativeStores.written stores) :
    ∃ write ∈ stores, byte ∈ footprint write.cell.address := by
  induction stores with
  | nil => simp [NativeStores.written] at touched
  | cons front rest ih =>
    simp only [NativeStores.written, Finset.mem_union] at touched
    rcases touched with direct | later
    · exact ⟨front, List.mem_cons_self, direct⟩
    · obtain ⟨write, present, live⟩ := ih later
      exact ⟨write, List.mem_cons_of_mem _ present, live⟩

theorem Includes.appending (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (map : Region mapCapacity)
    (frame : Table) (target : PackedTerms.Arena) (room : target.nodes.size < nodeCapacity) (node : PackedTerms.Node) :
    Includes layout map frame (NativeTermAppend.bytesOf remapRegisters layout target room node) := by
  intro byte touched
  obtain ⟨w, member, cell⟩ := one_of_stores _ byte touched
  obtain ⟨col, rfl⟩ := NativeTermAppend.field_members member
  exact Or.inl ⟨⟨target.nodes.size, room⟩, col, cell⟩

theorem Includes.edges {writes : Finset ℕ} {lo hi : ℕ} (copy : NativeMarkTable.Within layout.edges lo hi writes) :
    Includes layout map frame writes := by
  intro byte touched
  obtain ⟨i, _, _, atCell⟩ := copy byte touched
  exact Or.inr (Or.inl ⟨i, atCell⟩)

theorem Includes.lengths (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (map : Region mapCapacity) (frame : Table) :
    Includes layout map frame (mutableBytes frame) :=
  fun _ hit => Or.inr (Or.inr (Or.inr hit))

theorem Geometry.agenda_slice_apart (h : Geometry layout map frame agenda image base)
    (offset width : ℕ) (positive : 0 < width) (inside : offset + width ≤ 3 * (agendaCapacity + 1))
    (short : 8 * width ≤ 2 ^ 31) (field : Fin width) {writes : Finset ℕ}
    (privateWrites : Includes layout map frame writes) :
    Disjoint (footprint ((agenda.words.slice offset width positive inside short).cell field).address) writes := by
  apply Finset.disjoint_left.mpr
  intro byte held modified
  rcases privateWrites byte modified with ⟨i, j, node⟩ | ⟨e, edge⟩ | ⟨m, mapped⟩ | length
  · exact Finset.disjoint_left.mp
      (agenda.words.separate_arenas layout.nodes h.agendaNode offset width (4 * i.val) 4 positive (by decide) inside
        (by have bound := i.isLt; omega) short (by decide) field j) held node
  · exact Finset.disjoint_left.mp
      (agenda.words.separate_arenas layout.edges h.agendaEdge offset width e.val 1 positive (by decide)
        inside e.isLt short (by decide) field 0) held edge
  · exact Finset.disjoint_left.mp
      (agenda.words.separate_arenas map h.agendaMap offset width m.val 1 positive (by decide)
        inside m.isLt short (by decide) field 0) held mapped
  · have apart (i : Fin 7) :
        Disjoint (footprint ((agenda.words.slice offset width positive inside short).cell field).address)
          (frameBytes frame i) := by
      unfold frameBytes
      rw [← frameAddress frame i]
      exact agenda.words.separate_arenas (region frame) h.agendaFrame offset width 0 7 positive (by decide)
        inside (by decide) short (by decide) field i
    rcases Finset.mem_union.mp length with nodes | edges
    · exact Finset.disjoint_left.mp (apart NativeSubstitutionFrame.nodeCount) held nodes
    · exact Finset.disjoint_left.mp (apart NativeSubstitutionFrame.edgeCount) held edges

theorem Geometry.agenda_kept (h : Geometry layout map frame agenda image base)
    {equations : PackedEquations.Arena} {before after : MemoryBinding.Native} {regs : Finset _root_.X86Registers.Register}
    {writes : Finset ℕ} (ready : NativeAgendaRecords.Ready agenda equations before)
    (run : X86StateFrame.Frame regs writes before after) (privateWrites : Includes layout map frame writes) :
    NativeAgendaRecords.Ready agenda equations after := by
  refine ⟨ready.fits, ready.count.preserved run ?_, fun i j => (ready.node i j).preserved run ?_⟩
  · exact h.agenda_slice_apart 0 1 (by decide) (by omega) (by decide) 0 privateWrites
  · have bound := i.isLt.trans_le ready.fits
    exact h.agenda_slice_apart (3 * (i.val + 1)) 3 (by decide) (by omega) (by decide) j privateWrites

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionMemory
