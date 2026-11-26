import Mettapedia.Machines.TIsa.StoreInstructions.NativeArenaGeometry
import Mettapedia.Machines.TIsa.StoreInstructions.NativeUnifierHeaders
import Mettapedia.Machines.TIsa.StoreInstructions.PackedTerms

/-!
# A native arena for packed term headers and child spans

Four consecutive qwords form a node: kind, symbol, first child,
and number of children. Children are term handles in a separate
contiguous array. Capacity is not the number of initialized nodes.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeTermArena

open NativeArenaGeometry (Region)
open PackedTerms (Arena Node)
open X86PlacedMemory (Reads footprint)
open MemoryBinding (Native)

def field (node : Node) (i : Fin 4) : Word :=
  match i.val with
  | 0 => node.header.tag
  | 1 => node.header.symbol
  | 2 => node.childrenAt
  | _ => node.childrenCount

structure Layout (nodeCapacity edgeCapacity : ℕ) where
  nodes : Region (4 * nodeCapacity)
  edges : Region edgeCapacity

variable {nodeCapacity edgeCapacity : ℕ}

def Layout.record (layout : Layout nodeCapacity edgeCapacity) (i : Fin nodeCapacity) : WordRegion.Region 4 :=
  layout.nodes.slice (4 * i.val) 4 (by decide) (by have h := i.isLt; omega) (by decide)

def Layout.header (layout : Layout nodeCapacity edgeCapacity) (i : Fin nodeCapacity) : NativePackedOccurrence.Bank :=
  layout.nodes.slice (4 * i.val) 2 (by decide) (by have h := i.isLt; omega) (by decide)

def Layout.child (layout : Layout nodeCapacity edgeCapacity) (i : Fin edgeCapacity) : WordRegion.Region 1 :=
  layout.edges.slice i.val 1 (by decide) i.isLt (by decide)

theorem Layout.header_at (layout : Layout nodeCapacity edgeCapacity) (i : Fin nodeCapacity) (j : Fin 2) :
    ((layout.header i).cell j).address = ((layout.record i).cell ⟨j.val, by omega⟩).address := by
  simp only [Layout.header, Layout.record, Region.slice_address]

theorem Layout.record_word (layout : Layout nodeCapacity edgeCapacity) (handle : Word)
    (inside : handle.toNat < nodeCapacity) :
    (layout.record ⟨handle.toNat, inside⟩).pointer = layout.nodes.pointer + handle * 32 := by
  change layout.nodes.pointer + BitVec.ofNat 64 (8 * (4 * handle.toNat)) = _
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_mul]
  change 8 * (4 * handle.toNat) % 2 ^ 64 = handle.toNat * 32 % 2 ^ 64
  have size : 8 * (4 * handle.toNat) = handle.toNat * 32 := by omega
  rw [size]

theorem Layout.header_word (layout : Layout nodeCapacity edgeCapacity) (handle : Word)
    (inside : handle.toNat < nodeCapacity) :
    (layout.header ⟨handle.toNat, inside⟩).pointer = layout.nodes.pointer + handle * 32 :=
  layout.record_word handle inside

theorem Layout.separate_records (layout : Layout nodeCapacity edgeCapacity)
    (left right : Fin nodeCapacity) (order : left.val < right.val) (a b : Fin 4) :
    Disjoint (footprint ((layout.record left).cell a).address) (footprint ((layout.record right).cell b).address) :=
  layout.nodes.slices_disjoint _ _ _ _ _ _ _ _ _ _ (by omega) a b

structure Ready (layout : Layout nodeCapacity edgeCapacity) (arena : Arena) (native : Native) : Prop where
  nodesFit : arena.nodes.size ≤ nodeCapacity
  edgesFit : arena.children.size ≤ edgeCapacity
  node : ∀ (i : Fin arena.nodes.size) (j : Fin 4),
    Reads native ((layout.record ⟨i.val, Nat.lt_of_lt_of_le i.isLt nodesFit⟩).cell j).address
      (field arena.nodes[i] j)
  child : ∀ i : Fin arena.children.size,
    Reads native ((layout.child ⟨i.val, Nat.lt_of_lt_of_le i.isLt edgesFit⟩).cell 0).address arena.children[i]

theorem Ready.count_word {layout : Layout nodeCapacity edgeCapacity} {arena : Arena} {native : Native}
    (ready : Ready layout arena native) :
    (BitVec.ofNat 64 arena.nodes.size).toNat = arena.nodes.size := by
  have fit : arena.nodes.size < 2 ^ 64 := by
    have count := ready.nodesFit
    by_cases empty : nodeCapacity = 0
    · omega
    · have limit := layout.nodes.positive_room (show 0 < 4 * nodeCapacity by omega)
      omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]

def Ready.bank {layout : Layout nodeCapacity edgeCapacity} {arena : Arena} {native : Native}
    (ready : Ready layout arena native) (i : Fin arena.nodes.size) : NativePackedOccurrence.Bank :=
  layout.header ⟨i.val, i.isLt.trans_le ready.nodesFit⟩

theorem Ready.bank_word {layout : Layout nodeCapacity edgeCapacity} {arena : Arena} {native : Native}
    (ready : Ready layout arena native) (handle : Word) (inside : handle.toNat < arena.nodes.size) :
    (ready.bank ⟨handle.toNat, inside⟩).pointer = layout.nodes.pointer + handle * 32 :=
  layout.header_word handle (inside.trans_le ready.nodesFit)

theorem Ready.header_read {layout : Layout nodeCapacity edgeCapacity} {arena : Arena} {native : Native}
    (ready : Ready layout arena native) (i : Fin arena.nodes.size) :
    Reads native (NativePackedOccurrence.wordAt (ready.bank i) 0).cell.address arena.nodes[i].header.tag ∧
      Reads native (NativePackedOccurrence.wordAt (ready.bank i) 1).cell.address arena.nodes[i].header.symbol := by
  change Reads native ((ready.bank i).cell 0).address arena.nodes[i].header.tag ∧
    Reads native ((ready.bank i).cell 1).address arena.nodes[i].header.symbol
  simp only [Ready.bank, Layout.header_at]
  exact ⟨ready.node i 0, ready.node i 1⟩

theorem Ready.preserved {layout : Layout nodeCapacity edgeCapacity} {arena : Arena} {before after : Native}
    {registers : Finset _root_.X86Registers.Register} (ready : Ready layout arena before)
    (framed : X86StateFrame.Frame registers ∅ before after) :
    Ready layout arena after :=
  ⟨ready.nodesFit, ready.edgesFit, fun i j => (ready.node i j).preserved framed (by simp),
    fun i => (ready.child i).preserved framed (by simp)⟩

theorem Ready.kept {layout : Layout nodeCapacity edgeCapacity} {arena : Arena} {before after : Native}
    {registers : Finset _root_.X86Registers.Register} {bytes : Finset ℕ} (ready : Ready layout arena before)
    (framed : X86StateFrame.Frame registers bytes before after)
    (nodes : ∀ (i : Fin nodeCapacity) (j : Fin 4), Disjoint (footprint ((layout.record i).cell j).address) bytes)
    (edges : ∀ i : Fin edgeCapacity, Disjoint (footprint ((layout.child i).cell 0).address) bytes) :
    Ready layout arena after :=
  ⟨ready.nodesFit, ready.edgesFit, fun i j => (ready.node i j).preserved framed (nodes _ j),
    fun i => (ready.child i).preserved framed (edges _)⟩

namespace Examples

theorem scaling_alone_can_turn_a_bad_handle_into_zero :
    (BitVec.ofNat 64 (2 ^ 59)) * 32 = 0 ∧ (BitVec.ofNat 64 (2 ^ 59)).toNat ≥ 1 := by decide +kernel

theorem live_bound_is_stricter_than_capacity :
    (0 : Word).toNat < 1 ∧ ¬ (1 : Word).toNat < 1 ∧ (1 : Word).toNat < 4 := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.NativeTermArena
