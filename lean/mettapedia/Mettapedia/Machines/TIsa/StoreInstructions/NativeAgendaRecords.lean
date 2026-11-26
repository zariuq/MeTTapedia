import Mettapedia.Machines.TIsa.StoreInstructions.NativeArenaGeometry
import Mettapedia.Machines.TIsa.StoreInstructions.PackedEquations
import Mettapedia.Machines.TIsa.StoreInstructions.MemoryBinding

/-!
# A packed agenda with a native root cursor

Pending equations are a root into the packed equation graph,
in processing order. Slot zero of the native arena is metadata,
not an equation. Each positive handle names three consecutive
qwords. Popping a node changes only the root cursor.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaRecords

open NativeArenaGeometry (Region)
open PackedEquations (Arena Node readWords)
open X86PlacedMemory (Reads footprint)
open MemoryBinding (Native)
open _root_.X86Registers (Register)

inductive Top
  | empty
  | malformed
  | equation (node : Node)
  deriving DecidableEq, Repr

def top (arena : Arena) (root : Word) : Top :=
  if root.toNat = 0 then .empty
  else
    match arena[root.toNat - 1]? with
    | none => .malformed
    | some node => if node.older.toNat < root.toNat then .equation node else .malformed

theorem top_of_read (arena : Arena) (root : Word) (pending : List (Word × Word))
    (loaded : readWords arena root = some pending) :
    match pending with
    | [] => top arena root = .empty
    | first :: rest => ∃ node, top arena root = .equation node ∧
      (node.left, node.right) = first ∧ readWords arena node.older = some rest := by
  cases cursor : root.toNat with
  | zero =>
    have empty : pending = [] := by
      simpa only [readWords, PackedEquations.read, cursor, PackedEquations.readAux, Option.some.injEq, eq_comm] using loaded
    subst pending
    simp [top, cursor]
  | succ slot =>
    have position : root.toNat - 1 = slot := by omega
    cases found : arena[slot]? with
    | none => simp [readWords, PackedEquations.read, cursor, PackedEquations.readAux, found] at loaded
    | some node =>
      by_cases descends : node.older.toNat < root.toNat
      · have present : arena[root.toNat - 1]? = some node := by simpa only [position] using found
        have uncons := PackedEquations.read_link PackedEquations.wordCodes arena root node (by omega) present descends
        cases tail : readWords arena node.older with
        | none =>
          rw [readWords, uncons] at loaded
          rw [show PackedEquations.read PackedEquations.wordCodes arena node.older = none from tail] at loaded
          simp [PackedEquations.word_decode] at loaded
        | some rest =>
          have ordered : (node.left, node.right) :: rest = pending := by
            rw [readWords, uncons] at loaded
            rw [show PackedEquations.read PackedEquations.wordCodes arena node.older = some rest from tail] at loaded
            simpa [PackedEquations.word_decode] using loaded
          subst pending
          refine ⟨node, ?_, rfl, tail⟩
          simp [top, position, found, descends, show root.toNat ≠ 0 by omega]
      · have noStep : ¬node.older.toNat < slot + 1 := by omega
        simp [readWords, PackedEquations.read, cursor, PackedEquations.readAux, found, noStep] at loaded

def field (node : Node) (i : Fin 3) : Word :=
  match i.val with
  | 0 => node.older
  | 1 => node.left
  | _ => node.right

structure Layout (capacity : ℕ) where
  words : Region (3 * (capacity + 1))

variable {capacity : ℕ}

def Layout.header (layout : Layout capacity) : WordRegion.Region 1 :=
  layout.words.slice 0 1 (by decide) (by omega) (by decide)

/-- The reserved slot also stores the child arena base. Its
immutable pointer is separate from the mutable equation count. -/
def Layout.metadata (layout : Layout capacity) : WordRegion.Region 3 :=
  layout.words.slice 0 3 (by decide) (by omega) (by decide)

theorem Layout.count_child_base_apart (layout : Layout capacity) :
    Disjoint (footprint (layout.header.cell 0).address) (footprint (layout.metadata.cell 1).address) := by
  have count : (layout.header.cell 0).address = (layout.metadata.cell 0).address := by
    simp only [Layout.header, Layout.metadata, Region.slice_address]
    rfl
  rw [count]
  exact layout.metadata.separate_words (by decide)

theorem Layout.header_pointer (layout : Layout capacity) : layout.header.pointer = layout.words.pointer := by
  change layout.words.pointer + BitVec.ofNat 64 0 = _
  exact BitVec.add_zero _

def Layout.record (layout : Layout capacity) (i : Fin capacity) : WordRegion.Region 3 :=
  layout.words.slice (3 * (i.val + 1)) 3 (by decide) (by have h := i.isLt; omega) (by decide)

theorem Layout.record_pointer (layout : Layout capacity) (root : Word) (index : Fin capacity)
    (indexOf : root.toNat = index.val + 1) :
    (layout.record index).pointer = layout.words.pointer + root * 24 := by
  change layout.words.pointer + BitVec.ofNat 64 (8 * (3 * (index.val + 1))) = _
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_mul]
  change (8 * (3 * (index.val + 1))) % 2 ^ 64 = (root.toNat * 24) % 2 ^ 64
  rw [indexOf, show 8 * (3 * (index.val + 1)) = (index.val + 1) * 24 by omega]

theorem Layout.header_apart (layout : Layout capacity) (i : Fin capacity) (j : Fin 3) :
    Disjoint (footprint (layout.header.cell 0).address) (footprint ((layout.record i).cell j).address) :=
  layout.words.slices_disjoint _ _ _ _ _ _ _ _ _ _ (by omega) 0 j

theorem Layout.records_apart (layout : Layout capacity) (i k : Fin capacity) (q : i.val < k.val)
    (j l : Fin 3) :
    Disjoint (footprint ((layout.record i).cell j).address) (footprint ((layout.record k).cell l).address) :=
  layout.words.slices_disjoint _ _ _ _ _ _ _ _ _ _ (by omega) j l

/-- Private records may already have been written even though the
length visible in the metadata has not been published yet. -/
structure Records (layout : Layout capacity) (arena : Arena) (before : Native) : Prop where
  fits : arena.size ≤ capacity
  node : ∀ (i : Fin arena.size) (j : Fin 3),
    Reads before ((layout.record ⟨i.val, i.isLt.trans_le fits⟩).cell j).address (field arena[i] j)

structure Ready (layout : Layout capacity) (arena : Arena) (before : Native) : Prop where
  fits : arena.size ≤ capacity
  count : Reads before (layout.header.cell 0).address (BitVec.ofNat 64 arena.size)
  node : ∀ (i : Fin arena.size) (j : Fin 3),
    Reads before ((layout.record ⟨i.val, i.isLt.trans_le fits⟩).cell j).address (field arena[i] j)

theorem Ready.records {layout : Layout capacity} {arena : Arena} {before : Native}
    (ready : Ready layout arena before) : Records layout arena before :=
  ⟨ready.fits, ready.node⟩

theorem Ready.count_word {layout : Layout capacity} {arena : Arena} {before : Native} (ready : Ready layout arena before) :
    (BitVec.ofNat 64 arena.size).toNat = arena.size := by
  have range := layout.words.positive_room (show 0 < 3 * (capacity + 1) by omega)
  have fits := ready.fits
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem Ready.preserved {layout : Layout capacity} {arena : Arena} {before after : Native}
    {effects : Finset Register} (ready : Ready layout arena before)
    (frame : X86StateFrame.Frame effects ∅ before after) :
    Ready layout arena after :=
  ⟨ready.fits, ready.count.preserved frame (by simp), fun i j => (ready.node i j).preserved frame (by simp)⟩

namespace Examples

theorem zero_is_not_an_equation_even_with_a_live_node :
    top #[⟨0, 5, 7⟩] 0 = .empty := by decide +kernel

theorem zero_is_a_valid_term_handle_inside_the_agenda :
    top #[⟨0, 0, 7⟩] 1 = .equation ⟨0, 0, 7⟩ := by decide +kernel

theorem a_non_descending_link_is_not_a_logical_conflict :
    top #[⟨1, 5, 7⟩] 1 = .malformed := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaRecords
