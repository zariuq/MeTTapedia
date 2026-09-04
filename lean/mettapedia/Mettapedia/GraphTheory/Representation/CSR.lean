import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mettapedia.GraphTheory.Representation.Basic

/-!
# Compressed sparse row presentation

CSR stores every neighbour occurrence in one packed array and uses an offset
table to delimit each vertex row.  It is the cache-oriented refinement of
adjacency rows: row traversal remains degree-local, while dynamic insertion
is intentionally not hidden by the interface.
-/

namespace Mettapedia.GraphTheory.Representation.CSR

open Mettapedia.GraphTheory.Representation

/-- Concatenate a finite family of adjacency rows into one packed payload. -/
def packRows {n : Nat} (rows : Fin n → List (Fin n)) : List (Fin n) :=
  (List.ofFn rows).flatten

/-- Prefix length delimiting the packed rows before one vertex index. -/
def packOffset {n : Nat} (rows : Fin n → List (Fin n))
    (index : Fin (n + 1)) : Nat :=
  ((List.ofFn rows).take index).flatten.length

theorem packOffset_zero {n : Nat} (rows : Fin n → List (Fin n)) :
    packOffset rows ⟨0, Nat.zero_lt_succ n⟩ = 0 := by
  simp [packOffset]

theorem packOffset_mono {n : Nat} (rows : Fin n → List (Fin n)) :
    Monotone (packOffset rows) := by
  intro first second order
  change ((List.ofFn rows).take first).flatten.length ≤
    ((List.ofFn rows).take second).flatten.length
  apply List.IsPrefix.length_le
  apply List.IsPrefix.flatten
  rw [show (List.ofFn rows).take first =
      ((List.ofFn rows).take second).take first by
    rw [List.take_take, Nat.min_eq_left order]]
  exact List.take_prefix first ((List.ofFn rows).take second)

theorem packOffset_last {n : Nat} (rows : Fin n → List (Fin n)) :
    packOffset rows ⟨n, Nat.lt_succ_self n⟩ = (packRows rows).length := by
  simp only [packOffset, packRows, List.length_flatten, List.map_take]
  rw [List.take_of_length_le (by simp)]

/-- Prefix offsets select exactly the authored row from the flattened
payload.  This is the load-bearing theorem behind matrix/row-to-CSR
refinement. -/
theorem packedRow_eq {n : Nat} (rows : Fin n → List (Fin n))
    (vertex : Fin n) :
    ((packRows rows).drop (packOffset rows vertex.castSucc)).take
        (packOffset rows vertex.succ - packOffset rows vertex.castSucc) =
      rows vertex := by
  have offsetOrder :
      packOffset rows vertex.castSucc ≤ packOffset rows vertex.succ :=
    packOffset_mono rows (Fin.le_of_lt vertex.castSucc_lt_succ)
  rw [List.take_drop, Nat.add_sub_of_le offsetOrder]
  change
    ((List.ofFn rows).flatten.take
      ((List.ofFn rows).take (vertex.val + 1)).flatten.length).drop
        ((List.ofFn rows).take vertex.val).flatten.length = rows vertex
  simp only [List.length_flatten, List.map_take]
  rw [List.drop_take_succ_flatten_eq_getElem
    (List.ofFn rows) vertex.val (by simp)]
  simp

/-- Start offset of a vertex row. -/
def start {n : Nat} (offset : Fin (n + 1) → Nat) (vertex : Fin n) : Nat :=
  offset vertex.castSucc

/-- Exclusive end offset of a vertex row. -/
def stop {n : Nat} (offset : Fin (n + 1) → Nat) (vertex : Fin n) : Nat :=
  offset vertex.succ

/-- A packed CSR payload with the offset and simple-graph invariants needed by
its observers. -/
structure Rep (n : Nat) where
  offset : Fin (n + 1) → Nat
  neighbors : List (Fin n)
  offset_zero : offset ⟨0, Nat.zero_lt_succ n⟩ = 0
  offset_mono : Monotone offset
  offset_last : offset ⟨n, Nat.lt_succ_self n⟩ = neighbors.length
  symmetric : ∀ source target,
    target ∈ (neighbors.drop (start offset source)).take
        (stop offset source - start offset source) ↔
      source ∈ (neighbors.drop (start offset target)).take
        (stop offset target - start offset target)
  loopless : ∀ vertex,
    vertex ∉ (neighbors.drop (start offset vertex)).take
      (stop offset vertex - start offset vertex)
  nodup : ∀ vertex,
    ((neighbors.drop (start offset vertex)).take
      (stop offset vertex - start offset vertex)).Nodup

/-- The contiguous neighbour slice assigned to one vertex. -/
def row {n : Nat} (graph : Rep n) (vertex : Fin n) : List (Fin n) :=
  (graph.neighbors.drop (start graph.offset vertex)).take
    (stop graph.offset vertex - start graph.offset vertex)

def denote {n : Nat} (graph : Rep n) : SimpleGraph (Fin n) where
  Adj source target := target ∈ row graph source
  symm := ⟨fun source target => (graph.symmetric source target).mp⟩
  loopless := ⟨graph.loopless⟩

def accepts {n : Nat} (candidate query : Fin n) : Bool :=
  candidate == query

/-- Search the selected packed row. -/
def edge {n : Nat} (graph : Rep n) (source target : Fin n) : Measured Bool :=
  LinearProbe.run accepts target (row graph source)

/-- `n+1` offsets plus the packed neighbour cells. -/
def storageCells {n : Nat} (graph : Rep n) : Nat :=
  (n + 1) + graph.neighbors.length

theorem edge_sound {n : Nat} (graph : Rep n) (source target : Fin n) :
    (edge graph source target).value = true ↔
      (denote graph).Adj source target := by
  rw [edge, LinearProbe.run_value_eq_any]
  simp [accepts, denote]

def presentation (n : Nat) : Presentation n where
  Carrier := Rep n
  denote := denote
  edge := edge
  edge_sound := edge_sound
  storageCells := storageCells

abbrev theory (n : Nat) :=
  LinearProbe.theory (Entry := Fin n) (Query := Fin n) accepts

/-- CSR exposes the exact contiguous slice of the packed neighbour array. -/
def neighborsOf {n : Nat} (graph : Rep n) (vertex : Fin n) :
    Measured (List (Fin n)) :=
  ⟨row graph vertex, (row graph vertex).length⟩

theorem neighborsOf_exact {n : Nat} (graph : Rep n) (vertex : Fin n) :
    (neighborsOf graph vertex).value = row graph vertex ∧
      (neighborsOf graph vertex).work = (row graph vertex).length :=
  ⟨rfl, rfl⟩

/-- Every selected row is a genuine slice of the one packed payload. -/
theorem row_length_le_payload {n : Nat} (graph : Rep n) (vertex : Fin n) :
    (row graph vertex).length ≤ graph.neighbors.length := by
  simp [row]

/-- Negative packed-row canary: membership remains linear inside a row when
the target is absent. -/
theorem absent_neighbor_forces_full_row {n : Nat} (graph : Rep n)
    (source target : Fin n) (absent : target ∉ row graph source) :
    (edge graph source target).work = (row graph source).length := by
  apply LinearProbe.run_work_eq_length_of_no_match
  intro candidate member
  have different : candidate ≠ target := by
    intro equal
    exact absent (equal ▸ member)
  simp [accepts, different]

namespace Canary

def v0 : Fin 5 := ⟨0, by omega⟩
def v1 : Fin 5 := ⟨1, by omega⟩
def v2 : Fin 5 := ⟨2, by omega⟩
def v3 : Fin 5 := ⟨3, by omega⟩
def v4 : Fin 5 := ⟨4, by omega⟩

def offsets (index : Fin 6) : Nat :=
  [0, 3, 4, 5, 6, 6].get index

/-- CSR encoding of a three-leaf star plus one isolated vertex. -/
def starAndIsolated : Rep 5 where
  offset := offsets
  neighbors := [v1, v2, v3, v0, v0, v0]
  offset_zero := by decide
  offset_mono := by decide
  offset_last := by decide
  symmetric := by decide
  loopless := by decide
  nodup := by decide

/-- Positive canary: the centre occupies the first contiguous three cells. -/
theorem centre_slice : neighborsOf starAndIsolated v0 =
    ⟨[v1, v2, v3], 3⟩ := by
  decide

/-- Negative canary: an absent centre-to-isolated query scans all three cells
in the selected packed row. -/
theorem absent_after_full_centre_row :
    (edge starAndIsolated v0 v4).work = 3 := by
  decide

end Canary

#print axioms edge_sound
#print axioms packedRow_eq
#print axioms neighborsOf_exact
#print axioms row_length_le_payload
#print axioms absent_neighbor_forces_full_row
#print axioms Canary.centre_slice
#print axioms Canary.absent_after_full_centre_row

end Mettapedia.GraphTheory.Representation.CSR
