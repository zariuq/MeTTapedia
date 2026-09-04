import Mettapedia.GraphTheory.Representation.Basic

/-!
# Adjacency-row presentation

An adjacency-row representation stores the neighbours of each vertex.  It is
the natural sparse presentation for vertex-local traversal.  Membership inside
one row is still linear unless the row itself is given an additional index.
-/

namespace Mettapedia.GraphTheory.Representation.AdjacencyRows

open Mettapedia.GraphTheory.Representation

/-- Symmetric, loop-free adjacency rows with no duplicate neighbour in a row. -/
structure Rep (n : Nat) where
  row : Fin n → List (Fin n)
  symmetric : ∀ source target, target ∈ row source ↔ source ∈ row target
  loopless : ∀ vertex, vertex ∉ row vertex
  nodup : ∀ vertex, (row vertex).Nodup

/-- Read adjacency directly from the row membership relation. -/
def denote {n : Nat} (graph : Rep n) : SimpleGraph (Fin n) where
  Adj source target := target ∈ graph.row source
  symm := ⟨fun source target => (graph.symmetric source target).mp⟩
  loopless := ⟨graph.loopless⟩

def accepts {n : Nat} (candidate query : Fin n) : Bool :=
  candidate == query

@[simp] theorem accepts_eq_true_iff {n : Nat} (candidate query : Fin n) :
    accepts candidate query = true ↔ candidate = query := by
  simp [accepts]

/-- Search only the selected vertex's neighbour row. -/
def edge {n : Nat} (graph : Rep n) (source target : Fin n) : Measured Bool :=
  LinearProbe.run accepts target (graph.row source)

/-- One row header per vertex plus one cell per stored neighbour occurrence. -/
def storageCells {n : Nat} (graph : Rep n) : Nat :=
  n + (List.ofFn fun vertex => (graph.row vertex).length).sum

theorem edge_sound {n : Nat} (graph : Rep n) (source target : Fin n) :
    (edge graph source target).value = true ↔
      (denote graph).Adj source target := by
  rw [edge, LinearProbe.run_value_eq_any]
  simp [denote, accepts]

def presentation (n : Nat) : Presentation n where
  Carrier := Rep n
  denote := denote
  edge := edge
  edge_sound := edge_sound
  storageCells := storageCells

/-- The adjacency-row edge observer is an instance of the shared linear GSLT. -/
abbrev theory (n : Nat) :=
  LinearProbe.theory (Entry := Fin n) (Query := Fin n) accepts

/-- Initial machine state for an adjacency lookup. -/
def initial {n : Nat} (graph : Rep n) (source target : Fin n) :
    LinearProbe.State (Fin n) (Fin n) :=
  .scan target (graph.row source)

/-- Returning the complete neighbour row is exact and visits precisely the
stored degree of the selected vertex. -/
def neighbors {n : Nat} (graph : Rep n) (vertex : Fin n) :
    Measured (List (Fin n)) :=
  ⟨graph.row vertex, (graph.row vertex).length⟩

theorem neighbors_exact {n : Nat} (graph : Rep n) (vertex : Fin n) :
    (neighbors graph vertex).value = graph.row vertex ∧
      (neighbors graph vertex).work = (graph.row vertex).length :=
  ⟨rfl, rfl⟩

/-- Negative row-search result: a missing neighbour forces the complete
selected row to be inspected. -/
theorem absent_neighbor_forces_full_row {n : Nat} (graph : Rep n)
    (source target : Fin n) (absent : target ∉ graph.row source) :
    (edge graph source target).work = (graph.row source).length := by
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

/-- A three-leaf star plus one isolated vertex. -/
def starAndIsolated : Rep 5 where
  row vertex :=
    if vertex = v0 then [v1, v2, v3]
    else if vertex = v1 then [v0]
    else if vertex = v2 then [v0]
    else if vertex = v3 then [v0]
    else []
  symmetric := by decide
  loopless := by decide
  nodup := by decide

/-- Positive canary: the centre's complete neighbourhood is obtained in three
visits. -/
theorem centre_neighbors : neighbors starAndIsolated v0 =
    ⟨[v1, v2, v3], 3⟩ := by
  decide

/-- Negative canary: asking whether the isolated vertex is adjacent to the
centre inspects the centre's full three-entry row. -/
theorem absent_after_full_centre_row :
    (edge starAndIsolated v0 v4).work = 3 := by
  decide

end Canary

#print axioms edge_sound
#print axioms neighbors_exact
#print axioms absent_neighbor_forces_full_row
#print axioms Canary.centre_neighbors
#print axioms Canary.absent_after_full_centre_row

end Mettapedia.GraphTheory.Representation.AdjacencyRows
