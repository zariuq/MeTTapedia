import Mettapedia.GraphTheory.Representation.Basic

/-!
# Incidence-matrix presentation

An incidence matrix separates vertex identity from edge identity.  It makes
the question “does vertex `v` touch edge occurrence `e`?” a single-cell
observation and is therefore a natural base for edge-centric constraints and
for later hypergraph generalisation.  Recovering adjacency may require a scan
over all edge columns.
-/

namespace Mettapedia.GraphTheory.Representation.IncidenceMatrix

open Mettapedia.GraphTheory.Representation

/-- A simple undirected incidence matrix with exactly two distinct vertices
in every edge column. -/
structure Rep (n m : Nat) where
  cell : Fin n → Fin m → Bool
  columnSimple : ∀ edge,
    ∃ first second, first ≠ second ∧
      ∀ vertex, cell vertex edge = true ↔
        vertex = first ∨ vertex = second

abbrev Query (n : Nat) := Fin n × Fin n

def accepts {n m : Nat} (graph : Rep n m) (edge : Fin m)
    (query : Query n) : Bool :=
  (query.1 != query.2) && graph.cell query.1 edge &&
    graph.cell query.2 edge

/-- Two distinct vertices are adjacent when some edge column contains both. -/
def denote {n m : Nat} (graph : Rep n m) : SimpleGraph (Fin n) where
  Adj source target :=
    source ≠ target ∧
      ∃ edge : Fin m,
        graph.cell source edge = true ∧ graph.cell target edge = true
  symm := ⟨by
    rintro source target ⟨different, edge, sourceCell, targetCell⟩
    exact ⟨different.symm, edge, targetCell, sourceCell⟩⟩
  loopless := ⟨by simp⟩

/-- Adjacency scans edge columns until it finds a common incidence. -/
def edge {n m : Nat} (graph : Rep n m) (source target : Fin n) :
    Measured Bool :=
  LinearProbe.run (accepts graph) (source, target) (List.ofFn id)

/-- One Boolean cell for every vertex/edge pair. -/
def storageCells {n m : Nat} (_graph : Rep n m) : Nat :=
  n * m

theorem edge_sound {n m : Nat} (graph : Rep n m)
    (source target : Fin n) :
    (edge graph source target).value = true ↔
      (denote graph).Adj source target := by
  rw [edge, LinearProbe.run_value_eq_any]
  simp [accepts, denote, Bool.and_eq_true]
  constructor
  · rintro ⟨column, ⟨different, sourceCell⟩, targetCell⟩
    exact ⟨different, column, sourceCell, targetCell⟩
  · rintro ⟨different, column, sourceCell, targetCell⟩
    exact ⟨column, ⟨different, sourceCell⟩, targetCell⟩

/-- The fixed-column-count incidence presentation. -/
def presentation (n m : Nat) : Presentation n where
  Carrier := Rep n m
  denote := denote
  edge := edge
  edge_sound := edge_sound
  storageCells := storageCells

/-- Incidence conversion determines its number of edge columns from the
source graph.  This dependent presentation packages that column count with
the matrix instead of pretending it was fixed in advance. -/
def dependentPresentation (n : Nat) : Presentation n where
  Carrier := Σ m, Rep n m
  denote graph := denote graph.2
  edge graph := edge graph.2
  edge_sound graph := edge_sound graph.2
  storageCells graph := storageCells graph.2

/-- A direct incidence observation is one cell read. -/
def incident {n m : Nat} (graph : Rep n m) (vertex : Fin n)
    (edge : Fin m) : Measured Bool :=
  ⟨graph.cell vertex edge, 1⟩

theorem incident_one_probe {n m : Nat} (graph : Rep n m)
    (vertex : Fin n) (column : Fin m) :
    (incident graph vertex column).work = 1 :=
  rfl

/-- The adjacency observer is another instance of the shared linear GSLT,
this time scanning edge identities rather than stored endpoints. -/
abbrev theory {n m : Nat} (graph : Rep n m) :=
  LinearProbe.theory (accepts graph)

/-- Negative incidence result: when no column contains both vertices, the
adjacency observer inspects all `m` columns. -/
theorem absent_edge_forces_all_columns {n m : Nat} (graph : Rep n m)
    (source target : Fin n)
    (absent : ∀ column : Fin m, accepts graph column (source, target) = false) :
    (edge graph source target).work = m := by
  rw [edge]
  have allMiss : ∀ column ∈ List.ofFn (id : Fin m → Fin m),
      accepts graph column (source, target) = false := by
    intro column _
    exact absent column
  rw [LinearProbe.run_work_eq_length_of_no_match _ _ _ allMiss]
  simp

namespace Canary

def v0 : Fin 4 := ⟨0, by omega⟩
def v1 : Fin 4 := ⟨1, by omega⟩
def v2 : Fin 4 := ⟨2, by omega⟩
def v3 : Fin 4 := ⟨3, by omega⟩

def e0 : Fin 3 := ⟨0, by omega⟩
def e1 : Fin 3 := ⟨1, by omega⟩
def e2 : Fin 3 := ⟨2, by omega⟩

/-- Incidence matrix of the path `0--1--2--3`. -/
def path4 : Rep 4 3 where
  cell vertex column :=
    if column = e0 then vertex = v0 || vertex = v1
    else if column = e1 then vertex = v1 || vertex = v2
    else vertex = v2 || vertex = v3
  columnSimple := by decide

/-- Positive canary: checking that vertex 2 touches the final edge is one
cell observation. -/
theorem local_incidence_is_one_probe : incident path4 v2 e2 = ⟨true, 1⟩ := by
  decide

/-- Negative canary: discovering that the path endpoints are nonadjacent
scans all three edge columns. -/
theorem endpoints_nonadjacent_cost : (edge path4 v0 v3).work = 3 := by
  decide

end Canary

#print axioms edge_sound
#print axioms incident_one_probe
#print axioms absent_edge_forces_all_columns
#print axioms Canary.local_incidence_is_one_probe
#print axioms Canary.endpoints_nonadjacent_cost

end Mettapedia.GraphTheory.Representation.IncidenceMatrix
