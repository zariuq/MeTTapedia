import Mettapedia.GraphTheory.Representation.Basic

/-!
# Adjacency-matrix presentation

An adjacency matrix pays for every possible vertex pair and answers an edge
query with one cell read.  Symmetry and the empty diagonal are carried as
representation invariants rather than repaired by the observer.
-/

namespace Mettapedia.GraphTheory.Representation.AdjacencyMatrix

open Mettapedia.GSLT
open Mettapedia.GraphTheory.Representation

/-- A Boolean adjacency matrix satisfying the simple-graph laws. -/
structure Rep (n : Nat) where
  cell : Fin n → Fin n → Bool
  symmetric : ∀ source target, cell source target = cell target source
  loopless : ∀ vertex, cell vertex vertex = false

/-- Read the matrix as its extensional simple graph. -/
def denote {n : Nat} (graph : Rep n) : SimpleGraph (Fin n) where
  Adj source target := graph.cell source target = true
  symm := ⟨by
    intro source target adjacent
    rw [← graph.symmetric source target]
    exact adjacent⟩
  loopless := ⟨by
    intro vertex adjacent
    rw [graph.loopless vertex] at adjacent
    contradiction⟩

/-- An edge query is exactly one matrix-cell read. -/
def edge {n : Nat} (graph : Rep n) (source target : Fin n) : Measured Bool :=
  ⟨graph.cell source target, 1⟩

/-- The dense layout reserves one cell for every ordered vertex pair. -/
def storageCells {n : Nat} (_graph : Rep n) : Nat :=
  n * n

theorem edge_sound {n : Nat} (graph : Rep n) (source target : Fin n) :
    (edge graph source target).value = true ↔
      (denote graph).Adj source target :=
  Iff.rfl

/-- The adjacency-matrix member of the common representation portfolio. -/
def presentation (n : Nat) : Presentation n where
  Carrier := Rep n
  denote := denote
  edge := edge
  edge_sound := edge_sound
  storageCells := storageCells

/-- Matrix-query states expose the one primitive read explicitly. -/
inductive State (n : Nat) where
  | lookup (graph : Rep n) (source target : Fin n)
  | answer (value : Bool)

/-- The matrix has one operational rule: read the addressed cell. -/
inductive Step {n : Nat} : State n → State n → Prop where
  | read (graph : Rep n) (source target : Fin n) :
      Step (.lookup graph source target) (.answer (graph.cell source target))

/-- The authentic constant-probe adjacency-matrix GSLT. -/
def theory (n : Nat) : GSLT where
  Term := State n
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- Every lookup takes one and only one authored transition to its answer. -/
def lookupPath {n : Nat} (graph : Rep n) (source target : Fin n) :
    (theory n).RewritePath (.lookup graph source target)
      (.answer (edge graph source target).value) :=
  .cons (.read graph source target) (.nil _)

@[simp] theorem lookupPath_length {n : Nat} (graph : Rep n)
    (source target : Fin n) :
    (lookupPath graph source target).length = 1 :=
  rfl

theorem answer_normal {n : Nat} (answer : Bool) :
    (theory n).IsNormalForm (.answer answer) := by
  rintro ⟨target, step⟩
  cases step

/-- The empty dense matrix. -/
def empty (n : Nat) : Rep n where
  cell := fun _ _ => false
  symmetric := by simp
  loopless := by simp

theorem empty_denote (n : Nat) : denote (empty n) = (⊥ : SimpleGraph (Fin n)) := by
  ext source target
  simp [denote, empty]

/-- Negative dense-layout canary: even the empty graph reserves all `n²`
cells. -/
theorem empty_storage_quadratic (n : Nat) :
    storageCells (empty n) = n * n :=
  rfl

namespace Canary

/-- On eight isolated vertices the representation stores sixty-four cells
despite denoting no edges. -/
theorem empty8_storage : storageCells (empty 8) = 64 :=
  rfl

theorem empty8_has_no_edges (source target : Fin 8) :
    ¬(denote (empty 8)).Adj source target := by
  simp [denote, empty]

end Canary

#print axioms edge_sound
#print axioms lookupPath_length
#print axioms empty_denote
#print axioms empty_storage_quadratic
#print axioms Canary.empty8_has_no_edges

end Mettapedia.GraphTheory.Representation.AdjacencyMatrix
