import Mettapedia.GraphTheory.Representation.Transformations

/-!
# The finite graph-representation refinement-path GSLT

Concrete graph layouts are the terms of this GSLT.  Each rewrite applies one
total representation refinement whose commuting law was proved independently.
The resulting paths retain an ordered itinerary of constructed carriers.

The rewrites are atomic only at this refinement layer.  Each target is
computed by a whole conversion function, so this module does not expose the
internal loop, worklist, accumulator, or algorithmic cost of that conversion.
Detailed machines live in separate modules and prove exact agreement with
these refinements.
-/

namespace Mettapedia.GraphTheory.Representation.RepresentationGSLT

open Mettapedia.GSLT
open Mettapedia.GraphTheory.Representation
open Mettapedia.GraphTheory.Representation.Transformations

/-- The supported concrete layouts at a fixed finite vertex cardinality. -/
inductive State (n : Nat) where
  | edgeList (graph : EdgeList.Rep n)
  | matrix (graph : AdjacencyMatrix.Rep n)
  | adjacencyRows (graph : AdjacencyRows.Rep n)
  | neighborFinsets (graph : NeighborFinsets.Rep n)
  | incidence {m : Nat} (graph : IncidenceMatrix.Rep n m)
  | csr (graph : CSR.Rep n)

/-- A concise stage name suitable for diagrams and generated route labels. -/
def State.stageName {n : Nat} : State n → String
  | .edgeList _ => "edge-list"
  | .matrix _ => "adjacency-matrix"
  | .adjacencyRows _ => "adjacency-rows"
  | .neighborFinsets _ => "neighbor-finsets"
  | .incidence _ => "incidence-matrix"
  | .csr _ => "csr"

/-- Every concrete state has one independent simple-graph meaning. -/
def State.denote {n : Nat} : State n → SimpleGraph (Fin n)
  | .edgeList graph => EdgeList.denote graph
  | .matrix graph => AdjacencyMatrix.denote graph
  | .adjacencyRows graph => AdjacencyRows.denote graph
  | .neighborFinsets graph => NeighborFinsets.denote graph
  | .incidence graph => IncidenceMatrix.denote graph
  | .csr graph => CSR.denote graph

/-- The currently admitted abstract refinement legs.  Directedness is
intentional: a sound route need not be cheap or canonical in both directions.
These constructors do not claim that a whole conversion is one machine
operation. -/
inductive Step {n : Nat} : State n → State n → Prop where
  | edgeListToMatrix (graph : EdgeList.Rep n) :
      Step (.edgeList graph)
        (.matrix (toMatrix (EdgeList.presentation n) graph))
  | matrixToEdgeList (graph : AdjacencyMatrix.Rep n) :
      Step (.matrix graph) (.edgeList (matrixToEdgeList graph))
  | matrixToRows (graph : AdjacencyMatrix.Rep n) :
      Step (.matrix graph) (.adjacencyRows (matrixToRows graph))
  | rowsToMatrix (graph : AdjacencyRows.Rep n) :
      Step (.adjacencyRows graph) (.matrix (rowsToMatrix graph))
  | rowsToCSR (graph : AdjacencyRows.Rep n) :
      Step (.adjacencyRows graph) (.csr (Transformations.rowsToCSR graph))
  | matrixToNeighborFinsets (graph : AdjacencyMatrix.Rep n) :
      Step (.matrix graph)
        (.neighborFinsets (Transformations.matrixToNeighborFinsets graph))
  | neighborFinsetsToMatrix (graph : NeighborFinsets.Rep n) :
      Step (.neighborFinsets graph)
        (.matrix (toMatrix (NeighborFinsets.presentation n) graph))
  | matrixToIncidence (graph : AdjacencyMatrix.Rep n) :
      Step (.matrix graph) (.incidence (matrixToIncidence graph).2)
  | incidenceToMatrix {m : Nat} (graph : IncidenceMatrix.Rep n m) :
      Step (.incidence graph)
        (.matrix (toMatrix (IncidenceMatrix.presentation n m) graph))
  | csrToMatrix (graph : CSR.Rep n) :
      Step (.csr graph) (.matrix (toMatrix (CSR.presentation n) graph))

/-- The GSLT whose computations are representation refinements. -/
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

/-- Every abstract refinement leg preserves the independent graph meaning. -/
theorem step_commutes {n : Nat} {source target : State n}
    (step : Step source target) :
    source.denote = target.denote := by
  cases step with
  | edgeListToMatrix graph =>
      exact (toMatrix_commutes (EdgeList.presentation n) graph).symm
  | matrixToEdgeList graph =>
      exact (matrixToEdgeList_commutes graph).symm
  | matrixToRows graph =>
      exact (matrixToRows_commutes graph).symm
  | rowsToMatrix graph =>
      exact (rowsToMatrix_commutes graph).symm
  | rowsToCSR graph =>
      exact (rowsToCSR_commutes graph).symm
  | matrixToNeighborFinsets graph =>
      exact (matrixToNeighborFinsets_commutes graph).symm
  | neighborFinsetsToMatrix graph =>
      exact (toMatrix_commutes (NeighborFinsets.presentation n) graph).symm
  | matrixToIncidence graph =>
      exact (matrixToIncidence_commutes graph).symm
  | incidenceToMatrix graph =>
      exact (toMatrix_commutes
        (IncidenceMatrix.presentation n _) graph).symm
  | csrToMatrix graph =>
      exact (toMatrix_commutes (CSR.presentation n) graph).symm

/-- A complete path of representation rules preserves graph meaning. -/
theorem path_commutes {n : Nat} :
    {source target : State n} →
      (theory n).RewritePath source target →
        source.denote = target.denote
  | _, _, .nil _ => rfl
  | _, _, .cons step rest =>
      (step_commutes step).trans (path_commutes rest)

/-- Hence a transformation route neither invents nor loses any edge. -/
theorem path_adj_iff {n : Nat} {source target : State n}
    (path : (theory n).RewritePath source target) (u v : Fin n) :
    source.denote.Adj u v ↔ target.denote.Adj u v := by
  rw [path_commutes path]

/-! ## Total route selection through the matrix waist -/

/-- The layouts constructible by the current finite portfolio. -/
inductive Layout where
  | edgeList
  | matrix
  | adjacencyRows
  | neighborFinsets
  | incidence
  | csr
deriving DecidableEq, Repr

/-- The canonical matrix constructed from one representation state. -/
def canonicalMatrix {n : Nat} : State n → AdjacencyMatrix.Rep n
  | .edgeList graph => toMatrix (EdgeList.presentation n) graph
  | .matrix graph => graph
  | .adjacencyRows graph => rowsToMatrix graph
  | .neighborFinsets graph =>
      toMatrix (NeighborFinsets.presentation n) graph
  | .incidence (m := m) graph =>
      toMatrix (IncidenceMatrix.presentation n m) graph
  | .csr graph => toMatrix (CSR.presentation n) graph

/-- Every supported representation reaches its canonical matrix in at most
one abstract refinement leg. -/
def toCanonicalMatrixPath {n : Nat} :
    (source : State n) →
      (theory n).RewritePath source (.matrix (canonicalMatrix source))
  | .edgeList graph => .cons (.edgeListToMatrix graph) (.nil _)
  | .matrix _ => .nil _
  | .adjacencyRows graph => .cons (.rowsToMatrix graph) (.nil _)
  | .neighborFinsets graph =>
      .cons (.neighborFinsetsToMatrix graph) (.nil _)
  | .incidence graph => .cons (.incidenceToMatrix graph) (.nil _)
  | .csr graph => .cons (.csrToMatrix graph) (.nil _)

/-- Canonical target data for a selected layout.  Incidence column counts and
CSR offsets are computed from the matrix rather than supplied as oracles. -/
def materialize {n : Nat} (layout : Layout)
    (graph : AdjacencyMatrix.Rep n) : State n :=
  match layout with
  | .edgeList => .edgeList (matrixToEdgeList graph)
  | .matrix => .matrix graph
  | .adjacencyRows => .adjacencyRows (matrixToRows graph)
  | .neighborFinsets => .neighborFinsets (matrixToNeighborFinsets graph)
  | .incidence => .incidence (matrixToIncidence graph).2
  | .csr => .csr (rowsToCSR (matrixToRows graph))

/-- Every target layout is constructible from a matrix in at most two abstract
refinement legs. -/
def fromMatrixPath {n : Nat} :
    (layout : Layout) → (graph : AdjacencyMatrix.Rep n) →
      (theory n).RewritePath (.matrix graph) (materialize layout graph)
  | .edgeList, graph => .cons (.matrixToEdgeList graph) (.nil _)
  | .matrix, _ => .nil _
  | .adjacencyRows, graph => .cons (.matrixToRows graph) (.nil _)
  | .neighborFinsets, graph =>
      .cons (.matrixToNeighborFinsets graph) (.nil _)
  | .incidence, graph => .cons (.matrixToIncidence graph) (.nil _)
  | .csr, graph =>
      .cons (.matrixToRows graph)
        (.cons (.rowsToCSR (matrixToRows graph)) (.nil _))

/-- Concatenate proof-relevant representation paths. -/
def appendPath {n : Nat} {source middle target : State n}
    (first : (theory n).RewritePath source middle)
    (second : (theory n).RewritePath middle target) :
    (theory n).RewritePath source target :=
  match first with
  | .nil _ => second
  | .cons step rest => .cons step (appendPath rest second)

/-- A total source/layout compiler: first construct the common matrix waist,
then materialise the requested target. -/
def convertPath {n : Nat} (source : State n) (target : Layout) :
    (theory n).RewritePath source
      (materialize target (canonicalMatrix source)) :=
  appendPath (toCanonicalMatrixPath source)
    (fromMatrixPath target (canonicalMatrix source))

/-- Every total conversion route preserves the independent simple graph. -/
theorem convertPath_commutes {n : Nat} (source : State n) (target : Layout) :
    source.denote =
      (materialize target (canonicalMatrix source)).denote :=
  path_commutes (convertPath source target)

/-- No total conversion route invents or loses an edge. -/
theorem convertPath_adj_iff {n : Nat} (source : State n) (target : Layout)
    (u v : Fin n) :
    source.denote.Adj u v ↔
      (materialize target (canonicalMatrix source)).denote.Adj u v :=
  path_adj_iff (convertPath source target) u v

namespace Canary

/-- The edge-list-to-row route is a two-leg abstract refinement itinerary. -/
def path3ToRows :
    (theory 3).RewritePath
      (.edgeList EdgeList.Canary.path3)
      (.adjacencyRows
        (matrixToRows
          (toMatrix (EdgeList.presentation 3) EdgeList.Canary.path3))) :=
  .cons (.edgeListToMatrix _)
    (.cons (.matrixToRows _) (.nil _))

@[simp] theorem path3ToRows_length : path3ToRows.length = 2 :=
  rfl

/-- The composite retains the path graph exactly. -/
theorem path3ToRows_commutes :
    (State.edgeList EdgeList.Canary.path3).denote =
      (State.adjacencyRows
        (matrixToRows
          (toMatrix (EdgeList.presentation 3)
            EdgeList.Canary.path3))).denote :=
  path_commutes path3ToRows

/-- Extending the same route by one physical packing step reaches CSR. -/
def path3ToCSR :
    (theory 3).RewritePath
      (.edgeList EdgeList.Canary.path3)
      (.csr
        (rowsToCSR
          (matrixToRows
            (toMatrix (EdgeList.presentation 3) EdgeList.Canary.path3)))) :=
  .cons (.edgeListToMatrix _)
    (.cons (.matrixToRows _)
      (.cons (.rowsToCSR _) (.nil _)))

@[simp] theorem path3ToCSR_length : path3ToCSR.length = 3 :=
  rfl

theorem path3ToCSR_commutes :
    (State.edgeList EdgeList.Canary.path3).denote =
      (State.csr
        (rowsToCSR
          (matrixToRows
            (toMatrix (EdgeList.presentation 3)
              EdgeList.Canary.path3)))).denote :=
  path_commutes path3ToCSR

end Canary

#print axioms step_commutes
#print axioms path_commutes
#print axioms path_adj_iff
#print axioms convertPath_commutes
#print axioms convertPath_adj_iff
#print axioms Canary.path3ToRows_length
#print axioms Canary.path3ToRows_commutes
#print axioms Canary.path3ToCSR_length
#print axioms Canary.path3ToCSR_commutes

end Mettapedia.GraphTheory.Representation.RepresentationGSLT
