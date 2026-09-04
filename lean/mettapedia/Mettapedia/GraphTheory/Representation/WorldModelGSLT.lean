import Mettapedia.GraphTheory.Representation.RevisionPortfolio
import Mettapedia.GraphTheory.Representation.MatrixBridge
import Mettapedia.Logic.WorldModel.GSLTRealization

/-!
# Finite graphs as exact world-model query GSLTs

Finite simple graphs form a minimal world model under edge-set union and
adjacency extraction.  The adjacency-matrix carrier realizes that independent
world, while its one-cell query machine supplies an exact behavioral GSLT.
Other graph layouts can share the same semantic authority and differ only in
their revision/query resource accounts.
-/

namespace Mettapedia.GraphTheory.Representation.WorldModelGSLT

open Mettapedia.GSLT
open Mettapedia.GraphTheory.Representation
open Mettapedia.Logic.WorldModel

set_option autoImplicit false

/-- Independent finite-graph world model: revision unions edge knowledge and
extraction asks one adjacency question. -/
noncomputable instance simpleGraphWorldModel (n : Nat) :
    WorldModel (SimpleGraph (Fin n)) (EdgeQuery n) Bool := by
  classical
  exact {
    revise := ( · ⊔ · )
    empty := ⊥
    extract := fun graph query => decide (graph.Adj query.1 query.2)
  }

/-- The dense graph carrier realizes the independent simple-graph world
model. -/
noncomputable def matrixRealization (n : Nat) :
    GSLTRealization.Realization (SimpleGraph (Fin n))
      (AdjacencyMatrix.Rep n) (EdgeQuery n) Bool where
  denote := AdjacencyMatrix.denote
  empty := AdjacencyMatrix.empty n
  revise := RevisionPortfolio.unionMatrix
  extract := fun graph query =>
    (AdjacencyMatrix.edge graph query.1 query.2).value
  empty_sound := AdjacencyMatrix.empty_denote n
  revise_sound := RevisionPortfolio.unionMatrix_denote
  extract_sound := by
    classical
    intro graph query
    change graph.cell query.1 query.2 =
      decide ((AdjacencyMatrix.denote graph).Adj query.1 query.2)
    simp [AdjacencyMatrix.denote]

/-- State observation is independent of whether the matrix read has already
occurred. -/
def stateObservation {n : Nat} : AdjacencyMatrix.State n → Bool
  | .lookup graph source target => graph.cell source target
  | .answer value => value

theorem step_preserves_observation {n : Nat}
    {source target : AdjacencyMatrix.State n}
    (step : AdjacencyMatrix.Step source target) :
    stateObservation source = stateObservation target := by
  cases step
  rfl

theorem path_preserves_observation {n : Nat}
    : {source target : AdjacencyMatrix.State n} →
      (AdjacencyMatrix.theory n).RewritePath source target →
        stateObservation source = stateObservation target
  | _, _, .nil _ => rfl
  | _, _, .cons step rest =>
      (step_preserves_observation step).trans
        (path_preserves_observation rest)

/-- The only normal matrix-query states are answers. -/
theorem normal_iff_answer {n : Nat} (state : AdjacencyMatrix.State n) :
    (AdjacencyMatrix.theory n).IsNormalForm state ↔
      ∃ value, state = .answer value := by
  constructor
  · intro normal
    cases state with
    | lookup graph source target =>
        exact (normal ⟨.answer (graph.cell source target),
          .read graph source target⟩).elim
    | answer value => exact ⟨value, rfl⟩
  · rintro ⟨value, rfl⟩
    exact AdjacencyMatrix.answer_normal value

/-- The existing matrix query GSLT is an exact behavioral realization of
world-model extraction, including covered terminal reflection. -/
noncomputable def matrixQueryMachine (n : Nat) :
    GSLTRealization.ExactQueryGSLT (matrixRealization n) where
  theory := AdjacencyMatrix.theory n
  request := fun graph query => .lookup graph query.1 query.2
  answer := fun _ value => .answer value
  executePath := by
    intro graph query
    exact AdjacencyMatrix.lookupPath graph query.1 query.2
  answer_normal := fun _ value => AdjacencyMatrix.answer_normal value
  answer_reflect := by
    intro graph query value path
    exact (path_preserves_observation path).symm
  covered_normal := by
    intro graph query terminal path normal
    obtain ⟨value, rfl⟩ := (normal_iff_answer _).mp normal
    exact ⟨value, rfl⟩

theorem matrix_terminal_exact (n : Nat) (graph : AdjacencyMatrix.Rep n)
    (query : EdgeQuery n) (terminal : (AdjacencyMatrix.theory n).Term)
    (path : (AdjacencyMatrix.theory n).RewritePath
      (.lookup graph query.1 query.2) terminal)
    (normal : (AdjacencyMatrix.theory n).IsNormalForm terminal) :
    terminal = .answer (graph.cell query.1 query.2) := by
  have exact := (matrixQueryMachine n).covered_terminal_exact
    graph query terminal path normal
  simpa [matrixQueryMachine, matrixRealization, AdjacencyMatrix.edge] using exact

namespace Canary

/-- Positive: querying the represented path edge reaches `true`. -/
def pathEdgeExecution :
    (AdjacencyMatrix.theory 3).RewritePath
      (.lookup
        (RepresentationGSLT.canonicalMatrix
          (.edgeList EdgeList.Canary.path3))
        EdgeList.Canary.v0 EdgeList.Canary.v1)
      (.answer true) := by
  have cell :
      (RepresentationGSLT.canonicalMatrix
        (.edgeList EdgeList.Canary.path3)).cell
        EdgeList.Canary.v0 EdgeList.Canary.v1 = true :=
    MatrixBridge.Canary.path3_edge_cell
  simpa [AdjacencyMatrix.edge, cell] using
    AdjacencyMatrix.lookupPath
      (RepresentationGSLT.canonicalMatrix
        (.edgeList EdgeList.Canary.path3))
      EdgeList.Canary.v0 EdgeList.Canary.v1

/-- Negative: the same successful query cannot reach a covered false answer. -/
theorem pathEdge_cannot_answer_false :
    ¬ Nonempty ((AdjacencyMatrix.theory 3).RewritePath
      (.lookup
        (RepresentationGSLT.canonicalMatrix
          (.edgeList EdgeList.Canary.path3))
        EdgeList.Canary.v0 EdgeList.Canary.v1)
      (.answer false)) := by
  rintro ⟨path⟩
  have reflected := (matrixQueryMachine 3).answer_reflect
    (RepresentationGSLT.canonicalMatrix (.edgeList EdgeList.Canary.path3))
    (EdgeList.Canary.v0, EdgeList.Canary.v1) false path
  have cell := MatrixBridge.Canary.path3_edge_cell
  exact Bool.false_ne_true (reflected.trans cell)

end Canary

#print axioms matrixRealization
#print axioms matrixQueryMachine
#print axioms matrix_terminal_exact
#print axioms Canary.pathEdge_cannot_answer_false

end Mettapedia.GraphTheory.Representation.WorldModelGSLT
