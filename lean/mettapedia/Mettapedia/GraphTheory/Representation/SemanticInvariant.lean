import Mettapedia.GSLT.Core.SemanticInvariant
import Mettapedia.GraphTheory.Representation.RepresentationGSLT
import Mettapedia.GraphTheory.Representation.WorldModelGSLT

/-!
# Semantic invariants of finite-graph representation machines

The finite-graph representation portfolio has two different operational
machines and therefore two different conserved meanings:

* representation conversion preserves an independently denoted
  `SimpleGraph` while changing physical layout;
* adjacency-matrix query execution preserves the selected Boolean answer
  while changing control phase from request to response.

Both are instances of the generic `GSLT.SemanticInvariant` interface.  The
negative controls matter: layout names are not invariant under conversion,
and query phases are not invariant under query execution.  Thus the
interface records a selected mathematical observation rather than silently
declaring every property of a state to be semantic.
-/

namespace Mettapedia.GraphTheory.Representation.SemanticInvariant

open Mettapedia.GSLT
open Mettapedia.GraphTheory.Representation

set_option autoImplicit false

/-! ## Representation conversion -/

/-- Representation conversion preserves the independent finite simple graph.
The carrier layout is operational structure, not the denotation. -/
def graphMeaning (n : Nat) :
    GSLT.SemanticInvariant (RepresentationGSLT.theory n)
      (SimpleGraph (Fin n)) where
  denote := RepresentationGSLT.State.denote
  equation := by
    intro source target equal
    subst target
    rfl
  rewrite := RepresentationGSLT.step_commutes

/-- The generic conservation theorem recovers the existing graph-specific
path theorem. -/
theorem graphMeaning_path {n : Nat}
    {source target : RepresentationGSLT.State n}
    (path : (RepresentationGSLT.theory n).RewritePath source target) :
    source.denote = target.denote :=
  (graphMeaning n).rewritePath_eq path

namespace Canary

/-- Positive control: the two-step path-to-rows conversion remains in one
simple-graph fibre. -/
theorem path3_rows_same_graph :
    (RepresentationGSLT.State.edgeList EdgeList.Canary.path3).denote =
      (RepresentationGSLT.State.adjacencyRows
        (Transformations.matrixToRows
          (Transformations.toMatrix (EdgeList.presentation 3)
            EdgeList.Canary.path3))).denote :=
  graphMeaning_path RepresentationGSLT.Canary.path3ToRows

/-- Layout is deliberately not the conserved meaning of representation
conversion: the first path conversion changes its stage name. -/
theorem no_stage_name_invariant :
    ¬ ∃ invariant : GSLT.SemanticInvariant
        (RepresentationGSLT.theory 3) String,
      invariant.denote = RepresentationGSLT.State.stageName := by
  rintro ⟨invariant, identifies⟩
  let source : RepresentationGSLT.State 3 :=
    .edgeList EdgeList.Canary.path3
  let target : RepresentationGSLT.State 3 :=
    .matrix (Transformations.toMatrix
      (EdgeList.presentation 3) EdgeList.Canary.path3)
  have conserved : invariant.denote source = invariant.denote target :=
    invariant.rewrite
      (RepresentationGSLT.Step.edgeListToMatrix EdgeList.Canary.path3)
  have impossible : ("edge-list" : String) = "adjacency-matrix" := by
    calc
      "edge-list" = RepresentationGSLT.State.stageName source := rfl
      _ = invariant.denote source := (congrFun identifies source).symm
      _ = invariant.denote target := conserved
      _ = RepresentationGSLT.State.stageName target := congrFun identifies target
      _ = "adjacency-matrix" := rfl
  exact (by decide : ("edge-list" : String) ≠ "adjacency-matrix") impossible

end Canary

/-! ## Matrix queries -/

/-- A matrix query preserves its independently determined Boolean result
while moving from a lookup state to an answer state. -/
def matrixAnswer (n : Nat) :
    GSLT.SemanticInvariant (AdjacencyMatrix.theory n) Bool where
  denote := WorldModelGSLT.stateObservation
  equation := by
    intro source target equal
    subst target
    rfl
  rewrite := WorldModelGSLT.step_preserves_observation

/-- Query phase is intentionally operational rather than semantic. -/
def matrixQueryPhase {n : Nat} : AdjacencyMatrix.State n → Bool
  | .lookup _ _ _ => false
  | .answer _ => true

namespace Canary

/-- Positive control: the represented path edge has the same selected answer
before and after its matrix read. -/
theorem path_edge_answer_conserved :
    WorldModelGSLT.stateObservation
        (.lookup
          (RepresentationGSLT.canonicalMatrix
            (.edgeList EdgeList.Canary.path3))
          EdgeList.Canary.v0 EdgeList.Canary.v1) =
      WorldModelGSLT.stateObservation
        (.answer true : AdjacencyMatrix.State 3) :=
  (matrixAnswer 3).rewritePath_eq WorldModelGSLT.Canary.pathEdgeExecution

/-- Negative control: no semantic invariant can identify its denotation with
the request/answer phase, because an authentic query step changes that phase. -/
theorem no_matrix_phase_invariant :
    ¬ ∃ invariant : GSLT.SemanticInvariant
        (AdjacencyMatrix.theory 1) Bool,
      invariant.denote = matrixQueryPhase := by
  rintro ⟨invariant, identifies⟩
  let graph := AdjacencyMatrix.empty 1
  let vertex : Fin 1 := ⟨0, by decide⟩
  let source : AdjacencyMatrix.State 1 := .lookup graph vertex vertex
  let target : AdjacencyMatrix.State 1 := .answer (graph.cell vertex vertex)
  have conserved : invariant.denote source = invariant.denote target :=
    invariant.rewrite (AdjacencyMatrix.Step.read graph vertex vertex)
  have impossible : false = true := by
    calc
      false = matrixQueryPhase source := rfl
      _ = invariant.denote source := (congrFun identifies source).symm
      _ = invariant.denote target := conserved
      _ = matrixQueryPhase target := congrFun identifies target
      _ = true := rfl
  exact Bool.false_ne_true impossible

end Canary

#print axioms graphMeaning
#print axioms graphMeaning_path
#print axioms Canary.path3_rows_same_graph
#print axioms Canary.no_stage_name_invariant
#print axioms matrixAnswer
#print axioms Canary.path_edge_answer_conserved
#print axioms Canary.no_matrix_phase_invariant

end Mettapedia.GraphTheory.Representation.SemanticInvariant
