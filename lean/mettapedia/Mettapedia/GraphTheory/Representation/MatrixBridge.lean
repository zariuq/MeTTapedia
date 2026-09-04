import Mettapedia.GraphTheory.Representation.Transformations
import Mathlib.Data.Matrix.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-!
# Standard-matrix semantics for the adjacency-matrix GSLT

The operational adjacency-matrix presentation stores a curried Boolean cell
function.  This module identifies that data with Mathlib's standard `Matrix`
type, proves that its simple-graph meaning is exactly Boolean matrix
observation, and reflects the operational query GSLT into a raw-matrix query
machine.  Resource accounting remains outside this semantic bridge.
-/

namespace Mettapedia.GraphTheory.Representation.MatrixBridge

open Mettapedia.GSLT
open Mettapedia.GraphTheory.Representation

set_option autoImplicit false

/-- The standard Mathlib matrix underlying one adjacency-matrix state. -/
def toMatrix {n : Nat} (graph : AdjacencyMatrix.Rep n) :
    Matrix (Fin n) (Fin n) Bool :=
  graph.cell

/-- The exact simple-graph laws required of a Boolean matrix. -/
structure IsSimple {n : Nat} (matrix : Matrix (Fin n) (Fin n) Bool) : Prop where
  symmetric : ∀ source target, matrix source target = matrix target source
  loopless : ∀ vertex, matrix vertex vertex = false

/-- Every lawful standard Boolean matrix constructs an operational matrix
presentation without changing its cells. -/
def ofMatrix {n : Nat} (matrix : Matrix (Fin n) (Fin n) Bool)
    (lawful : IsSimple matrix) : AdjacencyMatrix.Rep n where
  cell := matrix
  symmetric := lawful.symmetric
  loopless := lawful.loopless

@[simp] theorem toMatrix_apply {n : Nat} (graph : AdjacencyMatrix.Rep n)
    (source target : Fin n) :
    toMatrix graph source target = graph.cell source target :=
  rfl

theorem toMatrix_isSimple {n : Nat} (graph : AdjacencyMatrix.Rep n) :
    IsSimple (toMatrix graph) :=
  ⟨graph.symmetric, graph.loopless⟩

@[simp] theorem toMatrix_ofMatrix {n : Nat}
    (matrix : Matrix (Fin n) (Fin n) Bool) (lawful : IsSimple matrix) :
    toMatrix (ofMatrix matrix lawful) = matrix :=
  rfl

@[simp] theorem ofMatrix_toMatrix {n : Nat}
    (graph : AdjacencyMatrix.Rep n) :
    ofMatrix (toMatrix graph) (toMatrix_isSimple graph) = graph := by
  cases graph
  rfl

/-- The operational representation is embedded faithfully in standard
Mathlib matrices. -/
theorem toMatrix_injective {n : Nat} :
    Function.Injective (@toMatrix n) := by
  intro first second equal
  cases first with
  | mk firstCell firstSymmetric firstLoopless =>
      cases second with
      | mk secondCell secondSymmetric secondLoopless =>
          change firstCell = secondCell at equal
          cases equal
          rfl

/-- Independent graph adjacency is exactly observation of the corresponding
standard matrix cell. -/
theorem denote_adj_iff_matrix {n : Nat} (graph : AdjacencyMatrix.Rep n)
    (source target : Fin n) :
    (AdjacencyMatrix.denote graph).Adj source target ↔
      toMatrix graph source target = true :=
  Iff.rfl

/-! ## Canonical Mathlib adjacency matrix

`toMatrix` preserves the runtime's compact Boolean cells.  Mathlib's
canonical `SimpleGraph.adjMatrix` instead uses a semiring-valued matrix.  The
following bridge keeps both views: a representation can remain Boolean in its
operational carrier while its declarative graph meaning is exactly Mathlib's
canonical natural-number adjacency matrix.
-/

/-- The decidable edge relation induced by the Boolean operational matrix. -/
@[reducible] def denoteDecidableRel {n : Nat} (graph : AdjacencyMatrix.Rep n) :
    DecidableRel (AdjacencyMatrix.denote graph).Adj :=
  fun source target =>
    decidable_of_iff (graph.cell source target = true) Iff.rfl

/-- Mathlib's canonical natural-number adjacency matrix for the graph denoted
by an operational Boolean adjacency representation. -/
def mathlibAdjacencyMatrix {n : Nat} (graph : AdjacencyMatrix.Rep n) :
    Matrix (Fin n) (Fin n) Nat :=
  @SimpleGraph.adjMatrix Nat (Fin n) (AdjacencyMatrix.denote graph)
    (denoteDecidableRel graph) _ _

/-- The canonical matrix is recognized by Mathlib as an adjacency matrix. -/
def mathlibAdjacencyIsAdjMatrix {n : Nat} (graph : AdjacencyMatrix.Rep n) :
    (mathlibAdjacencyMatrix graph).IsAdjMatrix :=
  @SimpleGraph.isAdjMatrix_adjMatrix Nat (Fin n) (AdjacencyMatrix.denote graph)
    (denoteDecidableRel graph) _ _

/-- The canonical matrix is the pointwise natural-number image of the runtime
Boolean matrix. -/
theorem mathlibAdjacencyMatrix_apply {n : Nat} (graph : AdjacencyMatrix.Rep n)
    (source target : Fin n) :
    mathlibAdjacencyMatrix graph source target =
      (toMatrix graph source target).toNat := by
  cases h : graph.cell source target <;>
    simp [mathlibAdjacencyMatrix, SimpleGraph.adjMatrix_apply,
      AdjacencyMatrix.denote, toMatrix, h]

/-- Reconstructing Mathlib's graph from the canonical matrix recovers exactly
the independently denoted graph. -/
theorem mathlibAdjacencyMatrix_toGraph {n : Nat} (graph : AdjacencyMatrix.Rep n) :
    (mathlibAdjacencyIsAdjMatrix graph).toGraph =
      AdjacencyMatrix.denote graph := by
  exact @SimpleGraph.toGraph_adjMatrix_eq Nat (Fin n)
    (AdjacencyMatrix.denote graph) (denoteDecidableRel graph) _ _

/-! ## Operational bridge -/

/-- Raw standard-matrix query states.  They deliberately do not contain a
simple-graph answer or an adjacency oracle. -/
inductive MatrixState (n : Nat) where
  | lookup (matrix : Matrix (Fin n) (Fin n) Bool)
      (source target : Fin n)
  | answer (value : Bool)

/-- One primitive standard-matrix cell read. -/
inductive MatrixStep {n : Nat} : MatrixState n → MatrixState n → Prop where
  | read (matrix : Matrix (Fin n) (Fin n) Bool)
      (source target : Fin n) :
      MatrixStep (.lookup matrix source target)
        (.answer (matrix source target))

def matrixTheory (n : Nat) : GSLT where
  Term := MatrixState n
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := MatrixStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- Structural encoding from the operational graph state to its standard
matrix state.  It never consults the eventual query answer. -/
def encodeState {n : Nat} : AdjacencyMatrix.State n → MatrixState n
  | .lookup graph source target => .lookup (toMatrix graph) source target
  | .answer value => .answer value

/-- One graph-matrix read is one standard-matrix read. -/
theorem encode_step {n : Nat} {source target : AdjacencyMatrix.State n}
    (step : AdjacencyMatrix.Step source target) :
    MatrixStep (encodeState source) (encodeState target) := by
  cases step
  exact .read _ _ _

/-- Conversely, a raw-matrix step whose source is represented by the graph
GSLT reconstructs the unique represented target and its source step. -/
theorem matrix_step_from_encoded_iff {n : Nat}
    (source : AdjacencyMatrix.State n) (target : MatrixState n) :
    MatrixStep (encodeState source) target ↔
      ∃ representedTarget,
        AdjacencyMatrix.Step source representedTarget ∧
          target = encodeState representedTarget := by
  constructor
  · intro step
    cases source with
    | lookup graph first second =>
        cases step
        exact ⟨.answer (graph.cell first second), .read graph first second, rfl⟩
    | answer value => cases step
  · rintro ⟨representedTarget, step, rfl⟩
    exact encode_step step

/-- Encoding an operational lookup path yields an exact raw-matrix path. -/
def encodeLookupPath {n : Nat} (graph : AdjacencyMatrix.Rep n)
    (source target : Fin n) :
    (matrixTheory n).RewritePath
      (encodeState (.lookup graph source target))
      (encodeState (.answer (graph.cell source target))) :=
  .cons (.read _ _ _) (.nil _)

namespace Canary

/-- Positive: the standard matrix exposes the same path edge as the graph
meaning. -/
theorem path3_edge_cell :
    toMatrix
        (Transformations.toMatrix (EdgeList.presentation 3)
          EdgeList.Canary.path3)
        EdgeList.Canary.v0 EdgeList.Canary.v1 = true := by
  change (EdgeList.edge EdgeList.Canary.path3
    EdgeList.Canary.v0 EdgeList.Canary.v1).value = true
  exact (EdgeList.edge_sound EdgeList.Canary.path3
    EdgeList.Canary.v0 EdgeList.Canary.v1).2 (by
      simp [EdgeList.denote, EdgeList.Canary.path3,
        EdgeList.Canary.v0, EdgeList.Canary.v1])

/-- Negative: the diagonal remains false; a matrix encoding cannot invent a
self-loop that is absent from Mathlib's simple-graph meaning. -/
theorem path3_diagonal_false :
    toMatrix
        (Transformations.toMatrix (EdgeList.presentation 3)
          EdgeList.Canary.path3)
        EdgeList.Canary.v1 EdgeList.Canary.v1 = false := by
  exact (Transformations.toMatrix
    (EdgeList.presentation 3) EdgeList.Canary.path3).loopless _

/-- Positive: the canonical Mathlib adjacency matrix records an actual path
edge as `1`. -/
theorem path3_mathlib_edge :
    mathlibAdjacencyMatrix
        (Transformations.toMatrix (EdgeList.presentation 3)
          EdgeList.Canary.path3)
        EdgeList.Canary.v0 EdgeList.Canary.v1 = 1 := by
  calc
    _ = (toMatrix (Transformations.toMatrix (EdgeList.presentation 3)
          EdgeList.Canary.path3) EdgeList.Canary.v0 EdgeList.Canary.v1).toNat :=
      mathlibAdjacencyMatrix_apply _ _ _
    _ = true.toNat := congrArg Bool.toNat path3_edge_cell
    _ = 1 := rfl

/-- Negative: the canonical Mathlib adjacency matrix cannot invent a diagonal
edge from the Boolean representation. -/
theorem path3_mathlib_diagonal :
    mathlibAdjacencyMatrix
        (Transformations.toMatrix (EdgeList.presentation 3)
          EdgeList.Canary.path3)
        EdgeList.Canary.v1 EdgeList.Canary.v1 = 0 := by
  calc
    _ = (toMatrix (Transformations.toMatrix (EdgeList.presentation 3)
          EdgeList.Canary.path3) EdgeList.Canary.v1 EdgeList.Canary.v1).toNat :=
      mathlibAdjacencyMatrix_apply _ _ _
    _ = false.toNat := congrArg Bool.toNat path3_diagonal_false
    _ = 0 := rfl

end Canary

#print axioms toMatrix_injective
#print axioms denote_adj_iff_matrix
#print axioms mathlibAdjacencyMatrix_apply
#print axioms mathlibAdjacencyMatrix_toGraph
#print axioms matrix_step_from_encoded_iff
#print axioms encodeLookupPath
#print axioms Canary.path3_diagonal_false
#print axioms Canary.path3_mathlib_edge
#print axioms Canary.path3_mathlib_diagonal

end Mettapedia.GraphTheory.Representation.MatrixBridge
