import Mettapedia.GraphTheory.Representation.Transformations

/-!
# Occurrence-by-occurrence edge-list to adjacency-matrix GSLT

The extensional refinement `Transformations.toMatrix` is the mathematical
specification of edge-list materialization.  It is intentionally not used as
one opaque operational rewrite here.  This machine starts from the empty
matrix, consumes one authored edge occurrence per step, and updates precisely
the corresponding symmetric pair of Boolean cells.  Its terminal carrier is
proved equal to the extensional refinement.
-/

namespace Mettapedia.GraphTheory.Representation.EdgeListToMatrixGSLT

open Mettapedia.GSLT
open Mettapedia.GraphTheory.Representation

set_option autoImplicit false

/-- Edge-list occurrence matching is symmetric in the queried endpoints. -/
theorem accepts_swap {n : Nat} (edge : EdgeList.Edge n) (u v : Fin n) :
    EdgeList.accepts edge (u, v) = EdgeList.accepts edge (v, u) := by
  rw [Bool.eq_iff_iff]
  simp only [EdgeList.accepts, Bool.and_eq_true, bne_iff_ne,
    Bool.or_eq_true, beq_iff_eq]
  aesop

/-- Insert one stored edge occurrence into an existing lawful matrix.  Loops
are ignored, matching the simple-graph denotation of the edge-list carrier. -/
def insertOccurrence {n : Nat} (matrix : AdjacencyMatrix.Rep n)
    (edge : EdgeList.Edge n) : AdjacencyMatrix.Rep n where
  cell u v := matrix.cell u v || EdgeList.accepts edge (u, v)
  symmetric := by
    intro u v
    rw [matrix.symmetric u v, accepts_swap edge u v]
  loopless := by
    intro u
    simp [matrix.loopless u, EdgeList.accepts]

@[simp] theorem insertOccurrence_cell {n : Nat}
    (matrix : AdjacencyMatrix.Rep n) (edge : EdgeList.Edge n)
    (u v : Fin n) :
    (insertOccurrence matrix edge).cell u v =
      (matrix.cell u v || EdgeList.accepts edge (u, v)) :=
  rfl

/-- A cell not addressed by the consumed occurrence is unchanged. -/
theorem insertOccurrence_cell_of_miss {n : Nat}
    (matrix : AdjacencyMatrix.Rep n) (edge : EdgeList.Edge n)
    (u v : Fin n) (miss : EdgeList.accepts edge (u, v) = false) :
    (insertOccurrence matrix edge).cell u v = matrix.cell u v := by
  simp [insertOccurrence, miss]

/-- A matching non-loop occurrence makes its addressed cell true. -/
theorem insertOccurrence_cell_of_hit {n : Nat}
    (matrix : AdjacencyMatrix.Rep n) (edge : EdgeList.Edge n)
    (u v : Fin n) (hit : EdgeList.accepts edge (u, v) = true) :
    (insertOccurrence matrix edge).cell u v = true := by
  simp [insertOccurrence, hit]

/-- Consume a list of occurrences into an accumulator matrix. -/
def buildFrom {n : Nat} :
    AdjacencyMatrix.Rep n → List (EdgeList.Edge n) → AdjacencyMatrix.Rep n
  | matrix, [] => matrix
  | matrix, edge :: rest => buildFrom (insertOccurrence matrix edge) rest

/-- The exact cell computed by the accumulator is the old cell or membership
in one of the remaining edge occurrences. -/
theorem buildFrom_cell {n : Nat} (matrix : AdjacencyMatrix.Rep n)
    (entries : List (EdgeList.Edge n)) (u v : Fin n) :
    (buildFrom matrix entries).cell u v =
      (matrix.cell u v || entries.any (EdgeList.accepts · (u, v))) := by
  induction entries generalizing matrix with
  | nil => simp [buildFrom]
  | cons edge rest inductionHypothesis =>
      rw [buildFrom, inductionHypothesis]
      simp only [insertOccurrence_cell, List.any_cons]
      rw [Bool.or_assoc]

/-- The occurrence-wise materializer starts from the empty matrix. -/
def materialize {n : Nat} (graph : EdgeList.Rep n) :
    AdjacencyMatrix.Rep n :=
  buildFrom (AdjacencyMatrix.empty n) graph.entries

theorem materialize_cell {n : Nat} (graph : EdgeList.Rep n)
    (u v : Fin n) :
    (materialize graph).cell u v =
      graph.entries.any (EdgeList.accepts · (u, v)) := by
  simp [materialize, buildFrom_cell, AdjacencyMatrix.empty]

/-- Adjacency-matrix values are determined by their cell function; invariant
proof fields carry no additional computational identity. -/
theorem matrix_ext {n : Nat} {first second : AdjacencyMatrix.Rep n}
    (cells : first.cell = second.cell) : first = second := by
  cases first with
  | mk firstCell firstSymmetric firstLoopless =>
      cases second with
      | mk secondCell secondSymmetric secondLoopless =>
          change firstCell = secondCell at cells
          cases cells
          rfl

/-- The detailed occurrence-wise algorithm computes exactly the pre-existing
extensional refinement, cell for cell—not merely an isomorphic graph. -/
theorem materialize_eq_refinement {n : Nat} (graph : EdgeList.Rep n) :
    materialize graph =
      Transformations.toMatrix (EdgeList.presentation n) graph := by
  apply matrix_ext
  funext u v
  rw [materialize_cell]
  change graph.entries.any (EdgeList.accepts · (u, v)) =
    (EdgeList.edge graph u v).value
  exact (LinearProbe.run_value_eq_any EdgeList.accepts (u, v)
    graph.entries).symm

/-! ## Small-step execution -/

/-- Machine states retain the unconsumed occurrences and the matrix built so
far. -/
inductive State (n : Nat) where
  | active (remaining : List (EdgeList.Edge n))
      (matrix : AdjacencyMatrix.Rep n)
  | done (matrix : AdjacencyMatrix.Rep n)

/-- One rewrite consumes one occurrence; the final rewrite exposes the
computed matrix. -/
inductive Step {n : Nat} : State n → State n → Prop where
  | write (edge : EdgeList.Edge n) (rest : List (EdgeList.Edge n))
      (matrix : AdjacencyMatrix.Rep n) :
      Step (.active (edge :: rest) matrix)
        (.active rest (insertOccurrence matrix edge))
  | finish (matrix : AdjacencyMatrix.Rep n) :
      Step (.active [] matrix) (.done matrix)

/-- The authentic occurrence-wise materialization GSLT. -/
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

/-- Executable single-step implementation. -/
def step? {n : Nat} : State n → Option (State n)
  | .active (edge :: rest) matrix =>
      some (.active rest (insertOccurrence matrix edge))
  | .active [] matrix => some (.done matrix)
  | .done _ => none

/-- Executable and relational one-step semantics agree exactly. -/
theorem step?_eq_some_iff {n : Nat} (source target : State n) :
    step? source = some target ↔ Step source target := by
  constructor
  · intro executed
    cases source with
    | active remaining matrix =>
        cases remaining with
        | nil =>
            simp only [step?, Option.some.injEq] at executed
            subst target
            exact .finish matrix
        | cons edge rest =>
            simp only [step?, Option.some.injEq] at executed
            subst target
            exact .write edge rest matrix
    | done matrix =>
        simp only [step?, reduceCtorEq] at executed
  · intro transition
    cases transition <;> rfl

/-- The exact matrix obtained by completing a machine state.  It is selected
independently of the step relation and exposes the loop invariant. -/
def State.completion {n : Nat} : State n → AdjacencyMatrix.Rep n
  | .active remaining matrix => buildFrom matrix remaining
  | .done matrix => matrix

/-- Every local transition preserves the exact eventual matrix, not only its
graph denotation. -/
theorem step_preserves_completion {n : Nat} {source target : State n}
    (step : Step source target) :
    source.completion = target.completion := by
  cases step <;> rfl

/-- Complete execution consumes every occurrence and then exposes the
accumulator. -/
def runPath {n : Nat} :
    (remaining : List (EdgeList.Edge n)) →
    (matrix : AdjacencyMatrix.Rep n) →
    (theory n).RewritePath (.active remaining matrix)
      (.done (buildFrom matrix remaining))
  | [], matrix => .cons (.finish matrix) (.nil _)
  | edge :: rest, matrix =>
      .cons (.write edge rest matrix)
        (runPath rest (insertOccurrence matrix edge))

@[simp] theorem runPath_length {n : Nat}
    (remaining : List (EdgeList.Edge n))
    (matrix : AdjacencyMatrix.Rep n) :
    (runPath remaining matrix).length = remaining.length + 1 := by
  induction remaining generalizing matrix with
  | nil => rfl
  | cons edge rest inductionHypothesis =>
      change 1 + (runPath rest (insertOccurrence matrix edge)).length =
        rest.length + 2
      rw [inductionHypothesis]
      omega

/-- The initial state for one edge-list graph. -/
def initial {n : Nat} (graph : EdgeList.Rep n) : State n :=
  .active graph.entries (AdjacencyMatrix.empty n)

/-- The detailed path terminates at the matrix computed by the occurrence-wise
algorithm.  `materialize_eq_refinement` identifies that endpoint exactly with
the established extensional refinement. -/
def materializePath {n : Nat} (graph : EdgeList.Rep n) :
    (theory n).RewritePath (initial graph)
      (.done (materialize graph)) :=
  runPath graph.entries (AdjacencyMatrix.empty n)

@[simp] theorem materializePath_length {n : Nat} (graph : EdgeList.Rep n) :
    (materializePath graph).length = graph.entries.length + 1 := by
  exact runPath_length graph.entries (AdjacencyMatrix.empty n)

/-- Terminal states are normal forms. -/
theorem done_normal {n : Nat} (matrix : AdjacencyMatrix.Rep n) :
    (theory n).IsNormalForm (.done matrix) := by
  rintro ⟨target, transition⟩
  cases transition

namespace Canary

open EdgeList.Canary

/-- The two stored occurrences of the path graph require two local writes and
one finalization step. -/
theorem path3_materialize_length :
    (materializePath path3).length = 3 := by
  simp [path3, materializePath_length]

/-- Positive control: the materialized path contains edge `0--1`. -/
theorem path3_edge_present :
    (materialize path3).cell v0 v1 = true := by
  decide

/-- Negative control: materialization does not invent edge `0--2`. -/
theorem path3_nonedge_absent :
    (materialize path3).cell v0 v2 = false := by
  decide

/-- Negative control: a loop occurrence performs no matrix update. -/
def loopOnly : EdgeList.Rep 1 :=
  ⟨[⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩]⟩

theorem loopOnly_materializes_empty :
    materialize loopOnly = AdjacencyMatrix.empty 1 := by
  apply matrix_ext
  funext u v
  rw [Fin.eq_zero u, Fin.eq_zero v]
  rfl

end Canary

#print axioms accepts_swap
#print axioms materialize_eq_refinement
#print axioms step?_eq_some_iff
#print axioms step_preserves_completion
#print axioms materializePath
#print axioms materializePath_length
#print axioms done_normal
#print axioms Canary.path3_edge_present
#print axioms Canary.path3_nonedge_absent
#print axioms Canary.loopOnly_materializes_empty

end Mettapedia.GraphTheory.Representation.EdgeListToMatrixGSLT
