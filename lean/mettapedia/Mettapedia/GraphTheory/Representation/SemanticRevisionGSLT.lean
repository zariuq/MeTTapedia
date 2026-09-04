import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.GSLT.Core.SemanticTransport
import Mettapedia.GraphTheory.Representation.AdjacencyMatrix
import Mettapedia.GraphTheory.Representation.RevisionQuery

/-!
# Semantic revision and query GSLT for finite simple graphs

Concrete graph presentations retain layout, resource, and construction data.
This module gives the independent operational meaning of a mixed edit/query
workload.  Its live graph is a Mathlib `SimpleGraph`; it records the authored
workload order and every answer occurrence, but contains no representation
layout or resource account.

The interpretation from `RevisionQuery.revisionTheory` is deliberately a
covered operational translation.  Thus a concrete step has its semantic
counterpart, and every semantic step leaving an interpreted concrete state is
realized by a concrete step.  Representation conversion is a different,
semantically silent machine and belongs to `SemanticInvariant` instead.
-/

namespace Mettapedia.GraphTheory.Representation.SemanticRevisionGSLT

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite

set_option autoImplicit false

/-- The independent Boolean answer to one graph adjacency query. -/
noncomputable def answer {n : Nat} (graph : SimpleGraph (Fin n))
    (query : EdgeQuery n) : Bool := by
  classical
  exact decide (graph.Adj query.1 query.2)

/-- The observable terminal result of an abstract revision/query workload. -/
structure Result (n : Nat) where
  graph : SimpleGraph (Fin n)
  answers : List Bool

/-- Abstract state for an ordered graph revision/query workload. -/
inductive State (n : Nat) where
  | active (graph : SimpleGraph (Fin n)) (remaining : List (WorkItem n))
      (answersReversed : List Bool)
  | finished (result : Result n)

/-- One abstract workload action: query the current graph, revise it, or
finish an exhausted schedule. -/
inductive Step {n : Nat} : State n → State n → Prop where
  | observe (graph : SimpleGraph (Fin n)) (query : EdgeQuery n)
      (remaining : List (WorkItem n)) (answersReversed : List Bool) :
      Step (.active graph (.query query :: remaining) answersReversed)
        (.active graph remaining (answer graph query :: answersReversed))
  | revise (graph : SimpleGraph (Fin n)) (change : EdgeEdit n)
      (remaining : List (WorkItem n)) (answersReversed : List Bool) :
      Step (.active graph (.edit change :: remaining) answersReversed)
        (.active (applyMeaning graph change) remaining answersReversed)
  | finish (graph : SimpleGraph (Fin n)) (answersReversed : List Bool) :
      Step (.active graph [] answersReversed)
        (.finished ⟨graph, answersReversed.reverse⟩)

/-- The independent semantic GSLT for finite simple-graph revision and
query. -/
noncomputable def theory (n : Nat) : GSLT where
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

/-- The exact executable semantic result of a finite workload. -/
noncomputable def executeAux {n : Nat} :
    (graph : SimpleGraph (Fin n)) → (workload : List (WorkItem n)) →
    (answersReversed : List Bool) → Result n
  | graph, [], answersReversed => ⟨graph, answersReversed.reverse⟩
  | graph, .query query :: remaining, answersReversed =>
      executeAux graph remaining (answer graph query :: answersReversed)
  | graph, .edit change :: remaining, answersReversed =>
      executeAux (applyMeaning graph change) remaining answersReversed

/-- Execute a workload from an empty answer history. -/
noncomputable def execute {n : Nat} (graph : SimpleGraph (Fin n))
    (workload : List (WorkItem n)) : Result n :=
  executeAux graph workload []

/-- Every semantic workload has a proof-relevant path to its exact result. -/
noncomputable def executeAuxPath {n : Nat} :
    (graph : SimpleGraph (Fin n)) → (workload : List (WorkItem n)) →
    (answersReversed : List Bool) →
    (theory n).RewritePath
      (.active graph workload answersReversed)
      (.finished (executeAux graph workload answersReversed))
  | graph, [], answersReversed =>
      .cons (.finish graph answersReversed) (.nil _)
  | graph, .query query :: remaining, answersReversed =>
      .cons (.observe graph query remaining answersReversed)
        (executeAuxPath graph remaining (answer graph query :: answersReversed))
  | graph, .edit change :: remaining, answersReversed =>
      .cons (.revise graph change remaining answersReversed)
        (executeAuxPath (applyMeaning graph change) remaining answersReversed)

/-- The complete semantic workload path. -/
noncomputable def executePath {n : Nat} (graph : SimpleGraph (Fin n))
    (workload : List (WorkItem n)) :
    (theory n).RewritePath
      (.active graph workload [])
      (.finished (execute graph workload)) :=
  executeAuxPath graph workload []

/-- Finished semantic results have no outgoing operational step. -/
theorem finished_normal {n : Nat} (result : Result n) :
    (theory n).IsNormalForm (.finished result) := by
  rintro ⟨target, step⟩
  cases step

/-! ## Semantic atomic graph queries -/

/-- The graph-level semantic machine for one adjacency observation.  Its
request retains the graph and address because those are the semantic support
of the result; its answer is the externally visible Boolean observation. -/
inductive QueryState (n : Nat) where
  | request (graph : SimpleGraph (Fin n)) (query : EdgeQuery n)
  | answer (value : Bool)

/-- One semantic graph observation computes exactly the current adjacency
answer. -/
inductive QueryStep {n : Nat} : QueryState n → QueryState n → Prop where
  | observe (graph : SimpleGraph (Fin n)) (query : EdgeQuery n) :
      QueryStep (.request graph query) (.answer (answer graph query))

/-- The independent GSLT for one graph adjacency observation. -/
noncomputable def queryTheory (n : Nat) : GSLT where
  Term := QueryState n
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := QueryStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- The selected semantic observation is unchanged by the administrative
request-to-answer transition. -/
noncomputable def queryObservation {n : Nat} : QueryState n → Bool
  | .request graph query => answer graph query
  | .answer value => value

theorem queryStep_preserves_observation {n : Nat}
    {source target : QueryState n} (step : QueryStep source target) :
    queryObservation source = queryObservation target := by
  cases step
  rfl

/-- The answer selected by a graph query is invariant across its request and
answer control states.  This is an invariant of the query control machine,
not an assertion that graph revision preserves graph meaning. -/
noncomputable def queryAnswerInvariant (n : Nat) :
    Mettapedia.GSLT.SemanticInvariant (queryTheory n) Bool where
  denote := queryObservation
  equation := by
    intro source target equal
    cases equal
    rfl
  rewrite := queryStep_preserves_observation

/-- The semantic atomic query has one explicit observation path. -/
noncomputable def queryPath {n : Nat} (graph : SimpleGraph (Fin n))
    (query : EdgeQuery n) :
    (queryTheory n).RewritePath (.request graph query)
      (.answer (answer graph query)) :=
  .cons (.observe graph query) (.nil _)

theorem queryPath_preserves_observation {n : Nat} :
    {source target : QueryState n} →
      (queryTheory n).RewritePath source target →
        queryObservation source = queryObservation target
  | _, _, .nil _ => rfl
  | _, _, .cons step rest =>
      (queryStep_preserves_observation step).trans
        (queryPath_preserves_observation rest)

/-- An answer state is a normal semantic query result. -/
theorem queryAnswer_normal {n : Nat} (value : Bool) :
    (queryTheory n).IsNormalForm (.answer value) := by
  rintro ⟨target, step⟩
  cases step

/-- A normal result of a semantic graph query is the unique adjacency
answer determined by its request. -/
theorem query_terminal_exact {n : Nat} (graph : SimpleGraph (Fin n))
    (query : EdgeQuery n) (terminal : QueryState n)
    (path : (queryTheory n).RewritePath (.request graph query) terminal)
    (normal : (queryTheory n).IsNormalForm terminal) :
    terminal = .answer (answer graph query) := by
  cases terminal with
  | request terminalGraph terminalQuery =>
      exact (normal ⟨.answer (answer terminalGraph terminalQuery),
        .observe terminalGraph terminalQuery⟩).elim
  | answer value =>
      have observed : answer graph query = value := by
        change queryObservation (n := n) (.request graph query) =
          queryObservation (n := n) (.answer value)
        exact queryPath_preserves_observation path
      cases observed
      rfl

/-- The one-query workload fragment has the same graph and Boolean result as
the atomic semantic query machine. -/
@[simp] theorem execute_single_query {n : Nat} (graph : SimpleGraph (Fin n))
    (query : EdgeQuery n) :
    execute graph [.query query] = ⟨graph, [answer graph query]⟩ :=
  rfl

/-- No semantic query path can invent an incorrect Boolean answer. -/
theorem query_cannot_answer_wrong {n : Nat} (graph : SimpleGraph (Fin n))
    (query : EdgeQuery n) (wrong : Bool)
    (different : wrong ≠ answer graph query) :
    ¬ Nonempty ((queryTheory n).RewritePath
      (.request graph query) (.answer wrong)) := by
  rintro ⟨path⟩
  have observed : answer graph query = wrong := by
    change queryObservation (n := n) (.request graph query) =
      queryObservation (n := n) (.answer wrong)
    exact queryPath_preserves_observation path
  exact different observed.symm

/-! ## Concrete-to-semantic interpretation -/

/-- Forget physical resource accounting while retaining the graph and the
ordered answer occurrences. -/
def interpretResult {n : Nat} (presentation : EditablePresentation n)
    (result : WorkloadResult presentation) : Result n :=
  ⟨presentation.denote result.graph, result.answers⟩

/-- Interpret a concrete workload state as the independent graph state. -/
def interpretState {n : Nat} (presentation : EditablePresentation n) :
    RevisionState presentation → State n
  | .active graph remaining answersReversed _ =>
      .active (presentation.denote graph) remaining answersReversed
  | .finished result => .finished (interpretResult presentation result)

/-- A concrete edge observation equals the semantic adjacency answer. -/
theorem edge_value_eq_answer {n : Nat} (presentation : EditablePresentation n)
    (graph : presentation.Carrier) (source target : Fin n) :
    (presentation.edge graph source target).value =
      answer (presentation.denote graph) (source, target) := by
  classical
  rw [Bool.eq_iff_iff]
  simpa [answer] using presentation.edge_sound graph source target

/-! ## Exact matrix-query factor -/

/-- Interpret a concrete matrix-query control state in the graph-level query
machine.  The matrix representation is forgotten only after its independently
proved `SimpleGraph` denotation has been taken. -/
def interpretMatrixState {n : Nat} : AdjacencyMatrix.State n → QueryState n
  | .lookup graph source target =>
      .request (AdjacencyMatrix.denote graph) (source, target)
  | .answer value => .answer value

/-- A concrete adjacency-matrix cell read equals the independent semantic
graph answer. -/
theorem matrix_cell_eq_answer {n : Nat} (graph : AdjacencyMatrix.Rep n)
    (source target : Fin n) :
    graph.cell source target =
      answer (AdjacencyMatrix.denote graph) (source, target) := by
  classical
  rw [Bool.eq_iff_iff]
  simpa [answer, AdjacencyMatrix.edge] using
    AdjacencyMatrix.edge_sound graph source target

/-- The concrete matrix query GSLT is an exact local operational
implementation of the independent graph-query GSLT. -/
noncomputable def matrixQueryTranslation (n : Nat) :
    CoveredTranslation (AdjacencyMatrix.theory n) (queryTheory n) where
  mapTerm := interpretMatrixState
  mapEquiv := by
    intro left right equivalent
    cases equivalent
    rfl
  cover :=
    { mapStep := by
        intro source target step
        cases step with
        | read graph source target =>
            change QueryStep
              (.request (AdjacencyMatrix.denote graph) (source, target))
              (.answer (graph.cell source target))
            rw [matrix_cell_eq_answer graph source target]
            exact .observe _ _
      liftStep := by
        intro source target semanticStep
        cases source with
        | lookup graph source target =>
            cases semanticStep
            exact ⟨.answer (graph.cell source target),
              .read graph source target,
              by
                simp only [interpretMatrixState]
                rw [matrix_cell_eq_answer graph source target]⟩
        | answer value =>
            cases semanticStep }

/-- The complete physical-matrix-to-Boolean semantic chain, formed by
composition of the exact matrix/query translation and the query invariant's
realization into a discrete answer GSLT. -/
noncomputable def matrixAnswerRealization (n : Nat) :
    OperationalRealization (AdjacencyMatrix.theory n) (GSLT.discrete Bool) :=
  (OperationalRealization.ofTranslation
      ((matrixQueryTranslation n).toOperational)).comp
    ((queryAnswerInvariant n).toDiscreteRealization)

@[simp] theorem matrixAnswerRealization_mapTerm {n : Nat}
    (state : AdjacencyMatrix.State n) :
    (matrixAnswerRealization n).mapTerm state =
      queryObservation (interpretMatrixState state) :=
  rfl

/-- A physical matrix read becomes a zero-length path at the independently
selected Boolean meaning. -/
theorem matrixAnswerRealization_step_length {n : Nat}
    {source target : AdjacencyMatrix.State n}
    (step : AdjacencyMatrix.Step source target) :
    ((matrixAnswerRealization n).mapStep step).length = 0 :=
  Mettapedia.GSLT.IndexedOperational.discreteExecutionPath_length _

/-- The exact matrix-to-graph-query reflection theorem in an immediately
usable form.  It covers all semantic transitions from represented matrix
states without asserting that unrelated semantic query states are matrices. -/
theorem matrix_step_iff {n : Nat} (source : AdjacencyMatrix.State n)
    (target : QueryState n) :
    QueryStep (interpretMatrixState source) target ↔
      ∃ concreteTarget,
        AdjacencyMatrix.Step source concreteTarget ∧
          interpretMatrixState concreteTarget = target := by
  constructor
  · exact (matrixQueryTranslation n).cover.liftStep
  · rintro ⟨concreteTarget, concreteStep, rfl⟩
    exact (matrixQueryTranslation n).cover.mapStep concreteStep

/-- The existing matrix machine and the semantic query machine agree on the
terminal Boolean observation at every request. -/
theorem matrix_query_terminal_factors {n : Nat} (graph : AdjacencyMatrix.Rep n)
    (source target : Fin n) :
    interpretMatrixState (n := n)
      (AdjacencyMatrix.State.answer (n := n) (graph.cell source target)) =
      QueryState.answer (n := n)
        (answer (AdjacencyMatrix.denote graph) (source, target)) := by
  simp only [interpretMatrixState]
  rw [matrix_cell_eq_answer graph source target]

/-- Each concrete workload step maps to precisely one semantic workload step.
The map forgets only physical layout and resources. -/
noncomputable def operationalTranslation {n : Nat}
    (presentation : EditablePresentation n) :
    OperationalTranslation (revisionTheory presentation) (theory n) where
  mapTerm := interpretState presentation
  mapEquiv := by
    intro left right equivalent
    cases equivalent
    rfl
  mapStep := by
    intro source target step
    cases step with
    | observe graph query remaining answersReversed used =>
        change Step
          (.active (presentation.denote graph) (.query query :: remaining)
            answersReversed)
          (.active (presentation.denote graph) remaining
            ((presentation.edge graph query.1 query.2).value :: answersReversed))
        rw [edge_value_eq_answer presentation graph query.1 query.2]
        exact .observe _ _ _ _
    | revise graph change remaining answersReversed used =>
        change Step
          (.active (presentation.denote graph) (.edit change :: remaining)
            answersReversed)
          (.active (presentation.denote (presentation.edit graph change).value)
            remaining answersReversed)
        rw [presentation.edit_sound graph change]
        exact .revise _ _ _ _
    | finish graph answersReversed used =>
        exact .finish (presentation.denote graph) answersReversed

/-- Semantic execution agrees exactly with the denotation of concrete
execution; resource accounting is intentionally outside this equality. -/
theorem interpret_executeAux {n : Nat} (presentation : EditablePresentation n) :
    (graph : presentation.Carrier) → (workload : List (WorkItem n)) →
    (answersReversed : List Bool) → (used : Resources) →
    interpretResult presentation
      (Mettapedia.GraphTheory.Representation.executeAux presentation graph
        workload answersReversed used) =
      executeAux (presentation.denote graph) workload answersReversed
  | graph, [], answersReversed, _ => rfl
  | graph, .query query :: remaining, answersReversed, used => by
      simp only [Mettapedia.GraphTheory.Representation.executeAux, executeAux]
      rw [edge_value_eq_answer presentation graph query.1 query.2]
      exact interpret_executeAux presentation graph remaining
        (answer (presentation.denote graph) query :: answersReversed)
        (used.seq (queryResources presentation.toPresentation graph query))
  | graph, .edit change :: remaining, answersReversed, used => by
      simp only [Mettapedia.GraphTheory.Representation.executeAux, executeAux]
      rw [← presentation.edit_sound graph change]
      exact interpret_executeAux presentation (presentation.edit graph change).value
        remaining answersReversed
        (used.seq (presentation.edit graph change).resources)

/-- The complete concrete result maps to the exact semantic result. -/
theorem interpret_execute {n : Nat} (presentation : EditablePresentation n)
    (graph : presentation.Carrier) (workload : List (WorkItem n)) :
    interpretResult presentation
      (Mettapedia.GraphTheory.Representation.execute presentation graph workload) =
      execute (presentation.denote graph) workload := by
  exact interpret_executeAux presentation graph workload [] Resources.zero

/-! ## Exact local reflection -/

/-- Every semantic step out of an interpreted concrete state is realized by
one concrete workload step.  This is local to the interpretation image: the
semantic state deliberately omits physical resources and layouts. -/
theorem step_iff {n : Nat} (presentation : EditablePresentation n)
    (source : RevisionState presentation) (target : State n) :
    Step (interpretState presentation source) target ↔
      ∃ concreteTarget,
        RevisionStep presentation source concreteTarget ∧
          interpretState presentation concreteTarget = target := by
  constructor
  · intro semanticStep
    cases source with
    | active graph remaining answersReversed used =>
        cases remaining with
        | nil =>
            cases semanticStep
            exact
              ⟨.finished ⟨graph, answersReversed.reverse, used⟩,
                .finish graph answersReversed used,
                rfl⟩
        | cons head remaining =>
            cases head with
            | query query =>
                cases semanticStep
                exact
                  ⟨.active graph remaining
                      ((presentation.edge graph query.1 query.2).value :: answersReversed)
                      (used.seq
                        (queryResources presentation.toPresentation graph query)),
                    .observe graph query remaining answersReversed used,
                    by
                      simp only [interpretState]
                      rw [edge_value_eq_answer presentation graph query.1 query.2]⟩
            | edit change =>
                cases semanticStep
                exact
                  ⟨.active (presentation.edit graph change).value remaining
                      answersReversed
                      (used.seq (presentation.edit graph change).resources),
                    .revise graph change remaining answersReversed used,
                    by
                      simp only [interpretState]
                      rw [presentation.edit_sound graph change]⟩
    | finished result =>
        cases semanticStep
  · rintro ⟨concreteTarget, concreteStep, rfl⟩
    exact (operationalTranslation presentation).mapStep concreteStep

/-- The concrete revision/query machine is a locally exact operational
realization of the semantic graph machine. -/
noncomputable def coveredTranslation {n : Nat}
    (presentation : EditablePresentation n) :
    CoveredTranslation (revisionTheory presentation) (theory n) where
  mapTerm := interpretState presentation
  mapEquiv := (operationalTranslation presentation).mapEquiv
  cover :=
    { mapStep := (operationalTranslation presentation).mapStep
      liftStep := by
        intro source target semanticStep
        exact (step_iff presentation source target).mp semanticStep }

namespace Canary

def v0 : Fin 2 := ⟨0, by omega⟩
def v1 : Fin 2 := ⟨1, by omega⟩
def edge01 : EdgeAddress 2 := ⟨v0, v1, by decide⟩

/-- The semantic graph changes under a genuine insertion. -/
theorem insert_changes_graph :
    applyMeaning (⊥ : SimpleGraph (Fin 2)) (.insert edge01) ≠ ⊥ := by
  intro unchanged
  have inserted := congrArg (fun graph => graph.Adj v0 v1) unchanged
  simp [edge01, v0, v1] at inserted

/-- Forgetting only control state is not a semantic invariant of revision:
the graph itself changes under an edit. -/
def stateGraph {n : Nat} : State n → SimpleGraph (Fin n)
  | .active graph _ _ => graph
  | .finished result => result.graph

/-- Negative control: graph denotation cannot be invariant for an authentic
revision GSLT, unlike representation conversion. -/
theorem no_graph_invariant_for_insert :
    ¬ ∃ invariant : Mettapedia.GSLT.SemanticInvariant
        (theory 2) (SimpleGraph (Fin 2)),
      invariant.denote = stateGraph := by
  rintro ⟨invariant, identifies⟩
  let source : State 2 :=
    .active ⊥ [.edit (.insert edge01)] []
  let target : State 2 :=
    .active (applyMeaning ⊥ (.insert edge01)) [] []
  have conserved : invariant.denote source = invariant.denote target := by
    change invariant.denote (.active ⊥ [.edit (.insert edge01)] []) =
      invariant.denote (.active (applyMeaning ⊥ (.insert edge01)) [] [])
    exact invariant.rewrite (.revise ⊥ (.insert edge01) [] [])
  have unchanged :
      (⊥ : SimpleGraph (Fin 2)) = applyMeaning ⊥ (.insert edge01) := by
    calc
      (⊥ : SimpleGraph (Fin 2)) = invariant.denote source := by
        exact (congrFun identifies source).symm
      _ = invariant.denote target := conserved
      _ = applyMeaning ⊥ (.insert edge01) := by
        exact congrFun identifies target
  exact insert_changes_graph unchanged.symm

end Canary

#print axioms operationalTranslation
#print axioms interpret_executeAux
#print axioms interpret_execute
#print axioms step_iff
#print axioms coveredTranslation
#print axioms query_terminal_exact
#print axioms queryAnswerInvariant
#print axioms queryPath
#print axioms execute_single_query
#print axioms query_cannot_answer_wrong
#print axioms matrixQueryTranslation
#print axioms matrixAnswerRealization
#print axioms matrixAnswerRealization_step_length
#print axioms matrix_step_iff
#print axioms matrix_query_terminal_factors
#print axioms Canary.insert_changes_graph
#print axioms Canary.no_graph_invariant_for_insert

end Mettapedia.GraphTheory.Representation.SemanticRevisionGSLT
