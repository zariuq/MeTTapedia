import Mettapedia.GSLT.Core.SemanticQuery
import Mettapedia.GraphTheory.Representation.Hypergraph
import Mettapedia.GraphTheory.Representation.Metagraph
import Mettapedia.GraphTheory.Representation.DistinctionBridge

/-!
# Semantic query GSLTs for higher graph representations

Hypergraph incidence, metagraph linkage, and sampled observational
distinction have different authored structures, but their atomic observations
share one semantic control shape.  This module interprets each concrete query
machine in `SemanticQuery`: the request retains exactly the mathematical world
and address that determine the answer, and the answer is selected by an
independently stated relation.

The distinction bridge is intentionally asymmetric.  Compilation preserves a
sampled distinction answer, but a Boolean matrix cannot reconstruct the
formula occurrence that witnessed that answer.  The operational square is
therefore indexed by the source sample rather than pretending that matrix
erasure has a global inverse.
-/

namespace Mettapedia.GraphTheory.Representation.HigherGraphSemanticGSLT

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational

set_option autoImplicit false

/-! ## Hypergraph incidence -/

/-- The mathematical incidence observation of a named hyperedge occurrence. -/
def hypergraphObserve {Vertex Edge : Type} [DecidableEq Vertex]
    (graph : Hypergraph.Rep Vertex Edge) (query : Vertex × Edge) : Bool :=
  decide (query.1 ∈ graph.incident query.2)

theorem hypergraphObserve_eq_true_iff {Vertex Edge : Type}
    [DecidableEq Vertex] (graph : Hypergraph.Rep Vertex Edge)
    (query : Vertex × Edge) :
    hypergraphObserve graph query = true ↔
      query.1 ∈ graph.incident query.2 := by
  simp [hypergraphObserve]

/-- Interpret a concrete finite-set incidence query in its semantic machine. -/
def interpretHypergraphState {Vertex Edge : Type} :
    Hypergraph.QueryState Vertex Edge →
      Mettapedia.GSLT.SemanticQuery.State
        (Hypergraph.Rep Vertex Edge) (Vertex × Edge) Bool
  | .lookup graph vertex edge => .request graph (vertex, edge)
  | .answer value => .answer value

theorem hypergraph_incident_eq_observe {Vertex Edge : Type}
    [DecidableEq Vertex] (graph : Hypergraph.Rep Vertex Edge)
    (vertex : Vertex) (edge : Edge) :
    (Hypergraph.incident graph vertex edge).value =
      hypergraphObserve graph (vertex, edge) :=
  rfl

/-- Finite-set membership is an exact implementation of semantic incidence. -/
def hypergraphQueryTranslation (Vertex Edge : Type) [DecidableEq Vertex] :
    CoveredTranslation (Hypergraph.queryTheory Vertex Edge)
      (Mettapedia.GSLT.SemanticQuery.theory
        (@hypergraphObserve Vertex Edge _)) where
  mapTerm := interpretHypergraphState
  mapEquiv := by
    intro left right equivalent
    cases equivalent
    rfl
  cover :=
    { mapStep := by
        intro source target step
        cases step with
        | read graph vertex edge =>
            exact .answer graph (vertex, edge)
      liftStep := by
        intro source target semanticStep
        cases source with
        | lookup graph vertex edge =>
            cases semanticStep
            exact ⟨.answer (Hypergraph.incident graph vertex edge).value,
              .read graph vertex edge, rfl⟩
        | answer value => cases semanticStep }

/-- Concrete hypergraph membership realizes compositionally into its
discrete Boolean meaning. -/
def hypergraphAnswerRealization (Vertex Edge : Type) [DecidableEq Vertex] :
    OperationalRealization (Hypergraph.queryTheory Vertex Edge)
      (GSLT.discrete Bool) :=
  (OperationalRealization.ofTranslation
      ((hypergraphQueryTranslation Vertex Edge).toOperational)).comp
    (Mettapedia.GSLT.SemanticQuery.answerRealization
      (@hypergraphObserve Vertex Edge _))

@[simp] theorem hypergraphAnswerRealization_mapTerm
    {Vertex Edge : Type} [DecidableEq Vertex]
    (state : Hypergraph.QueryState Vertex Edge) :
    (hypergraphAnswerRealization Vertex Edge).mapTerm state =
      Mettapedia.GSLT.SemanticQuery.observation
        (@hypergraphObserve Vertex Edge _) (interpretHypergraphState state) :=
  rfl

/-- Arbitrary-target reflection for represented hypergraph query states. -/
theorem hypergraph_step_iff {Vertex Edge : Type} [DecidableEq Vertex]
    (source : Hypergraph.QueryState Vertex Edge)
    (target : Mettapedia.GSLT.SemanticQuery.State
      (Hypergraph.Rep Vertex Edge) (Vertex × Edge) Bool) :
    Mettapedia.GSLT.SemanticQuery.Step
        (@hypergraphObserve Vertex Edge _)
        (interpretHypergraphState source) target ↔
      ∃ concreteTarget,
        Hypergraph.QueryStep source concreteTarget ∧
          interpretHypergraphState concreteTarget = target := by
  constructor
  · exact (hypergraphQueryTranslation Vertex Edge).cover.liftStep
  · rintro ⟨concreteTarget, concreteStep, rfl⟩
    exact (hypergraphQueryTranslation Vertex Edge).cover.mapStep concreteStep

/-! ## Directed labeled metagraph linkage -/

/-- The extensional linkage observation of a metagraph.  The world still
retains authored port order, labels, and enrichments even though this
particular observation asks only whether a target occurs. -/
noncomputable def metagraphObserve {Object Label Enrichment : Type}
    (graph : Metagraph.Rep Object Label Enrichment)
    (query : Object × Object) : Bool := by
  classical
  exact decide (Metagraph.Linked graph query.1 query.2)

theorem metagraphObserve_eq_true_iff {Object Label Enrichment : Type}
    (graph : Metagraph.Rep Object Label Enrichment)
    (query : Object × Object) :
    metagraphObserve graph query = true ↔
      Metagraph.Linked graph query.1 query.2 := by
  classical
  simp [metagraphObserve]

/-- Interpret an authored port scan in the semantic linkage machine. -/
def interpretMetagraphState {Object Label Enrichment : Type} :
    Metagraph.QueryState Object Label Enrichment →
      Mettapedia.GSLT.SemanticQuery.State
        (Metagraph.Rep Object Label Enrichment) (Object × Object) Bool
  | .lookup graph source target => .request graph (source, target)
  | .answer value => .answer value

theorem metagraph_linked_eq_observe {Object Label Enrichment : Type}
    [DecidableEq Object] (graph : Metagraph.Rep Object Label Enrichment)
    (source target : Object) :
    (Metagraph.linked graph source target).value =
      metagraphObserve graph (source, target) := by
  rw [Bool.eq_iff_iff]
  simpa [metagraphObserve] using Metagraph.linked_sound graph source target

/-- Ordered port probing is an exact implementation of semantic linkage. -/
noncomputable def metagraphQueryTranslation
    (Object Label Enrichment : Type) [DecidableEq Object] :
    CoveredTranslation (Metagraph.queryTheory Object Label Enrichment)
      (Mettapedia.GSLT.SemanticQuery.theory
        (@metagraphObserve Object Label Enrichment)) where
  mapTerm := interpretMetagraphState
  mapEquiv := by
    intro left right equivalent
    cases equivalent
    rfl
  cover :=
    { mapStep := by
        intro source target step
        cases step with
        | read graph source target =>
            change Mettapedia.GSLT.SemanticQuery.Step
              (@metagraphObserve Object Label Enrichment)
              (.request graph (source, target))
              (.answer (Metagraph.linked graph source target).value)
            rw [metagraph_linked_eq_observe graph source target]
            exact .answer graph (source, target)
      liftStep := by
        intro source target semanticStep
        cases source with
        | lookup graph source target =>
            cases semanticStep
            exact ⟨.answer (Metagraph.linked graph source target).value,
              .read graph source target,
              by
                simp only [interpretMetagraphState]
                rw [metagraph_linked_eq_observe graph source target]⟩
        | answer value => cases semanticStep }

/-- Concrete authored-port lookup realizes compositionally into its
discrete Boolean linkage meaning. -/
noncomputable def metagraphAnswerRealization
    (Object Label Enrichment : Type) [DecidableEq Object] :
    OperationalRealization (Metagraph.queryTheory Object Label Enrichment)
      (GSLT.discrete Bool) :=
  (OperationalRealization.ofTranslation
      ((metagraphQueryTranslation Object Label Enrichment).toOperational)).comp
    (Mettapedia.GSLT.SemanticQuery.answerRealization
      (@metagraphObserve Object Label Enrichment))

@[simp] theorem metagraphAnswerRealization_mapTerm
    {Object Label Enrichment : Type} [DecidableEq Object]
    (state : Metagraph.QueryState Object Label Enrichment) :
    (metagraphAnswerRealization Object Label Enrichment).mapTerm state =
      Mettapedia.GSLT.SemanticQuery.observation
        (@metagraphObserve Object Label Enrichment)
        (interpretMetagraphState state) :=
  rfl

/-- Arbitrary-target reflection for represented metagraph query states. -/
theorem metagraph_step_iff {Object Label Enrichment : Type}
    [DecidableEq Object]
    (source : Metagraph.QueryState Object Label Enrichment)
    (target : Mettapedia.GSLT.SemanticQuery.State
      (Metagraph.Rep Object Label Enrichment) (Object × Object) Bool) :
    Mettapedia.GSLT.SemanticQuery.Step
        (@metagraphObserve Object Label Enrichment)
        (interpretMetagraphState source) target ↔
      ∃ concreteTarget,
        Metagraph.QueryStep source concreteTarget ∧
          interpretMetagraphState concreteTarget = target := by
  constructor
  · exact
      (metagraphQueryTranslation Object Label Enrichment).cover.liftStep
  · rintro ⟨concreteTarget, concreteStep, rfl⟩
    exact
      (metagraphQueryTranslation Object Label Enrichment).cover.mapStep
        concreteStep

/-! ## Sampled distinction graphs -/

/-- The independently stated distinction answer for a source-addressable
finite sample. -/
def distinctionObserve {n : Nat}
    {R : DistinctionBridge.Pat → DistinctionBridge.Pat → Prop}
    {I : Mettapedia.OSLF.Formula.AtomSem}
    (sample : DistinctionBridge.Sample n R I)
    (query : Fin n × Fin n) : Bool :=
  @decide
    (Mettapedia.OSLF.Framework.DistinctionGraph.distinguished R I
      (sample.node query.1) (sample.node query.2))
    (sample.decision query.1 query.2)

/-- Reading the compiled matrix preserves exactly the sampled distinction
answer. -/
def compiledDistinctionObserve {n : Nat}
    {R : DistinctionBridge.Pat → DistinctionBridge.Pat → Prop}
    {I : Mettapedia.OSLF.Formula.AtomSem}
    (sample : DistinctionBridge.Sample n R I)
    (query : Fin n × Fin n) : Bool :=
  (DistinctionBridge.compile sample).cell query.1 query.2

@[simp] theorem compiledDistinctionObserve_eq {n : Nat}
    {R : DistinctionBridge.Pat → DistinctionBridge.Pat → Prop}
    {I : Mettapedia.OSLF.Formula.AtomSem}
    (sample : DistinctionBridge.Sample n R I)
    (query : Fin n × Fin n) :
    compiledDistinctionObserve sample query = distinctionObserve sample query :=
  rfl

/-- Compilation changes the observation implementation while leaving the
source-addressable query state intact.  Keeping the sample is the provenance
needed to state exact reflection. -/
def distinctionCompilationTranslation (n : Nat)
    (R : DistinctionBridge.Pat → DistinctionBridge.Pat → Prop)
    (I : Mettapedia.OSLF.Formula.AtomSem) :
    CoveredTranslation
      (Mettapedia.GSLT.SemanticQuery.theory
        (@compiledDistinctionObserve n R I))
      (Mettapedia.GSLT.SemanticQuery.theory
        (@distinctionObserve n R I)) where
  mapTerm := id
  mapEquiv := by
    intro left right equivalent
    exact equivalent
  cover :=
    { mapStep := by
        intro source target step
        cases step with
        | answer sample query =>
            change Mettapedia.GSLT.SemanticQuery.Step
              (@distinctionObserve n R I)
              (.request sample query)
              (.answer (compiledDistinctionObserve sample query))
            rw [compiledDistinctionObserve_eq sample query]
            exact .answer sample query
      liftStep := by
        intro source target semanticStep
        cases source with
        | request sample query =>
            cases semanticStep
            exact ⟨.answer (compiledDistinctionObserve sample query),
              .answer sample query,
              congrArg Mettapedia.GSLT.SemanticQuery.State.answer
                (compiledDistinctionObserve_eq sample query)⟩
        | answer value => cases semanticStep }

/-- Compiled sampled distinction queries realize into their discrete source
meaning by genuine composition through the source-indexed semantic query
GSLT. -/
def distinctionAnswerRealization (n : Nat)
    (R : DistinctionBridge.Pat → DistinctionBridge.Pat → Prop)
    (I : Mettapedia.OSLF.Formula.AtomSem) :
    OperationalRealization
      (Mettapedia.GSLT.SemanticQuery.theory
        (@compiledDistinctionObserve n R I))
      (GSLT.discrete Bool) :=
  (OperationalRealization.ofTranslation
      ((distinctionCompilationTranslation n R I).toOperational)).comp
    (Mettapedia.GSLT.SemanticQuery.answerRealization
      (@distinctionObserve n R I))

@[simp] theorem distinctionAnswerRealization_mapTerm {n : Nat}
    {R : DistinctionBridge.Pat → DistinctionBridge.Pat → Prop}
    {I : Mettapedia.OSLF.Formula.AtomSem}
    (state : Mettapedia.GSLT.SemanticQuery.State
      (DistinctionBridge.Sample n R I) (Fin n × Fin n) Bool) :
    (distinctionAnswerRealization n R I).mapTerm state =
      Mettapedia.GSLT.SemanticQuery.observation
        (@distinctionObserve n R I) state :=
  rfl

/-- The actual adjacency-matrix query path for a compiled sample reaches the
same independently selected distinction answer. -/
def compiledMatrixQueryPath {n : Nat}
    {R : DistinctionBridge.Pat → DistinctionBridge.Pat → Prop}
    {I : Mettapedia.OSLF.Formula.AtomSem}
    (sample : DistinctionBridge.Sample n R I)
    (query : Fin n × Fin n) :
    (AdjacencyMatrix.theory n).RewritePath
      (.lookup (DistinctionBridge.compile sample) query.1 query.2)
      (.answer (distinctionObserve sample query)) := by
  rw [← compiledDistinctionObserve_eq sample query]
  exact AdjacencyMatrix.lookupPath (DistinctionBridge.compile sample)
    query.1 query.2

/-! ## Discriminating controls -/

namespace Canary

/-- The semantic metagraph world retains authored structure even when two
worlds have the same extensional linkage observation. -/
theorem metagraph_worlds_remain_distinct :
    Metagraph.Canary.first ≠ Metagraph.Canary.reordered := by
  intro equal
  exact Metagraph.Canary.authored_ports_differ
    (congrArg (fun graph => graph.ports Metagraph.Canary.o0) equal)

/-- Matrix compilation cannot make erased separator identity recoverable. -/
theorem distinction_matrix_does_not_determine_witness :
    DistinctionBridge.Canary.firstWitness.erase =
        DistinctionBridge.Canary.secondWitness.erase ∧
      DistinctionBridge.Canary.firstWitness.witness ≠
        DistinctionBridge.Canary.secondWitness.witness :=
  DistinctionBridge.Canary.same_matrix_different_witnesses

end Canary

#print axioms hypergraphQueryTranslation
#print axioms hypergraphAnswerRealization
#print axioms hypergraph_step_iff
#print axioms metagraphQueryTranslation
#print axioms metagraphAnswerRealization
#print axioms metagraph_step_iff
#print axioms distinctionCompilationTranslation
#print axioms distinctionAnswerRealization
#print axioms compiledMatrixQueryPath
#print axioms Canary.metagraph_worlds_remain_distinct
#print axioms Canary.distinction_matrix_does_not_determine_witness

end Mettapedia.GraphTheory.Representation.HigherGraphSemanticGSLT
