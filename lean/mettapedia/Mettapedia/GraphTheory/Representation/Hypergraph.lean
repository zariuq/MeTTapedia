import Mettapedia.GraphTheory.Representation.RevisionPortfolio
import Mathlib.Tactic.FinCases

/-!
# Finite hypergraphs as incidence GSLTs

A hypergraph keeps a named hyperedge occurrence separate from the vertices it
contains.  Its two-section graph is useful for ordinary adjacency algorithms,
but it forgets which pairs belonged to one common higher-arity occurrence.
The Levi graph retains incidence by using separate vertex and hyperedge nodes.
-/

namespace Mettapedia.GraphTheory.Representation.Hypergraph

open Mettapedia.GSLT
open Mettapedia.GraphTheory.Representation

set_option autoImplicit false

/-- A finite-incidence hypergraph.  The vertex and hyperedge identifier types
need not have the same cardinality or interpretation. -/
structure Rep (Vertex Edge : Type*) where
  incident : Edge → Finset Vertex

@[ext] theorem Rep.ext {Vertex Edge : Type*} {first second : Rep Vertex Edge}
    (incident : first.incident = second.incident) : first = second := by
  cases first
  cases second
  cases incident
  rfl

/-- Incidence is one abstract finite-set membership operation. -/
def incident {Vertex Edge : Type*} [DecidableEq Vertex]
    (graph : Rep Vertex Edge) (vertex : Vertex) (edge : Edge) : Measured Bool :=
  ⟨decide (vertex ∈ graph.incident edge), 1⟩

theorem incident_sound {Vertex Edge : Type*} [DecidableEq Vertex]
    (graph : Rep Vertex Edge) (vertex : Vertex) (edge : Edge) :
    (incident graph vertex edge).value = true ↔
      vertex ∈ graph.incident edge := by
  simp [incident]

/-- The ordinary pairwise graph obtained by joining distinct vertices that
occur in a common hyperedge. -/
def twoSection {Vertex Edge : Type*} (graph : Rep Vertex Edge) :
    SimpleGraph Vertex where
  Adj first second :=
    first ≠ second ∧ ∃ edge, first ∈ graph.incident edge ∧
      second ∈ graph.incident edge
  symm := ⟨by
    rintro first second ⟨different, edge, firstMem, secondMem⟩
    exact ⟨different.symm, edge, secondMem, firstMem⟩⟩
  loopless := ⟨by simp⟩

/-- The incidence/Levi graph is bipartite by construction: ordinary vertices
connect only to named hyperedge occurrences. -/
def levi {Vertex Edge : Type*} (graph : Rep Vertex Edge) :
    SimpleGraph (Sum Vertex Edge) where
  Adj left right :=
    match left, right with
    | .inl vertex, .inr edge => vertex ∈ graph.incident edge
    | .inr edge, .inl vertex => vertex ∈ graph.incident edge
    | _, _ => False
  symm := ⟨by
    intro left right adjacent
    cases left <;> cases right <;> exact adjacent⟩
  loopless := ⟨by
    intro vertex adjacent
    cases vertex <;> exact adjacent⟩

@[simp] theorem levi_vertex_edge_adj {Vertex Edge : Type*}
    (graph : Rep Vertex Edge) (vertex : Vertex) (edge : Edge) :
    (levi graph).Adj (.inl vertex) (.inr edge) ↔
      vertex ∈ graph.incident edge :=
  Iff.rfl

@[simp] theorem levi_no_vertex_vertex {Vertex Edge : Type*}
    (graph : Rep Vertex Edge) (first second : Vertex) :
    ¬(levi graph).Adj (.inl first) (.inl second) := by
  simp [levi]

/-- Incidence-query states. -/
inductive QueryState (Vertex Edge : Type*) where
  | lookup (graph : Rep Vertex Edge) (vertex : Vertex) (edge : Edge)
  | answer (value : Bool)

inductive QueryStep {Vertex Edge : Type*} [DecidableEq Vertex] :
    QueryState Vertex Edge → QueryState Vertex Edge → Prop where
  | read (graph : Rep Vertex Edge) (vertex : Vertex) (edge : Edge) :
      QueryStep (.lookup graph vertex edge)
        (.answer (incident graph vertex edge).value)

def queryTheory (Vertex Edge : Type) [DecidableEq Vertex] : GSLT where
  Term := QueryState Vertex Edge
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

def queryPath {Vertex Edge : Type} [DecidableEq Vertex]
    (graph : Rep Vertex Edge) (vertex : Vertex) (edge : Edge) :
    (queryTheory Vertex Edge).RewritePath (.lookup graph vertex edge)
      (.answer (incident graph vertex edge).value) :=
  .cons (.read graph vertex edge) (.nil _)

/-- Hypergraph-to-Levi transformation states. -/
inductive TransformState (Vertex Edge : Type*) where
  | hypergraph (graph : Rep Vertex Edge)
  | leviGraph (graph : SimpleGraph (Sum Vertex Edge))

inductive TransformStep {Vertex Edge : Type*} :
    TransformState Vertex Edge → TransformState Vertex Edge → Prop where
  | encode (graph : Rep Vertex Edge) :
      TransformStep (.hypergraph graph) (.leviGraph (levi graph))

def transformTheory (Vertex Edge : Type) : GSLT where
  Term := TransformState Vertex Edge
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := TransformStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def leviPath {Vertex Edge : Type} (graph : Rep Vertex Edge) :
    (transformTheory Vertex Edge).RewritePath (.hypergraph graph)
      (.leviGraph (levi graph)) :=
  .cons (.encode graph) (.nil _)

namespace Canary

def v0 : Fin 3 := ⟨0, by omega⟩
def v1 : Fin 3 := ⟨1, by omega⟩
def v2 : Fin 3 := ⟨2, by omega⟩

/-- One genuine ternary occurrence. -/
def oneTriple : Rep (Fin 3) Unit where
  incident _ := {v0, v1, v2}

/-- Three pair occurrences carrying only pairwise information. -/
def threePairs : Rep (Fin 3) (Fin 3) where
  incident edge :=
    if edge = v0 then {v0, v1}
    else if edge = v1 then {v0, v2}
    else {v1, v2}

/-- Positive: the ternary membership query is represented directly. -/
theorem v2_incident_to_triple : incident oneTriple v2 () = ⟨true, 1⟩ := by
  decide

/-- Negative: clique/two-section expansion cannot distinguish one ternary
occurrence from three independent binary occurrences. -/
theorem twoSection_loses_hyperedge_grouping :
    twoSection oneTriple = twoSection threePairs := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    simp [twoSection, oneTriple, threePairs, v0, v1, v2]
  all_goals
    first
    | exact ⟨v0, by decide⟩
    | exact ⟨v1, by decide⟩
    | exact ⟨v2, by decide⟩

/-- The source hypergraphs nevertheless have different numbers of named edge
occurrences. -/
theorem edge_occurrence_counts_differ :
    Fintype.card Unit = 1 ∧ Fintype.card (Fin 3) = 3 := by
  decide

end Canary

#print axioms incident_sound
#print axioms levi_vertex_edge_adj
#print axioms queryPath
#print axioms leviPath
#print axioms Canary.twoSection_loses_hyperedge_grouping

end Mettapedia.GraphTheory.Representation.Hypergraph
