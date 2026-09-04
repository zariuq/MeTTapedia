import Mettapedia.GraphTheory.Representation.Basic

/-!
# Ordered edge-list presentation

An edge list is the natural streaming presentation of a sparse finite graph.
The order and multiplicity of occurrences remain available to operational
consumers, while `denote` forgets those intensional details and yields the
underlying simple graph.
-/

namespace Mettapedia.GraphTheory.Representation.EdgeList

open Mettapedia.GraphTheory.Representation

/-- One authored edge occurrence.  Orientation is operational data; the
simple-graph denotation forgets it. -/
structure Edge (n : Nat) where
  source : Fin n
  target : Fin n
deriving DecidableEq, Repr

/-- An ordered, occurrence-preserving edge payload. -/
structure Rep (n : Nat) where
  entries : List (Edge n)
deriving DecidableEq, Repr

/-- The undirected query addressed by an edge observation. -/
abbrev Query (n : Nat) := Fin n × Fin n

/-- An occurrence matches a query in either orientation. -/
def accepts {n : Nat} (edge : Edge n) (query : Query n) : Bool :=
  (query.1 != query.2) &&
    ((edge.source == query.1 && edge.target == query.2) ||
      (edge.source == query.2 && edge.target == query.1))

theorem accepts_eq_true_iff {n : Nat} (edge : Edge n) (query : Query n) :
    accepts edge query = true ↔
      query.1 ≠ query.2 ∧
        ((edge.source = query.1 ∧ edge.target = query.2) ∨
          (edge.source = query.2 ∧ edge.target = query.1)) := by
  simp [accepts, Bool.or_eq_true, Bool.and_eq_true]

/-- Forget occurrence order, orientation, multiplicity, and loops. -/
def denote {n : Nat} (graph : Rep n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun source target =>
    Edge.mk source target ∈ graph.entries

/-- Edge membership is computed by the authentic linear-probe GSLT. -/
def edge {n : Nat} (graph : Rep n) (source target : Fin n) : Measured Bool :=
  LinearProbe.run accepts (source, target) graph.entries

/-- Edge-list storage counts the two endpoint cells of every occurrence. -/
def storageCells {n : Nat} (graph : Rep n) : Nat :=
  2 * graph.entries.length

/-- The executable observer is exactly the extensional simple-graph
adjacency relation. -/
theorem edge_sound {n : Nat} (graph : Rep n) (source target : Fin n) :
    (edge graph source target).value = true ↔
      (denote graph).Adj source target := by
  rw [edge, LinearProbe.run_value_eq_any]
  simp only [List.any_eq_true]
  change (∃ x ∈ graph.entries, accepts x (source, target) = true) ↔
    source ≠ target ∧
      (Edge.mk source target ∈ graph.entries ∨
        Edge.mk target source ∈ graph.entries)
  constructor
  · rintro ⟨candidate, member, matched⟩
    have oriented := (accepts_eq_true_iff candidate (source, target)).mp matched
    rcases oriented with ⟨different, forward | backward⟩
    · have candidateEq : candidate = Edge.mk source target := by
        cases candidate
        simp_all
      exact ⟨different, Or.inl (candidateEq ▸ member)⟩
    · have candidateEq : candidate = Edge.mk target source := by
        cases candidate
        simp_all
      exact ⟨different, Or.inr (candidateEq ▸ member)⟩
  · rintro ⟨different, direct | reverse⟩
    · exact ⟨Edge.mk source target, direct,
        (accepts_eq_true_iff _ _).mpr
          ⟨different, Or.inl ⟨rfl, rfl⟩⟩⟩
    · exact ⟨Edge.mk target source, reverse,
        (accepts_eq_true_iff _ _).mpr
          ⟨different, Or.inr ⟨rfl, rfl⟩⟩⟩

/-- The edge-list member of the common representation portfolio. -/
def presentation (n : Nat) : Presentation n where
  Carrier := Rep n
  denote := denote
  edge := edge
  edge_sound := edge_sound
  storageCells := storageCells

/-- Streaming the authored edge occurrences needs exactly one visit per
occurrence and preserves their order and multiplicity. -/
def enumerate {n : Nat} (graph : Rep n) : Measured (List (Edge n)) :=
  ⟨graph.entries, graph.entries.length⟩

theorem enumerate_exact {n : Nat} (graph : Rep n) :
    (enumerate graph).value = graph.entries ∧
      (enumerate graph).work = graph.entries.length :=
  ⟨rfl, rfl⟩

/-- General negative result: an absent edge forces the linear observer to
inspect every occurrence. -/
theorem absent_edge_forces_full_scan {n : Nat} (graph : Rep n)
    (source target : Fin n)
    (absent : ∀ occurrence ∈ graph.entries,
      accepts occurrence (source, target) = false) :
    (edge graph source target).work = graph.entries.length :=
  LinearProbe.run_work_eq_length_of_no_match accepts (source, target)
    graph.entries absent

namespace Canary

def v0 : Fin 3 := ⟨0, by omega⟩
def v1 : Fin 3 := ⟨1, by omega⟩
def v2 : Fin 3 := ⟨2, by omega⟩

/-- A two-edge path, ordered as authored. -/
def path3 : Rep 3 :=
  ⟨[⟨v0, v1⟩, ⟨v1, v2⟩]⟩

/-- Positive canary: streaming preserves both edge occurrences in two visits. -/
theorem path3_enumeration : enumerate path3 =
    ⟨[⟨v0, v1⟩, ⟨v1, v2⟩], 2⟩ :=
  rfl

/-- Negative canary: the absent edge `0--2` requires both occurrences to be
inspected. -/
theorem path3_absent_edge_cost : (edge path3 v0 v2).work = 2 := by
  decide

end Canary

#print axioms edge_sound
#print axioms enumerate_exact
#print axioms absent_edge_forces_full_scan
#print axioms Canary.path3_absent_edge_cost

end Mettapedia.GraphTheory.Representation.EdgeList
