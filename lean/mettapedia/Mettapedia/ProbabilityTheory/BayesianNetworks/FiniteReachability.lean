import Mathlib.Data.Finset.Prod
import Mettapedia.GSLT.Parsing.FiniteHornSaturation
import Mettapedia.ProbabilityTheory.BayesianNetworks.DirectedGraph

/-!
# Executable finite graph reachability via exact unary Horn saturation

For a finite decidable graph, reflexive-transitive reachability is exactly the
least model of the unary Horn program containing one rule `{u} -> v` per edge
`u -> v`.  This module proves that equivalence and exposes executable
reachability and separation tests.

The use of Horn clauses here is derived from the algebra of reachability.  It
does not assert that a surrounding logic, probabilistic model, or source
language has Horn semantics.  The declarative `DirectedGraph.Path` relation
remains primary; finite saturation is a proved accelerator for this one
observer.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteReachability

open Mettapedia.GSLT.Parsing.FiniteHornSaturation
open Mettapedia.Logic.LP
open Mettapedia.ProbabilityTheory.BayesianNetworks

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The unary Horn rule associated with one directed edge. -/
def edgeRule (source target : V) : PropRule V :=
  { premises := {source}
    head := target }

/-- The finite unary Horn presentation of a decidable edge relation. -/
def edgeProgram (graph : DirectedGraph V) [DecidableRel graph.edges] :
    PropProgram V :=
  (((Finset.univ : Finset V).product (Finset.univ : Finset V)).filter
      fun endpoints => graph.edges endpoints.1 endpoints.2).image
    fun endpoints => edgeRule endpoints.1 endpoints.2

/-- A generated unary rule occurs exactly when its endpoints form an edge. -/
theorem edgeRule_mem_edgeProgram_iff (graph : DirectedGraph V)
    [DecidableRel graph.edges] (source target : V) :
    edgeRule source target ∈ edgeProgram graph ↔
      graph.edges source target := by
  constructor
  · intro member
    obtain ⟨endpoints, filtered, ruleEquality⟩ :=
      Finset.mem_image.mp member
    have edge := (Finset.mem_filter.mp filtered).2
    have targetEquality : endpoints.2 = target :=
      congrArg PropRule.head ruleEquality
    have premiseEquality :
        ({endpoints.1} : Finset V) = {source} :=
      congrArg PropRule.premises ruleEquality
    have sourceMember : endpoints.1 ∈ ({source} : Finset V) := by
      rw [← premiseEquality]
      simp
    have sourceEquality : endpoints.1 = source := by
      simpa using sourceMember
    simpa [sourceEquality, targetEquality] using edge
  · intro edge
    apply Finset.mem_image.mpr
    refine ⟨(source, target), ?_, rfl⟩
    simp [edge]

/-- Every rule in the generated program has a unique edge-shaped
presentation, up to equality of its endpoints. -/
theorem mem_edgeProgram_iff (graph : DirectedGraph V)
    [DecidableRel graph.edges] (rule : PropRule V) :
    rule ∈ edgeProgram graph ↔
      ∃ source target, graph.edges source target ∧
        rule = edgeRule source target := by
  constructor
  · intro member
    obtain ⟨endpoints, filtered, ruleEquality⟩ :=
      Finset.mem_image.mp member
    exact ⟨endpoints.1, endpoints.2,
      (Finset.mem_filter.mp filtered).2, ruleEquality.symm⟩
  · rintro ⟨source, target, edge, rfl⟩
    exact (edgeRule_mem_edgeProgram_iff graph source target).2 edge

/-- One graph edge transports unary-Horn derivability. -/
theorem derivable_of_edge (graph : DirectedGraph V)
    [DecidableRel graph.edges] (facts : Finset V)
    {source target : V} (edge : graph.edges source target)
    (sourceDerivable : Derivable (edgeProgram graph) facts source) :
    Derivable (edgeProgram graph) facts target := by
  apply Derivable.rule
    ((edgeRule_mem_edgeProgram_iff graph source target).2 edge)
  intro premise member
  have premiseEquality : premise = source := by
    simpa [edgeRule] using member
  exact premiseEquality ▸ sourceDerivable

/-- A declarative graph path transports unary-Horn derivability. -/
theorem derivable_of_reachable (graph : DirectedGraph V)
    [DecidableRel graph.edges] (facts : Finset V)
    {source target : V}
    (sourceDerivable : Derivable (edgeProgram graph) facts source)
    (reachable : graph.Reachable source target) :
    Derivable (edgeProgram graph) facts target := by
  induction reachable with
  | refl => exact sourceDerivable
  | @step source middle target edge _ inductionHypothesis =>
      exact inductionHypothesis
        (derivable_of_edge graph facts edge sourceDerivable)

/-- Unary-Horn derivability is neither weaker nor stronger than reachability
from one of the seed vertices. -/
theorem derivable_iff_reachable_from_seed (graph : DirectedGraph V)
    [DecidableRel graph.edges] (facts : Finset V) (target : V) :
    Derivable (edgeProgram graph) facts target ↔
      ∃ source ∈ facts, graph.Reachable source target := by
  constructor
  · intro derivation
    induction derivation with
    | fact member =>
        exact ⟨_, member, DirectedGraph.reachable_refl graph _⟩
    | @rule rule ruleMember premisesDerivable inductionHypothesis =>
        obtain ⟨source, head, edge, ruleEquality⟩ :=
          (mem_edgeProgram_iff graph rule).1 ruleMember
        subst rule
        have sourceDerivation :=
          premisesDerivable source (by simp [edgeRule])
        obtain ⟨seed, seedMember, seedReachable⟩ :=
          inductionHypothesis source (by simp [edgeRule])
        exact ⟨seed, seedMember,
          DirectedGraph.reachable_trans graph seedReachable
            (DirectedGraph.edge_reachable graph edge)⟩
  · rintro ⟨source, sourceMember, reachable⟩
    exact derivable_of_reachable graph facts
      (Derivable.fact sourceMember) reachable

/-- Executable set of all vertices reachable from the finite seed set. -/
def reachableFrom (graph : DirectedGraph V) [DecidableRel graph.edges]
    (sources : Finset V) : Finset V :=
  saturateFast (edgeProgram graph) sources

/-- Exactness of the executable finite reachability accelerator. -/
theorem mem_reachableFrom_iff (graph : DirectedGraph V)
    [DecidableRel graph.edges] (sources : Finset V) (target : V) :
    target ∈ reachableFrom graph sources ↔
      ∃ source ∈ sources, graph.Reachable source target := by
  rw [reachableFrom, saturateFast_iff_derivable,
    derivable_iff_reachable_from_seed]

/-- Boolean reachability from one source. -/
def reaches (graph : DirectedGraph V) [DecidableRel graph.edges]
    (source target : V) : Bool :=
  decide (target ∈ reachableFrom graph {source})

/-- The Boolean query reflects and preserves declarative graph paths. -/
theorem reaches_eq_true_iff (graph : DirectedGraph V)
    [DecidableRel graph.edges] (source target : V) :
    reaches graph source target = true ↔ graph.Reachable source target := by
  rw [reaches, decide_eq_true_eq, mem_reachableFrom_iff]
  simp

/-- Boolean separation of two finite endpoint sets in a directed graph. -/
def separated (graph : DirectedGraph V) [DecidableRel graph.edges]
    (left right : Finset V) : Bool :=
  decide (Disjoint (reachableFrom graph left) right)

/-- Exactness of finite separation: no right endpoint is reachable from any
left endpoint. -/
theorem separated_eq_true_iff (graph : DirectedGraph V)
    [DecidableRel graph.edges] (left right : Finset V) :
    separated graph left right = true ↔
      ∀ source ∈ left, ∀ target ∈ right,
        ¬ graph.Reachable source target := by
  rw [separated, decide_eq_true_eq]
  constructor
  · intro disjoint source sourceMember target targetMember reachable
    apply Finset.disjoint_left.mp disjoint
      ((mem_reachableFrom_iff graph left target).2
        ⟨source, sourceMember, reachable⟩)
      targetMember
  · intro unreachable
    apply Finset.disjoint_left.mpr
    intro target reachable targetMember
    obtain ⟨source, sourceMember, path⟩ :=
      (mem_reachableFrom_iff graph left target).1 reachable
    exact unreachable source sourceMember target targetMember path

/-! ## Executable positive and negative controls -/

namespace Canary

abbrev Vertex := Fin 4

def a : Vertex := 0
def b : Vertex := 1
def c : Vertex := 2
def isolated : Vertex := 3

def chain : DirectedGraph Vertex where
  edges source target :=
    (source = a ∧ target = b) ∨
      (source = b ∧ target = c)

instance : DecidableRel chain.edges := by
  intro source target
  exact inferInstanceAs (Decidable
    ((source = a ∧ target = b) ∨
      (source = b ∧ target = c)))

/-- Positive control: saturation finds the two-edge path. -/
theorem chain_reaches_c : reaches chain a c = true := by
  decide

/-- Negative control: saturation does not invent a path to an isolated
vertex. -/
theorem chain_rejects_isolated : reaches chain a isolated = false := by
  decide

/-- Set separation uses the same exact closure and accepts the isolated
endpoint. -/
theorem chain_separates_isolated :
    separated chain {a} {isolated} = true := by
  decide

end Canary

end Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteReachability
