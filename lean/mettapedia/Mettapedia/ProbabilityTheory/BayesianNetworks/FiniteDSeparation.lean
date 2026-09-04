import Mettapedia.GSLT.LanguageDef.KernelAuthority
import Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparationMoralEquiv
import Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteReachability

/-!
# A finite exact d-separation decision profile

The semantic definition of d-separation quantifies over trails of arbitrary
length.  On a finite Bayesian-network graph, the standard moralized ancestral
graph construction reduces that infinitary-looking condition to finite graph
separation.  This module makes the reduction executable and proves its exact
boundary.

Endpoint sets are required to be disjoint from the conditioning set in this
first profile.  The checker tests that requirement and reports only the
conjunction of support and semantic d-separation.  Conditions outside the
profile are unsupported, not refuted.  The finite reachability subroutine is
the exact unary-Horn least-model accelerator proved in `FiniteReachability`.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteDSeparation

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation
open Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteReachability

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Finite data submitted to the d-separation decision profile. -/
structure Condition (V : Type*) where
  X : Finset V
  Y : Finset V
  Z : Finset V
  deriving DecidableEq

namespace Condition

/-- Compatibility permits an `X`/`Y` overlap only when it is conditioned. -/
def Compatible (condition : Condition V) : Prop :=
  condition.X ∩ condition.Y ⊆ condition.Z

/-- The supported finite profile keeps both endpoint sets outside `Z`. -/
def Supported (condition : Condition V) : Prop :=
  Disjoint condition.X condition.Z ∧ Disjoint condition.Y condition.Z

/-- Declarative meaning of the finite condition on a graph. -/
def Meaning (graph : DirectedGraph V) (condition : Condition V) : Prop :=
  condition.Compatible ∧
    DSeparatedFull graph condition.X condition.Y condition.Z

end Condition

/-- Compute all ancestors of `X ∪ Y ∪ Z` by exact reachability in the reverse
graph. -/
def relevantFinset (graph : DirectedGraph V) [DecidableRel graph.edges]
    (condition : Condition V) : Finset V :=
  reachableFrom graph.reverse ((condition.X ∪ condition.Y) ∪ condition.Z)

/-- The computed ancestor set is extensionally the semantic ancestor closure. -/
theorem mem_relevantFinset_iff (graph : DirectedGraph V)
    [DecidableRel graph.edges] (condition : Condition V) (vertex : V) :
    vertex ∈ relevantFinset graph condition ↔
      vertex ∈ relevantVertices graph condition.X condition.Y condition.Z := by
  rw [relevantFinset, mem_reachableFrom_iff]
  constructor
  · rintro ⟨target, targetMember, reversePath⟩
    apply Or.inr
    refine ⟨target, ?_, (DirectedGraph.reverse_reachable (G := graph)).1
      reversePath⟩
    change (target ∈ condition.X ∨ target ∈ condition.Y) ∨
      target ∈ condition.Z
    rcases Finset.mem_union.mp targetMember with xy | z
    · exact Or.inl (Finset.mem_union.mp xy)
    · exact Or.inr z
  · intro relevant
    rcases relevant with seed | ⟨target, targetMember, path⟩
    · refine ⟨vertex, ?_, DirectedGraph.reachable_refl graph.reverse vertex⟩
      change (vertex ∈ condition.X ∨ vertex ∈ condition.Y) ∨
        vertex ∈ condition.Z at seed
      apply Finset.mem_union.mpr
      rcases seed with xy | z
      · exact Or.inl (Finset.mem_union.mpr xy)
      · exact Or.inr z
    · refine ⟨target, ?_,
        (DirectedGraph.reverse_reachable (G := graph)).2 path⟩
      change (target ∈ condition.X ∨ target ∈ condition.Y) ∨
        target ∈ condition.Z at targetMember
      apply Finset.mem_union.mpr
      rcases targetMember with xy | z
      · exact Or.inl (Finset.mem_union.mpr xy)
      · exact Or.inr z

/-- Set equality form of the computed ancestor theorem. -/
theorem coe_relevantFinset (graph : DirectedGraph V)
    [DecidableRel graph.edges] (condition : Condition V) :
    (relevantFinset graph condition : Set V) =
      relevantVertices graph condition.X condition.Y condition.Z := by
  ext vertex
  exact mem_relevantFinset_iff graph condition vertex

/-- The computed finite ancestral subgraph. -/
def ancestralGraphFinite (graph : DirectedGraph V)
    [DecidableRel graph.edges] (condition : Condition V) : DirectedGraph V :=
  inducedSubgraph graph (relevantFinset graph condition : Set V)

instance ancestralGraphFinite_decidableRel
    (graph : DirectedGraph V) [DecidableRel graph.edges]
    (condition : Condition V) :
    DecidableRel (ancestralGraphFinite graph condition).edges := by
  intro source target
  unfold ancestralGraphFinite inducedSubgraph
  change Decidable
    (source ∈ relevantFinset graph condition ∧
      target ∈ relevantFinset graph condition ∧ graph.edges source target)
  infer_instance

/-- Moralize the computed finite ancestral subgraph. -/
def moralAncestralGraphFinite (graph : DirectedGraph V)
    [DecidableRel graph.edges] (condition : Condition V) : DirectedGraph V :=
  moralGraph (ancestralGraphFinite graph condition)

/-- The executable construction denotes the ordinary moralized ancestral
graph exactly. -/
theorem moralAncestralGraphFinite_eq (graph : DirectedGraph V)
    [DecidableRel graph.edges] (condition : Condition V) :
    moralAncestralGraphFinite graph condition =
      moralAncestralGraph graph condition.X condition.Y condition.Z := by
  unfold moralAncestralGraphFinite ancestralGraphFinite moralAncestralGraph
  rw [coe_relevantFinset]

instance moralAncestralGraphFinite_decidableRel
    (graph : DirectedGraph V) [DecidableRel graph.edges]
    (condition : Condition V) :
    DecidableRel (moralAncestralGraphFinite graph condition).edges := by
  intro source target
  unfold moralAncestralGraphFinite moralGraph moralUndirectedEdge
    UndirectedEdge
  infer_instance

/-- Relevant vertices outside the conditioning set, as finite data. -/
def relevantOutsideFinset (graph : DirectedGraph V)
    [DecidableRel graph.edges] (condition : Condition V) : Finset V :=
  relevantFinset graph condition \ condition.Z

/-- The computed moralized ancestral graph with conditioning vertices
removed. -/
def separationGraph (graph : DirectedGraph V) [DecidableRel graph.edges]
    (condition : Condition V) : DirectedGraph V :=
  inducedSubgraph (moralAncestralGraphFinite graph condition)
    (relevantOutsideFinset graph condition : Set V)

instance separationGraph_decidableRel
    (graph : DirectedGraph V) [DecidableRel graph.edges]
    (condition : Condition V) :
    DecidableRel (separationGraph graph condition).edges := by
  intro source target
  unfold separationGraph inducedSubgraph
  letI := moralAncestralGraphFinite_decidableRel graph condition
  change Decidable
    (source ∈ relevantOutsideFinset graph condition ∧
      target ∈ relevantOutsideFinset graph condition ∧
        (moralAncestralGraphFinite graph condition).edges source target)
  infer_instance

/-- The computed graph is exactly the semantic moralized ancestral graph with
`Z` removed. -/
theorem separationGraph_eq (graph : DirectedGraph V)
    [DecidableRel graph.edges] (condition : Condition V) :
    separationGraph graph condition =
      moralAncestralWithoutConditioning graph
        condition.X condition.Y condition.Z := by
  have outsideEquality :
      (relevantOutsideFinset graph condition : Set V) =
        relevantOutsideConditioning graph
          condition.X condition.Y condition.Z := by
    ext vertex
    simp [relevantOutsideFinset, relevantOutsideConditioning,
      mem_relevantFinset_iff]
  unfold separationGraph moralAncestralWithoutConditioning
  rw [moralAncestralGraphFinite_eq, outsideEquality]

/-! ## Trail-to-reachability bridge -/

omit [Fintype V] [DecidableEq V] in
/-- Intersect two pointwise vertex invariants along the same path. -/
theorem pathVerticesIn_inter {left right : Set V} :
    ∀ {path : List V},
      PathVerticesIn left path → PathVerticesIn right path →
        PathVerticesIn (left ∩ right) path
  | [], _, _ => trivial
  | _ :: _, ⟨headLeft, tailLeft⟩, ⟨headRight, tailRight⟩ =>
      ⟨⟨headLeft, headRight⟩,
        pathVerticesIn_inter tailLeft tailRight⟩

omit [Fintype V] [DecidableEq V] in
/-- If a path's endpoints and every internal vertex avoid `Z`, then every
vertex on the path lies outside `Z`. -/
theorem pathVerticesIn_compl_of_pathAvoidsInternals
    (Z : Set V) :
    ∀ {path : List V} {source target : V},
      PathEndpoints path = some (source, target) →
      source ∉ Z → target ∉ Z →
      PathAvoidsInternals Z path →
      PathVerticesIn Zᶜ path := by
  intro path
  induction path with
  | nil =>
      intro source target endpoints
      simp [PathEndpoints] at endpoints
  | cons first rest inductionHypothesis =>
      cases rest with
      | nil =>
          intro source target endpoints sourceOutside _ _
          have sourceEq : first = source := by
            simpa using head_of_pathEndpoints endpoints
          subst source
          exact ⟨sourceOutside, trivial⟩
      | cons second tail =>
          cases tail with
          | nil =>
              intro source target endpoints sourceOutside targetOutside _
              have sourceEq : first = source := by
                simpa using head_of_pathEndpoints endpoints
              have targetEq : second = target := by
                simpa [List.getLast?] using getLast_of_pathEndpoints endpoints
              subst source
              subst target
              exact ⟨sourceOutside, ⟨targetOutside, trivial⟩⟩
          | cons third tail =>
              intro source target endpoints sourceOutside targetOutside avoids
              have sourceEq : first = source := by
                simpa using head_of_pathEndpoints endpoints
              subst source
              have secondOutside : second ∉ Z := by
                exact avoids.1
              have tailAvoids :
                  PathAvoidsInternals Z (second :: third :: tail) :=
                avoids.2
              have tailLast :
                  (second :: third :: tail).getLast? = some target := by
                simpa [List.getLast?] using getLast_of_pathEndpoints endpoints
              have tailEndpoints :
                  PathEndpoints (second :: third :: tail) =
                    some (second, target) :=
                pathEndpoints_of_head_last (by simp) (by simp) tailLast
              exact ⟨sourceOutside,
                inductionHypothesis tailEndpoints secondOutside
                  targetOutside tailAvoids⟩

omit [Fintype V] [DecidableEq V] in
/-- In a symmetric graph, every undirected trail presents a directed
reachability path between its endpoints. -/
theorem reachable_of_isTrail_of_symmetric (graph : DirectedGraph V)
    (symmetric : ∀ {source target}, graph.edges source target →
      graph.edges target source) :
    ∀ {path : List V} {source target : V},
      PathEndpoints path = some (source, target) →
      IsTrail graph path → graph.Reachable source target := by
  intro path source target endpoints trail
  induction trail generalizing source target with
  | single vertex =>
      have sourceEq : vertex = source := by
        simpa using head_of_pathEndpoints endpoints
      have targetEq : vertex = target := by
        simpa [List.getLast?] using getLast_of_pathEndpoints endpoints
      subst source
      subst target
      exact DirectedGraph.reachable_refl graph vertex
  | @cons first second rest edge tail inductionHypothesis =>
      have sourceEq : first = source := by
        simpa using head_of_pathEndpoints endpoints
      subst source
      have tailLast : (second :: rest).getLast? = some target := by
        simpa [List.getLast?] using getLast_of_pathEndpoints endpoints
      have tailEndpoints :
          PathEndpoints (second :: rest) = some (second, target) :=
        pathEndpoints_of_head_last (by simp) (by simp) tailLast
      have tailReachable := inductionHypothesis tailEndpoints
      have directedEdge : graph.edges first second := by
        rcases edge with forward | backward
        · exact forward
        · exact symmetric backward
      exact DirectedGraph.Path.step directedEdge tailReachable

/-! ## Exact reduction to finite separation -/

/-- For supported endpoint sets, semantic separation in the moralized
ancestral graph is exactly absence of reachability in the computed graph with
the conditioning vertices removed. -/
theorem separatedInMoralAncestral_iff_no_reachable
    (graph : DirectedGraph V) [DecidableRel graph.edges]
    (condition : Condition V) (supported : condition.Supported) :
    SeparatedInMoralAncestral graph
        condition.X condition.Y condition.Z ↔
      ∀ source ∈ condition.X, ∀ target ∈ condition.Y,
        source ≠ target →
          ¬ (separationGraph graph condition).Reachable source target := by
  constructor
  · intro separated source sourceMember target targetMember distinct
    have sourceOutside : source ∉ condition.Z := by
      exact fun sourceInZ =>
        Finset.disjoint_left.mp supported.1 sourceMember sourceInZ
    rw [separationGraph_eq]
    exact
      not_reachable_moralAncestralWithoutConditioning_of_separatedInMoralAncestral
        graph condition.X condition.Y condition.Z separated
        sourceMember targetMember sourceOutside distinct
  · intro noReach source sourceMember target targetMember distinct witness
    rcases witness with
      ⟨path, pathNonempty, endpoints, trail, avoidsInternals⟩
    have sourceOutside : source ∉ condition.Z := by
      exact fun sourceInZ =>
        Finset.disjoint_left.mp supported.1 sourceMember sourceInZ
    have targetOutside : target ∉ condition.Z := by
      exact fun targetInZ =>
        Finset.disjoint_left.mp supported.2 targetMember targetInZ
    rcases path with _ | ⟨first, rest⟩
    · exact pathNonempty rfl
    · have firstEquality : first = source := by
        simpa using head_of_pathEndpoints endpoints
      subst first
      have relevantPath :
          PathVerticesIn
            (relevantVertices graph condition.X condition.Y condition.Z)
            (source :: rest) :=
        pathVerticesIn_of_isTrail_moralAncestral_of_head
          graph condition.X condition.Y condition.Z
          (endpoint_in_relevant_X graph condition.X condition.Y condition.Z
            sourceMember)
          trail
      have outsidePath :
          PathVerticesIn (condition.Z : Set V)ᶜ (source :: rest) :=
        pathVerticesIn_compl_of_pathAvoidsInternals
          condition.Z endpoints sourceOutside targetOutside avoidsInternals
      have relevantOutsidePath :
          PathVerticesIn
            (relevantOutsideConditioning graph
              condition.X condition.Y condition.Z)
            (source :: rest) := by
        change PathVerticesIn
          (relevantVertices graph condition.X condition.Y condition.Z ∩
            (condition.Z : Set V)ᶜ)
          (source :: rest)
        exact pathVerticesIn_inter relevantPath outsidePath
      have reducedTrail :
          IsTrail
            (moralAncestralWithoutConditioning graph
              condition.X condition.Y condition.Z)
            (source :: rest) :=
        isTrail_inducedSubgraph_of_isTrail_and_vertices
          (moralAncestralGraph graph condition.X condition.Y condition.Z)
          (relevantOutsideConditioning graph
            condition.X condition.Y condition.Z)
          trail relevantOutsidePath
      have reachable :
          (moralAncestralWithoutConditioning graph
            condition.X condition.Y condition.Z).Reachable source target :=
        reachable_of_isTrail_of_symmetric
          (moralAncestralWithoutConditioning graph
            condition.X condition.Y condition.Z)
          (moralAncestralWithoutConditioning_edge_symm
            graph condition.X condition.Y condition.Z)
          endpoints reducedTrail
      apply noReach source sourceMember target targetMember distinct
      rw [separationGraph_eq]
      exact reachable

omit [Fintype V] in
/-- Compatibility plus the supported-profile boundary forces the two endpoint
sets to be disjoint. -/
theorem disjoint_X_Y_of_compatible_supported (condition : Condition V)
    (compatible : condition.Compatible)
    (supported : condition.Supported) :
    Disjoint condition.X condition.Y := by
  apply Finset.disjoint_left.mpr
  intro vertex vertexInX vertexInY
  have vertexInZ : vertex ∈ condition.Z :=
    compatible (Finset.mem_inter.mpr ⟨vertexInX, vertexInY⟩)
  exact Finset.disjoint_left.mp supported.1 vertexInX vertexInZ

/-- Executable finite d-separation profile.  A `false` result may mean either
that the semantic condition fails or that the input lies outside the declared
support boundary. -/
def check (graph : DirectedGraph V) [DecidableRel graph.edges]
    (condition : Condition V) : Bool :=
  decide (condition.X ∩ condition.Y ⊆ condition.Z) &&
    (decide
        (Disjoint condition.X condition.Z ∧
          Disjoint condition.Y condition.Z) &&
      separated (separationGraph graph condition)
        condition.X condition.Y)

/-- Exactness of the executable profile against full trail-based
d-separation. -/
theorem check_eq_true_iff (graph : DirectedGraph V)
    [DecidableRel graph.edges] (condition : Condition V)
    (acyclic : graph.IsAcyclic)
    (irreflexive : ∀ vertex, ¬ graph.edges vertex vertex) :
    check graph condition = true ↔
      condition.Meaning graph ∧ condition.Supported := by
  constructor
  · intro accepted
    have acceptedParts :
        condition.Compatible ∧ condition.Supported ∧
          separated (separationGraph graph condition)
            condition.X condition.Y = true := by
      simpa [check, Condition.Compatible, Condition.Supported,
        Bool.and_eq_true] using accepted
    rcases acceptedParts with
      ⟨compatible, supported, finiteSeparated⟩
    have noReach :=
      (separated_eq_true_iff
        (separationGraph graph condition)
        condition.X condition.Y).1 finiteSeparated
    have moralSeparated :
        SeparatedInMoralAncestral graph
          condition.X condition.Y condition.Z :=
      (separatedInMoralAncestral_iff_no_reachable
        graph condition supported).2
        (fun source sourceMember target targetMember _ =>
          noReach source sourceMember target targetMember)
    have dSeparated :
        DSeparatedFull graph condition.X condition.Y condition.Z :=
      (dsepFull_iff_separatedInMoralAncestral
        graph condition.X condition.Y condition.Z
        acyclic irreflexive).2 moralSeparated
    exact ⟨⟨compatible, dSeparated⟩, supported⟩
  · rintro ⟨⟨compatible, dSeparated⟩, supported⟩
    have moralSeparated :
        SeparatedInMoralAncestral graph
          condition.X condition.Y condition.Z :=
      (dsepFull_iff_separatedInMoralAncestral
        graph condition.X condition.Y condition.Z
        acyclic irreflexive).1 dSeparated
    have noReachDistinct :=
      (separatedInMoralAncestral_iff_no_reachable
        graph condition supported).1 moralSeparated
    have endpointDisjoint : Disjoint condition.X condition.Y :=
      disjoint_X_Y_of_compatible_supported condition
        compatible supported
    have finiteSeparated :
        separated (separationGraph graph condition)
          condition.X condition.Y = true := by
      apply (separated_eq_true_iff
        (separationGraph graph condition)
        condition.X condition.Y).2
      intro source sourceMember target targetMember reachable
      have distinct : source ≠ target := by
        intro equality
        exact Finset.disjoint_left.mp endpointDisjoint sourceMember
          (equality ▸ targetMember)
      exact noReachDistinct source sourceMember target targetMember
        distinct reachable
    have compatibleRaw : condition.X ∩ condition.Y ⊆ condition.Z :=
      compatible
    have supportedRaw :
        Disjoint condition.X condition.Z ∧
          Disjoint condition.Y condition.Z :=
      supported
    simp [check, compatibleRaw, supportedRaw, finiteSeparated]

/-- The exact finite profile as a direct GSLT kernel authority. -/
def decisionKernel (graph : DirectedGraph V)
    [DecidableRel graph.edges]
    (acyclic : graph.IsAcyclic)
    (irreflexive : ∀ vertex, ¬ graph.edges vertex vertex) :
    Checker.DecisionKernel (Condition V)
      (fun condition => condition.Meaning graph ∧ condition.Supported) where
  decide := check graph
  correct := fun condition =>
    check_eq_true_iff graph condition acyclic irreflexive

/-! ## Executable positive and negative controls -/

namespace Canary

open FiniteReachability.Canary

/-- Every edge of the finite chain strictly increases its vertex index. -/
theorem chain_edge_lt {source target : Vertex}
    (edge : chain.edges source target) : source.val < target.val := by
  rcases edge with edge | edge
  · rcases edge with ⟨rfl, rfl⟩
    decide
  · rcases edge with ⟨rfl, rfl⟩
    decide

/-- Reachability in the chain weakly increases vertex indices. -/
theorem chain_path_le {source target : Vertex}
    (path : chain.Reachable source target) : source.val ≤ target.val := by
  induction path with
  | refl => exact Nat.le_refl _
  | step edge _ inductionHypothesis =>
      exact Nat.le_trans (Nat.le_of_lt (chain_edge_lt edge))
        inductionHypothesis

/-- The finite chain is acyclic by its increasing rank. -/
theorem chain_acyclic : chain.IsAcyclic := by
  intro source cycle
  rcases cycle with ⟨target, edge, pathBack⟩
  exact (Nat.not_lt_of_ge (chain_path_le pathBack))
    (chain_edge_lt edge)

/-- The chain edge relation is irreflexive. -/
theorem chain_irreflexive (vertex : Vertex) :
    ¬ chain.edges vertex vertex :=
  DirectedGraph.isAcyclic_irrefl chain chain_acyclic vertex

/-- Conditioning on the middle vertex blocks the only path from `a` to
`c`. -/
def blocked : Condition Vertex where
  X := {a}
  Y := {c}
  Z := {b}

/-- Without the middle vertex in the conditioning set, the path remains
open. -/
def unblocked : Condition Vertex where
  X := {a}
  Y := {c}
  Z := ∅

/-- Positive computational control. -/
theorem check_blocked : check chain blocked = true := by
  decide

/-- Negative computational control. -/
theorem check_unblocked : check chain unblocked = false := by
  decide

/-- The positive computation denotes actual full d-separation. -/
theorem blocked_meaning_and_supported :
    blocked.Meaning chain ∧ blocked.Supported :=
  (check_eq_true_iff chain blocked chain_acyclic
    chain_irreflexive).1 check_blocked

/-- The negative control lies inside the profile, so rejection here means
that the d-separation judgment itself fails. -/
theorem unblocked_supported : unblocked.Supported := by
  unfold Condition.Supported unblocked
  decide

theorem unblocked_not_meaning : ¬ unblocked.Meaning chain := by
  intro meaning
  have accepted : check chain unblocked = true :=
    (check_eq_true_iff chain unblocked chain_acyclic
      chain_irreflexive).2 ⟨meaning, unblocked_supported⟩
  simp [check_unblocked] at accepted

end Canary

end Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteDSeparation
