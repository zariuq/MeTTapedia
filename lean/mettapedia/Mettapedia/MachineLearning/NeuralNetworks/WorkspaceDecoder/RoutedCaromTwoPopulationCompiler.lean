import Mathlib

/-!
# Routed CAROM: a two-population graph compiler

Ashwin and Postlethwaite, *Designing heteroclinic and excitable networks in
phase space using two populations of coupled cells* (2015,
arXiv:1506.03212), associate one `p`-cell to every graph vertex and one
`y`-cell to every graph edge.  The `p` population records the current state;
the `y` population is active during a selected transition.

This file isolates the finite structural layer of that construction.  It
compiles a loop-free directed multigraph to a bipartite population of state
and transition cells and proves that two coupling steps recover exactly the
original graph relation.  A generalized compiler may merge transition cells
through an address map.  Every original edge survives such merging, but exact
recovery is guaranteed by injective addresses; an executable collision
fixture shows that a noninjective address can introduce a spurious
transition.

No differential equation is defined here.  In particular, this development
does not prove existence, robustness, attraction, dwell time, or excitation
thresholds for a heteroclinic or excitable network.  Those analytic
obligations remain separate from this exact finite wiring theorem.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

namespace RoutedCarom

universe uVertex uEdge uLabel

/-- A finite-source directed multigraph with the one-cycle exclusion used by
the source construction.  Parallel edges remain distinct values of `Edge`. -/
structure DirectedTransitionGraph
    (Vertex : Type uVertex) (Edge : Type uEdge) where
  source : Edge → Vertex
  target : Edge → Vertex
  noSelfLoop : ∀ edge, source edge ≠ target edge

variable {Vertex : Type uVertex} {Edge : Type uEdge}

/-- The directed transition relation represented by the graph's edge
population. -/
def graphTransition
    (graph : DirectedTransitionGraph Vertex Edge)
    (source target : Vertex) : Prop :=
  ∃ edge, graph.source edge = source ∧ graph.target edge = target

/-- One state cell per vertex and one transition cell per graph edge. -/
abbrev TwoPopulationCell (Vertex : Type uVertex) (Edge : Type uEdge) :=
  Vertex ⊕ Edge

/-- Bipartite coupling of the source construction: a state cell activates
exactly its outgoing transition cells, and a transition cell excites exactly
its target state cell.  There are no within-population coupling edges in this
finite structural interface. -/
def twoPopulationCoupled
    (graph : DirectedTransitionGraph Vertex Edge) :
    TwoPopulationCell Vertex Edge →
      TwoPopulationCell Vertex Edge → Prop
  | .inl vertex, .inr edge => graph.source edge = vertex
  | .inr edge, .inl vertex => graph.target edge = vertex
  | _, _ => False

/-- A graph-level transition is executed by a state-to-transition coupling
followed by a transition-to-state coupling. -/
def twoPopulationTransition
    (graph : DirectedTransitionGraph Vertex Edge)
    (source target : Vertex) : Prop :=
  ∃ edge,
    twoPopulationCoupled graph (.inl source) (.inr edge) ∧
      twoPopulationCoupled graph (.inr edge) (.inl target)

/-- Structural correspondence crown: the two-population compiler introduces
neither missing nor spurious graph transitions. -/
theorem twoPopulationTransition_iff_graphTransition
    (graph : DirectedTransitionGraph Vertex Edge)
    (source target : Vertex) :
    twoPopulationTransition graph source target ↔
      graphTransition graph source target := by
  simp [twoPopulationTransition, twoPopulationCoupled, graphTransition]

/-- The source's one-cycle exclusion is inherited by the compiled
two-population transition relation. -/
theorem not_twoPopulationTransition_self
    (graph : DirectedTransitionGraph Vertex Edge)
    (vertex : Vertex) :
    ¬twoPopulationTransition graph vertex vertex := by
  rw [twoPopulationTransition_iff_graphTransition]
  rintro ⟨edge, source_eq, target_eq⟩
  apply graph.noSelfLoop edge
  exact source_eq.trans target_eq.symm

/-- The finite compiler uses exactly one cell for every vertex and every edge. -/
theorem twoPopulationCell_card
    [Fintype Vertex] [Fintype Edge] :
    Fintype.card (TwoPopulationCell Vertex Edge) =
      Fintype.card Vertex + Fintype.card Edge := by
  exact Fintype.card_sum

/-! ## Address-compressed transition populations -/

/-- A compressed transition population replaces each edge cell by its label.
Incoming and outgoing incidence are compiled independently, so two edges with
the same label may cross-wire. -/
def compressedPopulationCoupled
    {Label : Type uLabel}
    (graph : DirectedTransitionGraph Vertex Edge)
    (label : Edge → Label) :
    (Vertex ⊕ Label) → (Vertex ⊕ Label) → Prop
  | .inl vertex, .inr address =>
      ∃ edge, graph.source edge = vertex ∧ label edge = address
  | .inr address, .inl vertex =>
      ∃ edge, label edge = address ∧ graph.target edge = vertex
  | _, _ => False

/-- Two-step transition relation after transition cells are merged by an
address map. -/
def compressedPopulationTransition
    {Label : Type uLabel}
    (graph : DirectedTransitionGraph Vertex Edge)
    (label : Edge → Label)
    (source target : Vertex) : Prop :=
  ∃ address,
    compressedPopulationCoupled graph label (.inl source) (.inr address) ∧
      compressedPopulationCoupled graph label (.inr address) (.inl target)

/-- Compression never deletes an original graph transition: the same edge
witness supplies both halves of the compiled two-step path. -/
theorem graphTransition_implies_compressedPopulationTransition
    {Label : Type uLabel}
    (graph : DirectedTransitionGraph Vertex Edge)
    (label : Edge → Label)
    (source target : Vertex)
    (transition : graphTransition graph source target) :
    compressedPopulationTransition graph label source target := by
  rcases transition with ⟨edge, source_eq, target_eq⟩
  exact ⟨label edge, ⟨edge, source_eq, rfl⟩,
    ⟨edge, rfl, target_eq⟩⟩

/-- Injective transition addresses prevent cross-wiring, so compression
recovers the original graph relation exactly. -/
theorem compressedPopulationTransition_iff_graphTransition_of_injective
    {Label : Type uLabel}
    (graph : DirectedTransitionGraph Vertex Edge)
    (label : Edge → Label)
    (label_injective : Function.Injective label)
    (source target : Vertex) :
    compressedPopulationTransition graph label source target ↔
      graphTransition graph source target := by
  constructor
  · rintro ⟨address,
      ⟨sourceEdge, source_eq, source_label_eq⟩,
      ⟨targetEdge, target_label_eq, target_eq⟩⟩
    have edge_eq : sourceEdge = targetEdge :=
      label_injective (source_label_eq.trans target_label_eq.symm)
    subst targetEdge
    exact ⟨sourceEdge, source_eq, target_eq⟩
  · exact graphTransition_implies_compressedPopulationTransition
      graph label source target

/-- Under injective addressing, the one-cycle exclusion remains valid after
compression. -/
theorem not_compressedPopulationTransition_self_of_injective
    {Label : Type uLabel}
    (graph : DirectedTransitionGraph Vertex Edge)
    (label : Edge → Label)
    (label_injective : Function.Injective label)
    (vertex : Vertex) :
    ¬compressedPopulationTransition graph label vertex vertex := by
  rw [compressedPopulationTransition_iff_graphTransition_of_injective
    graph label label_injective]
  rintro ⟨edge, source_eq, target_eq⟩
  exact graph.noSelfLoop edge (source_eq.trans target_eq.symm)

/-! ## Positive and negative executable fixtures -/

/-- Three vertices and three transition cells realize a directed three-cycle. -/
def threeCycleGraph : DirectedTransitionGraph (Fin 3) (Fin 3) where
  source := fun edge => edge
  target := fun edge => edge + 1
  noSelfLoop := by
    intro edge
    fin_cases edge <;> decide

/-- The two-population compiler recovers all and only the selected cycle
edges in a representative finite fixture. -/
theorem threeCycle_twoPopulation :
    twoPopulationTransition threeCycleGraph 0 1 ∧
      twoPopulationTransition threeCycleGraph 1 2 ∧
      twoPopulationTransition threeCycleGraph 2 0 ∧
      ¬twoPopulationTransition threeCycleGraph 0 2 := by
  constructor
  · rw [twoPopulationTransition_iff_graphTransition]
    exact ⟨0, rfl, by decide⟩
  constructor
  · rw [twoPopulationTransition_iff_graphTransition]
    exact ⟨1, rfl, by decide⟩
  constructor
  · rw [twoPopulationTransition_iff_graphTransition]
    exact ⟨2, rfl, by decide⟩
  · rw [twoPopulationTransition_iff_graphTransition]
    rintro ⟨edge, source_eq, target_eq⟩
    fin_cases edge <;>
      simp_all [threeCycleGraph]

/-- A two-edge graph whose edges have disjoint sources and targets. -/
def collisionGraph : DirectedTransitionGraph (Fin 4) (Fin 2) where
  source := fun edge => if edge = 0 then 0 else 2
  target := fun edge => if edge = 0 then 1 else 3
  noSelfLoop := by
    intro edge
    fin_cases edge <;> decide

/-- Merging both transition cells into one address is genuinely
noninjective. -/
theorem constantTransitionAddress_not_injective :
    ¬Function.Injective (fun _ : Fin 2 => ()) := by
  intro injective
  have falseEquality : (0 : Fin 2) = 1 := injective rfl
  exact Fin.zero_ne_one falseEquality

/-- The original graph has no transition from vertex zero to vertex three. -/
theorem collisionGraph_original_cross_absent :
    ¬graphTransition collisionGraph 0 3 := by
  rintro ⟨edge, source_eq, target_eq⟩
  fin_cases edge <;>
    simp_all [collisionGraph]

/-- Address collision cross-wires the source of edge `0 → 1` with the target
of edge `2 → 3`, creating the spurious transition `0 → 3`. -/
theorem constantTransitionAddress_creates_spurious_cross :
    compressedPopulationTransition collisionGraph
      (fun _ : Fin 2 => ()) 0 3 := by
  refine ⟨(), ?_, ?_⟩
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, rfl, by decide⟩

#print axioms twoPopulationTransition_iff_graphTransition
#print axioms not_twoPopulationTransition_self
#print axioms compressedPopulationTransition_iff_graphTransition_of_injective
#print axioms constantTransitionAddress_creates_spurious_cross

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
