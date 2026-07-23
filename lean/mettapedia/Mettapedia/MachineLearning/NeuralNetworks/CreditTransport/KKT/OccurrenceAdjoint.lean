import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Core
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Tactic

/-!
# Occurrence-aware reverse covectors on finite DAGs

Reverse credit is represented as a continuous linear functional on each node
space.  Parent slots are indexed occurrences, so parallel uses of a shared
state remain distinct summands.  Parameter uses are indexed independently for
the same reason.  This module establishes the metric-free aggregation layer;
the residual-Lagrangian module connects these coefficients to actual
Fréchet derivatives.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT

universe uNode uOccurrence uState uParameter uParameterOccurrence

variable {Node : Type uNode} [Fintype Node]
variable (ParentOccurrence : Node → Node → Type uOccurrence)
variable [parentOccurrenceFintype :
  ∀ source target, Fintype (ParentOccurrence source target)]
variable (NodeSpace : Node → Type uState)
variable [nodeNormedAddCommGroup :
  ∀ node, NormedAddCommGroup (NodeSpace node)]
variable [nodeNormedSpace : ∀ node, NormedSpace ℝ (NodeSpace node)]

/-- Reverse credit at one node, kept as a covector rather than identified
with a gradient through an inner product. -/
abbrev NodeCovector (node : Node) := NodeSpace node →L[ℝ] ℝ

/-- A ranked occurrence graph.  A parent occurrence goes from `source` to a
strictly later `target`; parallel occurrences are allowed. -/
structure RankedOccurrenceDAG where
  rank : Node → ℕ
  active : ∀ {source target}, ParentOccurrence source target → Bool
  forward : ∀ {source target},
    (occurrence : ParentOccurrence source target) →
    active occurrence = true → rank source < rank target

variable (graph : RankedOccurrenceDAG ParentOccurrence)

/-- Pull a target covector back through one declared parent occurrence. -/
noncomputable def parentPullback
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node)
    {source target : Node} (occurrence : ParentOccurrence source target) :
    NodeCovector NodeSpace source :=
  credit target ∘L parentDerivative occurrence

namespace RankedOccurrenceDAG

/-- Largest node rank in the finite graph. -/
noncomputable def maxRank : ℕ :=
  Finset.univ.sup graph.rank

/-- Remaining reverse-recursion height.  Active children have strictly
smaller reverse height. -/
noncomputable def reverseHeight (node : Node) : ℕ :=
  maxRank (ParentOccurrence := ParentOccurrence) graph - graph.rank node

omit parentOccurrenceFintype in
theorem rank_le_maxRank (node : Node) :
    graph.rank node ≤ maxRank (ParentOccurrence := ParentOccurrence) graph := by
  exact Finset.le_sup (Finset.mem_univ node)

omit parentOccurrenceFintype in
theorem reverseHeight_lt_of_active
    {source target : Node}
    (occurrence : ParentOccurrence source target)
    (active : graph.active occurrence = true) :
    reverseHeight (ParentOccurrence := ParentOccurrence) graph target <
      reverseHeight (ParentOccurrence := ParentOccurrence) graph source := by
  have forward := graph.forward occurrence active
  have targetBound := rank_le_maxRank
    (ParentOccurrence := ParentOccurrence) graph target
  simp only [reverseHeight]
  omega

/-- Sum every active target-to-source pullback, preserving occurrence
multiplicity. -/
noncomputable def parentAggregate
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node) (source : Node) :
    NodeCovector NodeSpace source :=
  ∑ target : Node, ∑ occurrence : ParentOccurrence source target,
    if graph.active occurrence then
      parentPullback ParentOccurrence NodeSpace parentDerivative credit occurrence
    else 0

/-- Direct objective credit plus every active child-occurrence pullback. -/
noncomputable def reverseAggregate
    (direct : ∀ node, NodeCovector NodeSpace node)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node) (source : Node) :
    NodeCovector NodeSpace source :=
  direct source + parentAggregate
    (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
    graph parentDerivative credit source

/-- Canonical reverse covectors, constructed by well-founded recursion from
later nodes to earlier nodes.  Every recursive call follows an active parent
occurrence and therefore decreases `reverseHeight`. -/
noncomputable def reverseSolution
    (direct : ∀ node, NodeCovector NodeSpace node)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target) :
    ∀ node, NodeCovector NodeSpace node :=
  WellFounded.fix
      (measure (reverseHeight (ParentOccurrence := ParentOccurrence) graph)).wf
      fun source recurse =>
    direct source +
      ∑ target : Node, ∑ occurrence : ParentOccurrence source target,
        if active : graph.active occurrence = true then
          recurse target (reverseHeight_lt_of_active
              (ParentOccurrence := ParentOccurrence) graph occurrence active) ∘L
            parentDerivative occurrence
        else 0

/-- The well-founded construction satisfies the exact occurrence-aware
reverse recursion. -/
theorem reverseSolution_eq_reverseAggregate
    (direct : ∀ node, NodeCovector NodeSpace node)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (source : Node) :
    reverseSolution (ParentOccurrence := ParentOccurrence)
        (NodeSpace := NodeSpace) graph direct parentDerivative source =
      reverseAggregate (ParentOccurrence := ParentOccurrence)
        (NodeSpace := NodeSpace) graph direct parentDerivative
        (reverseSolution (ParentOccurrence := ParentOccurrence)
          (NodeSpace := NodeSpace) graph direct parentDerivative) source := by
  rw [reverseSolution, WellFounded.fix_eq]
  rfl

/-- A finite strictly ranked occurrence DAG has exactly one reverse-covector
solution for every direct objective family and family of active partials. -/
theorem reverseSolution_existsUnique
    (direct : ∀ node, NodeCovector NodeSpace node)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target) :
    ∃! credit : ∀ node, NodeCovector NodeSpace node,
      ∀ source, credit source =
        reverseAggregate (ParentOccurrence := ParentOccurrence)
          (NodeSpace := NodeSpace) graph direct parentDerivative credit source := by
  refine ⟨reverseSolution (ParentOccurrence := ParentOccurrence)
      (NodeSpace := NodeSpace) graph direct parentDerivative,
    reverseSolution_eq_reverseAggregate (ParentOccurrence := ParentOccurrence)
      (NodeSpace := NodeSpace) graph direct parentDerivative, ?_⟩
  intro credit recurrence
  funext source
  induction source using
      (measure (reverseHeight
        (ParentOccurrence := ParentOccurrence) graph)).wf.induction with
  | h source inductionHypothesis =>
      rw [recurrence source,
        reverseSolution_eq_reverseAggregate (ParentOccurrence := ParentOccurrence)
          (NodeSpace := NodeSpace) graph direct parentDerivative source,
        reverseAggregate]
      congr 1
      simp only [parentAggregate]
      apply Finset.sum_congr rfl
      intro target _
      apply Finset.sum_congr rfl
      intro occurrence _
      by_cases active : graph.active occurrence = true
      · simp only [active, if_true, parentPullback]
        rw [inductionHypothesis target
          (reverseHeight_lt_of_active (ParentOccurrence := ParentOccurrence)
            graph occurrence active)]
      · simp [active]

/-- The state-stationarity coefficient of
`objective - sum(adjoint * residual)` at one node. -/
noncomputable def stateStationarityCoefficient
    (direct : ∀ node, NodeCovector NodeSpace node)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node) (source : Node) :
    NodeCovector NodeSpace source :=
  direct source - credit source +
    parentAggregate (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
      graph parentDerivative credit source

/-- Vanishing occurrence-aware state coefficients are exactly the reverse
covector recursion.  The following residual-Lagrangian layer must still prove
that these coefficients are the derivative of the actual constrained
objective. -/
theorem stateStationarity_iff_reverseRecursion
    (direct : ∀ node, NodeCovector NodeSpace node)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node) :
    (∀ source,
      stateStationarityCoefficient
        (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
        graph direct parentDerivative credit source = 0) ↔
    (∀ source,
      credit source = reverseAggregate
        (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
        graph direct parentDerivative credit source) := by
  constructor
  · intro stationary source
    have h := stationary source
    rw [stateStationarityCoefficient] at h
    rw [reverseAggregate]
    calc
      credit source = direct source +
          parentAggregate (ParentOccurrence := ParentOccurrence)
            (NodeSpace := NodeSpace) graph parentDerivative credit source -
          (direct source - credit source +
            parentAggregate (ParentOccurrence := ParentOccurrence)
              (NodeSpace := NodeSpace) graph parentDerivative credit source) := by
            abel
      _ = direct source +
          parentAggregate (ParentOccurrence := ParentOccurrence)
            (NodeSpace := NodeSpace) graph parentDerivative credit source := by
            rw [h, sub_zero]
  · intro recursion source
    rw [stateStationarityCoefficient, recursion source, reverseAggregate]
    abel

end RankedOccurrenceDAG

/-! ## Tied parameter occurrences -/

variable {Parameter : Type uParameter} [Fintype Parameter]
variable (ParameterOccurrence : Parameter → Node → Type uParameterOccurrence)
variable [parameterOccurrenceFintype :
  ∀ parameter owner, Fintype (ParameterOccurrence parameter owner)]
variable (ParameterSpace : Parameter → Type*)
variable [parameterNormedAddCommGroup :
  ∀ parameter, NormedAddCommGroup (ParameterSpace parameter)]
variable [parameterNormedSpace :
  ∀ parameter, NormedSpace ℝ (ParameterSpace parameter)]

/-- Parameter credit remains a covector on the shared parameter space. -/
abbrev ParameterCovector (parameter : Parameter) :=
  ParameterSpace parameter →L[ℝ] ℝ

/-- Direct parameter dependence plus every active occurrence pullback. -/
noncomputable def tiedParameterAggregate
    (active : ∀ {parameter owner},
      ParameterOccurrence parameter owner → Bool)
    (direct : ∀ parameter, ParameterCovector ParameterSpace parameter)
    (parameterDerivative : ∀ {parameter owner}, ParameterOccurrence parameter owner →
      ParameterSpace parameter →L[ℝ] NodeSpace owner)
    (credit : ∀ node, NodeCovector NodeSpace node) (parameter : Parameter) :
    ParameterCovector ParameterSpace parameter :=
  direct parameter +
    ∑ owner : Node, ∑ occurrence : ParameterOccurrence parameter owner,
      if active occurrence then credit owner ∘L parameterDerivative occurrence else 0

/-! ## Exact multiplicity fixtures -/

/-- Two potential parent slots per ordered node pair.  The graph mask activates
exactly the two slots from node `0` to node `1`. -/
abbrev twoSlotOccurrence (_source _target : Fin 2) : Type := Fin 2

noncomputable def twoSlotGraph : RankedOccurrenceDAG twoSlotOccurrence where
  rank := fun node => node.val
  active := fun {source target} _ => decide (source = 0 ∧ target = 1)
  forward := by
    intro source target _ active
    rcases of_decide_eq_true active with ⟨rfl, rfl⟩
    norm_num

noncomputable def twoSlotPartial
    {source target : Fin 2} (occurrence : twoSlotOccurrence source target) :
    ℝ →L[ℝ] ℝ :=
  (if occurrence.val = 0 then 3 else 6) • ContinuousLinearMap.id ℝ ℝ

noncomputable def twoSlotCredit : ∀ _node : Fin 2, ℝ →L[ℝ] ℝ :=
  fun node => (if node = 1 then 1 else 0) • ContinuousLinearMap.id ℝ ℝ

noncomputable def zeroDirect : ∀ _node : Fin 2, ℝ →L[ℝ] ℝ :=
  fun _ => 0

/-- Both parallel parent occurrences contribute to the shared source. -/
theorem twoSlot_parentAggregate_counts_both_occurrences :
    RankedOccurrenceDAG.parentAggregate
      (ParentOccurrence := twoSlotOccurrence)
      (NodeSpace := fun _ : Fin 2 => ℝ)
      twoSlotGraph twoSlotPartial twoSlotCredit 0 1 = 9 := by
  norm_num [RankedOccurrenceDAG.parentAggregate, twoSlotGraph,
    twoSlotOccurrence, twoSlotPartial, twoSlotCredit, parentPullback]

/-- Keeping either one of the two occurrence contributions loses credit. -/
theorem twoSlot_single_occurrence_is_incorrect :
    (3 : ℝ) ≠ 9 ∧ (6 : ℝ) ≠ 9 := by
  norm_num

/-- Two potential tied uses per owner; the fixture mask activates both uses
only at node `1`. -/
abbrev twoTiedParameterOccurrence (_parameter : Unit) (_owner : Fin 2) : Type :=
  Fin 2

noncomputable def twoTiedParameterPartial
    {parameter : Unit} {owner : Fin 2}
    (occurrence : twoTiedParameterOccurrence parameter owner) : ℝ →L[ℝ] ℝ :=
  (if occurrence.val = 0 then 2 else 4) • ContinuousLinearMap.id ℝ ℝ

noncomputable def zeroParameterDirect : ∀ _parameter : Unit, ℝ →L[ℝ] ℝ :=
  fun _ => 0

/-- Tied aggregation preserves both parameter-use occurrences. -/
theorem twoTiedParameterAggregate_counts_both_occurrences :
    tiedParameterAggregate
      (NodeSpace := fun _ : Fin 2 => ℝ)
      (ParameterOccurrence := twoTiedParameterOccurrence)
      (ParameterSpace := fun _ : Unit => ℝ)
      (fun {_parameter owner} _ => decide (owner = 1)) zeroParameterDirect
      twoTiedParameterPartial twoSlotCredit () 1 = 6 := by
  norm_num [tiedParameterAggregate, twoTiedParameterOccurrence,
    twoTiedParameterPartial, twoSlotCredit, zeroParameterDirect, Fin.sum_univ_two]

#print axioms RankedOccurrenceDAG.stateStationarity_iff_reverseRecursion
#print axioms RankedOccurrenceDAG.reverseSolution_existsUnique
#print axioms twoSlot_parentAggregate_counts_both_occurrences
#print axioms twoSlot_single_occurrence_is_incorrect
#print axioms twoTiedParameterAggregate_counts_both_occurrences

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT
