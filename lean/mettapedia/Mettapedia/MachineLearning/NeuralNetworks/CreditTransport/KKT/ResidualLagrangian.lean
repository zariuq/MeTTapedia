import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.OccurrenceAdjoint
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Residual Lagrangians on heterogeneous finite state families

This module differentiates the actual constrained objective

`objective x - ∑ v, credit v (x v - forward v x)`.

The derivative is obtained from `HasFDerivAt` certificates for the objective
and every node operator.  No reverse recursion is assumed.  The subsequent
occurrence-decomposition theorem identifies its coordinate coefficients with
the metric-free reverse covectors of `OccurrenceAdjoint`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT

universe uNode uState

variable {Node : Type uNode} [Fintype Node] [DecidableEq Node]
variable (NodeSpace : Node → Type uState)
variable [∀ node, NormedAddCommGroup (NodeSpace node)]
variable [∀ node, NormedSpace ℝ (NodeSpace node)]

/-- Fréchet differentiability with all algebraic and topological structures
coherently inherited from the declared real normed spaces. -/
abbrev HasRealFDerivAt {Domain Codomain : Type*}
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Codomain] [NormedSpace ℝ Codomain]
    (function : Domain → Codomain)
    (derivative : Domain →L[ℝ] Codomain) (point : Domain) : Prop :=
  @HasFDerivAt ℝ _ Domain
    NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Codomain NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    function derivative point

/-- The heterogeneous product of all differentiable node states. -/
abbrev GlobalState := ∀ node, NodeSpace node

/-- One node's constraint residual, with orientation `state - prediction`. -/
def nodeResidual
    (forward : ∀ node, GlobalState NodeSpace → NodeSpace node)
    (node : Node) (state : GlobalState NodeSpace) : NodeSpace node :=
  state node - forward node state

/-- The actual residual Lagrangian.  Reverse credit is a family of covectors,
so its action on each heterogeneous residual is scalar and can be summed. -/
noncomputable def residualLagrangian
    (objective : GlobalState NodeSpace → ℝ)
    (forward : ∀ node, GlobalState NodeSpace → NodeSpace node)
    (credit : ∀ node, NodeCovector NodeSpace node)
    (state : GlobalState NodeSpace) : ℝ :=
  objective state - ∑ node, credit node (nodeResidual NodeSpace forward node state)

/-- The derivative predicted directly by finite-sum calculus, before any
occurrence decomposition of the node Jacobians. -/
noncomputable def residualLagrangianDerivative
    (objectiveDerivative : GlobalState NodeSpace →L[ℝ] ℝ)
    (forwardDerivative : ∀ node,
      GlobalState NodeSpace →L[ℝ] NodeSpace node)
    (credit : ∀ node, NodeCovector NodeSpace node) :
    GlobalState NodeSpace →L[ℝ] ℝ :=
  objectiveDerivative -
    ∑ node, credit node ∘L
      (ContinuousLinearMap.proj node - forwardDerivative node)

omit [DecidableEq Node] in
/-- The residual of one actual node operator has derivative
`coordinate projection - operator derivative`. -/
theorem hasFDerivAt_nodeResidual
    (forward : ∀ node, GlobalState NodeSpace → NodeSpace node)
    (forwardDerivative : ∀ node,
      GlobalState NodeSpace →L[ℝ] NodeSpace node)
    (state : GlobalState NodeSpace) (node : Node)
    (hForward : HasRealFDerivAt
      (forward node) (forwardDerivative node) state) :
    HasRealFDerivAt (fun current => current node - forward node current)
      (ContinuousLinearMap.proj node - forwardDerivative node) state := by
  exact (ContinuousLinearMap.proj node).hasFDerivAt.sub hForward

omit [DecidableEq Node] in
/-- Exact derivative of the actual finite residual Lagrangian.  This is the
calculus step that prevents a reverse recursion from being smuggled in as an
assumption. -/
theorem hasFDerivAt_residualLagrangian
    (objective : GlobalState NodeSpace → ℝ)
    (forward : ∀ node, GlobalState NodeSpace → NodeSpace node)
    (credit : ∀ node, NodeCovector NodeSpace node)
    (state : GlobalState NodeSpace)
    (objectiveDerivative : GlobalState NodeSpace →L[ℝ] ℝ)
    (forwardDerivative : ∀ node,
      GlobalState NodeSpace →L[ℝ] NodeSpace node)
    (hObjective : HasRealFDerivAt objective objectiveDerivative state)
    (hForward : ∀ node,
      HasRealFDerivAt (forward node) (forwardDerivative node) state) :
    HasRealFDerivAt
      (objective - ∑ node,
        (credit node) ∘ (fun current => current node - forward node current))
      (objectiveDerivative -
        ∑ node, credit node ∘L
          (ContinuousLinearMap.proj node - forwardDerivative node))
      state := by
  have hResidualTerm : ∀ node,
      HasRealFDerivAt
        ((credit node) ∘
          (fun current => current node - forward node current))
        (credit node ∘L
          (ContinuousLinearMap.proj node - forwardDerivative node))
        state := by
    intro node
    exact (credit node).hasFDerivAt.comp state
      (hasFDerivAt_nodeResidual NodeSpace forward forwardDerivative state node
        (hForward node))
  have hSum : HasRealFDerivAt
      (∑ node, (credit node) ∘
        (fun current => current node - forward node current))
      (∑ node, credit node ∘L
        (ContinuousLinearMap.proj node - forwardDerivative node))
      state := by
    exact HasFDerivAt.sum fun node _ => hResidualTerm node
  exact hObjective.sub hSum

/-! ## Occurrence decomposition of the actual Jacobians -/

universe uOccurrence

variable (ParentOccurrence : Node → Node → Type uOccurrence)
variable [∀ source target, Fintype (ParentOccurrence source target)]

/-- Assemble a global node-operator derivative from its active parent-slot
partials.  Parallel slots remain separate terms. -/
noncomputable def occurrenceForwardDerivative
    (graph : RankedOccurrenceDAG ParentOccurrence)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (target : Node) : GlobalState NodeSpace →L[ℝ] NodeSpace target :=
  ∑ source, ∑ occurrence : ParentOccurrence source target,
    if graph.active occurrence then
      parentDerivative occurrence ∘L ContinuousLinearMap.proj source
    else 0

/-- Restrict a global objective derivative to one node coordinate. -/
noncomputable def objectiveCoordinate
    (objectiveDerivative : GlobalState NodeSpace →L[ℝ] ℝ)
    (source : Node) : NodeCovector NodeSpace source :=
  objectiveDerivative ∘L ContinuousLinearMap.single ℝ NodeSpace source

/-- Restricting an occurrence-assembled Jacobian to one coordinate recovers
exactly the sum of active partials from that source. -/
theorem occurrenceForwardDerivative_comp_single
    (graph : RankedOccurrenceDAG ParentOccurrence)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (source target : Node) :
    (occurrenceForwardDerivative NodeSpace ParentOccurrence graph
        parentDerivative target ∘L
      ContinuousLinearMap.single ℝ NodeSpace source) =
    (∑ occurrence : ParentOccurrence source target,
      if graph.active occurrence then parentDerivative occurrence else 0 :
        NodeSpace source →L[ℝ] NodeSpace target) := by
  ext direction
  simp only [occurrenceForwardDerivative, sum_apply,
    ContinuousLinearMap.comp_apply]
  rw [Finset.sum_eq_single source]
  · apply Finset.sum_congr rfl
    intro occurrence _
    by_cases active : graph.active occurrence = true
    · simp [active, ContinuousLinearMap.single_apply]
    · simp [active]
  · intro other _ hne
    apply Finset.sum_eq_zero
    intro occurrence _
    by_cases active : graph.active occurrence = true
    · simp [active, ContinuousLinearMap.single_apply, hne]
    · simp [active]
  · simp

/-- After occurrence decomposition, each coordinate of the actual
Lagrangian derivative is the state-stationarity coefficient from the reverse
covector recursion. -/
theorem residualLagrangianCoordinate_eq_stateStationarityCoefficient
    (graph : RankedOccurrenceDAG ParentOccurrence)
    (objectiveDerivative : GlobalState NodeSpace →L[ℝ] ℝ)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node)
    (source : Node) :
    (residualLagrangianDerivative NodeSpace objectiveDerivative
        (occurrenceForwardDerivative NodeSpace ParentOccurrence graph
          parentDerivative) credit ∘L
      ContinuousLinearMap.single ℝ NodeSpace source) =
    RankedOccurrenceDAG.stateStationarityCoefficient
      (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
      graph (objectiveCoordinate NodeSpace objectiveDerivative)
      parentDerivative credit source := by
  ext direction
  have coordinateSum :
      (∑ target, credit target (Pi.single source direction target)) =
        credit source direction := by
    rw [Finset.sum_eq_single source]
    · simp
    · intro other _ hne
      simp [Pi.single_eq_of_ne hne]
    · simp
  have transportedSum :
      (∑ target, credit target
        ((occurrenceForwardDerivative NodeSpace ParentOccurrence graph
          parentDerivative target) (Pi.single source direction))) =
      ∑ target, ∑ occurrence : ParentOccurrence source target,
        (if graph.active occurrence then
          credit target ∘L parentDerivative occurrence else 0) direction := by
    apply Finset.sum_congr rfl
    intro target _
    have restricted := congrArg
      (fun derivative : NodeSpace source →L[ℝ] NodeSpace target =>
        credit target (derivative direction))
      (occurrenceForwardDerivative_comp_single NodeSpace ParentOccurrence
        graph parentDerivative source target)
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.single_apply] at restricted
    rw [restricted]
    rw [sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro occurrence _
    by_cases active : graph.active occurrence = true
    · simp [active, ContinuousLinearMap.comp_apply]
    · simp [active]
  simp [residualLagrangianDerivative, objectiveCoordinate,
    RankedOccurrenceDAG.stateStationarityCoefficient,
    RankedOccurrenceDAG.parentAggregate, parentPullback,
    ContinuousLinearMap.single_apply, Finset.sum_sub_distrib]
  rw [coordinateSum, transportedSum]
  ring

/-- Coordinate stationarity of the occurrence-assembled residual-Lagrangian
derivative is equivalent to the exact reverse covector recursion. -/
theorem occurrenceResidualStationary_iff_reverseRecursion
    (graph : RankedOccurrenceDAG ParentOccurrence)
    (objectiveDerivative : GlobalState NodeSpace →L[ℝ] ℝ)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node) :
    (∀ source,
      residualLagrangianDerivative NodeSpace objectiveDerivative
          (occurrenceForwardDerivative NodeSpace ParentOccurrence graph
            parentDerivative) credit ∘L
        ContinuousLinearMap.single ℝ NodeSpace source = 0) ↔
    (∀ source,
      credit source = RankedOccurrenceDAG.reverseAggregate
        (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
        graph (objectiveCoordinate NodeSpace objectiveDerivative)
        parentDerivative credit source) := by
  rw [← RankedOccurrenceDAG.stateStationarity_iff_reverseRecursion
    (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
    graph (objectiveCoordinate NodeSpace objectiveDerivative)
    parentDerivative credit]
  constructor <;> intro stationary source
  · rw [← residualLagrangianCoordinate_eq_stateStationarityCoefficient
      NodeSpace ParentOccurrence graph objectiveDerivative parentDerivative
      credit source]
    exact stationary source
  · rw [residualLagrangianCoordinate_eq_stateStationarityCoefficient
      NodeSpace ParentOccurrence graph objectiveDerivative parentDerivative
      credit source]
    exact stationary source

/-- The combined KKT-to-reverse-credit result: actual node and objective
derivative certificates first establish the derivative of the residual
Lagrangian; stationarity of that derivative is then equivalent to the reverse
recursion. -/
theorem hasFDerivAt_residualLagrangian_and_stationary_iff_reverseRecursion
    (graph : RankedOccurrenceDAG ParentOccurrence)
    (objective : GlobalState NodeSpace → ℝ)
    (forward : ∀ node, GlobalState NodeSpace → NodeSpace node)
    (credit : ∀ node, NodeCovector NodeSpace node)
    (state : GlobalState NodeSpace)
    (objectiveDerivative : GlobalState NodeSpace →L[ℝ] ℝ)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (hObjective : HasRealFDerivAt objective objectiveDerivative state)
    (hForward : ∀ node, HasRealFDerivAt (forward node)
      (occurrenceForwardDerivative NodeSpace ParentOccurrence graph
        parentDerivative node) state) :
    HasRealFDerivAt
        (objective - ∑ node,
          (credit node) ∘ (fun current => current node - forward node current))
        (residualLagrangianDerivative NodeSpace objectiveDerivative
          (occurrenceForwardDerivative NodeSpace ParentOccurrence graph
            parentDerivative) credit)
        state ∧
      ((∀ source,
        residualLagrangianDerivative NodeSpace objectiveDerivative
            (occurrenceForwardDerivative NodeSpace ParentOccurrence graph
              parentDerivative) credit ∘L
          ContinuousLinearMap.single ℝ NodeSpace source = 0) ↔
       (∀ source,
        credit source = RankedOccurrenceDAG.reverseAggregate
          (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
          graph (objectiveCoordinate NodeSpace objectiveDerivative)
          parentDerivative credit source)) := by
  exact ⟨hasFDerivAt_residualLagrangian NodeSpace objective forward credit
      state objectiveDerivative
      (occurrenceForwardDerivative NodeSpace ParentOccurrence graph
        parentDerivative) hObjective hForward,
    occurrenceResidualStationary_iff_reverseRecursion NodeSpace
      ParentOccurrence graph objectiveDerivative parentDerivative credit⟩

#print axioms hasFDerivAt_nodeResidual
#print axioms hasFDerivAt_residualLagrangian
#print axioms occurrenceForwardDerivative_comp_single
#print axioms residualLagrangianCoordinate_eq_stateStationarityCoefficient
#print axioms occurrenceResidualStationary_iff_reverseRecursion
#print axioms hasFDerivAt_residualLagrangian_and_stationary_iff_reverseRecursion

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT
