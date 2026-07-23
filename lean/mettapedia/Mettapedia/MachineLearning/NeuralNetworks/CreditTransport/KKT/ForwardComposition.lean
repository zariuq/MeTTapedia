import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.ParameterLagrangian
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Feasible forward composition and the KKT envelope identity

This module connects a stationary residual Lagrangian to the derivative of an
actual feasible forward computation.  The evaluator is a genuine function of
the shared parameters with an actual Fréchet derivative.  Feasibility makes
the Lagrangian and task objective agree along that path; state stationarity
then removes the evaluator tangent and leaves exactly the parameter partial.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT

section Envelope

variable {State Parameter : Type*}
variable [NormedAddCommGroup State] [NormedSpace ℝ State]
variable [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

/-- The actual state-parameter path followed by a forward evaluator. -/
def jointPath (evaluate : Parameter → State) (parameter : Parameter) :
    State × Parameter :=
  (evaluate parameter, parameter)

/-- Tangent of the joint path: evaluator tangent paired with the identity
parameter tangent. -/
noncomputable def jointPathDerivative
    (evaluateDerivative : Parameter →L[ℝ] State) :
    Parameter →L[ℝ] State × Parameter :=
  evaluateDerivative.prod (ContinuousLinearMap.id ℝ Parameter)

/-- Chain-rule certificate for the actual joint path. -/
theorem hasFDerivAt_jointPath
    (evaluate : Parameter → State)
    (evaluateDerivative : Parameter →L[ℝ] State)
    (parameter : Parameter)
    (hEvaluate : HasRealFDerivAt evaluate evaluateDerivative parameter) :
    HasRealFDerivAt (jointPath evaluate)
      (jointPathDerivative evaluateDerivative) parameter := by
  exact hEvaluate.prodMk (hasFDerivAt_id parameter)

/-- If the joint Lagrangian derivative vanishes in every state direction,
its derivative along the actual evaluator path is exactly its parameter
partial. -/
theorem stationary_jointPathDerivative_eq_parameterPartial
    (jointDerivative : State × Parameter →L[ℝ] ℝ)
    (evaluateDerivative : Parameter →L[ℝ] State)
    (stateStationary :
      jointDerivative ∘L ContinuousLinearMap.inl ℝ State Parameter = 0) :
    jointDerivative ∘L jointPathDerivative evaluateDerivative =
      jointDerivative ∘L ContinuousLinearMap.inr ℝ State Parameter := by
  ext direction
  have stateTerm : jointDerivative (evaluateDerivative direction, 0) = 0 := by
    have applied := congrArg
      (fun derivative : State →L[ℝ] ℝ =>
        derivative (evaluateDerivative direction)) stateStationary
    simpa using applied
  calc
    jointDerivative
        ((jointPathDerivative evaluateDerivative) direction) =
      jointDerivative (evaluateDerivative direction, direction) := by
        rfl
    _ = jointDerivative
        ((evaluateDerivative direction, 0) + (0, direction)) := by
          simp
    _ = jointDerivative (evaluateDerivative direction, 0) +
        jointDerivative (0, direction) := by
          rw [map_add]
    _ = jointDerivative (0, direction) := by rw [stateTerm, zero_add]
    _ = (jointDerivative ∘L
        ContinuousLinearMap.inr ℝ State Parameter) direction := by
          rfl

/-- Feasible-path envelope theorem.  The Lagrangian and objective are actual
functions on the joint state-parameter space.  Their equality is required
only locally along the actual evaluator path. -/
theorem feasible_envelope_parameterPartial_eq_taskDerivative
    (objective lagrangian : State × Parameter → ℝ)
    (evaluate : Parameter → State)
    (jointPoint : State × Parameter)
    (parameterPoint : Parameter)
    (jointObjectiveDerivative jointLagrangianDerivative :
      State × Parameter →L[ℝ] ℝ)
    (evaluateDerivative : Parameter →L[ℝ] State)
    (pointEq : jointPoint = jointPath evaluate parameterPoint)
    (hObjective : HasRealFDerivAt objective
      jointObjectiveDerivative jointPoint)
    (hLagrangian : HasRealFDerivAt lagrangian
      jointLagrangianDerivative jointPoint)
    (hEvaluate : HasRealFDerivAt evaluate
      evaluateDerivative parameterPoint)
    (stateStationary : jointLagrangianDerivative ∘L
      ContinuousLinearMap.inl ℝ State Parameter = 0)
    (feasibleAgreement :
      (fun parameter => lagrangian (jointPath evaluate parameter)) =ᶠ[nhds parameterPoint]
      (fun parameter => objective (jointPath evaluate parameter))) :
    HasRealFDerivAt
        (fun parameter => objective (jointPath evaluate parameter))
        (jointObjectiveDerivative ∘L
          jointPathDerivative evaluateDerivative) parameterPoint ∧
      jointLagrangianDerivative ∘L
          ContinuousLinearMap.inr ℝ State Parameter =
        jointObjectiveDerivative ∘L
          jointPathDerivative evaluateDerivative := by
  subst jointPoint
  have hPath := hasFDerivAt_jointPath evaluate evaluateDerivative
    parameterPoint hEvaluate
  have hObjectivePath := hObjective.comp parameterPoint hPath
  change HasRealFDerivAt
    (fun parameter => objective (jointPath evaluate parameter))
    (jointObjectiveDerivative ∘L jointPathDerivative evaluateDerivative)
    parameterPoint at hObjectivePath
  have hLagrangianPath := hLagrangian.comp parameterPoint hPath
  change HasRealFDerivAt
    (fun parameter => lagrangian (jointPath evaluate parameter))
    (jointLagrangianDerivative ∘L jointPathDerivative evaluateDerivative)
    parameterPoint at hLagrangianPath
  have hLagrangianAsObjective :=
    hLagrangianPath.congr_of_eventuallyEq feasibleAgreement.symm
  have pathDerivativeEq := hLagrangianAsObjective.unique hObjectivePath
  have stationaryReduction :=
    stationary_jointPathDerivative_eq_parameterPartial
      jointLagrangianDerivative evaluateDerivative stateStationary
  exact ⟨hObjectivePath, stationaryReduction.symm.trans pathDerivativeEq⟩

end Envelope

/-! ## Joint residual Lagrangian -/

universe uNode uState uParameter uParameterSpace

variable {Node : Type uNode} [Fintype Node]
variable (NodeSpace : Node → Type uState)
variable [∀ node, NormedAddCommGroup (NodeSpace node)]
variable [∀ node, NormedSpace ℝ (NodeSpace node)]

variable {Parameter : Type uParameter} [Fintype Parameter]
variable (ParameterSpace : Parameter → Type uParameterSpace)
variable [∀ parameter, NormedAddCommGroup (ParameterSpace parameter)]
variable [∀ parameter, NormedSpace ℝ (ParameterSpace parameter)]

/-- Joint differentiable domain of all node states and shared parameters. -/
abbrev JointStateParameter :=
  GlobalState NodeSpace × GlobalParameter ParameterSpace

/-- One actual residual on the joint state-parameter domain. -/
def jointNodeResidual
    (forward : ∀ node,
      JointStateParameter NodeSpace ParameterSpace → NodeSpace node)
    (node : Node)
    (point : JointStateParameter NodeSpace ParameterSpace) : NodeSpace node :=
  point.1 node - forward node point

/-- Residual Lagrangian on the actual joint state-parameter domain. -/
noncomputable def jointResidualLagrangian
    (objective : JointStateParameter NodeSpace ParameterSpace → ℝ)
    (forward : ∀ node,
      JointStateParameter NodeSpace ParameterSpace → NodeSpace node)
    (credit : ∀ node, NodeCovector NodeSpace node)
    (point : JointStateParameter NodeSpace ParameterSpace) : ℝ :=
  objective point -
    ∑ node, credit node
      (jointNodeResidual NodeSpace ParameterSpace forward node point)

/-- Coordinate projection from the joint domain to one node state. -/
noncomputable def jointNodeProjection (node : Node) :
    JointStateParameter NodeSpace ParameterSpace →L[ℝ] NodeSpace node :=
  ContinuousLinearMap.proj node ∘L
    ContinuousLinearMap.fst ℝ (GlobalState NodeSpace)
      (GlobalParameter ParameterSpace)

/-- Exact derivative expected from finite-sum calculus. -/
noncomputable def jointResidualLagrangianDerivative
    (objectiveDerivative :
      JointStateParameter NodeSpace ParameterSpace →L[ℝ] ℝ)
    (forwardDerivative : ∀ node,
      JointStateParameter NodeSpace ParameterSpace →L[ℝ] NodeSpace node)
    (credit : ∀ node, NodeCovector NodeSpace node) :
    JointStateParameter NodeSpace ParameterSpace →L[ℝ] ℝ :=
  objectiveDerivative -
    ∑ node, credit node ∘L
      (jointNodeProjection NodeSpace ParameterSpace node -
        forwardDerivative node)

/-- Exact derivative of the actual joint residual Lagrangian. -/
theorem hasFDerivAt_jointResidualLagrangian
    (objective : JointStateParameter NodeSpace ParameterSpace → ℝ)
    (forward : ∀ node,
      JointStateParameter NodeSpace ParameterSpace → NodeSpace node)
    (credit : ∀ node, NodeCovector NodeSpace node)
    (point : JointStateParameter NodeSpace ParameterSpace)
    (objectiveDerivative :
      JointStateParameter NodeSpace ParameterSpace →L[ℝ] ℝ)
    (forwardDerivative : ∀ node,
      JointStateParameter NodeSpace ParameterSpace →L[ℝ] NodeSpace node)
    (hObjective : HasRealFDerivAt objective objectiveDerivative point)
    (hForward : ∀ node,
      HasRealFDerivAt (forward node) (forwardDerivative node) point) :
    HasRealFDerivAt
      (fun current => jointResidualLagrangian NodeSpace ParameterSpace
        objective forward credit current)
      (jointResidualLagrangianDerivative NodeSpace ParameterSpace
        objectiveDerivative forwardDerivative credit) point := by
  have hResidualTerm : ∀ node,
      HasRealFDerivAt
        ((credit node) ∘
          (fun current => current.1 node - forward node current))
        (credit node ∘L
          (jointNodeProjection NodeSpace ParameterSpace node -
            forwardDerivative node)) point := by
    intro node
    exact (credit node).hasFDerivAt.comp point
      ((jointNodeProjection NodeSpace ParameterSpace node).hasFDerivAt.sub
        (hForward node))
  have hSum : HasRealFDerivAt
      (∑ node, (credit node) ∘
        (fun current => current.1 node - forward node current))
      (∑ node, credit node ∘L
        (jointNodeProjection NodeSpace ParameterSpace node -
          forwardDerivative node)) point := by
    exact HasFDerivAt.sum fun node _ => hResidualTerm node
  have hCore := hObjective.sub hSum
  convert hCore using 1
  · funext current
    simp only [jointResidualLagrangian, jointNodeResidual,
      Pi.sub_apply, Finset.sum_apply, Function.comp_apply]
  · rfl

/-! ## State and parameter restrictions of the joint derivative -/

omit [Fintype Parameter] in
/-- Restricting the joint residual-Lagrangian derivative to state directions
recovers the state-only derivative from `ResidualLagrangian`. -/
theorem jointResidualLagrangianDerivative_comp_inl
    (objectiveDerivative :
      JointStateParameter NodeSpace ParameterSpace →L[ℝ] ℝ)
    (forwardDerivative : ∀ node,
      JointStateParameter NodeSpace ParameterSpace →L[ℝ] NodeSpace node)
    (credit : ∀ node, NodeCovector NodeSpace node) :
    jointResidualLagrangianDerivative NodeSpace ParameterSpace
        objectiveDerivative forwardDerivative credit ∘L
      ContinuousLinearMap.inl ℝ (GlobalState NodeSpace)
        (GlobalParameter ParameterSpace) =
    residualLagrangianDerivative NodeSpace
      (objectiveDerivative ∘L
        ContinuousLinearMap.inl ℝ (GlobalState NodeSpace)
          (GlobalParameter ParameterSpace))
      (fun node => forwardDerivative node ∘L
        ContinuousLinearMap.inl ℝ (GlobalState NodeSpace)
          (GlobalParameter ParameterSpace)) credit := by
  ext direction
  simp [jointResidualLagrangianDerivative,
    residualLagrangianDerivative, jointNodeProjection,
    ContinuousLinearMap.comp_apply]

omit [Fintype Parameter] in
/-- Restricting the joint derivative to parameter directions recovers the
parameter-only derivative from `ParameterLagrangian`. -/
theorem jointResidualLagrangianDerivative_comp_inr
    (objectiveDerivative :
      JointStateParameter NodeSpace ParameterSpace →L[ℝ] ℝ)
    (forwardDerivative : ∀ node,
      JointStateParameter NodeSpace ParameterSpace →L[ℝ] NodeSpace node)
    (credit : ∀ node, NodeCovector NodeSpace node) :
    jointResidualLagrangianDerivative NodeSpace ParameterSpace
        objectiveDerivative forwardDerivative credit ∘L
      ContinuousLinearMap.inr ℝ (GlobalState NodeSpace)
        (GlobalParameter ParameterSpace) =
    parameterResidualLagrangianDerivative NodeSpace ParameterSpace
      (objectiveDerivative ∘L
        ContinuousLinearMap.inr ℝ (GlobalState NodeSpace)
          (GlobalParameter ParameterSpace))
      (fun node => forwardDerivative node ∘L
        ContinuousLinearMap.inr ℝ (GlobalState NodeSpace)
          (GlobalParameter ParameterSpace)) credit := by
  ext direction
  simp [jointResidualLagrangianDerivative,
    parameterResidualLagrangianDerivative, jointNodeProjection,
    ContinuousLinearMap.comp_apply]

variable [DecidableEq Node]

/-- A covector on a finite heterogeneous product is zero when all coordinate
restrictions are zero. -/
theorem piCovector_eq_zero_of_comp_single_eq_zero
    (derivative : GlobalState NodeSpace →L[ℝ] ℝ)
    (coordinateZero : ∀ node,
      derivative ∘L ContinuousLinearMap.single ℝ NodeSpace node = 0) :
    derivative = 0 := by
  ext direction
  have decomposition :
      direction = ∑ node, Pi.single node (direction node) := by
    funext target
    simp [Finset.sum_apply]
  rw [decomposition, map_sum]
  apply Finset.sum_eq_zero
  intro node _
  have applied := congrArg
    (fun coordinate : NodeSpace node →L[ℝ] ℝ => coordinate (direction node))
    (coordinateZero node)
  simpa using applied

universe uParentOccurrence

variable (ParentOccurrence : Node → Node → Type uParentOccurrence)
variable [∀ source target, Fintype (ParentOccurrence source target)]

omit [Fintype Parameter] in
/-- Exact reverse recursion makes the full joint Lagrangian stationary in
every state direction, provided the state partials of the actual joint node
operators are the declared active parent-occurrence derivatives. -/
theorem reverseRecursion_implies_jointStateStationary
    (graph : RankedOccurrenceDAG ParentOccurrence)
    (objectiveDerivative :
      JointStateParameter NodeSpace ParameterSpace →L[ℝ] ℝ)
    (forwardDerivative : ∀ node,
      JointStateParameter NodeSpace ParameterSpace →L[ℝ] NodeSpace node)
    (parentDerivative : ∀ {source target},
      ParentOccurrence source target →
        NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node)
    (forwardStateOccurrence : ∀ node,
      forwardDerivative node ∘L
          ContinuousLinearMap.inl ℝ (GlobalState NodeSpace)
            (GlobalParameter ParameterSpace) =
        occurrenceForwardDerivative NodeSpace ParentOccurrence graph
          parentDerivative node)
    (recurrence : ∀ source,
      credit source = RankedOccurrenceDAG.reverseAggregate
        (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
        graph
        (objectiveCoordinate NodeSpace
          (objectiveDerivative ∘L
            ContinuousLinearMap.inl ℝ (GlobalState NodeSpace)
              (GlobalParameter ParameterSpace)))
        parentDerivative credit source) :
    jointResidualLagrangianDerivative NodeSpace ParameterSpace
        objectiveDerivative forwardDerivative credit ∘L
      ContinuousLinearMap.inl ℝ (GlobalState NodeSpace)
        (GlobalParameter ParameterSpace) = 0 := by
  have forwardFamilyEq :
      (fun node => forwardDerivative node ∘L
        ContinuousLinearMap.inl ℝ (GlobalState NodeSpace)
          (GlobalParameter ParameterSpace)) =
      occurrenceForwardDerivative NodeSpace ParentOccurrence graph
        parentDerivative := by
    funext node
    exact forwardStateOccurrence node
  rw [jointResidualLagrangianDerivative_comp_inl,
    forwardFamilyEq]
  apply piCovector_eq_zero_of_comp_single_eq_zero NodeSpace
  exact (occurrenceResidualStationary_iff_reverseRecursion
    NodeSpace ParentOccurrence graph
    (objectiveDerivative ∘L
      ContinuousLinearMap.inl ℝ (GlobalState NodeSpace)
        (GlobalParameter ParameterSpace))
    parentDerivative credit).2 recurrence

universe uParameterOccurrence

variable [DecidableEq Parameter]
variable (ParameterOccurrence : Parameter → Node → Type uParameterOccurrence)
variable [∀ parameter owner, Fintype (ParameterOccurrence parameter owner)]

omit [DecidableEq Node] in
/-- Each shared-parameter coordinate of the joint derivative is the exact
tied-occurrence aggregate. -/
theorem jointParameterCoordinate_eq_tiedParameterAggregate
    (active : ∀ {parameter owner},
      ParameterOccurrence parameter owner → Bool)
    (objectiveDerivative :
      JointStateParameter NodeSpace ParameterSpace →L[ℝ] ℝ)
    (forwardDerivative : ∀ node,
      JointStateParameter NodeSpace ParameterSpace →L[ℝ] NodeSpace node)
    (parameterDerivative : ∀ {parameter owner},
      ParameterOccurrence parameter owner →
        ParameterSpace parameter →L[ℝ] NodeSpace owner)
    (credit : ∀ node, NodeCovector NodeSpace node)
    (forwardParameterOccurrence : ∀ owner,
      forwardDerivative owner ∘L
          ContinuousLinearMap.inr ℝ (GlobalState NodeSpace)
            (GlobalParameter ParameterSpace) =
        occurrenceParameterDerivative NodeSpace ParameterSpace
          ParameterOccurrence active parameterDerivative owner)
    (parameter : Parameter) :
    jointResidualLagrangianDerivative NodeSpace ParameterSpace
          objectiveDerivative forwardDerivative credit ∘L
        ContinuousLinearMap.inr ℝ (GlobalState NodeSpace)
          (GlobalParameter ParameterSpace) ∘L
      ContinuousLinearMap.single ℝ ParameterSpace parameter =
    tiedParameterAggregate
      (NodeSpace := NodeSpace)
      (ParameterOccurrence := ParameterOccurrence)
      (ParameterSpace := ParameterSpace)
      active
      (parameterObjectiveCoordinate ParameterSpace
        (objectiveDerivative ∘L
          ContinuousLinearMap.inr ℝ (GlobalState NodeSpace)
            (GlobalParameter ParameterSpace)))
      parameterDerivative credit parameter := by
  have forwardFamilyEq :
      (fun owner => forwardDerivative owner ∘L
        ContinuousLinearMap.inr ℝ (GlobalState NodeSpace)
          (GlobalParameter ParameterSpace)) =
      occurrenceParameterDerivative NodeSpace ParameterSpace
        ParameterOccurrence active parameterDerivative := by
    funext owner
    exact forwardParameterOccurrence owner
  have restriction := jointResidualLagrangianDerivative_comp_inr
    NodeSpace ParameterSpace objectiveDerivative forwardDerivative credit
  calc
    (jointResidualLagrangianDerivative NodeSpace ParameterSpace
          objectiveDerivative forwardDerivative credit ∘L
        ContinuousLinearMap.inr ℝ (GlobalState NodeSpace)
          (GlobalParameter ParameterSpace)) ∘L
        ContinuousLinearMap.single ℝ ParameterSpace parameter =
      parameterResidualLagrangianDerivative NodeSpace ParameterSpace
          (objectiveDerivative ∘L
            ContinuousLinearMap.inr ℝ (GlobalState NodeSpace)
              (GlobalParameter ParameterSpace))
          (fun owner => forwardDerivative owner ∘L
            ContinuousLinearMap.inr ℝ (GlobalState NodeSpace)
              (GlobalParameter ParameterSpace)) credit ∘L
        ContinuousLinearMap.single ℝ ParameterSpace parameter := by
          rw [restriction]
    _ = parameterResidualLagrangianDerivative NodeSpace ParameterSpace
          (objectiveDerivative ∘L
            ContinuousLinearMap.inr ℝ (GlobalState NodeSpace)
              (GlobalParameter ParameterSpace))
          (occurrenceParameterDerivative NodeSpace ParameterSpace
            ParameterOccurrence active parameterDerivative) credit ∘L
        ContinuousLinearMap.single ℝ ParameterSpace parameter := by
          rw [forwardFamilyEq]
    _ = tiedParameterAggregate
          (NodeSpace := NodeSpace)
          (ParameterOccurrence := ParameterOccurrence)
          (ParameterSpace := ParameterSpace)
          active
          (parameterObjectiveCoordinate ParameterSpace
            (objectiveDerivative ∘L
              ContinuousLinearMap.inr ℝ (GlobalState NodeSpace)
                (GlobalParameter ParameterSpace)))
          parameterDerivative credit parameter :=
      parameterResidualLagrangianCoordinate_eq_tiedParameterAggregate
        NodeSpace ParameterSpace ParameterOccurrence active
        (objectiveDerivative ∘L
          ContinuousLinearMap.inr ℝ (GlobalState NodeSpace)
            (GlobalParameter ParameterSpace))
        parameterDerivative credit parameter

/-- Arbitrary-DAG KKT-to-task-derivative crown.  An actual differentiable
forward evaluator is locally feasible for the actual joint node operators.
The actual joint objective and residual Lagrangian are differentiated; exact
reverse recursion removes every evaluator-tangent term; each resulting task
derivative coordinate is the sum over all active tied parameter occurrences. -/
theorem arbitraryDAG_KKT_parameterAggregate_eq_composedTaskDerivative
    (graph : RankedOccurrenceDAG ParentOccurrence)
    (activeParameter : ∀ {parameter owner},
      ParameterOccurrence parameter owner → Bool)
    (objective : JointStateParameter NodeSpace ParameterSpace → ℝ)
    (forward : ∀ node,
      JointStateParameter NodeSpace ParameterSpace → NodeSpace node)
    (evaluate : GlobalParameter ParameterSpace → GlobalState NodeSpace)
    (parameterPoint : GlobalParameter ParameterSpace)
    (credit : ∀ node, NodeCovector NodeSpace node)
    (objectiveDerivative :
      JointStateParameter NodeSpace ParameterSpace →L[ℝ] ℝ)
    (forwardDerivative : ∀ node,
      JointStateParameter NodeSpace ParameterSpace →L[ℝ] NodeSpace node)
    (evaluateDerivative :
      GlobalParameter ParameterSpace →L[ℝ] GlobalState NodeSpace)
    (parentDerivative : ∀ {source target},
      ParentOccurrence source target →
        NodeSpace source →L[ℝ] NodeSpace target)
    (parameterDerivative : ∀ {parameter owner},
      ParameterOccurrence parameter owner →
        ParameterSpace parameter →L[ℝ] NodeSpace owner)
    (hObjective : HasRealFDerivAt objective objectiveDerivative
      (jointPath evaluate parameterPoint))
    (hForward : ∀ node, HasRealFDerivAt (forward node)
      (forwardDerivative node) (jointPath evaluate parameterPoint))
    (hEvaluate : HasRealFDerivAt evaluate evaluateDerivative parameterPoint)
    (forwardStateOccurrence : ∀ node,
      forwardDerivative node ∘L
          ContinuousLinearMap.inl ℝ (GlobalState NodeSpace)
            (GlobalParameter ParameterSpace) =
        occurrenceForwardDerivative NodeSpace ParentOccurrence graph
          parentDerivative node)
    (forwardParameterOccurrence : ∀ owner,
      forwardDerivative owner ∘L
          ContinuousLinearMap.inr ℝ (GlobalState NodeSpace)
            (GlobalParameter ParameterSpace) =
        occurrenceParameterDerivative NodeSpace ParameterSpace
          ParameterOccurrence activeParameter parameterDerivative owner)
    (recurrence : ∀ source,
      credit source = RankedOccurrenceDAG.reverseAggregate
        (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
        graph
        (objectiveCoordinate NodeSpace
          (objectiveDerivative ∘L
            ContinuousLinearMap.inl ℝ (GlobalState NodeSpace)
              (GlobalParameter ParameterSpace)))
        parentDerivative credit source)
    (feasible : ∀ᶠ current in nhds parameterPoint,
      ∀ node, evaluate current node =
        forward node (jointPath evaluate current)) :
    HasRealFDerivAt
        (fun current => objective (jointPath evaluate current))
        (objectiveDerivative ∘L jointPathDerivative evaluateDerivative)
        parameterPoint ∧
      ∀ parameter,
        (objectiveDerivative ∘L jointPathDerivative evaluateDerivative) ∘L
            ContinuousLinearMap.single ℝ ParameterSpace parameter =
          tiedParameterAggregate
            (NodeSpace := NodeSpace)
            (ParameterOccurrence := ParameterOccurrence)
            (ParameterSpace := ParameterSpace)
            activeParameter
            (parameterObjectiveCoordinate ParameterSpace
              (objectiveDerivative ∘L
                ContinuousLinearMap.inr ℝ (GlobalState NodeSpace)
                  (GlobalParameter ParameterSpace)))
            parameterDerivative credit parameter := by
  let lagrangian := jointResidualLagrangian NodeSpace ParameterSpace
    objective forward credit
  let lagrangianDerivative :=
    jointResidualLagrangianDerivative NodeSpace ParameterSpace
      objectiveDerivative forwardDerivative credit
  have hLagrangian : HasRealFDerivAt lagrangian lagrangianDerivative
      (jointPath evaluate parameterPoint) := by
    exact hasFDerivAt_jointResidualLagrangian NodeSpace ParameterSpace
      objective forward credit (jointPath evaluate parameterPoint)
      objectiveDerivative forwardDerivative hObjective hForward
  have stateStationary : lagrangianDerivative ∘L
      ContinuousLinearMap.inl ℝ (GlobalState NodeSpace)
        (GlobalParameter ParameterSpace) = 0 := by
    exact reverseRecursion_implies_jointStateStationary NodeSpace
      ParameterSpace ParentOccurrence graph objectiveDerivative
      forwardDerivative parentDerivative credit forwardStateOccurrence recurrence
  have feasibleAgreement :
      (fun current => lagrangian (jointPath evaluate current)) =ᶠ[nhds parameterPoint]
      (fun current => objective (jointPath evaluate current)) := by
    filter_upwards [feasible] with current hCurrent
    simp only [lagrangian, jointResidualLagrangian, jointNodeResidual]
    have residualZero : ∀ node,
        (jointPath evaluate current).1 node -
          forward node (jointPath evaluate current) = 0 := by
      intro node
      change evaluate current node -
        forward node (jointPath evaluate current) = 0
      rw [hCurrent node]
      exact sub_self _
    simp [residualZero]
  have envelope := feasible_envelope_parameterPartial_eq_taskDerivative
    objective lagrangian evaluate (jointPath evaluate parameterPoint)
    parameterPoint objectiveDerivative lagrangianDerivative
    evaluateDerivative rfl hObjective hLagrangian hEvaluate
    stateStationary feasibleAgreement
  refine ⟨envelope.1, ?_⟩
  intro parameter
  rw [← envelope.2, ContinuousLinearMap.comp_assoc]
  exact jointParameterCoordinate_eq_tiedParameterAggregate NodeSpace
    ParameterSpace ParameterOccurrence activeParameter objectiveDerivative
    forwardDerivative parameterDerivative credit forwardParameterOccurrence parameter

#print axioms hasFDerivAt_jointPath
#print axioms stationary_jointPathDerivative_eq_parameterPartial
#print axioms feasible_envelope_parameterPartial_eq_taskDerivative
#print axioms hasFDerivAt_jointResidualLagrangian
#print axioms jointResidualLagrangianDerivative_comp_inl
#print axioms jointResidualLagrangianDerivative_comp_inr
#print axioms piCovector_eq_zero_of_comp_single_eq_zero
#print axioms reverseRecursion_implies_jointStateStationary
#print axioms jointParameterCoordinate_eq_tiedParameterAggregate
#print axioms arbitraryDAG_KKT_parameterAggregate_eq_composedTaskDerivative

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT
