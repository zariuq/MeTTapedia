import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.ResidualLagrangian

/-!
# Tied-parameter derivatives of a residual Lagrangian

Slow parameters are differentiated while the node state and reverse covectors
are fixed.  Parameter uses are occurrences, so reuse by several nodes or by
several slots of one node contributes once per active occurrence.  The main
result differentiates the actual parameterized residual Lagrangian and
identifies each shared-parameter coordinate with `tiedParameterAggregate`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT

universe uNode uState uParameter uParameterSpace uParameterOccurrence

variable {Node : Type uNode} [Fintype Node]
variable (NodeSpace : Node → Type uState)
variable [∀ node, NormedAddCommGroup (NodeSpace node)]
variable [∀ node, NormedSpace ℝ (NodeSpace node)]

variable {Parameter : Type uParameter} [Fintype Parameter] [DecidableEq Parameter]
variable (ParameterSpace : Parameter → Type uParameterSpace)
variable [∀ parameter, NormedAddCommGroup (ParameterSpace parameter)]
variable [∀ parameter, NormedSpace ℝ (ParameterSpace parameter)]

/-- Heterogeneous product of all tied slow parameters. -/
abbrev GlobalParameter := ∀ parameter, ParameterSpace parameter

/-- A node residual viewed as a function of the slow parameters, with the
node-state family held fixed. -/
def parameterizedNodeResidual
    (state : ∀ node, NodeSpace node)
    (forward : ∀ node, GlobalParameter ParameterSpace → NodeSpace node)
    (node : Node) (parameter : GlobalParameter ParameterSpace) : NodeSpace node :=
  state node - forward node parameter

/-- The actual residual Lagrangian as a function of shared slow parameters. -/
noncomputable def parameterResidualLagrangian
    (objective : GlobalParameter ParameterSpace → ℝ)
    (state : ∀ node, NodeSpace node)
    (forward : ∀ node, GlobalParameter ParameterSpace → NodeSpace node)
    (credit : ∀ node, NodeCovector NodeSpace node)
    (parameter : GlobalParameter ParameterSpace) : ℝ :=
  objective parameter -
    ∑ node, credit node
      (parameterizedNodeResidual NodeSpace ParameterSpace state forward node parameter)

/-- Simplified parameter derivative: the direct objective covector plus every
node-credit pullback through that node's full parameter Jacobian. -/
noncomputable def parameterResidualLagrangianDerivative
    (objectiveDerivative : GlobalParameter ParameterSpace →L[ℝ] ℝ)
    (forwardDerivative : ∀ node,
      GlobalParameter ParameterSpace →L[ℝ] NodeSpace node)
    (credit : ∀ node, NodeCovector NodeSpace node) :
    GlobalParameter ParameterSpace →L[ℝ] ℝ :=
  objectiveDerivative + ∑ node, credit node ∘L forwardDerivative node

omit [DecidableEq Parameter] in
/-- Exact derivative of the actual parameterized residual Lagrangian.  The
plus sign in the pullback term follows from subtracting residuals oriented as
`state - forward`. -/
theorem hasFDerivAt_parameterResidualLagrangian
    (objective : GlobalParameter ParameterSpace → ℝ)
    (state : ∀ node, NodeSpace node)
    (forward : ∀ node, GlobalParameter ParameterSpace → NodeSpace node)
    (credit : ∀ node, NodeCovector NodeSpace node)
    (parameter : GlobalParameter ParameterSpace)
    (objectiveDerivative : GlobalParameter ParameterSpace →L[ℝ] ℝ)
    (forwardDerivative : ∀ node,
      GlobalParameter ParameterSpace →L[ℝ] NodeSpace node)
    (hObjective : HasRealFDerivAt objective objectiveDerivative parameter)
    (hForward : ∀ node,
      HasRealFDerivAt (forward node) (forwardDerivative node) parameter) :
    HasRealFDerivAt
      (fun current => parameterResidualLagrangian NodeSpace ParameterSpace
        objective state forward credit current)
      (parameterResidualLagrangianDerivative NodeSpace ParameterSpace
        objectiveDerivative forwardDerivative credit)
      parameter := by
  have hResidualTerm : ∀ node,
      HasRealFDerivAt
        ((credit node) ∘
          (fun current => state node - forward node current))
        (-(credit node ∘L forwardDerivative node)) parameter := by
    intro node
    have h := (credit node).hasFDerivAt.comp parameter
      ((hForward node).const_sub (state node))
    have derivativeEq :
        credit node ∘L (-forwardDerivative node) =
          -(credit node ∘L forwardDerivative node) := by
      ext direction
      simp
    rw [derivativeEq] at h
    exact h
  have hSum : HasRealFDerivAt
      (∑ node, (credit node) ∘
        (fun current => state node - forward node current))
      (∑ node, -(credit node ∘L forwardDerivative node)) parameter := by
    exact HasFDerivAt.sum fun node _ => hResidualTerm node
  have hCore := hObjective.sub hSum
  have hDerivative :
      objectiveDerivative -
          ∑ node, -(credit node ∘L forwardDerivative node) =
        parameterResidualLagrangianDerivative NodeSpace ParameterSpace
          objectiveDerivative forwardDerivative credit := by
    rw [parameterResidualLagrangianDerivative, Finset.sum_neg_distrib]
    abel
  rw [hDerivative] at hCore
  convert hCore using 1
  funext current
  simp only [parameterResidualLagrangian, parameterizedNodeResidual,
    Pi.sub_apply, Finset.sum_apply, Function.comp_apply]

/-! ## Parameter-occurrence decomposition -/

variable (ParameterOccurrence : Parameter → Node → Type uParameterOccurrence)
variable [∀ parameter owner, Fintype (ParameterOccurrence parameter owner)]

/-- Assemble each node's global parameter Jacobian from all active tied-use
occurrences. -/
noncomputable def occurrenceParameterDerivative
    (active : ∀ {parameter owner},
      ParameterOccurrence parameter owner → Bool)
    (parameterDerivative : ∀ {parameter owner},
      ParameterOccurrence parameter owner →
        ParameterSpace parameter →L[ℝ] NodeSpace owner)
    (owner : Node) :
    GlobalParameter ParameterSpace →L[ℝ] NodeSpace owner :=
  ∑ parameter : Parameter,
    ∑ occurrence : ParameterOccurrence parameter owner,
      if active occurrence then
        parameterDerivative occurrence ∘L ContinuousLinearMap.proj parameter
      else 0

/-- Restrict a global parameter-objective derivative to one shared parameter
coordinate. -/
noncomputable def parameterObjectiveCoordinate
    (objectiveDerivative : GlobalParameter ParameterSpace →L[ℝ] ℝ)
    (parameter : Parameter) : ParameterCovector ParameterSpace parameter :=
  objectiveDerivative ∘L
    ContinuousLinearMap.single ℝ ParameterSpace parameter

omit [Fintype Node] in
/-- Restricting an occurrence-assembled node Jacobian to one shared parameter
coordinate recovers precisely all active uses of that parameter at the node. -/
theorem occurrenceParameterDerivative_comp_single
    (active : ∀ {parameter owner},
      ParameterOccurrence parameter owner → Bool)
    (parameterDerivative : ∀ {parameter owner},
      ParameterOccurrence parameter owner →
        ParameterSpace parameter →L[ℝ] NodeSpace owner)
    (parameter : Parameter) (owner : Node) :
    occurrenceParameterDerivative NodeSpace ParameterSpace ParameterOccurrence
        active parameterDerivative owner ∘L
      ContinuousLinearMap.single ℝ ParameterSpace parameter =
    (∑ occurrence : ParameterOccurrence parameter owner,
      if active occurrence then parameterDerivative occurrence else 0 :
        ParameterSpace parameter →L[ℝ] NodeSpace owner) := by
  ext direction
  simp only [occurrenceParameterDerivative, sum_apply,
    ContinuousLinearMap.comp_apply]
  rw [Finset.sum_eq_single parameter]
  · apply Finset.sum_congr rfl
    intro occurrence _
    by_cases enabled : active occurrence = true
    · simp [enabled, ContinuousLinearMap.single_apply]
    · simp [enabled]
  · intro other _ hne
    apply Finset.sum_eq_zero
    intro occurrence _
    by_cases enabled : active occurrence = true
    · simp [enabled, ContinuousLinearMap.single_apply, hne]
    · simp [enabled]
  · simp

/-- Every shared-parameter coordinate of the residual-Lagrangian derivative
is exactly the direct parameter covector plus all active tied-occurrence
pullbacks. -/
theorem parameterResidualLagrangianCoordinate_eq_tiedParameterAggregate
    (active : ∀ {parameter owner},
      ParameterOccurrence parameter owner → Bool)
    (objectiveDerivative : GlobalParameter ParameterSpace →L[ℝ] ℝ)
    (parameterDerivative : ∀ {parameter owner},
      ParameterOccurrence parameter owner →
        ParameterSpace parameter →L[ℝ] NodeSpace owner)
    (credit : ∀ node, NodeCovector NodeSpace node)
    (parameter : Parameter) :
    parameterResidualLagrangianDerivative NodeSpace ParameterSpace
        objectiveDerivative
        (occurrenceParameterDerivative NodeSpace ParameterSpace
          ParameterOccurrence active parameterDerivative) credit ∘L
      ContinuousLinearMap.single ℝ ParameterSpace parameter =
    tiedParameterAggregate
      (NodeSpace := NodeSpace)
      (ParameterOccurrence := ParameterOccurrence)
      (ParameterSpace := ParameterSpace)
      active
      (parameterObjectiveCoordinate ParameterSpace objectiveDerivative)
      parameterDerivative credit parameter := by
  ext direction
  have transportedSum :
      (∑ owner, credit owner
        ((occurrenceParameterDerivative NodeSpace ParameterSpace
          ParameterOccurrence active parameterDerivative owner)
          (Pi.single parameter direction))) =
      ∑ owner, ∑ occurrence : ParameterOccurrence parameter owner,
        (if active occurrence then
          credit owner ∘L parameterDerivative occurrence else 0) direction := by
    apply Finset.sum_congr rfl
    intro owner _
    have restricted := congrArg
      (fun derivative : ParameterSpace parameter →L[ℝ] NodeSpace owner =>
        credit owner (derivative direction))
      (occurrenceParameterDerivative_comp_single NodeSpace ParameterSpace
        ParameterOccurrence active parameterDerivative parameter owner)
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.single_apply] at restricted
    rw [restricted, sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro occurrence _
    by_cases enabled : active occurrence = true
    · simp [enabled, ContinuousLinearMap.comp_apply]
    · simp [enabled]
  simp [parameterResidualLagrangianDerivative,
    parameterObjectiveCoordinate, tiedParameterAggregate,
    ContinuousLinearMap.single_apply]
  exact transportedSum

/-- Combined tied-parameter theorem: actual derivative certificates establish
the parameter residual-Lagrangian derivative, and every coordinate of that
derivative is the exact occurrence sum. -/
theorem hasFDerivAt_parameterResidualLagrangian_and_coordinate_eq_tiedAggregate
    (active : ∀ {parameter owner},
      ParameterOccurrence parameter owner → Bool)
    (objective : GlobalParameter ParameterSpace → ℝ)
    (state : ∀ node, NodeSpace node)
    (forward : ∀ node, GlobalParameter ParameterSpace → NodeSpace node)
    (credit : ∀ node, NodeCovector NodeSpace node)
    (parameterPoint : GlobalParameter ParameterSpace)
    (objectiveDerivative : GlobalParameter ParameterSpace →L[ℝ] ℝ)
    (parameterDerivative : ∀ {parameter owner},
      ParameterOccurrence parameter owner →
        ParameterSpace parameter →L[ℝ] NodeSpace owner)
    (hObjective : HasRealFDerivAt objective objectiveDerivative parameterPoint)
    (hForward : ∀ owner, HasRealFDerivAt (forward owner)
      (occurrenceParameterDerivative NodeSpace ParameterSpace
        ParameterOccurrence active parameterDerivative owner) parameterPoint) :
    HasRealFDerivAt
        (fun current => parameterResidualLagrangian NodeSpace ParameterSpace
          objective state forward credit current)
        (parameterResidualLagrangianDerivative NodeSpace ParameterSpace
          objectiveDerivative
          (occurrenceParameterDerivative NodeSpace ParameterSpace
            ParameterOccurrence active parameterDerivative) credit)
        parameterPoint ∧
      ∀ parameter,
        parameterResidualLagrangianDerivative NodeSpace ParameterSpace
            objectiveDerivative
            (occurrenceParameterDerivative NodeSpace ParameterSpace
              ParameterOccurrence active parameterDerivative) credit ∘L
          ContinuousLinearMap.single ℝ ParameterSpace parameter =
        tiedParameterAggregate
          (NodeSpace := NodeSpace)
          (ParameterOccurrence := ParameterOccurrence)
          (ParameterSpace := ParameterSpace)
          active
          (parameterObjectiveCoordinate ParameterSpace objectiveDerivative)
          parameterDerivative credit parameter := by
  exact ⟨hasFDerivAt_parameterResidualLagrangian NodeSpace ParameterSpace
      objective state forward credit parameterPoint objectiveDerivative
      (occurrenceParameterDerivative NodeSpace ParameterSpace
        ParameterOccurrence active parameterDerivative) hObjective hForward,
    parameterResidualLagrangianCoordinate_eq_tiedParameterAggregate
      NodeSpace ParameterSpace ParameterOccurrence active objectiveDerivative
      parameterDerivative credit⟩

#print axioms hasFDerivAt_parameterResidualLagrangian
#print axioms occurrenceParameterDerivative_comp_single
#print axioms parameterResidualLagrangianCoordinate_eq_tiedParameterAggregate
#print axioms hasFDerivAt_parameterResidualLagrangian_and_coordinate_eq_tiedAggregate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT
