import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.ForwardComposition
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Hilbert-gradient presentation of occurrence-aware covectors

The KKT foundation is metric-free.  This module adds real Hilbert-space
structure only to derive the familiar adjoint-Jacobian gradient formulas by
Fréchet--Riesz representation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT

open scoped InnerProduct

universe uNode uOccurrence uState uParameter uParameterOccurrence
  uParameterSpace

variable {Node : Type uNode} [Fintype Node]
variable (ParentOccurrence : Node → Node → Type uOccurrence)
variable [∀ source target, Fintype (ParentOccurrence source target)]
variable (NodeSpace : Node → Type uState)
variable [∀ node, NormedAddCommGroup (NodeSpace node)]
variable [∀ node, InnerProductSpace ℝ (NodeSpace node)]
variable [∀ node, CompleteSpace (NodeSpace node)]

/-- Riesz representative of a node covector. -/
noncomputable def covectorGradient {node : Node}
    (credit : NodeCovector NodeSpace node) : NodeSpace node :=
  (InnerProductSpace.toDual ℝ (NodeSpace node)).symm credit

omit [Fintype Node] in
@[simp] theorem covectorGradient_add {node : Node}
    (first second : NodeCovector NodeSpace node) :
    covectorGradient NodeSpace (first + second) =
      covectorGradient NodeSpace first + covectorGradient NodeSpace second := by
  simp [covectorGradient]

omit [Fintype Node] in
@[simp] theorem covectorGradient_zero {node : Node} :
    covectorGradient NodeSpace (0 : NodeCovector NodeSpace node) = 0 := by
  simp [covectorGradient]

omit [Fintype Node] in
theorem covectorGradient_sum {node : Node} {Index : Type*}
    (items : Finset Index) (credit : Index → NodeCovector NodeSpace node) :
    covectorGradient NodeSpace (∑ item ∈ items, credit item) =
      ∑ item ∈ items, covectorGradient NodeSpace (credit item) := by
  simp [covectorGradient]

omit [Fintype Node] in
/-- Riesz representation turns covector composition into the usual adjoint
Jacobian action. -/
theorem covectorGradient_comp
    {source target : Node}
    (derivative : NodeSpace source →L[ℝ] NodeSpace target)
    (credit : NodeCovector NodeSpace target) :
    covectorGradient NodeSpace (credit ∘L derivative) =
      ContinuousLinearMap.adjoint derivative
        (covectorGradient NodeSpace credit) := by
  apply (InnerProductSpace.toDual ℝ (NodeSpace source)).injective
  ext direction
  calc
    (InnerProductSpace.toDual ℝ (NodeSpace source)
        (covectorGradient NodeSpace (credit ∘L derivative))) direction =
        (credit ∘L derivative) direction :=
      InnerProductSpace.toDual_symm_apply
    _ = credit (derivative direction) := rfl
    _ = @inner ℝ (NodeSpace target) _
          (covectorGradient NodeSpace credit) (derivative direction) :=
      (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)).symm
    _ = @inner ℝ (NodeSpace source) _
          (ContinuousLinearMap.adjoint derivative
            (covectorGradient NodeSpace credit)) direction :=
      (ContinuousLinearMap.adjoint_inner_left derivative direction
        (covectorGradient NodeSpace credit)).symm
    _ = (InnerProductSpace.toDual ℝ (NodeSpace source)
          (ContinuousLinearMap.adjoint derivative
            (covectorGradient NodeSpace credit))) direction := rfl

/-- The reverse covector equation becomes the standard sum of direct
gradients and adjoint-Jacobian child gradients. -/
theorem covectorGradient_reverseAggregate
    (graph : RankedOccurrenceDAG ParentOccurrence)
    (direct : ∀ node, NodeCovector NodeSpace node)
    (parentDerivative : ∀ {source target},
      ParentOccurrence source target →
        NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node)
    (source : Node) :
    covectorGradient NodeSpace
        (RankedOccurrenceDAG.reverseAggregate
          (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
          graph direct parentDerivative credit source) =
      covectorGradient NodeSpace (direct source) +
        ∑ target : Node, ∑ occurrence : ParentOccurrence source target,
          if graph.active occurrence then
            ContinuousLinearMap.adjoint (parentDerivative occurrence)
              (covectorGradient NodeSpace (credit target))
          else 0 := by
  simp only [RankedOccurrenceDAG.reverseAggregate,
    RankedOccurrenceDAG.parentAggregate, parentPullback,
    covectorGradient_add]
  rw [covectorGradient_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro target _
  rw [covectorGradient_sum]
  apply Finset.sum_congr rfl
  intro occurrence _
  by_cases active : graph.active occurrence = true
  · simp only [active, if_true]
    exact covectorGradient_comp NodeSpace (parentDerivative occurrence)
      (credit target)
  · simp [active, covectorGradient_zero]

/-! ## Tied-parameter gradient corollary -/

variable {Parameter : Type uParameter} [Fintype Parameter]
variable (ParameterOccurrence : Parameter → Node → Type uParameterOccurrence)
variable [∀ parameter owner, Fintype (ParameterOccurrence parameter owner)]
variable (ParameterSpace : Parameter → Type uParameterSpace)
variable [∀ parameter, NormedAddCommGroup (ParameterSpace parameter)]
variable [∀ parameter, InnerProductSpace ℝ (ParameterSpace parameter)]
variable [∀ parameter, CompleteSpace (ParameterSpace parameter)]

/-- Riesz representative of a shared-parameter covector. -/
noncomputable def parameterCovectorGradient {parameter : Parameter}
    (credit : ParameterCovector ParameterSpace parameter) :
    ParameterSpace parameter :=
  (InnerProductSpace.toDual ℝ (ParameterSpace parameter)).symm credit

omit [Fintype Parameter] in
@[simp] theorem parameterCovectorGradient_add {parameter : Parameter}
    (first second : ParameterCovector ParameterSpace parameter) :
    parameterCovectorGradient ParameterSpace (first + second) =
      parameterCovectorGradient ParameterSpace first +
        parameterCovectorGradient ParameterSpace second := by
  simp [parameterCovectorGradient]

omit [Fintype Parameter] in
@[simp] theorem parameterCovectorGradient_zero {parameter : Parameter} :
    parameterCovectorGradient ParameterSpace
      (0 : ParameterCovector ParameterSpace parameter) = 0 := by
  simp [parameterCovectorGradient]

omit [Fintype Parameter] in
theorem parameterCovectorGradient_sum {parameter : Parameter} {Index : Type*}
    (items : Finset Index)
    (credit : Index → ParameterCovector ParameterSpace parameter) :
    parameterCovectorGradient ParameterSpace (∑ item ∈ items, credit item) =
      ∑ item ∈ items,
        parameterCovectorGradient ParameterSpace (credit item) := by
  simp [parameterCovectorGradient]

omit [Fintype Node] [Fintype Parameter] in
/-- A node covector pulled back through a shared-parameter occurrence is
represented by the adjoint parameter Jacobian applied to the node gradient. -/
theorem parameterCovectorGradient_comp
    {parameter : Parameter} {node : Node}
    (derivative : ParameterSpace parameter →L[ℝ] NodeSpace node)
    (credit : NodeCovector NodeSpace node) :
    parameterCovectorGradient ParameterSpace (credit ∘L derivative) =
      ContinuousLinearMap.adjoint derivative
        (covectorGradient NodeSpace credit) := by
  apply (InnerProductSpace.toDual ℝ (ParameterSpace parameter)).injective
  ext direction
  calc
    (InnerProductSpace.toDual ℝ (ParameterSpace parameter)
        (parameterCovectorGradient ParameterSpace
          (credit ∘L derivative))) direction =
        (credit ∘L derivative) direction :=
      InnerProductSpace.toDual_symm_apply
    _ = credit (derivative direction) := rfl
    _ = @inner ℝ (NodeSpace node) _
          (covectorGradient NodeSpace credit) (derivative direction) :=
      (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)).symm
    _ = @inner ℝ (ParameterSpace parameter) _
          (ContinuousLinearMap.adjoint derivative
            (covectorGradient NodeSpace credit)) direction :=
      (ContinuousLinearMap.adjoint_inner_left derivative direction
        (covectorGradient NodeSpace credit)).symm
    _ = (InnerProductSpace.toDual ℝ (ParameterSpace parameter)
          (ContinuousLinearMap.adjoint derivative
            (covectorGradient NodeSpace credit))) direction := rfl

omit [Fintype Parameter] in
/-- Tied parameter occurrence aggregation becomes the sum of the corresponding
adjoint-Jacobian node gradients. -/
theorem parameterCovectorGradient_tiedAggregate
    (active : ∀ {parameter owner},
      ParameterOccurrence parameter owner → Bool)
    (direct : ∀ parameter, ParameterCovector ParameterSpace parameter)
    (parameterDerivative : ∀ {parameter owner},
      ParameterOccurrence parameter owner →
        ParameterSpace parameter →L[ℝ] NodeSpace owner)
    (credit : ∀ node, NodeCovector NodeSpace node)
    (parameter : Parameter) :
    parameterCovectorGradient ParameterSpace
        (tiedParameterAggregate
          (NodeSpace := NodeSpace)
          (ParameterOccurrence := ParameterOccurrence)
          (ParameterSpace := ParameterSpace)
          active direct parameterDerivative credit parameter) =
      parameterCovectorGradient ParameterSpace (direct parameter) +
        ∑ owner : Node,
          ∑ occurrence : ParameterOccurrence parameter owner,
            if active occurrence then
              ContinuousLinearMap.adjoint (parameterDerivative occurrence)
                (covectorGradient NodeSpace (credit owner))
            else 0 := by
  simp only [tiedParameterAggregate, parameterCovectorGradient_add]
  rw [parameterCovectorGradient_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro owner _
  rw [parameterCovectorGradient_sum]
  apply Finset.sum_congr rfl
  intro occurrence _
  by_cases enabled : active occurrence = true
  · simp only [enabled, if_true]
    exact parameterCovectorGradient_comp NodeSpace ParameterSpace
      (parameterDerivative occurrence)
      (credit owner)
  · simp [enabled, parameterCovectorGradient_zero]

#print axioms covectorGradient_comp
#print axioms covectorGradient_reverseAggregate
#print axioms parameterCovectorGradient_comp
#print axioms parameterCovectorGradient_tiedAggregate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT
