import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.OccurrenceAdjoint

/-!
# Occurrence reindexing and fixed-mask restriction

Occurrence names are representation choices; occurrence multiplicity is not.
This module proves invariance under typed bijections preserving activity and
local derivatives, then partitions reverse credit into active and inactive
pullbacks.  A concrete masked fixture shows why including a removed branch
changes the derivative.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT

universe uNode uOccurrence₁ uOccurrence₂ uState uParameter
  uParameterOccurrence₁ uParameterOccurrence₂ uParameterSpace

variable {Node : Type uNode} [Fintype Node]
variable (ParentOccurrence₁ : Node → Node → Type uOccurrence₁)
variable (ParentOccurrence₂ : Node → Node → Type uOccurrence₂)
variable [∀ source target, Fintype (ParentOccurrence₁ source target)]
variable [∀ source target, Fintype (ParentOccurrence₂ source target)]
variable (NodeSpace : Node → Type uState)
variable [∀ node, NormedAddCommGroup (NodeSpace node)]
variable [∀ node, NormedSpace ℝ (NodeSpace node)]

/-- Parent aggregation is invariant under a typed occurrence bijection that
preserves the active mask and the actual local derivative attached to each
occurrence.  Endpoint sets alone are insufficient because the bijection is on
occurrences, not merely source-target pairs. -/
theorem parentAggregate_eq_of_occurrenceEquiv
    (graph₁ : RankedOccurrenceDAG ParentOccurrence₁)
    (graph₂ : RankedOccurrenceDAG ParentOccurrence₂)
    (parentDerivative₁ : ∀ {source target},
      ParentOccurrence₁ source target →
        NodeSpace source →L[ℝ] NodeSpace target)
    (parentDerivative₂ : ∀ {source target},
      ParentOccurrence₂ source target →
        NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node)
    (occurrenceEquiv : ∀ source target,
      ParentOccurrence₁ source target ≃ ParentOccurrence₂ source target)
    (activePreserved : ∀ {source target}
      (occurrence : ParentOccurrence₁ source target),
      graph₂.active (occurrenceEquiv source target occurrence) =
        graph₁.active occurrence)
    (derivativePreserved : ∀ {source target}
      (occurrence : ParentOccurrence₁ source target),
      parentDerivative₂ (occurrenceEquiv source target occurrence) =
        parentDerivative₁ occurrence)
    (source : Node) :
    RankedOccurrenceDAG.parentAggregate
        (ParentOccurrence := ParentOccurrence₁) (NodeSpace := NodeSpace)
        graph₁ parentDerivative₁ credit source =
      RankedOccurrenceDAG.parentAggregate
        (ParentOccurrence := ParentOccurrence₂) (NodeSpace := NodeSpace)
        graph₂ parentDerivative₂ credit source := by
  unfold RankedOccurrenceDAG.parentAggregate
  apply Finset.sum_congr rfl
  intro target _
  apply Fintype.sum_equiv (occurrenceEquiv source target)
  intro occurrence
  simp only [activePreserved occurrence, parentPullback,
    derivativePreserved occurrence]

/-- The full reverse equation inherits occurrence-reindexing invariance. -/
theorem reverseAggregate_eq_of_occurrenceEquiv
    (graph₁ : RankedOccurrenceDAG ParentOccurrence₁)
    (graph₂ : RankedOccurrenceDAG ParentOccurrence₂)
    (direct : ∀ node, NodeCovector NodeSpace node)
    (parentDerivative₁ : ∀ {source target},
      ParentOccurrence₁ source target →
        NodeSpace source →L[ℝ] NodeSpace target)
    (parentDerivative₂ : ∀ {source target},
      ParentOccurrence₂ source target →
        NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node)
    (occurrenceEquiv : ∀ source target,
      ParentOccurrence₁ source target ≃ ParentOccurrence₂ source target)
    (activePreserved : ∀ {source target}
      (occurrence : ParentOccurrence₁ source target),
      graph₂.active (occurrenceEquiv source target occurrence) =
        graph₁.active occurrence)
    (derivativePreserved : ∀ {source target}
      (occurrence : ParentOccurrence₁ source target),
      parentDerivative₂ (occurrenceEquiv source target occurrence) =
        parentDerivative₁ occurrence)
    (source : Node) :
    RankedOccurrenceDAG.reverseAggregate
        (ParentOccurrence := ParentOccurrence₁) (NodeSpace := NodeSpace)
        graph₁ direct parentDerivative₁ credit source =
      RankedOccurrenceDAG.reverseAggregate
        (ParentOccurrence := ParentOccurrence₂) (NodeSpace := NodeSpace)
        graph₂ direct parentDerivative₂ credit source := by
  unfold RankedOccurrenceDAG.reverseAggregate
  rw [parentAggregate_eq_of_occurrenceEquiv
    ParentOccurrence₁ ParentOccurrence₂ NodeSpace graph₁ graph₂
    parentDerivative₁ parentDerivative₂ credit occurrenceEquiv
    activePreserved derivativePreserved source]

/-! ## Tied parameter occurrence reindexing -/

variable {Parameter : Type uParameter}
variable (ParameterOccurrence₁ : Parameter → Node → Type uParameterOccurrence₁)
variable (ParameterOccurrence₂ : Parameter → Node → Type uParameterOccurrence₂)
variable [∀ parameter owner, Fintype (ParameterOccurrence₁ parameter owner)]
variable [∀ parameter owner, Fintype (ParameterOccurrence₂ parameter owner)]
variable (ParameterSpace : Parameter → Type uParameterSpace)
variable [∀ parameter, NormedAddCommGroup (ParameterSpace parameter)]
variable [∀ parameter, NormedSpace ℝ (ParameterSpace parameter)]

/-- Tied-parameter aggregation is invariant under a typed bijection preserving
the mask and parameter-to-owner derivative of every use occurrence. -/
theorem tiedParameterAggregate_eq_of_occurrenceEquiv
    (active₁ : ∀ {parameter owner},
      ParameterOccurrence₁ parameter owner → Bool)
    (active₂ : ∀ {parameter owner},
      ParameterOccurrence₂ parameter owner → Bool)
    (direct : ∀ parameter, ParameterCovector ParameterSpace parameter)
    (parameterDerivative₁ : ∀ {parameter owner},
      ParameterOccurrence₁ parameter owner →
        ParameterSpace parameter →L[ℝ] NodeSpace owner)
    (parameterDerivative₂ : ∀ {parameter owner},
      ParameterOccurrence₂ parameter owner →
        ParameterSpace parameter →L[ℝ] NodeSpace owner)
    (credit : ∀ node, NodeCovector NodeSpace node)
    (occurrenceEquiv : ∀ parameter owner,
      ParameterOccurrence₁ parameter owner ≃
        ParameterOccurrence₂ parameter owner)
    (activePreserved : ∀ {parameter owner}
      (occurrence : ParameterOccurrence₁ parameter owner),
      active₂ (occurrenceEquiv parameter owner occurrence) = active₁ occurrence)
    (derivativePreserved : ∀ {parameter owner}
      (occurrence : ParameterOccurrence₁ parameter owner),
      parameterDerivative₂ (occurrenceEquiv parameter owner occurrence) =
        parameterDerivative₁ occurrence)
    (parameter : Parameter) :
    tiedParameterAggregate
        (NodeSpace := NodeSpace)
        (ParameterOccurrence := ParameterOccurrence₁)
        (ParameterSpace := ParameterSpace)
        active₁ direct parameterDerivative₁ credit parameter =
      tiedParameterAggregate
        (NodeSpace := NodeSpace)
        (ParameterOccurrence := ParameterOccurrence₂)
        (ParameterSpace := ParameterSpace)
        active₂ direct parameterDerivative₂ credit parameter := by
  unfold tiedParameterAggregate
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro owner _
  apply Fintype.sum_equiv (occurrenceEquiv parameter owner)
  intro occurrence
  simp only [activePreserved occurrence, derivativePreserved occurrence]

/-! ## Exact fixed-mask partition -/

variable {ParentOccurrence : Node → Node → Type uOccurrence₁}
variable [∀ source target, Fintype (ParentOccurrence source target)]

/-- Sum of the pullbacks excluded by a fixed graph mask. -/
noncomputable def RankedOccurrenceDAG.inactiveParentAggregate
    (graph : RankedOccurrenceDAG ParentOccurrence)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node) (source : Node) :
    NodeCovector NodeSpace source :=
  ∑ target : Node, ∑ occurrence : ParentOccurrence source target,
    if graph.active occurrence then 0
    else parentPullback ParentOccurrence NodeSpace
      parentDerivative credit occurrence

/-- Sum of all potential pullbacks before applying a fixed mask. -/
noncomputable def RankedOccurrenceDAG.allParentAggregate
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node) (source : Node) :
    NodeCovector NodeSpace source :=
  ∑ target : Node, ∑ occurrence : ParentOccurrence source target,
    parentPullback ParentOccurrence NodeSpace parentDerivative credit occurrence

/-- Active and inactive pullbacks partition the full occurrence sum exactly. -/
theorem RankedOccurrenceDAG.parentAggregate_add_inactive_eq_all
    (graph : RankedOccurrenceDAG ParentOccurrence)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node) (source : Node) :
    RankedOccurrenceDAG.parentAggregate
        (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
        graph
        parentDerivative credit source +
      RankedOccurrenceDAG.inactiveParentAggregate
        (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
        graph
        parentDerivative credit source =
      RankedOccurrenceDAG.allParentAggregate
        (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
        parentDerivative credit source := by
  unfold RankedOccurrenceDAG.parentAggregate
    RankedOccurrenceDAG.inactiveParentAggregate
    RankedOccurrenceDAG.allParentAggregate
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro target _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro occurrence _
  by_cases active : graph.active occurrence = true <;> simp [active]

/-- Removing all inactive occurrences subtracts exactly their pullback sum. -/
theorem RankedOccurrenceDAG.parentAggregate_eq_all_sub_inactive
    (graph : RankedOccurrenceDAG ParentOccurrence)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node) (source : Node) :
    RankedOccurrenceDAG.parentAggregate
        (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
        graph
        parentDerivative credit source =
      RankedOccurrenceDAG.allParentAggregate
          (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
          parentDerivative credit source -
        RankedOccurrenceDAG.inactiveParentAggregate
          (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
          graph
          parentDerivative credit source := by
  rw [← RankedOccurrenceDAG.parentAggregate_add_inactive_eq_all
    (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
    graph parentDerivative credit source]
  abel

/-! ## Executable mask boundary -/

/-- The same two-slot graph with only the first parallel occurrence active. -/
noncomputable def twoSlotFirstOnlyGraph : RankedOccurrenceDAG twoSlotOccurrence where
  rank := fun node => node.val
  active := fun {source target} occurrence =>
    decide (source = 0 ∧ target = 1 ∧ occurrence = 0)
  forward := by
    intro source target occurrence active
    rcases of_decide_eq_true active with ⟨rfl, rfl, rfl⟩
    norm_num

/-- Masking the second slot removes exactly its six-unit pullback. -/
theorem twoSlotFirstOnly_active_inactive_partition :
    RankedOccurrenceDAG.parentAggregate
        (ParentOccurrence := twoSlotOccurrence)
        (NodeSpace := fun _ : Fin 2 => ℝ)
        twoSlotFirstOnlyGraph twoSlotPartial twoSlotCredit 0 1 = 3 ∧
      RankedOccurrenceDAG.inactiveParentAggregate
        (ParentOccurrence := twoSlotOccurrence)
        (NodeSpace := fun _ : Fin 2 => ℝ)
        twoSlotFirstOnlyGraph twoSlotPartial twoSlotCredit 0 1 = 6 := by
  constructor <;>
    norm_num [RankedOccurrenceDAG.parentAggregate,
      RankedOccurrenceDAG.inactiveParentAggregate, twoSlotFirstOnlyGraph,
      twoSlotOccurrence, twoSlotPartial, twoSlotCredit, parentPullback]

/-- Including the masked occurrence changes reverse credit from three to nine;
the fixed mask is part of the differentiated problem. -/
theorem including_masked_slot_changes_parentAggregate :
    RankedOccurrenceDAG.parentAggregate
        (ParentOccurrence := twoSlotOccurrence)
        (NodeSpace := fun _ : Fin 2 => ℝ)
        twoSlotFirstOnlyGraph twoSlotPartial twoSlotCredit 0 1 ≠
      RankedOccurrenceDAG.parentAggregate
        (ParentOccurrence := twoSlotOccurrence)
        (NodeSpace := fun _ : Fin 2 => ℝ)
        twoSlotGraph twoSlotPartial twoSlotCredit 0 1 := by
  norm_num [RankedOccurrenceDAG.parentAggregate, twoSlotFirstOnlyGraph,
    twoSlotGraph, twoSlotOccurrence, twoSlotPartial, twoSlotCredit,
    parentPullback]

#print axioms parentAggregate_eq_of_occurrenceEquiv
#print axioms reverseAggregate_eq_of_occurrenceEquiv
#print axioms tiedParameterAggregate_eq_of_occurrenceEquiv
#print axioms RankedOccurrenceDAG.parentAggregate_add_inactive_eq_all
#print axioms RankedOccurrenceDAG.parentAggregate_eq_all_sub_inactive
#print axioms twoSlotFirstOnly_active_inactive_partition
#print axioms including_masked_slot_changes_parentAggregate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT
