import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.OccurrenceAdjoint

/-!
# Gradient routing on occurrence-aware computation DAGs

Cloud et al., *Gradient Routing: Masking Gradients to Localize Computation in
Neural Networks* (2024), Section 3 and Algorithm 1, multiply each reverse-mode
edge occurrence by an example-dependent scalar while leaving the forward
activation unchanged.  This file isolates that mathematical operation on the
occurrence-aware reverse-covector calculus.

The result is a weighted reverse recursion on finite ranked DAGs.  It has a
unique solution, recovers ordinary reverse mode when every route is one, and
reduces to direct objective credit when every route is zero.  Routes in
`[0, 1]` cannot enlarge an individual pullback; a negative fixture records why
that hypothesis matters.

The theorems concern the routed derivative recurrence itself.  They do not
claim that a learned route localizes representations, improves an optimizer,
or reproduces the empirical absorption measurements in the source paper.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT

universe uNode uOccurrence uState

variable {Node : Type uNode} [Fintype Node]
variable (ParentOccurrence : Node → Node → Type uOccurrence)
variable [parentOccurrenceFintype :
  ∀ source target, Fintype (ParentOccurrence source target)]
variable (NodeSpace : Node → Type uState)
variable [nodeNormedAddCommGroup :
  ∀ node, NormedAddCommGroup (NodeSpace node)]
variable [nodeNormedSpace : ∀ node, NormedSpace ℝ (NodeSpace node)]

/-- A scalar route is attached to each individual parent occurrence.  Keeping
occurrences explicit permits parallel uses of the same source and target to
receive different routes. -/
abbrev OccurrenceRoute :=
  ∀ {source target}, ParentOccurrence source target → ℝ

/-- Ordinary reverse mode is the route assigning one to every occurrence. -/
def unitRoute : OccurrenceRoute ParentOccurrence :=
  fun {_source _target} _occurrence => 1

/-- The zero route blocks every propagated child contribution. -/
def zeroRoute : OccurrenceRoute ParentOccurrence :=
  fun {_source _target} _occurrence => 0

namespace RankedOccurrenceDAG

variable (graph : RankedOccurrenceDAG ParentOccurrence)

/-- Sum every active target-to-source pullback after multiplying it by its
occurrence route.  This is the source paper's routed reverse aggregation,
generalized from scalar node derivatives to heterogeneous node covectors. -/
noncomputable def routedParentAggregate
    (route : OccurrenceRoute ParentOccurrence)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node) (source : Node) :
    NodeCovector NodeSpace source :=
  ∑ target : Node, ∑ occurrence : ParentOccurrence source target,
    if graph.active occurrence then
      route occurrence •
        parentPullback ParentOccurrence NodeSpace parentDerivative credit occurrence
    else 0

/-- Direct objective credit plus every routed active pullback. -/
noncomputable def routedReverseAggregate
    (route : OccurrenceRoute ParentOccurrence)
    (direct : ∀ node, NodeCovector NodeSpace node)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node) (source : Node) :
    NodeCovector NodeSpace source :=
  direct source + routedParentAggregate
    (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
    graph route parentDerivative credit source

/-- Canonical routed reverse covectors, constructed from later nodes to
earlier nodes along the same well-founded rank used by ordinary reverse mode. -/
noncomputable def routedReverseSolution
    (route : OccurrenceRoute ParentOccurrence)
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
          route occurrence •
            (recurse target (reverseHeight_lt_of_active
                (ParentOccurrence := ParentOccurrence) graph occurrence active) ∘L
              parentDerivative occurrence)
        else 0

/-- The well-founded construction satisfies the weighted reverse recurrence. -/
theorem routedReverseSolution_eq_routedReverseAggregate
    (route : OccurrenceRoute ParentOccurrence)
    (direct : ∀ node, NodeCovector NodeSpace node)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (source : Node) :
    routedReverseSolution (ParentOccurrence := ParentOccurrence)
        (NodeSpace := NodeSpace) graph route direct parentDerivative source =
      routedReverseAggregate (ParentOccurrence := ParentOccurrence)
        (NodeSpace := NodeSpace) graph route direct parentDerivative
        (routedReverseSolution (ParentOccurrence := ParentOccurrence)
          (NodeSpace := NodeSpace) graph route direct parentDerivative) source := by
  rw [routedReverseSolution, WellFounded.fix_eq]
  rfl

/-- A finite strictly ranked occurrence DAG has exactly one routed reverse
solution for every direct covector family and local derivative family. -/
theorem routedReverseSolution_existsUnique
    (route : OccurrenceRoute ParentOccurrence)
    (direct : ∀ node, NodeCovector NodeSpace node)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target) :
    ∃! credit : ∀ node, NodeCovector NodeSpace node,
      ∀ source, credit source =
        routedReverseAggregate (ParentOccurrence := ParentOccurrence)
          (NodeSpace := NodeSpace) graph route direct parentDerivative credit source := by
  refine ⟨routedReverseSolution (ParentOccurrence := ParentOccurrence)
      (NodeSpace := NodeSpace) graph route direct parentDerivative,
    routedReverseSolution_eq_routedReverseAggregate
      (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
      graph route direct parentDerivative, ?_⟩
  intro credit recurrence
  funext source
  induction source using
      (measure (reverseHeight
        (ParentOccurrence := ParentOccurrence) graph)).wf.induction with
  | h source inductionHypothesis =>
      rw [recurrence source,
        routedReverseSolution_eq_routedReverseAggregate
          (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
          graph route direct parentDerivative source,
        routedReverseAggregate]
      congr 1
      simp only [routedParentAggregate]
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

/-- Unit routing recovers the ordinary occurrence-aware parent aggregation
exactly, including parallel occurrence multiplicity. -/
theorem routedParentAggregate_unit
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node) (source : Node) :
    routedParentAggregate (ParentOccurrence := ParentOccurrence)
        (NodeSpace := NodeSpace) graph (unitRoute ParentOccurrence)
        parentDerivative credit source =
      parentAggregate (ParentOccurrence := ParentOccurrence)
        (NodeSpace := NodeSpace) graph parentDerivative credit source := by
  simp [routedParentAggregate, unitRoute, parentAggregate]

/-- Unit routing recovers the ordinary reverse aggregation. -/
theorem routedReverseAggregate_unit
    (direct : ∀ node, NodeCovector NodeSpace node)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node) (source : Node) :
    routedReverseAggregate (ParentOccurrence := ParentOccurrence)
        (NodeSpace := NodeSpace) graph (unitRoute ParentOccurrence)
        direct parentDerivative credit source =
      reverseAggregate (ParentOccurrence := ParentOccurrence)
        (NodeSpace := NodeSpace) graph direct parentDerivative credit source := by
  rw [routedReverseAggregate, reverseAggregate,
    routedParentAggregate_unit (ParentOccurrence := ParentOccurrence)
      (NodeSpace := NodeSpace)]

/-- The canonical unit-routed solution is ordinary reverse mode, not merely a
second definition with the same intended reading. -/
theorem routedReverseSolution_unit
    (direct : ∀ node, NodeCovector NodeSpace node)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target) :
    routedReverseSolution (ParentOccurrence := ParentOccurrence)
        (NodeSpace := NodeSpace) graph (unitRoute ParentOccurrence)
        direct parentDerivative =
      reverseSolution (ParentOccurrence := ParentOccurrence)
        (NodeSpace := NodeSpace) graph direct parentDerivative := by
  rcases reverseSolution_existsUnique (ParentOccurrence := ParentOccurrence)
      (NodeSpace := NodeSpace) graph direct parentDerivative with
    ⟨ordinary, ordinaryRecurrence, ordinaryUnique⟩
  have routedRecurrence :
      ∀ source,
        routedReverseSolution (ParentOccurrence := ParentOccurrence)
            (NodeSpace := NodeSpace) graph (unitRoute ParentOccurrence)
            direct parentDerivative source =
          reverseAggregate (ParentOccurrence := ParentOccurrence)
            (NodeSpace := NodeSpace) graph direct parentDerivative
            (routedReverseSolution (ParentOccurrence := ParentOccurrence)
              (NodeSpace := NodeSpace) graph (unitRoute ParentOccurrence)
              direct parentDerivative) source := by
    intro source
    rw [routedReverseSolution_eq_routedReverseAggregate,
      routedReverseAggregate_unit]
  have routedEqOrdinary := ordinaryUnique _ routedRecurrence
  have canonicalEqOrdinary := ordinaryUnique _
    (reverseSolution_eq_reverseAggregate
      (ParentOccurrence := ParentOccurrence) (NodeSpace := NodeSpace)
      graph direct parentDerivative)
  exact routedEqOrdinary.trans canonicalEqOrdinary.symm

/-- A zero route removes every propagated child contribution. -/
theorem routedParentAggregate_zero
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node) (source : Node) :
    routedParentAggregate (ParentOccurrence := ParentOccurrence)
        (NodeSpace := NodeSpace) graph (zeroRoute ParentOccurrence)
        parentDerivative credit source = 0 := by
  simp [routedParentAggregate, zeroRoute]

/-- With every route zero, the unique reverse solution is direct objective
credit alone. -/
theorem routedReverseSolution_zero
    (direct : ∀ node, NodeCovector NodeSpace node)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target) :
    routedReverseSolution (ParentOccurrence := ParentOccurrence)
        (NodeSpace := NodeSpace) graph (zeroRoute ParentOccurrence)
        direct parentDerivative = direct := by
  funext source
  rw [routedReverseSolution_eq_routedReverseAggregate, routedReverseAggregate,
    routedParentAggregate_zero]
  exact add_zero _

omit [Fintype Node] parentOccurrenceFintype in
/-- A route in `[0, 1]` cannot amplify the norm of one pulled-back
occurrence.  This is a local statement; sums of many routed occurrences still
require their own aggregate bound. -/
theorem routedPullback_norm_le
    (route : OccurrenceRoute ParentOccurrence)
    (parentDerivative : ∀ {source target}, ParentOccurrence source target →
      NodeSpace source →L[ℝ] NodeSpace target)
    (credit : ∀ node, NodeCovector NodeSpace node)
    {source target : Node}
    (occurrence : ParentOccurrence source target)
    (routeBounds : route occurrence ∈ Set.Icc (0 : ℝ) 1) :
    ‖route occurrence •
        parentPullback ParentOccurrence NodeSpace parentDerivative credit occurrence‖ ≤
      ‖parentPullback ParentOccurrence NodeSpace parentDerivative credit occurrence‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg routeBounds.1]
  calc
    route occurrence *
          ‖parentPullback ParentOccurrence NodeSpace parentDerivative credit occurrence‖
        ≤ 1 *
          ‖parentPullback ParentOccurrence NodeSpace parentDerivative credit occurrence‖ :=
      mul_le_mul_of_nonneg_right routeBounds.2 (norm_nonneg _)
    _ = ‖parentPullback ParentOccurrence NodeSpace parentDerivative credit occurrence‖ :=
      one_mul _

end RankedOccurrenceDAG

/-! ## Forward-value boundary

The source implementation uses a stopped-gradient copy of the activation.
Stopping a derivative is not represented by equality in Lean.  The following
identity records only the forward-value equation that such an implementation
must preserve.
-/

/-- Masking an activation against a forward-equal stopped copy leaves its
ordinary value unchanged. -/
theorem routedActivation_forward_value
    {State : Type*} [AddCommGroup State] [Module ℝ State]
    (mask : ℝ) (activation : State) :
    mask • activation + (1 - mask) • activation = activation := by
  rw [← add_smul]
  simp

/-! ## Executable occurrence fixtures -/

/-- Route only the first of the two parallel occurrence slots, at half
strength. -/
noncomputable def halfFirstRoute :
    OccurrenceRoute twoSlotOccurrence :=
  fun {_source _target} occurrence =>
    if occurrence.val = 0 then (1 / 2 : ℝ) else 0

/-- The routed aggregate is `1/2 * 3 + 0 * 6 = 3/2`; occurrence routing is
therefore neither node masking nor ordinary reverse mode. -/
theorem twoSlot_halfFirstRoute_eq_three_halves :
    RankedOccurrenceDAG.routedParentAggregate
      (ParentOccurrence := twoSlotOccurrence)
      (NodeSpace := fun _ : Fin 2 => ℝ)
      twoSlotGraph halfFirstRoute twoSlotPartial twoSlotCredit 0 1 =
      (3 / 2 : ℝ) := by
  norm_num [RankedOccurrenceDAG.routedParentAggregate, halfFirstRoute,
    twoSlotGraph, twoSlotOccurrence, twoSlotPartial, twoSlotCredit,
    parentPullback]

/-- Unit routing on the same nontrivial parallel-edge graph recovers all nine
units of ordinary reverse credit. -/
theorem twoSlot_unitRoute_eq_nine :
    RankedOccurrenceDAG.routedParentAggregate
      (ParentOccurrence := twoSlotOccurrence)
      (NodeSpace := fun _ : Fin 2 => ℝ)
      twoSlotGraph (unitRoute twoSlotOccurrence)
      twoSlotPartial twoSlotCredit 0 1 = 9 := by
  rw [RankedOccurrenceDAG.routedParentAggregate_unit]
  exact twoSlot_parentAggregate_counts_both_occurrences

/-- Negative routes fall outside the nonamplification theorem and reverse the
ordinary aggregate in this scalar fixture. -/
def negativeUnitRoute :
    OccurrenceRoute twoSlotOccurrence :=
  fun {_source _target} _occurrence => -1

theorem twoSlot_negativeRoute_reverses_credit :
    RankedOccurrenceDAG.routedParentAggregate
      (ParentOccurrence := twoSlotOccurrence)
      (NodeSpace := fun _ : Fin 2 => ℝ)
      twoSlotGraph negativeUnitRoute twoSlotPartial twoSlotCredit 0 1 = -9 := by
  norm_num [RankedOccurrenceDAG.routedParentAggregate, negativeUnitRoute,
    twoSlotGraph, twoSlotOccurrence, twoSlotPartial, twoSlotCredit,
    parentPullback]

#print axioms RankedOccurrenceDAG.routedReverseSolution_existsUnique
#print axioms RankedOccurrenceDAG.routedReverseSolution_unit
#print axioms RankedOccurrenceDAG.routedReverseSolution_zero
#print axioms RankedOccurrenceDAG.routedPullback_norm_le
#print axioms routedActivation_forward_value
#print axioms twoSlot_halfFirstRoute_eq_three_halves
#print axioms twoSlot_negativeRoute_reverses_credit

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT
