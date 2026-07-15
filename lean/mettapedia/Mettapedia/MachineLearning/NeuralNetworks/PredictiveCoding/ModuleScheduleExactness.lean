import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.PreconditionedLearning

/-!
# Module-valued scheduled aggregation

This file isolates the algebraic core of scheduled reverse aggregation.  Edge
gains remain real scalars, while parent errors may live in any faithful real
module, including finite-dimensional vector spaces.  Universal exactness is
therefore characterized by the same grouped target-gain criterion as in the
scalar case.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

section ModuleSchedule

variable {Node Edge M : Type*} [Fintype Node] [Fintype Edge]
  [DecidableEq Node] [AddCommGroup M] [Module ℝ M]

/-- One real-weighted, module-valued parent contribution. -/
noncomputable def moduleParentContribution
    (target : Edge → Node) (gain : Edge → ℝ)
    (parentError : Node → M) (e : Edge) : M :=
  gain e • parentError (target e)

/-- Full module-valued aggregation over outgoing edge occurrences. -/
noncomputable def moduleFullParentAggregate
    (source : Edge → Node) (target : Edge → Node) (gain : Edge → ℝ)
    (parentError : Node → M) (v : Node) : M :=
  ∑ e : Edge,
    if source e = v then moduleParentContribution target gain parentError e else 0

/-- Module-valued aggregation of contributions that have arrived by `time`. -/
noncomputable def moduleScheduledParentAggregate
    (source : Edge → Node) (target : Edge → Node) (gain : Edge → ℝ)
    (parentError : Node → M) (arrival : Edge → ℕ)
    (time : ℕ) (v : Node) : M :=
  ∑ e : Edge,
    if source e = v then
      if arrival e ≤ time then
        moduleParentContribution target gain parentError e
      else 0
    else 0

/-- Module-valued sum of contributions still absent at `time`. -/
noncomputable def moduleMissedParentAggregate
    (source : Edge → Node) (target : Edge → Node) (gain : Edge → ℝ)
    (parentError : Node → M) (arrival : Edge → ℕ)
    (time : ℕ) (v : Node) : M :=
  ∑ e : Edge,
    if source e = v then
      if arrival e ≤ time then 0
      else moduleParentContribution target gain parentError e
    else 0

omit [Fintype Node] in
theorem moduleScheduled_add_missed_eq_full
    (source : Edge → Node) (target : Edge → Node) (gain : Edge → ℝ)
    (parentError : Node → M) (arrival : Edge → ℕ)
    (time : ℕ) (v : Node) :
    moduleScheduledParentAggregate source target gain parentError arrival time v +
        moduleMissedParentAggregate source target gain parentError arrival time v =
      moduleFullParentAggregate source target gain parentError v := by
  classical
  unfold moduleScheduledParentAggregate moduleMissedParentAggregate
    moduleFullParentAggregate
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hs : source e = v
  · by_cases ha : arrival e ≤ time <;> simp [hs, ha]
  · simp [hs]

omit [Fintype Node] in
/-- Scheduled aggregation is exact precisely when the omitted module-valued
sum is zero. -/
theorem moduleScheduledParentAggregate_eq_full_iff_missed_eq_zero
    (source : Edge → Node) (target : Edge → Node) (gain : Edge → ℝ)
    (parentError : Node → M) (arrival : Edge → ℕ)
    (time : ℕ) (v : Node) :
    moduleScheduledParentAggregate source target gain parentError arrival time v =
        moduleFullParentAggregate source target gain parentError v ↔
      moduleMissedParentAggregate source target gain parentError arrival time v = 0 := by
  have hsum := moduleScheduled_add_missed_eq_full source target gain
    parentError arrival time v
  constructor
  · intro hexact
    rw [hexact] at hsum
    exact add_eq_left.mp hsum
  · intro hzero
    rw [hzero, add_zero] at hsum
    exact hsum

/-- Total scalar gain of all missed edges from `v` to one fixed target. -/
noncomputable def moduleMissedTargetGain
    (source : Edge → Node) (target : Edge → Node) (gain : Edge → ℝ)
    (arrival : Edge → ℕ) (time : ℕ) (v targetNode : Node) : ℝ :=
  ∑ e : Edge,
    if source e = v ∧ time < arrival e ∧ target e = targetNode then gain e else 0

/-- Regroup a module-valued missed aggregate by target. -/
theorem moduleMissedParentAggregate_eq_sum_targetGain
    (source : Edge → Node) (target : Edge → Node) (gain : Edge → ℝ)
    (parentError : Node → M) (arrival : Edge → ℕ)
    (time : ℕ) (v : Node) :
    moduleMissedParentAggregate source target gain parentError arrival time v =
      ∑ targetNode : Node,
        moduleMissedTargetGain source target gain arrival time v targetNode •
          parentError targetNode := by
  classical
  unfold moduleMissedParentAggregate moduleMissedTargetGain
    moduleParentContribution
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hs : source e = v
  · by_cases ha : arrival e ≤ time
    · simp [hs, ha, not_lt_of_ge ha]
    · have hlt : time < arrival e := Nat.lt_of_not_ge ha
      simp [hs, ha, hlt]
  · simp [hs]

/-- Universal exactness quantifies over all module-valued parent errors. -/
def moduleScheduleUniversallyExactAtNode
    (source : Edge → Node) (target : Edge → Node) (gain : Edge → ℝ)
    (arrival : Edge → ℕ) (time : ℕ) (v : Node) : Prop :=
  ∀ parentError : Node → M,
    moduleScheduledParentAggregate source target gain parentError arrival time v =
      moduleFullParentAggregate source target gain parentError v

/-- For a faithful real module, universal exactness holds exactly when every
missed target-group gain is zero. -/
theorem moduleScheduleUniversallyExactAtNode_iff_targetGain_zero
    [FaithfulSMul ℝ M]
    (source : Edge → Node) (target : Edge → Node) (gain : Edge → ℝ)
    (arrival : Edge → ℕ) (time : ℕ) (v : Node) :
    moduleScheduleUniversallyExactAtNode (M := M)
        source target gain arrival time v ↔
      ∀ targetNode,
        moduleMissedTargetGain source target gain arrival time v targetNode = 0 := by
  constructor
  · intro huniversal targetNode
    apply FaithfulSMul.eq_of_smul_eq_smul (α := M)
    intro value
    have hexact := huniversal (fun node => if node = targetNode then value else 0)
    have hmissed :=
      (moduleScheduledParentAggregate_eq_full_iff_missed_eq_zero
        source target gain (fun node => if node = targetNode then value else 0)
        arrival time v).1 hexact
    rw [moduleMissedParentAggregate_eq_sum_targetGain] at hmissed
    simpa using hmissed
  · intro hcoeff parentError
    apply (moduleScheduledParentAggregate_eq_full_iff_missed_eq_zero
      source target gain parentError arrival time v).2
    rw [moduleMissedParentAggregate_eq_sum_targetGain]
    simp [hcoeff]

end ModuleSchedule

/-! ## Vector-valued fixtures -/

abbrev ScheduleVector := Fin 2 → ℝ

/-- Two missed parallel edges with gains `+1` and `-1` cancel for every
two-dimensional parent-error vector. -/
theorem moduleSignedCancellation_universallyExact_positive_example :
    moduleScheduleUniversallyExactAtNode (M := ScheduleVector)
      (fun _ : Fin 2 => (0 : Fin 1)) (fun _ : Fin 2 => (0 : Fin 1))
      (fun e : Fin 2 => if e.val = 0 then 1 else -1)
      (fun _ : Fin 2 => 1) 0 0 := by
  rw [moduleScheduleUniversallyExactAtNode_iff_targetGain_zero]
  intro targetNode
  fin_cases targetNode
  norm_num [moduleMissedTargetGain, Fin.sum_univ_succ]

/-- A single missed nonzero edge is not universally exact for vector-valued
parent errors. -/
theorem moduleSingleMissedEdge_not_universallyExact_negative_example :
    ¬ moduleScheduleUniversallyExactAtNode (M := ScheduleVector)
      (fun _ : Fin 1 => (0 : Fin 1)) (fun _ : Fin 1 => (0 : Fin 1))
      (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 1) 0 0 := by
  rw [moduleScheduleUniversallyExactAtNode_iff_targetGain_zero]
  push Not
  refine ⟨0, ?_⟩
  norm_num [moduleMissedTargetGain, Fin.sum_univ_succ]

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
