import Mathlib

/-!
# Exactly-once boundaries for task-free plateau consolidation

Aljundi, Chakravarty, and Tuytelaars, *Task-Free Continual Learning*
(CVPR 2019, arXiv:1812.03596), update parameter-importance weights when a
sliding loss window reaches a plateau.  Algorithm 1 prevents repeated updates
with a flag `P`: a plateau sets `P = 1`, and a later loss peak resets `P = 0`.

This file formalizes that gate as the sequential state transition printed in
lines 13--21.  A plateau followed by no simultaneous peak locks the gate, so
the same observation cannot emit a second consolidation.  A peak rearms it.
The two tests are independent `if` statements in the source, however.  If
their numeric conditions overlap on one observation, the plateau first emits
a consolidation and the peak immediately rearms the gate.  The unchanged
observation can then emit again.  A simple threshold inequality is sufficient
to exclude this overlap, and an executable fixture shows the failure when it
is absent.

The result audits the event discipline only.  It does not establish that low
loss mean and variance identify a semantic task plateau, that the hard buffer
is representative, that importance estimates are calibrated, or that the
method retains benchmark performance.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace TaskFreePlateauGate

noncomputable section

/-! ## Source-shaped state and observations -/

/-- `armed = true` corresponds to `P = 0` in Algorithm 1: the next qualifying
plateau may consolidate. -/
structure GateState where
  armed : Bool
deriving DecidableEq, Repr

/-- Statistics and thresholds read by the two sequential tests in
Algorithm 1. -/
structure WindowObservation where
  windowMean : ℝ
  windowStd : ℝ
  meanThreshold : ℝ
  stdThreshold : ℝ
  previousPlateauMean : ℝ
  previousPlateauStd : ℝ

/-- Lines 13--18: both current window statistics lie below their plateau
thresholds. -/
def plateauCondition (observation : WindowObservation) : Prop :=
  observation.windowMean < observation.meanThreshold ∧
    observation.windowStd < observation.stdThreshold

/-- Lines 19--21: the current mean exceeds the previous plateau mean by more
than one previous plateau standard deviation. -/
def peakCondition (observation : WindowObservation) : Prop :=
  observation.previousPlateauMean + observation.previousPlateauStd <
    observation.windowMean

/-- A consolidation is emitted only when the gate is armed and the plateau
condition holds. -/
def shouldConsolidate
    (state : GateState) (observation : WindowObservation) : Prop :=
  state.armed = true ∧ plateauCondition observation

/-- The two `if` statements of Algorithm 1 in their printed order.  A
qualifying plateau first disarms the gate; a simultaneous peak then rearms it
because the second test is not an `else`. -/
noncomputable def step
    (state : GateState) (observation : WindowObservation) : GateState := by
  classical
  exact
    let afterPlateau :=
      if shouldConsolidate state observation then false else state.armed
    { armed := if peakCondition observation then true else afterPlateau }

/-! ## Exactly-once positive boundary -/

/-- Every detected peak rearms the gate. -/
theorem step_armed_of_peak
    {state : GateState} {observation : WindowObservation}
    (peak : peakCondition observation) :
    (step state observation).armed = true := by
  classical
  simp [step, peak]

/-- A consolidation with no simultaneous peak leaves the gate disarmed. -/
theorem step_disarmed_of_consolidation_of_not_peak
    {state : GateState} {observation : WindowObservation}
    (consolidates : shouldConsolidate state observation)
    (not_peak : ¬ peakCondition observation) :
    (step state observation).armed = false := by
  classical
  simp [step, consolidates, not_peak]

/-- Consequently the same plateau observation cannot consolidate twice unless
its peak test also fires. -/
theorem same_observation_does_not_repeat_of_not_peak
    {state : GateState} {observation : WindowObservation}
    (consolidates : shouldConsolidate state observation)
    (not_peak : ¬ peakCondition observation) :
    ¬ shouldConsolidate (step state observation) observation := by
  have disarmed :=
    step_disarmed_of_consolidation_of_not_peak consolidates not_peak
  simp [shouldConsolidate, disarmed]

/-- If the plateau mean threshold is no greater than the previous
plateau-plus-deviation peak boundary, the plateau and peak tests are
disjoint. -/
theorem plateau_not_peak_of_meanThreshold_le_peakBoundary
    {observation : WindowObservation}
    (threshold_order :
      observation.meanThreshold ≤
        observation.previousPlateauMean +
          observation.previousPlateauStd)
    (plateau : plateauCondition observation) :
    ¬ peakCondition observation := by
  intro peak
  exact (not_lt_of_ge threshold_order)
    (lt_trans peak plateau.1)

/-- The threshold-order certificate turns a consolidation into an
exactly-once event for an unchanged observation. -/
theorem same_observation_does_not_repeat_of_threshold_order
    {state : GateState} {observation : WindowObservation}
    (threshold_order :
      observation.meanThreshold ≤
        observation.previousPlateauMean +
          observation.previousPlateauStd)
    (consolidates : shouldConsolidate state observation) :
    ¬ shouldConsolidate (step state observation) observation := by
  exact same_observation_does_not_repeat_of_not_peak consolidates
    (plateau_not_peak_of_meanThreshold_le_peakBoundary
      threshold_order consolidates.2)

/-! ## Sequential-`if` overlap boundary -/

/-- If both source tests fire, the second `if` immediately rearms the gate. -/
theorem simultaneous_peak_rearms_after_consolidation
    {state : GateState} {observation : WindowObservation}
    (_consolidates : shouldConsolidate state observation)
    (peak : peakCondition observation) :
    (step state observation).armed = true := by
  exact step_armed_of_peak peak

/-- With an unchanged observation, simultaneous plateau and peak conditions
permit immediate repeated consolidation. -/
theorem simultaneous_peak_allows_same_observation_repeat
    {state : GateState} {observation : WindowObservation}
    (consolidates : shouldConsolidate state observation)
    (peak : peakCondition observation) :
    shouldConsolidate (step state observation) observation := by
  exact ⟨step_armed_of_peak peak, consolidates.2⟩

/-! ## Executable fixtures -/

def stablePlateauObservation : WindowObservation where
  windowMean := 0
  windowStd := 0
  meanThreshold := 1
  stdThreshold := 1
  previousPlateauMean := 0
  previousPlateauStd := 1

def peakObservation : WindowObservation where
  windowMean := 2
  windowStd := 2
  meanThreshold := 1
  stdThreshold := 1
  previousPlateauMean := 0
  previousPlateauStd := 1

def overlapObservation : WindowObservation where
  windowMean := 0
  windowStd := 0
  meanThreshold := 1
  stdThreshold := 1
  previousPlateauMean := -2
  previousPlateauStd := 1

/-- A stable plateau consolidates once, the unchanged plateau is blocked, a
later peak rearms, and the next stable plateau consolidates again. -/
theorem plateau_peak_plateau_lifecycle :
    shouldConsolidate ⟨true⟩ stablePlateauObservation ∧
      ¬ shouldConsolidate
        (step ⟨true⟩ stablePlateauObservation)
        stablePlateauObservation ∧
      (step
        (step ⟨true⟩ stablePlateauObservation)
        peakObservation).armed = true ∧
      shouldConsolidate
        (step
          (step ⟨true⟩ stablePlateauObservation)
          peakObservation)
        stablePlateauObservation := by
  classical
  norm_num [shouldConsolidate, plateauCondition, peakCondition, step,
    stablePlateauObservation, peakObservation]

/-- The printed sequential tests can overlap: this observation consolidates,
is immediately rearmed, and consolidates again without any statistical
change. -/
theorem sequential_if_overlap_repeats_consolidation :
    shouldConsolidate ⟨true⟩ overlapObservation ∧
      peakCondition overlapObservation ∧
      shouldConsolidate
        (step ⟨true⟩ overlapObservation)
        overlapObservation := by
  classical
  norm_num [shouldConsolidate, plateauCondition, peakCondition, step,
    overlapObservation]

end

end TaskFreePlateauGate

end Mettapedia.MachineLearning.ContinualLearning
