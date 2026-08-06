import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.ResidualBoundary
import Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry.InterferenceGram
import Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry.MetricDictionary

/-!
# A prospective-interference toy model

This file formalizes the scalar mechanism illustrated by Figure 1 of Song and
collaborators, *Inferring Neural Activity Before Plasticity as a Foundation
for Learning Beyond Backpropagation* (Nature Neuroscience 27, 2024).  Its
theoretical companion is Millidge, Song, Salvatori, Lukasiewicz, and Bogacz,
*A Theoretical Framework for Inference and Learning in Predictive Coding
Networks* (arXiv:2207.12316).  One hidden scalar is shared by an
already-correct output and a newly corrected output.

An exact backpropagation repair changes the shared hidden scalar and therefore
changes the old output exactly when both the old readout path and hidden
displacement are nonzero.  A prospective repair performs the same hidden
correction while compensating the old readout, hence fixes the new output and
preserves the old one.  The example is classified using the existing
forgetting geometry: scalar curvatures commute and the sequential connection
remainder vanishes at the old optimum, while the metric/optimum mismatch is
nonzero.  Broader neural and behavioral claims remain reproduction targets.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier

open Mettapedia.MachineLearning.ContinualLearning
open Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry

/-! ## Exact shared-hidden repair -/

/-- Scalar output of one readout from a shared hidden activation. -/
noncomputable def sharedHiddenOutput
    (readout hidden input : ℝ) : ℝ :=
  readout * hidden * input

/-- Half-squared error used to state strict degradation of a previously
correct output without imposing an arbitrary sign convention. -/
noncomputable def halfSquaredOutputError
    (target prediction : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (target - prediction) ^ 2

/-- Hidden activation that exactly fits the newly targeted output. -/
noncomputable def bpRepairedHidden
    (errorReadout input errorTarget : ℝ) : ℝ :=
  errorTarget / (errorReadout * input)

/-- Compensated old readout after changing the shared hidden activation. -/
noncomputable def prospectiveCorrectReadout
    (oldHidden oldCorrectReadout newHidden : ℝ) : ℝ :=
  oldCorrectReadout * oldHidden / newHidden

/-- Backpropagation's hidden repair exactly fixes the targeted output whenever
the new readout path is nonzero. -/
theorem bpRepairedHidden_fixes_errorOutput
    (errorReadout input errorTarget : ℝ)
    (hpath : errorReadout * input ≠ 0) :
    sharedHiddenOutput errorReadout
        (bpRepairedHidden errorReadout input errorTarget) input =
      errorTarget := by
  rw [sharedHiddenOutput, bpRepairedHidden]
  rw [show errorReadout * (errorTarget / (errorReadout * input)) * input =
      (errorTarget / (errorReadout * input)) * (errorReadout * input) by ring]
  exact div_mul_cancel₀ errorTarget hpath

/-- Exact change in the already-correct output after moving the shared hidden
activation. -/
theorem sharedHiddenOutput_change_exact
    (correctReadout input oldHidden newHidden : ℝ) :
    sharedHiddenOutput correctReadout newHidden input -
        sharedHiddenOutput correctReadout oldHidden input =
      (correctReadout * input) * (newHidden - oldHidden) := by
  simp [sharedHiddenOutput]
  ring

/-- Iff characterization of prospective interference: ordinary hidden repair
changes the correct output exactly when the old path is live and the repair
actually moves the hidden activation. -/
theorem bp_hiddenRepair_changes_correctOutput_iff
    (correctReadout input oldHidden newHidden : ℝ) :
    sharedHiddenOutput correctReadout newHidden input ≠
        sharedHiddenOutput correctReadout oldHidden input ↔
      correctReadout * input ≠ 0 ∧ newHidden ≠ oldHidden := by
  rw [← sub_ne_zero]
  rw [sharedHiddenOutput_change_exact]
  rw [mul_ne_zero_iff, sub_ne_zero]

/-- Exact strict-loss version of the Figure-1 interference condition.  A
hidden repair strictly worsens an output that was previously exact iff the
old readout path is live and the hidden activity actually moves. -/
theorem hiddenRepair_strictly_degrades_preservedOutput_iff
    (correctReadout input oldHidden newHidden : ℝ) :
    halfSquaredOutputError
        (sharedHiddenOutput correctReadout oldHidden input)
        (sharedHiddenOutput correctReadout newHidden input) >
        halfSquaredOutputError
          (sharedHiddenOutput correctReadout oldHidden input)
          (sharedHiddenOutput correctReadout oldHidden input) ↔
      correctReadout * input ≠ 0 ∧ newHidden ≠ oldHidden := by
  have hzero :
      halfSquaredOutputError
          (sharedHiddenOutput correctReadout oldHidden input)
          (sharedHiddenOutput correctReadout oldHidden input) = 0 := by
    simp [halfSquaredOutputError]
  rw [hzero]
  constructor
  · intro hpositive
    have houtputs :
        sharedHiddenOutput correctReadout newHidden input ≠
          sharedHiddenOutput correctReadout oldHidden input := by
      intro heq
      rw [heq] at hpositive
      simp [halfSquaredOutputError] at hpositive
    exact (bp_hiddenRepair_changes_correctOutput_iff
      correctReadout input oldHidden newHidden).mp houtputs
  · intro hconditions
    have houtputs :
        sharedHiddenOutput correctReadout newHidden input ≠
          sharedHiddenOutput correctReadout oldHidden input :=
      (bp_hiddenRepair_changes_correctOutput_iff
        correctReadout input oldHidden newHidden).mpr hconditions
    have hdifference :
        sharedHiddenOutput correctReadout oldHidden input -
            sharedHiddenOutput correctReadout newHidden input ≠ 0 :=
      sub_ne_zero.mpr houtputs.symm
    unfold halfSquaredOutputError
    nlinarith [sq_pos_of_ne_zero hdifference]

/-- Prospective readout compensation preserves the old output exactly. -/
theorem prospectiveCorrectReadout_preserves_output
    (input oldHidden oldCorrectReadout newHidden : ℝ)
    (hnew : newHidden ≠ 0) :
    sharedHiddenOutput
        (prospectiveCorrectReadout oldHidden oldCorrectReadout newHidden)
        newHidden input =
      sharedHiddenOutput oldCorrectReadout oldHidden input := by
  rw [sharedHiddenOutput, prospectiveCorrectReadout, sharedHiddenOutput]
  rw [show oldCorrectReadout * oldHidden / newHidden * newHidden * input =
      (oldCorrectReadout * oldHidden / newHidden * newHidden) * input by ring]
  rw [div_mul_cancel₀ _ hnew]

/-- The prospective pair simultaneously fixes the new output and preserves
the old output. -/
theorem prospectiveRepair_fixes_and_preserves
    (input oldHidden oldCorrectReadout errorReadout errorTarget : ℝ)
    (hpath : errorReadout * input ≠ 0)
    (hnew : bpRepairedHidden errorReadout input errorTarget ≠ 0) :
    sharedHiddenOutput errorReadout
        (bpRepairedHidden errorReadout input errorTarget) input = errorTarget ∧
      sharedHiddenOutput
          (prospectiveCorrectReadout oldHidden oldCorrectReadout
            (bpRepairedHidden errorReadout input errorTarget))
          (bpRepairedHidden errorReadout input errorTarget) input =
        sharedHiddenOutput oldCorrectReadout oldHidden input := by
  exact ⟨bpRepairedHidden_fixes_errorOutput _ _ _ hpath,
    prospectiveCorrectReadout_preserves_output _ _ _ _ hnew⟩

/-- Full weights/data characterization of the prospective advantage.  Under
a live target path and nonzero prospective hidden state, prospective readout
compensation has strictly lower preserved-output loss than ordinary hidden
repair exactly when the old path is live and the repair moves the hidden
state. -/
theorem prospectiveRepair_strictAdvantage_iff
    (input oldHidden oldCorrectReadout errorReadout errorTarget : ℝ)
    (hnew : bpRepairedHidden errorReadout input errorTarget ≠ 0) :
    halfSquaredOutputError
        (sharedHiddenOutput oldCorrectReadout oldHidden input)
        (sharedHiddenOutput oldCorrectReadout
          (bpRepairedHidden errorReadout input errorTarget) input) >
      halfSquaredOutputError
        (sharedHiddenOutput oldCorrectReadout oldHidden input)
        (sharedHiddenOutput
          (prospectiveCorrectReadout oldHidden oldCorrectReadout
            (bpRepairedHidden errorReadout input errorTarget))
          (bpRepairedHidden errorReadout input errorTarget) input) ↔
      oldCorrectReadout * input ≠ 0 ∧
        bpRepairedHidden errorReadout input errorTarget ≠ oldHidden := by
  rw [prospectiveCorrectReadout_preserves_output
    input oldHidden oldCorrectReadout
    (bpRepairedHidden errorReadout input errorTarget) hnew]
  exact hiddenRepair_strictly_degrades_preservedOutput_iff
    oldCorrectReadout input oldHidden
      (bpRepairedHidden errorReadout input errorTarget)

/-- Figure-1 crown: ordinary and prospective repairs share the exact new
target, while the prospective repair has a strict preserved-output advantage
under precisely the live-old-path and hidden-movement conditions. -/
theorem prospectiveRepair_target_and_advantage
    (input oldHidden oldCorrectReadout errorReadout errorTarget : ℝ)
    (hpath : errorReadout * input ≠ 0)
    (hnew : bpRepairedHidden errorReadout input errorTarget ≠ 0) :
    sharedHiddenOutput errorReadout
        (bpRepairedHidden errorReadout input errorTarget) input = errorTarget ∧
      (halfSquaredOutputError
          (sharedHiddenOutput oldCorrectReadout oldHidden input)
          (sharedHiddenOutput oldCorrectReadout
            (bpRepairedHidden errorReadout input errorTarget) input) >
        halfSquaredOutputError
          (sharedHiddenOutput oldCorrectReadout oldHidden input)
          (sharedHiddenOutput
            (prospectiveCorrectReadout oldHidden oldCorrectReadout
              (bpRepairedHidden errorReadout input errorTarget))
            (bpRepairedHidden errorReadout input errorTarget) input) ↔
        oldCorrectReadout * input ≠ 0 ∧
          bpRepairedHidden errorReadout input errorTarget ≠ oldHidden) := by
  exact ⟨bpRepairedHidden_fixes_errorOutput _ _ _ hpath,
    prospectiveRepair_strictAdvantage_iff _ _ _ _ _ hnew⟩

/-- Positive Figure-1-style fixture.  Ordinary repair changes the old unit
output to one half; prospective repair changes the old readout to two,
preserving the unit output while fixing the new target at one half. -/
theorem prospectiveInterference_halfTarget_positiveFixture :
    bpRepairedHidden 1 1 (1 / 2) = 1 / 2 ∧
      sharedHiddenOutput 1 (bpRepairedHidden 1 1 (1 / 2)) 1 = 1 / 2 ∧
      prospectiveCorrectReadout 1 1 (bpRepairedHidden 1 1 (1 / 2)) = 2 ∧
      sharedHiddenOutput
          (prospectiveCorrectReadout 1 1 (bpRepairedHidden 1 1 (1 / 2)))
          (bpRepairedHidden 1 1 (1 / 2)) 1 = 1 := by
  norm_num [bpRepairedHidden, sharedHiddenOutput, prospectiveCorrectReadout]

/-- Negative boundary: if the repair leaves the hidden activation unchanged,
ordinary backpropagation does not harm the correct output. -/
theorem unchangedHidden_no_prospective_advantage
    (correctReadout input hidden : ℝ) :
    halfSquaredOutputError
        (sharedHiddenOutput correctReadout hidden input)
        (sharedHiddenOutput correctReadout hidden input) = 0 := by
  simp [halfSquaredOutputError]

/-! ## Forgetting-geometry classification -/

/-- Scalar unit-curvature task with a chosen optimum. -/
noncomputable def scalarOptimumTask (optimum : ℝ) : QuadraticTask (Fin 1) where
  curvature := 1
  optimum := fun _ => optimum

/-- Scalar parameter vector. -/
noncomputable def scalarParameter (parameter : ℝ) : Fin 1 → ℝ :=
  fun _ => parameter

/-- Scalar task curvatures commute, hence the degree-two interference energy
is zero regardless of conflicting optima. -/
theorem scalarOptimumTasks_interferenceEnergy_zero
    (firstOptimum secondOptimum : ℝ) :
    pairwiseInterferenceEnergy
        (scalarOptimumTask firstOptimum).curvature
        (scalarOptimumTask secondOptimum).curvature = 0 := by
  rw [pairwiseInterferenceEnergy_eq_zero_iff_commute]
  exact Commute.refl _

/-- At the first task's optimum, its gradient is zero, so the exact sequential
connection remainder vanishes. -/
theorem scalarOptimumTasks_connectionRemainder_zero
    (firstOptimum secondOptimum stepSize : ℝ) :
    quadraticConnectionRemainder
        (scalarOptimumTask firstOptimum)
        (scalarOptimumTask secondOptimum) stepSize
        (scalarParameter firstOptimum) = 0 := by
  funext i
  fin_cases i
  simp [quadraticConnectionRemainder, QuadraticTask.gradient,
    scalarOptimumTask, scalarParameter]

/-- A unit additive repair at the old optimum has exact metric mismatch equal
to the displacement between task optima. -/
theorem scalarOptimumTasks_metricMismatch_exact
    (oldOptimum newOptimum : ℝ) :
    quadraticMetricMismatchAgainstReference
        (scalarOptimumTask oldOptimum)
        (scalarOptimumTask newOptimum) 1
        (scalarParameter oldOptimum) (scalarParameter oldOptimum) =
      scalarParameter (newOptimum - oldOptimum) := by
  funext i
  fin_cases i
  simp [quadraticMetricMismatchAgainstReference, additiveTwoTaskUpdate,
    QuadraticTask.gradient, scalarOptimumTask, scalarParameter]

/-- Classification crown: prospective interference in this scalar toy is an
optimum/metric conflict, not curvature-order interference or a sequential
connection effect. -/
theorem prospectiveInterference_metric_not_connection
    (oldOptimum newOptimum : ℝ) (hmove : newOptimum ≠ oldOptimum) :
    pairwiseInterferenceEnergy
        (scalarOptimumTask oldOptimum).curvature
        (scalarOptimumTask newOptimum).curvature = 0 ∧
      quadraticConnectionRemainder
        (scalarOptimumTask oldOptimum)
        (scalarOptimumTask newOptimum) 1
        (scalarParameter oldOptimum) = 0 ∧
      quadraticMetricMismatchAgainstReference
        (scalarOptimumTask oldOptimum)
        (scalarOptimumTask newOptimum) 1
        (scalarParameter oldOptimum) (scalarParameter oldOptimum) ≠ 0 := by
  refine ⟨scalarOptimumTasks_interferenceEnergy_zero _ _,
    scalarOptimumTasks_connectionRemainder_zero _ _ _, ?_⟩
  rw [scalarOptimumTasks_metricMismatch_exact]
  intro hzero
  have hi := congrFun hzero (0 : Fin 1)
  simp [scalarParameter] at hi
  exact hmove (sub_eq_zero.mp hi)

/-! ## Empirical boundary -/

inductive ProspectiveClaimStatus
  | exactScalarTheorem
  | pinnedReproductionTarget
  deriving DecidableEq, Repr

structure ProspectiveBoundaryClaim where
  description : String
  status : ProspectiveClaimStatus
  deriving DecidableEq, Repr

/-- Broad benchmark, biological, and optimizer comparisons are retained as
reproduction targets rather than asserted as mathematical propositions. -/
def prospectiveEmpiricalTargets : List ProspectiveBoundaryClaim :=
  [ { description := "prospective configuration reduces interference on the published benchmarks"
      status := .pinnedReproductionTarget }
  , { description := "prospective configuration is a general biological learning mechanism"
      status := .pinnedReproductionTarget }
  , { description := "prospective configuration dominates backpropagation beyond the scalar toy"
      status := .pinnedReproductionTarget }
  ]

theorem prospectiveEmpiricalTargets_count :
    prospectiveEmpiricalTargets.length = 3 := by
  decide

#print axioms bp_hiddenRepair_changes_correctOutput_iff
#print axioms prospectiveRepair_target_and_advantage
#print axioms prospectiveInterference_metric_not_connection

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier
