import Mettapedia.Cybernetics.ApproximateAdequacy.BisimulationMetric

/-!
# Control: discounting forgives a delayed failure

A deterministic world raises an alarm two steps after the start; the model
never does.  On deterministic chains at discount `1`, coupling bounds and
Girard–Pappas approximate bisimulations are the same certificates
(`CouplingBound.isApproxBisimulation_ofFunction`,
`couplingBound_of_isApproxBisimulation`).  Below discount `1` they separate:

* the bisimulation metric at the start is exactly `c²` (`metric_start`),
  pinned by a coupling bound and the expression "the alarm two steps ahead";
  at `c = 1/2` it is `1/4`;
* no approximate bisimulation below `1` relates the start to the model
  (`not_approxBisimilar`).

A discounted metric certifies near-term predictions strongly and far-term
ones weakly: an error `n` steps ahead costs `c ^ n`
(`CouplingBound.abs_expect_plan_sub_le`).
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.ApproximateAdequacy.DelayedFailure

open Finset
open Mettapedia.Cybernetics.MindWorldApproximation

/-- Three stages of the world. -/
inductive Stage
  | start
  | middle
  | fail
  deriving DecidableEq

instance : Fintype Stage where
  elems := {.start, .middle, .fail}
  complete x := by cases x <;> simp

/-- The world's deterministic step. -/
def next (_ : Unit) : Stage → Stage
  | .start => .middle
  | .middle => .fail
  | .fail => .fail

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The alarm observable. -/
def alarm : Stage → 𝕜
  | .fail => 1
  | _ => 0

/-- **The world**: the alarm sounds two steps after the start. -/
def world : LabelledMarkovChain 𝕜 Unit Unit Stage :=
  LabelledMarkovChain.ofFunction next fun _ => alarm

/-- **The model**: the alarm never sounds. -/
def calm : LabelledMarkovChain 𝕜 Unit Unit Unit :=
  LabelledMarkovChain.ofFunction (fun _ u => u) fun _ _ => 0

/-- The bound: `c²` at the start, `c` in the middle, `1` at the failure. -/
def bound (c : 𝕜) : Stage → Unit → 𝕜
  | .start, _ => c * c
  | .middle, _ => c
  | .fail, _ => 1

theorem couplingBound {c : 𝕜} (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) :
    CouplingBound world calm c (bound c) := by
  refine couplingBound_ofFunction_iff.mpr ⟨fun s _ => ?_, fun _ s _ => ?_, fun _ s _ => ?_⟩
  · cases s <;> simp only [bound] <;> first | exact mul_nonneg c_nonneg c_nonneg | exact c_nonneg |
      exact zero_le_one
  · cases s <;> simp [bound, alarm, mul_nonneg c_nonneg c_nonneg, c_nonneg]
  · cases s <;> simp only [bound, next] <;> first | exact le_rfl | nlinarith

/-- The expression "the alarm two steps ahead". -/
def alarmAhead : FunctionalExpression 𝕜 Unit Unit :=
  .next () (.next () (.observe ()))

theorem eval_alarmAhead_start (c : 𝕜) : alarmAhead.eval world c .start = c * (c * 1) := by
  simp [alarmAhead, FunctionalExpression.eval, world, LabelledMarkovChain.ofFunction, expect_dirac,
    next, alarm]

theorem eval_alarmAhead_calm (c : 𝕜) : alarmAhead.eval calm c () = 0 := by
  simp [alarmAhead, FunctionalExpression.eval, calm, LabelledMarkovChain.ofFunction, expect_dirac]

/-- **The metric at the start is exactly `c²`.** -/
theorem metric_start {c : ℝ} (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) :
    bisimulationMetric world calm c .start () = c * c := by
  apply le_antisymm
  · exact bisimulationMetric_le (couplingBound c_nonneg c_le) c_nonneg _ _
  · have lower := abs_eval_sub_le_bisimulationMetric (P := world) (Q := calm) c_nonneg c_le
      alarmAhead .start ()
    rw [eval_alarmAhead_start, eval_alarmAhead_calm, sub_zero, mul_one,
      abs_of_nonneg (mul_nonneg c_nonneg c_nonneg)] at lower
    exact lower

theorem metric_start_half : bisimulationMetric world calm (1 / 2 : ℝ) .start () = 1 / 4 := by
  rw [metric_start (by norm_num) (by norm_num)]
  norm_num

/-- **No approximate bisimulation below `1`**: the failure two steps ahead is
an observation error `1`, whatever the delay. -/
theorem not_approxBisimilar {ε : 𝕜} (small : ε < 1) :
    ¬ ApproxBisimilar observationGap (fun s s' => next () s = s')
      (fun u u' => (fun _ u => u) () u = u')
      (world (𝕜 := 𝕜)).observation (calm (𝕜 := 𝕜)).observation ε Stage.start () := by
  rw [approxBisimilar_update_iff observationGap_comm]
  intro close
  have atTwo := (observationGap_le_iff.mp (close 2)).2 ()
  simp [LabelledMarkovChain.observation, world, calm, LabelledMarkovChain.ofFunction, next,
    alarm] at atTwo
  linarith

end Mettapedia.Cybernetics.ApproximateAdequacy.DelayedFailure
