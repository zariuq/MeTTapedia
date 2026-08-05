import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-!
# Two-stage approximation budgets for streaming subspace sketches

Continuous Subspace Optimization first truncates each projected-gradient
packet and then applies Frequent Directions to the stream of truncated
packets.  Its covariance-sketch estimate therefore has two distinct error
sources:

1. packetwise truncation error; and
2. error of the streaming sketch relative to the aggregate truncated packet.

This file proves the normed-space composition theorem behind that argument.
It applies to matrices equipped with an applicable norm, but is stated for an
arbitrary normed additive group because neither positivity nor multiplication
is used by the proof.  Packetwise errors add, and the sketch error is then
added by a second triangle inequality.

The result does not prove a singular-value truncation theorem or the
Frequent-Directions residual bound.  Those are explicit input certificates.
The negative fixtures show why both the packetwise and sketch terms are
load-bearing, and why a sum of local bounds need not be an exact error.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace TwoStageSketchApproximation

open scoped BigOperators

variable {Step Value : Type*}
variable [Fintype Step] [NormedAddCommGroup Value]

/-- Aggregate a finite stream in its declared coordinate space. -/
def aggregate (packet : Step → Value) : Value :=
  ∑ step, packet step

/-- The distance between two aggregate streams is at most the sum of their
packetwise distances. -/
theorem norm_aggregate_sub_le_sum_norm
    (exact approximate : Step → Value) :
    ‖aggregate exact - aggregate approximate‖ ≤
      ∑ step, ‖exact step - approximate step‖ := by
  calc
    ‖aggregate exact - aggregate approximate‖ =
        ‖∑ step, (exact step - approximate step)‖ := by
      rw [Finset.sum_sub_distrib]
      rfl
    _ ≤ ∑ step, ‖exact step - approximate step‖ := by
      simpa using
        norm_sum_le (Finset.univ : Finset Step)
          (fun step ↦ exact step - approximate step)

/-- General two-stage certificate.  Local truncation budgets control the
exact-to-approximate aggregate; a separate sketch budget controls the
approximate aggregate-to-sketch leg. -/
theorem twoStageSketch_error_le
    (exact approximate : Step → Value)
    (sketch : Value)
    (localBudget : Step → ℝ)
    (sketchBudget : ℝ)
    (hlocal :
      ∀ step,
        ‖exact step - approximate step‖ ≤ localBudget step)
    (hsketch :
      ‖aggregate approximate - sketch‖ ≤ sketchBudget) :
    ‖aggregate exact - sketch‖ ≤
      (∑ step, localBudget step) + sketchBudget := by
  calc
    ‖aggregate exact - sketch‖ =
        ‖(aggregate exact - aggregate approximate) +
          (aggregate approximate - sketch)‖ := by
      congr 1
      abel
    _ ≤ ‖aggregate exact - aggregate approximate‖ +
        ‖aggregate approximate - sketch‖ :=
      norm_add_le _ _
    _ ≤ (∑ step, ‖exact step - approximate step‖) +
        sketchBudget :=
      add_le_add
        (norm_aggregate_sub_le_sum_norm exact approximate)
        hsketch
    _ ≤ (∑ step, localBudget step) + sketchBudget := by
      gcongr with step
      exact hlocal step

/-- Source-shaped specialization: if every packetwise truncation error is
identified exactly with its tail energy and the streaming sketch has its own
certified residual, their sum bounds the final error. -/
theorem tailEnergy_add_sketchResidual_bounds_final
    (exact approximate : Step → Value)
    (sketch : Value)
    (tailEnergy : Step → ℝ)
    (sketchResidual : ℝ)
    (htruncation :
      ∀ step,
        ‖exact step - approximate step‖ = tailEnergy step)
    (hsketch :
      ‖aggregate approximate - sketch‖ ≤ sketchResidual) :
    ‖aggregate exact - sketch‖ ≤
      (∑ step, tailEnergy step) + sketchResidual := by
  apply twoStageSketch_error_le exact approximate sketch
    tailEnergy sketchResidual
  · intro step
    exact (htruncation step).le
  · exact hsketch

/-! ## Positive and negative fixtures -/

/-- Both triangle inequalities can be tight.  The final error four is exactly
the sum of packetwise budgets one and two and sketch budget one. -/
theorem scalar_twoStage_bound_is_tight :
    let exact : Fin 2 → ℝ := ![3, 5]
    let approximate : Fin 2 → ℝ := ![2, 3]
    let localBudget : Fin 2 → ℝ := ![1, 2]
    let sketch : ℝ := 4
    let sketchBudget : ℝ := 1
    (∀ step,
      |exact step - approximate step| ≤ localBudget step) ∧
      |aggregate approximate - sketch| ≤ sketchBudget ∧
      |aggregate exact - sketch| =
        (∑ step, localBudget step) + sketchBudget := by
  norm_num [aggregate, Fin.sum_univ_two]

/-- Packet errors can cancel in the aggregate.  The local sum is therefore a
safe upper bound, not in general an equality. -/
theorem opposing_packet_errors_make_local_sum_strict :
    let exact : Fin 2 → ℝ := ![1, -1]
    let approximate : Fin 2 → ℝ := ![0, 0]
    |aggregate exact - aggregate approximate| = 0 ∧
      (∑ step, |exact step - approximate step|) = 2 := by
  norm_num [aggregate, Fin.sum_univ_two]

/-- Perfect packetwise approximation alone does not control a downstream
sketch.  The second-stage certificate cannot be omitted. -/
theorem zero_local_error_does_not_bound_bad_sketch :
    let exact : Unit → ℝ := fun _ ↦ 0
    let approximate : Unit → ℝ := fun _ ↦ 0
    let sketch : ℝ := 1
    (∀ step, |exact step - approximate step| = 0) ∧
      |aggregate exact - sketch| = 1 := by
  norm_num [aggregate]

#print axioms norm_aggregate_sub_le_sum_norm
#print axioms twoStageSketch_error_le
#print axioms tailEnergy_add_sketchResidual_bounds_final
#print axioms scalar_twoStage_bound_is_tight
#print axioms opposing_packet_errors_make_local_sum_strict
#print axioms zero_local_error_does_not_bound_bad_sketch

end TwoStageSketchApproximation

end Mettapedia.MachineLearning.ContinualLearning
