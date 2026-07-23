import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Dynamics

/-!
# Finite simultaneous damped settling

This module isolates the execution semantics of a fixed-depth workspace
settling loop.  At every sweep, all candidates and gates are captured from
one pre-write workspace and one simultaneous averaged interpolation is then
applied.  Repeating that sweep for a positive configured depth is exactly a
finite iterate of the existing `GatedOperatorFamily.step` semantics.

The result is structural.  Memory, control, masks, and slow parameters are
treated as fixed inside the supplied kernel, and no floating-point,
convergence, or trained-parameter claim is made.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Finset Function

universe uSlot uOperator uContent

/-- A recurrence depth accepted by the implemented workspace configuration. -/
structure PositiveRecurrenceDepth where
  value : ℕ
  positive : 0 < value

namespace PositiveRecurrenceDepth

theorem value_ne_zero (depth : PositiveRecurrenceDepth) : depth.value ≠ 0 :=
  Nat.ne_of_gt depth.positive

end PositiveRecurrenceDepth

/-- One closed settling kernel after memory, control, masks, and slow
parameters have been fixed.  A candidate is broadcast across slots, while its
write gate may depend on the candidate and the destination slot. -/
structure BroadcastDampedSweepKernel
    (Slot : Type uSlot) (Operator : Type uOperator) (Content : Type uContent) where
  candidate : Operator → Workspace Slot Content → Content
  gate : Operator → Workspace Slot Content → Content → Slot → ℝ

/-- The pre-write snapshot used by one simultaneous sweep.  Every candidate
and gate in the snapshot was computed from the same `before` workspace. -/
structure DampedSweepSnapshot
    (Slot : Type uSlot) (Operator : Type uOperator) (Content : Type uContent) where
  before : Workspace Slot Content
  candidates : Operator → Content
  gates : Operator → Slot → ℝ

namespace BroadcastDampedSweepKernel

variable {Slot : Type uSlot} {Operator : Type uOperator} {Content : Type uContent}
  [operatorFintype : Fintype Operator]
  [NormedAddCommGroup Content] [NormedSpace ℝ Content]

/-- Capture all operator candidates and gates before writing any slot. -/
noncomputable def capture
    (kernel : BroadcastDampedSweepKernel Slot Operator Content)
    (workspace : Workspace Slot Content) :
    DampedSweepSnapshot Slot Operator Content where
  before := workspace
  candidates := fun operator => kernel.candidate operator workspace
  gates := fun operator slot =>
    kernel.gate operator workspace (kernel.candidate operator workspace) slot

/-- Apply one captured simultaneous averaged interpolation. -/
noncomputable def applySnapshot
    (snapshot : DampedSweepSnapshot Slot Operator Content) :
    Workspace Slot Content :=
  fun slot => snapshot.before slot +
    GatedOperatorFamily.operatorAverageScale (Operator := Operator) •
      ∑ operator, snapshot.gates operator slot •
        (snapshot.candidates operator - snapshot.before slot)

/-- One source-shaped sweep: capture first, then perform one simultaneous
write from that immutable snapshot. -/
noncomputable def sourceStep
    (kernel : BroadcastDampedSweepKernel Slot Operator Content)
    (workspace : Workspace Slot Content) : Workspace Slot Content :=
  applySnapshot (kernel.capture workspace)

/-- The broadcast sweep kernel as the existing general gated-operator family.
The entire workspace is the read, the candidate is the latent, and the write
broadcasts that latent to every slot. -/
noncomputable def asGatedOperatorFamily
    (kernel : BroadcastDampedSweepKernel Slot Operator Content) :
    GatedOperatorFamily Slot Operator Content (Workspace Slot Content) Content where
  read := fun _operator workspace => workspace
  transform := fun operator workspace => kernel.candidate operator workspace
  gate := kernel.gate
  write := fun _operator _workspace candidate _slot => candidate

/-- The independently stated capture-and-apply sweep is exactly the existing
simultaneous `GatedOperatorFamily.step`. -/
theorem sourceStep_eq_gatedStep
    (kernel : BroadcastDampedSweepKernel Slot Operator Content)
    (workspace : Workspace Slot Content) :
    kernel.sourceStep workspace = kernel.asGatedOperatorFamily.step workspace := by
  funext slot
  rfl

/-- Execute exactly `depth` simultaneous sweeps, updating the workspace only
between complete sweeps. -/
noncomputable def sourceSettle
    (kernel : BroadcastDampedSweepKernel Slot Operator Content) :
    ℕ → Workspace Slot Content → Workspace Slot Content
  | 0, workspace => workspace
  | depth + 1, workspace => sourceSettle kernel depth (kernel.sourceStep workspace)

/-- Fixed-depth source execution is exactly finite iteration of one captured
simultaneous sweep. -/
theorem sourceSettle_eq_iterate
    (kernel : BroadcastDampedSweepKernel Slot Operator Content)
    (depth : ℕ) (workspace : Workspace Slot Content) :
    kernel.sourceSettle depth workspace =
      (kernel.sourceStep^[depth]) workspace := by
  induction depth generalizing workspace with
  | zero => rfl
  | succ depth ih =>
      rw [sourceSettle, Function.iterate_succ_apply]
      exact ih (kernel.sourceStep workspace)

/-- Fixed-depth source execution is also exactly iteration of the existing
gated-family step. -/
theorem sourceSettle_eq_gatedStep_iterate
    (kernel : BroadcastDampedSweepKernel Slot Operator Content)
    (depth : ℕ) (workspace : Workspace Slot Content) :
    kernel.sourceSettle depth workspace =
      (kernel.asGatedOperatorFamily.step^[depth]) workspace := by
  rw [kernel.sourceSettle_eq_iterate]
  congr 1

/-- The state trace contains the initial workspace and the result after every
complete sweep, hence exactly `depth + 1` states. -/
noncomputable def sourceTrace
    (kernel : BroadcastDampedSweepKernel Slot Operator Content)
    : ℕ → Workspace Slot Content → List (Workspace Slot Content)
  | 0, workspace => [workspace]
  | depth + 1, workspace =>
      workspace :: sourceTrace kernel depth (kernel.sourceStep workspace)

@[simp] theorem sourceTrace_length
    (kernel : BroadcastDampedSweepKernel Slot Operator Content)
    (depth : ℕ) (workspace : Workspace Slot Content) :
    (kernel.sourceTrace depth workspace).length = depth + 1 := by
  induction depth generalizing workspace with
  | zero => rfl
  | succ depth ih =>
      simp [sourceTrace, ih]

/-- A positive-depth trace exposes the pre-write workspace first and then the
trace beginning at exactly one complete simultaneous sweep. -/
@[simp] theorem sourceTrace_succ_eq
    (kernel : BroadcastDampedSweepKernel Slot Operator Content)
    (depth : ℕ) (workspace : Workspace Slot Content) :
    kernel.sourceTrace (depth + 1) workspace =
      workspace :: kernel.sourceTrace depth (kernel.sourceStep workspace) := rfl

/-- The last trace state is the exact configured-depth settling result. -/
theorem sourceTrace_getLast?_eq
    (kernel : BroadcastDampedSweepKernel Slot Operator Content)
    (depth : ℕ) (workspace : Workspace Slot Content) :
    (kernel.sourceTrace depth workspace).getLast? =
      some (kernel.sourceSettle depth workspace) := by
  induction depth generalizing workspace with
  | zero => rfl
  | succ depth ih =>
      cases depth with
      | zero => rfl
      | succ remaining =>
          simpa only [sourceTrace, sourceSettle, List.getLast?_cons_cons]
            using ih (kernel.sourceStep workspace)

/-- A positive configured depth performs at least the first simultaneous
sweep; zero-sweep behavior is excluded by the configuration witness. -/
theorem sourceSettle_positiveDepth_eq
    (kernel : BroadcastDampedSweepKernel Slot Operator Content)
    (depth : PositiveRecurrenceDepth) (workspace : Workspace Slot Content) :
    kernel.sourceSettle depth.value workspace =
      kernel.sourceSettle (depth.value - 1) (kernel.sourceStep workspace) := by
  rcases depth with ⟨value, hvalue⟩
  cases value with
  | zero => simp at hvalue
  | succ remaining => rfl

end BroadcastDampedSweepKernel

/-! ## Executable positive and negative fixtures -/

namespace FiniteDampedSettlingFixtures

abbrev OneSlot := Fin 1
abbrev TwoOperators := Fin 2

/-- A nonlinear state-dependent two-operator fixture.  Operator zero proposes
three; operator one proposes twice the current slot; both gates are one. -/
noncomputable def nonlinearBroadcastKernel :
    BroadcastDampedSweepKernel OneSlot TwoOperators ℝ where
  candidate := fun operator workspace =>
    if operator = 0 then 3 else 2 * workspace 0
  gate := fun _operator _workspace _candidate _slot => 1

private noncomputable def initialOne : Workspace OneSlot ℝ := fun _slot => 1

theorem nonlinearBroadcastKernel_step_formula
    (workspace : Workspace OneSlot ℝ) :
    nonlinearBroadcastKernel.sourceStep workspace 0 = workspace 0 + 3 / 2 := by
  norm_num [BroadcastDampedSweepKernel.sourceStep,
    BroadcastDampedSweepKernel.capture,
    BroadcastDampedSweepKernel.applySnapshot,
    GatedOperatorFamily.operatorAverageScale, nonlinearBroadcastKernel,
    Fin.sum_univ_two]

/-- Two configured simultaneous sweeps are genuinely two updates, not an
equilibrium alias or a one-step abbreviation. -/
theorem depthTwo_simultaneous_result :
    nonlinearBroadcastKernel.sourceSettle 2 initialOne 0 = 4 := by
  rw [BroadcastDampedSweepKernel.sourceSettle]
  rw [BroadcastDampedSweepKernel.sourceSettle]
  rw [BroadcastDampedSweepKernel.sourceSettle]
  rw [nonlinearBroadcastKernel_step_formula]
  rw [nonlinearBroadcastKernel_step_formula]
  norm_num [initialOne]

theorem depthOne_simultaneous_result :
    nonlinearBroadcastKernel.sourceSettle 1 initialOne 0 = 5 / 2 := by
  rw [BroadcastDampedSweepKernel.sourceSettle]
  rw [BroadcastDampedSweepKernel.sourceSettle]
  rw [nonlinearBroadcastKernel_step_formula]
  norm_num [initialOne]

/-- Off-by-one depth is observable in the same fixture. -/
theorem depthOne_ne_depthTwo :
    nonlinearBroadcastKernel.sourceSettle 1 initialOne ≠
      nonlinearBroadcastKernel.sourceSettle 2 initialOne := by
  intro heq
  have hcoordinate := congrFun heq 0
  rw [depthOne_simultaneous_result, depthTwo_simultaneous_result] at hcoordinate
  norm_num at hcoordinate

/-- An alternative sequential interpretation updates from operator zero
before recomputing operator one's state-dependent candidate. -/
noncomputable def sequentialTwoOperatorStep
    (workspace : Workspace OneSlot ℝ) : Workspace OneSlot ℝ :=
  let afterFirst : Workspace OneSlot ℝ := fun slot =>
    workspace slot + (1 / 2 : ℝ) * (3 - workspace slot)
  fun slot => afterFirst slot +
    (1 / 2 : ℝ) * (2 * afterFirst 0 - afterFirst slot)

/-- Sequential writes are not a valid reading of the simultaneous source
loop: they disagree after one sweep on a state-dependent fixture. -/
theorem sequential_write_ne_simultaneous_snapshot :
    sequentialTwoOperatorStep initialOne ≠
      nonlinearBroadcastKernel.sourceStep initialOne := by
  intro heq
  have hcoordinate := congrFun heq 0
  norm_num [sequentialTwoOperatorStep, initialOne,
    nonlinearBroadcastKernel_step_formula] at hcoordinate

def depthTwo : PositiveRecurrenceDepth := ⟨2, by norm_num⟩

theorem depthTwo_is_positive : 0 < depthTwo.value := depthTwo.positive

end FiniteDampedSettlingFixtures

#print axioms BroadcastDampedSweepKernel.sourceStep_eq_gatedStep
#print axioms BroadcastDampedSweepKernel.sourceSettle_eq_iterate
#print axioms BroadcastDampedSweepKernel.sourceSettle_eq_gatedStep_iterate
#print axioms BroadcastDampedSweepKernel.sourceTrace_succ_eq
#print axioms BroadcastDampedSweepKernel.sourceTrace_getLast?_eq
#print axioms FiniteDampedSettlingFixtures.depthTwo_simultaneous_result
#print axioms FiniteDampedSettlingFixtures.depthOne_ne_depthTwo
#print axioms FiniteDampedSettlingFixtures.sequential_write_ne_simultaneous_snapshot

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
