import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentExecutionBraid
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentThreeEventControls

/-!
# Six actual publication orders and their complete execution braid

The first event publishes x : X, p : Id X x x at occurrence one. The other
events publish independent points at occurrences two and three. All six
orders are admitted by the actual step; the two full exchange routes retain
the same event permutation and the same complete helper comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ExecutionBraidControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull.Controls TelescopeControls DependentRun.Controls

private theorem quiet_admitted {state : State Tower.rules Nat} (candidate : HelperFiring setting.levels Nat state)
    (shapes : candidate.toFiring.Shapes)
    (enabled : MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : Nat => ()) state.present
      (candidate.toFiring.selection.commit (T := Unit)))
    (information : candidate.toFiring.information = [])
    (guards : candidate.toFiring.guards = []) (queries : candidate.toFiring.queries = []) :
    (helperStep setting.levels Nat).Admits candidate := by
  refine ⟨shapes, enabled, ⟨_, 𝟙 _, ?_⟩, ?_⟩
  · rw [information]
    exact Frames.models_nil _
  · intro observer solution solved
    constructor
    · rw [guards]
      exact Frames.models_nil _
    · intro query member
      rw [queries] at member
      exact False.elim (List.not_mem_nil member)

private theorem residual_shapes {state : State Tower.rules Nat}
    (first second : HelperFiring setting.levels Nat state) (accepted : (helperStep setting.levels Nat).Admits first)
    (shapes : second.toFiring.Shapes) : (helperResidual first accepted second).toFiring.Shapes :=
  Natural.shapes_move (Helpers.lift first.helpers.weaken second.helpers) second.data shapes

theorem third_initially_admitted : (helperStep setting.levels Nat).Admits third := by
  apply quiet_admitted third
  · refine ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, ?_⟩
    intro made member
    obtain rfl := List.mem_singleton.mp member
    exact Make.ofRow_wellTyped pointRow
  · apply (enabled_iff _).mpr
    decide
  · rfl
  · rfl
  · rfl

def offered (index : Fin 3) : HelperFiring setting.levels Nat baseState :=
  Fin.cases first (fun later => Fin.cases second (fun _ => third) later) index

set_option maxHeartbeats 1000000 in
theorem schedule (a b c : Fin 3) (apart : [a, b, c].Nodup) :
    (helperTransport setting.levels Nat).TripleSchedule (offered a) (offered b) (offered c) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp at apart
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · first | exact firstAdmitted | exact secondAdmitted | exact third_initially_admitted
    · apply quiet_admitted
      · apply residual_shapes
        first | exact firstAdmitted.1 | exact secondAdmitted.1 | exact third_initially_admitted.1
      · apply (enabled_iff _).mpr
        decide
      · rfl
      · rfl
      · rfl
    · apply quiet_admitted
      · apply residual_shapes
        apply residual_shapes
        first | exact firstAdmitted.1 | exact secondAdmitted.1 | exact third_initially_admitted.1
      · apply (enabled_iff _).mpr
        decide
      · rfl
      · rfl
      · rfl

theorem schedules : (helperTransport setting.levels Nat).SixSchedules first second third :=
  ⟨schedule 0 1 2 (by decide), schedule 0 2 1 (by decide),
    schedule 1 0 2 (by decide), schedule 1 2 0 (by decide),
    schedule 2 0 1 (by decide), schedule 2 1 0 (by decide)⟩

theorem actual_three_cell : (helperTransport setting.levels Nat).Cell baseState [first, second, third] :=
  schedules.cell

theorem complete_braid :
    Transport.RunRearrangement.events (helperTransport setting.levels Nat) (ExecutionBraid.leftRoute schedules) =
      Transport.RunRearrangement.events (helperTransport setting.levels Nat) (ExecutionBraid.rightRoute schedules) ∧
    RunStateGroupoid.endpointMap setting.levels Nat (ExecutionBraid.leftRoute schedules) =
      RunStateGroupoid.endpointMap setting.levels Nat (ExecutionBraid.rightRoute schedules) :=
  ⟨ExecutionBraid.event_braid schedules, ExecutionBraid.boundary_braid schedules⟩

theorem both_orders_publish_all_three :
    schedules.abc.run.last.present = {1, 2, 3} ∧ schedules.cba.run.last.present = {1, 2, 3} := by decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ExecutionBraidControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ExecutionBraidControls.actual_three_cell
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ExecutionBraidControls.complete_braid
