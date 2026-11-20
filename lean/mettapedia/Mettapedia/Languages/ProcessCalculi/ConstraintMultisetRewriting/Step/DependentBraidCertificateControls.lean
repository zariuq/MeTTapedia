import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentBraidCertificate
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentExecutionBraidControls

/-!
# A shared certificate does not erase the observer's transport

The certified pair of executions really publishes different raw variable
positions. Its typed-row comparison includes the retained boundary map.
Reordering the input helper layout also changes the certificate's index.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BraidCertificate.Controls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull.Controls ExecutionBraidControls

def rawIndex (state : State Tower.rules Nat) : Option Nat :=
  match (state.label 1).2.code with
  | .var index => some index.val
  | _ => none

theorem raw_observation_differs : rawIndex schedules.abc.run.last ≠ rawIndex schedules.cba.run.last := by
  decide

theorem typed_observation_transports :
    schedules.cba.run.last.label 1 =
      (schedules.abc.run.last.label 1).reindex (checked schedules).boundary :=
  typed_rows schedules (checked schedules) 1

theorem rotated : (helperTransport setting.levels Nat).SixSchedules
    DependentRun.Controls.second DependentRun.Controls.first DependentRun.Controls.third :=
  ⟨schedules.bac, schedules.bca, schedules.abc, schedules.acb, schedules.cba, schedules.cab⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BraidCertificate.Controls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BraidCertificate.Controls.raw_observation_differs
