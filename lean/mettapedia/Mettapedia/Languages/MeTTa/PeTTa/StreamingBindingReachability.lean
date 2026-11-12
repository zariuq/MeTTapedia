import Mettapedia.Languages.MeTTa.PeTTa.StreamingBindingPreservation
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintReadout

/-!
# Actual request prefixes earn the binding hypotheses

Entry, every bounded endpoint and every pending task retain the proved
streaming invariant. Source readout therefore obtains idempotence from the
actual reached answer, rather than a runtime check or a supplied conclusion.
The subtype interfaces carry propositions that execution erases.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Streaming.BindingInvariant

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

theorem enter_refines (world : World) (expression : Atom) : stateRefines [] (enter world expression) := by
  have valid : Unifying.Idempotent [] := by simp [Unifying.Idempotent,Subst.lookup]
  refine ⟨(agenda_cons _ _ _).mpr ⟨⟨?_,by simp [framesRefine]⟩,by simp [agendaRefines]⟩,by simp [enter]⟩
  simpa only [Unifying.ControlRefines,Unifying.BindingRefines] using And.intro valid (Unifying.Refines.refl valid)

theorem every_request_prefix_refines (registry : SpaceSemantics.Program) (fuel : Nat)
    (world : World) (expression : Atom) : stateRefines [] (advance registry fuel (enter world expression)) :=
  advance_refines registry fuel [] (enter world expression) (enter_refines world expression)

theorem every_reachable_request_refines {registry : SpaceSemantics.Program} {world : World}
    {expression : Atom} {reached : State}
    (path : Relation.ReflTransGen (Transition registry) (enter world expression) reached) :
    stateRefines [] reached := path_refines path (enter_refines world expression)

theorem reached_answer_idempotent (registry : SpaceSemantics.Program) (fuel : Nat)
    (world : World) (expression : Atom) (answer : Unifying.Answer)
    (returned : answer ∈ (advance registry fuel (enter world expression)).answers) :
    Unifying.Idempotent answer.bindings :=
  ((every_request_prefix_refines registry fuel world expression).2 answer returned).1

theorem reached_task_refines (registry : SpaceSemantics.Program) (fuel : Nat)
    (world : World) (expression : Atom) (task : Task)
    (pending : Job.execute task ∈ (advance registry fuel (enter world expression)).agenda) :
    Unifying.ControlRefines [] task.control :=
  ((every_request_prefix_refines registry fuel world expression).1 _ pending).1

theorem reached_evaluation_idempotent (registry : SpaceSemantics.Program) (fuel : Nat)
    (world : World) (expression : Atom) (bindings : Subst) (body : Atom) (caller : List Frame)
    (pending : Job.execute ⟨.evaluate bindings body,caller⟩ ∈ (advance registry fuel (enter world expression)).agenda) :
    Unifying.Idempotent bindings := by
  have valid := reached_task_refines registry fuel world expression ⟨.evaluate bindings body,caller⟩ pending
  simp only [Unifying.ControlRefines] at valid
  exact valid.1

theorem reached_answer_source_readout (registry : SpaceSemantics.Program) (fuel : Nat)
    (world : World) (expression : Atom) (answer : Unifying.Answer)
    (returned : answer ∈ (advance registry fuel (enter world expression)).answers)
    (constraints : EagerDFS.Destination.Equations) (model : EagerDFS.Destination.Environment)
    (represented : OutputPlan.ConstraintAdmission.Represents constraints answer.bindings)
    (resolved : EagerDFS.Destination.resolve constraints = some model) (observations : List Atom) :
    Mettapedia.Languages.ProcessCalculi.MORK.VariantReadout.joint (observations.map (EagerDFS.Destination.read model)) =
      Mettapedia.Languages.ProcessCalculi.MORK.VariantReadout.joint (observations.map (Unifying.resolve answer.bindings)) :=
  UnifyingConstraintPresentation.source_runtime_joint_readout constraints answer.bindings model represented
    (reached_answer_idempotent registry fuel world expression answer returned) resolved observations

def enterRefined (world : World) (expression : Atom) : {state : State // stateRefines [] state} :=
  ⟨enter world expression,enter_refines world expression⟩

def advanceRefined (registry : SpaceSemantics.Program) (fuel : Nat) {initial : Subst}
    (source : {state : State // stateRefines initial state}) : {state : State // stateRefines initial state} :=
  ⟨advance registry fuel source.val,advance_refines registry fuel initial source.val source.property⟩

end Mettapedia.Languages.MeTTa.PeTTa.Streaming.BindingInvariant
