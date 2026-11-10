import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RecordedChoice
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EscapeEventLifting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PreparedPublicationsControls

/-!
# Choice recording and escape use the admitted-event layer

Empty choice fibres create no event. Different actual chosen answers remain
different records. The existing store-changing escape instance updates its
public names and is the unique observer lift above its forgotten run.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RecordedChoice.EventControls

open Interface
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RecordedChoice.Controls
open AdmissionObservationCover.Controls (World)
open SettlementCoverage.Controls (allFalse quiet_admitted)

theorem empty_choices_have_no_event (target : Unit) :
    ¬ Nonempty (noChoices.step.effectCore.Event noChoices.step.eventAdmission () target) := by
  rintro ⟨event⟩
  have impossible : Empty := event.firing.2
  exact nomatch impossible

def run (choice : World → World) : chooseAny.step.Run () :=
  .cons ⟨(), choice⟩ (quiet_admitted id) (.nil _)

theorem observer_records_choice (choice : World → World) :
    chooseAny.record (run choice) = FreeMonoid.of ⟨(), ⟨(), choice⟩⟩ := by
  rw [Choices.record_eq_word]
  rfl

theorem choices_remain_distinct : chooseAny.record (run id) ≠ chooseAny.record (run (fun _ => allFalse)) := by
  intro same
  rw [Choices.record_eq_word, Choices.record_eq_word] at same
  have words := congrArg FreeMonoid.toList same
  change ([⟨(), ⟨(), (id : World → World)⟩⟩] : List ((_ : Unit) × (Σ _ : Unit, World → World))) =
    [⟨(), ⟨(), (fun _ : World => allFalse)⟩⟩] at words
  have first := List.cons.inj words |>.1
  have choices := eq_of_heq (Sigma.mk.inj first).2
  have maps : (id : World → World) = fun _ => allFalse := eq_of_heq (Sigma.mk.inj choices).2
  have different := congrFun (congrFun maps (fun _ => true)) (0 : Fin 2)
  cases different

theorem observation_erases (choice : World → World) :
    chooseAny.observer.forget.mapPath
      (chooseAny.observer.decorate ((run choice).eventPath chooseAny.step)
        (1 : FreeMonoid ((_ : Unit) × (Σ f : Unit, chooseAny.Choice (s := ()) f)))) =
      (run choice).eventPath chooseAny.step :=
  EventObserver.forget_decorate _ _ _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RecordedChoice.EventControls

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EscapeEventControls

open PublicationTransportControls

abbrev P := program strict
abbrev D := strictEscape

def start : Escaped P := ⟨[], [true], []⟩

theorem admitted : P.Admits (s := []) false :=
  ⟨Presentation.Controls.prepares [] (), by simp [strict]⟩

def run : D.step.Run start := .cons false admitted (.nil _)

theorem published_names : run.last.names = [true, false] := rfl

theorem observer_agrees :
    P.observeRunEnd D.eventObserver (D.forget run) (start.names, start.record) =
      ⟨run.last.state, (run.last.names, run.last.record)⟩ := D.eventObserver_run_agrees run

theorem event_path_erases :
    D.eventObserver.forget.mapPath (D.liftEvents.mapPath (run.eventPath D.step)) =
      P.endpointPath ⟨D.forget run, D.forgotten_last run⟩ := D.lifted_run_erases run

theorem actual_lift_unique (other : Quiver.PathStar (D.observedState start))
    (erases : D.eventObserver.forget.pathStar (D.observedState start) other =
      ⟨run.last.state, P.endpointPath ⟨D.forget run, D.forgotten_last run⟩⟩) :
    other = D.liftEvents.pathStar start ⟨run.last, run.eventPath D.step⟩ :=
  D.escaping_run_unique run other erases

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EscapeEventControls
