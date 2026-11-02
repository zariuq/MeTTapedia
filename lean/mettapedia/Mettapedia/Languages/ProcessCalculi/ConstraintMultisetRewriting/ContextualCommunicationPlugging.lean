import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationReflection
import Mettapedia.OSLF.Syntax.RhoScopedChannelSeparation

/-!
# Communication through the original open continuation and name classes

The source instance retains a continuation under the received name plus its
ambient scope. Its target uses the original capture-avoiding receive operation.
Normalizing source parallel components gives two consumed occurrences, while
output normalization follows the complete resulting process class.

Channel agreement is equality in the declared source name quotient. It is
recovered from an actual CMR firing through no-invention, not assumed from a
particular matching procedure or from raw syntactic equality.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationPlugging

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoScopedInstanceReadout RhoScopedParallelEvents RhoScopedParallelInventory
open RhoIntrinsicCanonicalBag RhoScopedConstructorInventory RhoIntrinsicReadback
open ContextualCommunicationProfiles ContextualCommunicationAdequacy ContextualCommunicationReflection
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

def communicationRoot {context : Ctx sig} (channel : Term sig context Srt.nm)
    (payload : Term sig context Srt.pr) (body : Term sig (Srt.nm :: context) Srt.pr) :
    ContextualCommunicationProfiles.Root core context :=
  ⟨⟨.communication, trivial⟩, communication channel payload body⟩

theorem communication_source {context : Ctx sig} (channel : Term sig context Srt.nm)
    (payload : Term sig context Srt.pr) (body : Term sig (Srt.nm :: context) Srt.pr) :
    (communicationRoot channel payload body).source =
      join (outputClass (project channel) (project payload)) (inputClass (project channel) (project body)) :=
  Communication.source_class (communication channel payload body)

theorem communication_target {context : Ctx sig} (channel : Term sig context Srt.nm)
    (payload : Term sig context Srt.pr) (body : Term sig (Srt.nm :: context) Srt.pr) :
    (communicationRoot channel payload body).target = receive (quote (project payload)) (project body) :=
  Communication.target_class (communication channel payload body)

theorem communication_target_is_capture_avoiding {context : Ctx sig}
    (channel : Term sig context Srt.nm) (payload : Term sig context Srt.pr)
    (body : Term sig (Srt.nm :: context) Srt.pr) :
    (communicationRoot channel payload body).target =
      project (bind (receiveRaw (quoteRaw payload)) body) := by
  rw [communication_target, quote_project, receive_project]

theorem normalized_card {context : Ctx sig} (process : Process context) :
    (normalized process).card = (components process).card := by
  have counted := congrArg Multiset.card (values_read process)
  simpa only [normalized, values, Multiset.card_map] using counted

theorem communication_takes_two_occurrences {context : Ctx sig}
    (channel : Term sig context Srt.nm) (payload : Term sig context Srt.pr)
    (body : Term sig (Srt.nm :: context) Srt.pr) :
    (instanceRule (communicationRoot channel payload body)).take.length = 2 := by
  change (normalized (communicationRoot channel payload body).source).toList.length = 2
  rw [Multiset.length_toList, normalized_card, communication_source,
    join_components, output_components, input_components, Multiset.card_add]
  rfl

theorem communication_has_occurrence_execution {context : Ctx sig}
    (channel : Term sig context Srt.nm) (payload : Term sig context Srt.pr)
    (body : Term sig (Srt.nm :: context) Srt.pr) :
    ∃ before after : Configuration (Process context) (ContextualCommunicationProfiles.Occurrence context),
      before.equations = [] ∧ labels ContextualCommunicationProfiles.label before.present =
        normalized (join (outputClass (project channel) (project payload))
          (inputClass (project channel) (project body))) ∧
      InterpretedStep core (ContextualCommunicationProfiles.action context).identity before after ∧
      labels ContextualCommunicationProfiles.label after.present =
        normalized (project (bind (receiveRaw (quoteRaw payload)) body)) := by
  have event := root_has_declared_source_step (communicationRoot channel payload body)
  rw [communication_source, communication_target_is_capture_avoiding] at event
  exact every_source_step_has_occurrence_execution _ _ event

theorem interpreted_communication_requires_channel_agreement {context : Ctx sig}
    (assignment : Sub sig context context)
    (before after : Configuration (Process context) (ContextualCommunicationProfiles.Occurrence context))
    (sender receiver : Name context) (payload : Process context)
    (body : Process (Srt.nm :: context))
    (sourceRead : observe assignment before.present =
      join (outputClass sender payload) (inputClass receiver body))
    (executed : InterpretedStep core assignment before after) : sender = receiver := by
  have event := executed.no_invention
  rw [sourceRead] at event
  exact RhoScopedChannelSeparation.channels_agree_of_original_reaction sender receiver payload body event

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationPlugging
