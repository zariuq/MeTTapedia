import Mettapedia.CognitiveArchitecture.TriggeredMindAgentSpace
import Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute

/-!
# Realizing recurrent GSLT routes as triggered mind-agent occurrences

A checked recurrent controller proves legal GSLT execution and productive
finite prefixes.  It does not by itself prove that a triggered cognitive space
generated corresponding work.  This module supplies the independent bridge.

A `Codec` maps each temporally indexed route occurrence to one authored
trigger/resident occurrence and proves that the space generated it at the same
index.  Bounded scheduler selection then transports over the generated route.
Generation, selection, semantic recurrence, service fulfillment, and payment
remain distinct contracts.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.TriggeredOccurrenceRouteRealization

noncomputable section

open Mettapedia.CognitiveArchitecture.TriggeredMindAgentSpace
open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute
open Mettapedia.GSLT.Dynamics.SemanticPhysicalRouteBinding
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

universe uAuthority uCertificate uTrigger uResident

/-! ## Independent triggered-space realization -/

/-- A checked route occurrence realizes as triggered work only through an
independently proved space-generation codec. -/
structure Codec
    {AuthorityId : Type uAuthority} {theory : GSLT}
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (claim : RecurrentTraceClaim theory stepAuthority.Certificate)
    {Trigger : Type uTrigger} {Resident : Type uResident}
    (space : Space Trigger Resident) (trace : Space.TriggerTrace Trigger)
    (represents : TraceLink theory stepAuthority.Certificate ->
      Trigger -> Resident -> Prop) where
  triggerOf : ControlledOccurrence theory stepAuthority.Certificate -> Trigger
  residentOf : ControlledOccurrence theory stepAuthority.Certificate -> Resident
  semanticBinding : forall occurrence,
    represents occurrence.action (triggerOf occurrence) (residentOf occurrence)
  generated : forall occurrence,
    space.Generated trace occurrence.index
      (Space.occurrenceAt occurrence.index
        (triggerOf occurrence) (residentOf occurrence))

namespace Codec

variable {AuthorityId : Type uAuthority} {theory : GSLT}
variable {stepAuthority : StepAuthority.{uAuthority, uCertificate}
  AuthorityId theory}
variable {claim : RecurrentTraceClaim theory stepAuthority.Certificate}
variable {Trigger : Type uTrigger} {Resident : Type uResident}
variable {space : Space Trigger Resident} {trace : Space.TriggerTrace Trigger}
variable {represents : TraceLink theory stepAuthority.Certificate ->
  Trigger -> Resident -> Prop}

/-- Realize one exact route occurrence as one exact triggered-space
occurrence. -/
def realize
    (codec : Codec stepAuthority claim space trace represents)
    (occurrence : ControlledOccurrence theory stepAuthority.Certificate) :
    TriggeredOccurrence Trigger Resident :=
  Space.occurrenceAt occurrence.index
    (codec.triggerOf occurrence) (codec.residentOf occurrence)

@[simp] theorem realize_generatedAt
    (codec : Codec stepAuthority claim space trace represents)
    (occurrence : ControlledOccurrence theory stepAuthority.Certificate) :
    (codec.realize occurrence).generatedAt = occurrence.index :=
  rfl

/-- The realized trigger/resident pair denotes the checked controller action
under the independently authored representation relation. -/
theorem realize_represents
    (codec : Codec stepAuthority claim space trace represents)
    (occurrence : ControlledOccurrence theory stepAuthority.Certificate) :
    represents occurrence.action (codec.realize occurrence).trigger
      (codec.realize occurrence).resident := by
  change represents occurrence.action
    (codec.triggerOf occurrence) (codec.residentOf occurrence)
  exact codec.semanticBinding occurrence

/-- Codec realization is genuine authored generation, not merely a conversion
between record shapes. -/
theorem realize_generated
    (codec : Codec stepAuthority claim space trace represents)
    (occurrence : ControlledOccurrence theory stepAuthority.Certificate) :
    space.Generated trace (codec.realize occurrence).generatedAt
      (codec.realize occurrence) := by
  change space.Generated trace occurrence.index
    (Space.occurrenceAt occurrence.index
      (codec.triggerOf occurrence) (codec.residentOf occurrence))
  exact codec.generated occurrence

/-- Temporal occurrence identity survives triggered-space realization even if
the same trigger and resident repeat forever. -/
theorem realize_distinct_of_index_ne
    (codec : Codec stepAuthority claim space trace represents)
    {first second : ControlledOccurrence theory stepAuthority.Certificate}
    (different : first.index ≠ second.index) :
    codec.realize first ≠ codec.realize second := by
  intro equalOccurrences
  exact different
    (congrArg TriggeredOccurrence.generatedAt equalOccurrences)

/-- Realize every occurrence retained by a finite checked route. -/
def realizeRoute
    [DecidableEq theory.Term]
    (codec : Codec stepAuthority claim space trace represents)
    (accepting : theory.Term -> Bool)
    (route : FiniteRoute (auditedRevisionTheory stepAuthority accepting)
      (ControlledOccurrence theory stepAuthority.Certificate) claim.root) :
    List (TriggeredOccurrence Trigger Resident) :=
  route.occurrences.map codec.realize

/-- A realized route member retains a source checked occurrence and the
authored semantic relation connecting its action to the generated work. -/
theorem mem_realizeRoute_has_source
    [DecidableEq theory.Term]
    (codec : Codec stepAuthority claim space trace represents)
    (accepting : theory.Term -> Bool)
    (route : FiniteRoute (auditedRevisionTheory stepAuthority accepting)
      (ControlledOccurrence theory stepAuthority.Certificate) claim.root)
    {generated : TriggeredOccurrence Trigger Resident}
    (member : generated ∈ codec.realizeRoute accepting route) :
    exists source, source ∈ route.occurrences /\
      codec.realize source = generated /\
      represents source.action generated.trigger generated.resident := by
  rcases List.mem_map.mp member with ⟨source, sourceMember, realized⟩
  refine ⟨source, sourceMember, realized, ?_⟩
  rw [← realized]
  exact codec.realize_represents source

/-- Every member of a realized route was generated by the authored space at
its retained epoch. -/
theorem mem_realizeRoute_generated
    [DecidableEq theory.Term]
    (codec : Codec stepAuthority claim space trace represents)
    (accepting : theory.Term -> Bool)
    (route : FiniteRoute (auditedRevisionTheory stepAuthority accepting)
      (ControlledOccurrence theory stepAuthority.Certificate) claim.root)
    {generated : TriggeredOccurrence Trigger Resident}
    (member : generated ∈ codec.realizeRoute accepting route) :
    space.Generated trace generated.generatedAt generated := by
  rcases List.mem_map.mp member with ⟨occurrence, _member, rfl⟩
  exact codec.realize_generated occurrence

/-- A bounded generated-work selector transports pointwise over every
realized checked route. -/
theorem mem_realizeRoute_selected
    [DecidableEq theory.Term]
    (codec : Codec stepAuthority claim space trace represents)
    (accepting : theory.Term -> Bool)
    (route : FiniteRoute (auditedRevisionTheory stepAuthority accepting)
      (ControlledOccurrence theory stepAuthority.Certificate) claim.root)
    {selectionWindow : Nat}
    {selected : Nat -> TriggeredOccurrence Trigger Resident -> Prop}
    (selection : BoundedGeneratedSelection space trace selectionWindow selected)
    {generated : TriggeredOccurrence Trigger Resident}
    (member : generated ∈ codec.realizeRoute accepting route) :
    exists offset, offset < selectionWindow /\
      selected (generated.generatedAt + offset) generated :=
  selection.selects generated.generatedAt generated
    (codec.mem_realizeRoute_generated accepting route member)

end Codec

/-! ## The recurrent heartbeat background service -/

namespace ServiceCanary

open Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Canary
open Mettapedia.CognitiveArchitecture.TriggeredMindAgentSpace.ServiceCanary

/-- The checked loop action represents exactly the heartbeat trigger delivered
to the authored background provider. -/
def serviceMeaning
    (action : TraceLink loopTheory loopStepAuthority.Certificate)
    (trigger : Trigger) (resident : Resident) : Prop :=
  action.target = () /\ trigger = () /\ resident = providerPosition

theorem serviceMeaning_forces_provider
    {action : TraceLink loopTheory loopStepAuthority.Certificate}
    {trigger : Trigger} {resident : Resident}
    (meaning : serviceMeaning action trigger resident) :
    resident = providerPosition :=
  meaning.2.2

/-- The independently authored heartbeat space realizes each checked loop
occurrence as work for the resident background provider. -/
def serviceCodec :
    Codec loopStepAuthority loopClaim serviceSpace heartbeatTrace
      serviceMeaning where
  triggerOf := fun _ => ()
  residentOf := fun _ => providerPosition
  semanticBinding := by
    intro occurrence
    exact ⟨Subsingleton.elim _ _, rfl, rfl⟩
  generated := by
    intro occurrence
    exact serviceSpace.generated_occurrenceAt
      heartbeatTrace occurrence.index () providerPosition
      rfl rfl

def loopExecution :
    ControlledExecution loopController loopClaim.root :=
  loopController.canonicalExecution loopClaim.root

/-- The exact accepted recurrent prefix used by the cognitive-space bridge. -/
def checkedPrefix (depth : Nat) :
    FiniteRoute
      (auditedRevisionTheory loopStepAuthority alwaysAccepting)
      (ControlledOccurrence loopTheory loopStepAuthority.Certificate)
      loopClaim.root :=
  finitePrefix loopStepAuthority alwaysAccepting loopClaim
    (loop_locally_valid alwaysAccepting) loopExecution depth

/-- The corresponding exact generated mind-agent occurrence list. -/
def generatedPrefix (depth : Nat) : List Occurrence :=
  serviceCodec.realizeRoute alwaysAccepting (checkedPrefix depth)

theorem checked_occurrence_count : forall depth,
    (occurrencePrefix loopStepAuthority loopClaim
      loopExecution depth).length = depth := by
  intro depth
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp [occurrencePrefix, inductionHypothesis]

/-- A demand for `depth` recurrent steps produces exactly `depth` generated
background-service occurrences. -/
theorem generatedPrefix_length (depth : Nat) :
    (generatedPrefix depth).length = depth := by
  simp [generatedPrefix, Codec.realizeRoute, checkedPrefix,
    checked_occurrence_count]

/-- Every generated prefix member is genuine authored work and is selected
within the existing bounded generated-work schedule. -/
theorem generatedPrefix_member_is_generated_and_selected
    (depth : Nat) {occurrence : Occurrence}
    (member : occurrence ∈ generatedPrefix depth) :
    serviceSpace.Generated heartbeatTrace
        occurrence.generatedAt occurrence /\
      exists offset, offset < 1 /\
        selectedGenerated (occurrence.generatedAt + offset)
          occurrence := by
  constructor
  · exact serviceCodec.mem_realizeRoute_generated
      alwaysAccepting (checkedPrefix depth) member
  · exact serviceCodec.mem_realizeRoute_selected
      alwaysAccepting (checkedPrefix depth)
      generatedSelection member

/-- Route realization preserves the background provider's exact ownership. -/
theorem generatedPrefix_member_owned_by_analyst
    (depth : Nat) {occurrence : Occurrence}
    (member : occurrence ∈ generatedPrefix depth) :
    residentOwner occurrence.resident =
      Mettapedia.CognitiveArchitecture.CognitiveSchematicAttentionEconomy.Canary.Actor.analyst := by
  obtain ⟨routeOccurrence, _routeMember, _realized, meaning⟩ :=
    serviceCodec.mem_realizeRoute_has_source
      alwaysAccepting (checkedPrefix depth) member
  have provider := serviceMeaning_forces_provider meaning
  rw [provider]
  rfl

/-- The same resident and trigger at different route indices remain distinct
generated work occurrences. -/
theorem repeated_route_occurrences_remain_distinct :
    serviceCodec.realize
        (occurrenceAt loopStepAuthority loopClaim loopExecution 0) ≠
      serviceCodec.realize
        (occurrenceAt loopStepAuthority loopClaim loopExecution 1) :=
  serviceCodec.realize_distinct_of_index_ne (by decide)

/-- Positive integration control: the accepted GSLT recurrence, productive
generated route, and ECAN long-term service guarantee all hold, but remain
separate conjuncts. -/
theorem checked_recurrence_realizes_background_service :
    loopClaim.Meaning alwaysAccepting /\
      (forall depth occurrence, occurrence ∈ generatedPrefix depth ->
        serviceSpace.Generated heartbeatTrace
          occurrence.generatedAt occurrence) /\
      Mettapedia.CognitiveArchitecture.AttentionEconomy.HonorsLongTermProtection
        Mettapedia.CognitiveArchitecture.MindAgentServiceScheduling.Canary.longTermServiceEconomy
        1 2
        (Mettapedia.CognitiveArchitecture.MindAgentServiceScheduling.scheduledFromOccurrences
          (fun occurrence : Occurrence => residentOwner occurrence.resident)
          selectedGenerated) := by
  refine ⟨accepting_loop_has_both_consequences.2, ?_,
    triggered_background_service_honorsLongTerm⟩
  intro depth occurrence member
  exact (generatedPrefix_member_is_generated_and_selected depth member).1

/-- Negative activation control: no codec can reinterpret the silent trace as
generated recurrent work. -/
theorem silent_trace_has_no_route_codec :
    ¬ Nonempty
      (Codec loopStepAuthority loopClaim serviceSpace silentTrace
        serviceMeaning) := by
  rintro ⟨codec⟩
  let routeOccurrence :=
    occurrenceAt loopStepAuthority loopClaim loopExecution 0
  have generated := codec.generated routeOccurrence
  exact serviceSpace.no_generated_of_no_trigger
    silentTrace routeOccurrence.index rfl
      ⟨codec.realize routeOccurrence, by simpa [Codec.realize] using generated⟩

/-- Negative scheduler control: genuine generated route work does not make a
never-selecting scheduler select it. -/
theorem generation_does_not_imply_selection :
    let routeOccurrence :=
      occurrenceAt loopStepAuthority loopClaim loopExecution 0
    let generated := serviceCodec.realize routeOccurrence
    serviceSpace.Generated heartbeatTrace
        generated.generatedAt generated /\
      ¬ exists cycle, neverSelected cycle generated := by
  dsimp only
  constructor
  · exact serviceCodec.realize_generated _
  · simp [neverSelected]

end ServiceCanary

#print axioms Codec.realize_generated
#print axioms Codec.realize_represents
#print axioms Codec.realize_distinct_of_index_ne
#print axioms Codec.mem_realizeRoute_has_source
#print axioms Codec.mem_realizeRoute_generated
#print axioms Codec.mem_realizeRoute_selected
#print axioms ServiceCanary.serviceMeaning_forces_provider
#print axioms ServiceCanary.generatedPrefix_length
#print axioms
  ServiceCanary.generatedPrefix_member_is_generated_and_selected
#print axioms ServiceCanary.checked_recurrence_realizes_background_service
#print axioms ServiceCanary.silent_trace_has_no_route_codec
#print axioms ServiceCanary.generation_does_not_imply_selection

end
end Mettapedia.CognitiveArchitecture.TriggeredOccurrenceRouteRealization
