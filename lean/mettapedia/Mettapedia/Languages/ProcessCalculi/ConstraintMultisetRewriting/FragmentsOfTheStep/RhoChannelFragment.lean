import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RhoStoreBisimulation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.HeatingBisimulation

/-!
# Rho is the channel-communication fragment of the step

The store holds rho processes as occurrences. A rule is in the **channel-communication fragment**
(`ChannelCommunication`) when it reads, checks and tells nothing, takes exactly the parallel
components of a communication redex and makes exactly the components of its result. Intrinsically
(`channelCommunication_iff`, from `core_root_shape`): it takes one message `x!(q)` and one receiver
`for(y <- x) K` on the same name, and makes the components of `K` instantiated at `@q`. Nothing in
the language changes: the fragment is a property of rule sets, and rho stays a client hosted on the
step. Reads (a receive that keeps its message, a peek) are not in the fragment, and a peek is not
rho (`RhoPeekOutside.peek_not_rho`).

* `channel_fragment_bisimulation`: the step restricted to the channel-communication fragment, at
  the identity solution (`ChannelStep`), is **strongly bisimilar** to rho's reduction with
  communication alone, through representation (`ContextualCommunicationAdequacy.Represents`: the
  store holds exactly the components of the process, and the identity models its knowledge). Both
  directions are proved, for every rule of the fragment, not only for the compiled roots.
* `channelStep_iff_view`: a fragment firing and a compiled firing are interchangeable through the
  view, so the fragment adds no behaviour beyond the compiled rule set.

## Where heating enters

Exactly once, in the relation: `Represents` asks the store to be the **heating** of the process,
`labels = normalized process`, the bag of its parallel components (`represents_iff_view`). Rho's
structural congruence is already the equality of `Process`, and `RhoScopedParallelInventory.processEquiv`
identifies that quotient with the free commutative monoid on prime components, so parallel
composition is the union of stores (`ContextualCommunicationProfiles.normalized_join`). The step
itself never applies the congruence. Without heating the joint firing is impossible
(`RhoStoreBisimulation.heating_is_needed`).

## Controls

* Positive: `communication_in_fragment`, a communication redex is in the fragment, and its firing
  exists (`ContextualCommunicationPlugging.communication_has_occurrence_execution`).
* Negative, just outside: `reflection_outside_breaks`. The reflection rule `*@P → P` takes one
  occurrence and is not a communication. Adding it, the step fires on a store representing `*@0`,
  where rho's communication-only reduction and the fragment's step have no step.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.RhoChannelFragment

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoScopedParallelInventory RhoScopedConstructorInventory RhoIntrinsicReadback
open RhoScopedInstanceReadout (receive)
open ContextualCommunicationProfiles ContextualCommunicationAdequacy ContextualCommunicationPlugging
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (labels)
open HeatingBisimulation TransitionMaps

variable {context : Ctx sig}

local instance : DecidableEq (Process context) := Classical.decEq _

/-- Rho's reduction with communication alone. -/
abbrev RhoStep (source target : Process context) : Prop :=
  RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules)
    (admitted := RhoScopedParallelEvents.core) source target

/-- **The channel-communication fragment**: no reads, checks or tells; the takes are the components
of a communication redex and the makes are the components of its result. -/
def ChannelCommunication (rule : RuleInstance (Process context)) : Prop :=
  rule.read = [] ∧ rule.checks = [] ∧ rule.tell = [] ∧
    ∃ root : ContextualCommunicationProfiles.Root RhoScopedParallelEvents.core context,
      (rule.take : Multiset (Process context)) = normalized root.source ∧
        (rule.produce : Multiset (Process context)) = normalized root.target

/-- The compiled rule set: one rule instance per communication redex. -/
def compiled (rule : RuleInstance (Process context)) : Prop :=
  ∃ root : ContextualCommunicationProfiles.Root RhoScopedParallelEvents.core context, rule = instanceRule root

/-- **The step restricted to the channel-communication fragment**, at the identity solution. -/
def ChannelStep (before after : Configuration (Process context) (Occurrence context)) : Prop :=
  RuleStep (action context) label (action context).identity (ChannelCommunication (context := context))
    before after

theorem compiled_in_fragment {rule : RuleInstance (Process context)} (member : compiled rule) :
    ChannelCommunication rule := by
  obtain ⟨root, rfl⟩ := member
  exact ⟨rfl, rfl, rfl, root, instance_take root, instance_produce root⟩

theorem fragment_takeMake : TakeMake (ChannelCommunication (context := context)) :=
  fun _ member => ⟨member.1, member.2.1⟩

theorem compiled_takeMake : TakeMake (compiled (context := context)) :=
  fun _ member => fragment_takeMake _ (compiled_in_fragment member)

theorem realized_identity :
    PositiveResourceProjection.realized (action context) (action context).identity
      (label (context := context)) = label := by
  funext occurrence
  exact (action context).apply_identity _

theorem map_identity (values : List (Process context)) :
    values.map ((action context).apply (action context).identity) = values := by
  have identity : (action context).apply (action context).identity = id := by
    funext process
    exact (action context).apply_identity process
  rw [identity, List.map_id]

/-- At the identity, the view of a configuration is the bag of its labels. -/
theorem view_identity (C : Configuration (Process context) (Occurrence context)) :
    view (action context) label (action context).identity C = labels label C.present := by
  unfold view
  rw [realized_identity]

/-- **Representation is heating**: the identity models the knowledge, and the view is the bag of
the process's parallel components. -/
theorem represents_iff_view {C : Configuration (Process context) (Occurrence context)}
    {process : Process context} :
    Represents C process ↔ (action context).Models (action context).identity C.equations ∧
      view (action context) label (action context).identity C = normalized process := by
  rw [view_identity]
  rfl

/-- The fragment's reaction is the compiled reaction. -/
theorem reaction_fragment_le {consumed produced : Multiset (Process context)}
    (reacts : reaction (action context) (action context).identity ChannelCommunication consumed produced) :
    reaction (action context) (action context).identity compiled consumed produced := by
  obtain ⟨rule, ⟨_, _, _, root, takes, makes⟩, _, rfl, rfl⟩ := reacts
  refine ⟨instanceRule root, ⟨root, rfl⟩, (action context).models_nil _, ?_, ?_⟩
  · rw [map_identity, map_identity, takes, instance_take]
  · rw [map_identity, map_identity, makes, instance_produce]

theorem interpretedStep_iff_compiled {before after : Configuration (Process context) (Occurrence context)} :
    InterpretedStep RhoScopedParallelEvents.core (action context).identity before after ↔
      RuleStep (action context) label (action context).identity compiled before after := by
  constructor
  · rintro ⟨root, step, solved⟩
    exact ⟨instanceRule root, ⟨root, rfl⟩, step, solved⟩
  · rintro ⟨_, ⟨root, rfl⟩, step, solved⟩
    exact ⟨root, step, solved⟩

/-- **A fragment firing is a compiled firing up to the view**, from every modelled configuration. -/
theorem channelStep_iff_view {before : Configuration (Process context) (Occurrence context)}
    (modelled : (action context).Models (action context).identity before.equations)
    (after : Multiset (Process context)) :
    (∃ C', ChannelStep before C' ∧ view (action context) label (action context).identity C' = after) ↔
      ∃ C', InterpretedStep RhoScopedParallelEvents.core (action context).identity before C' ∧
        view (action context) label (action context).identity C' = after := by
  constructor
  · rintro ⟨C', step, rfl⟩
    have moved := view_step fragment_takeMake rfl IndexedOccurrences.supply step
    obtain ⟨consumed, produced, frame, reacts, source, target⟩ := moved
    obtain ⟨C'', step', viewed⟩ := view_lift compiled_takeMake rfl IndexedOccurrences.supply modelled
      ⟨consumed, produced, frame, reaction_fragment_le reacts, source, target⟩
    exact ⟨C'', interpretedStep_iff_compiled.mpr step', viewed⟩
  · rintro ⟨C', step, rfl⟩
    obtain ⟨_, member, fires, solved⟩ := interpretedStep_iff_compiled.mp step
    exact ⟨C', ⟨_, compiled_in_fragment member, fires, solved⟩, rfl⟩

/-- **The channel-communication fragment of the step is strongly bisimilar to rho's
communication**, through representation, in both directions. The step here is `RuleStep`, which
keeps only firings whose resulting knowledge is satisfied at the chosen solution
(`A.Models σ after.equations`); the bisimulation is with that filtered step. -/
theorem channel_fragment_bisimulation :
    IsBisimulation (ChannelStep (context := context)) RhoStep Represents := by
  refine ⟨fun {C source C'} represented step => ?_, fun {C source target} represented event => ?_⟩
  · have fires : ∃ D, ChannelStep C D ∧
        view (action context) label (action context).identity D =
          view (action context) label (action context).identity C' := ⟨C', step, rfl⟩
    obtain ⟨C'', executed, viewed⟩ := (channelStep_iff_view represented.1 _).mp fires
    obtain ⟨target, event, representedAfter⟩ :=
      RhoStoreBisimulation.interpreted_step_has_source_step represented executed
    refine ⟨target, event, step.modelled, ?_⟩
    have sameView := viewed.symm.trans ((represents_iff_view.mp representedAfter).2)
    rw [view_identity] at sameView
    exact sameView
  · obtain ⟨after, executed, representedAfter⟩ :=
      (RhoStoreBisimulation.represents_bisimulation (admitted := RhoScopedParallelEvents.core)).1
        represented event
    obtain ⟨_, member, fires, solved⟩ := interpretedStep_iff_compiled.mp executed
    exact ⟨after, ⟨_, compiled_in_fragment member, fires, solved⟩, representedAfter⟩

/-! ## The positive example -/

theorem normalized_output (name : Name context) (payload : Process context) :
    normalized (outputClass name payload) = {outputClass name payload} :=
  normalized_singleton_of_card_one _ (by
    rw [normalized_card, output_components, Multiset.card_singleton])

theorem normalized_input (name : Name context) (body : Process (Srt.nm :: context)) :
    normalized (inputClass name body) = {inputClass name body} :=
  normalized_singleton_of_card_one _ (by
    rw [normalized_card, input_components, Multiset.card_singleton])

/-- **Positive control.** A communication redex is in the fragment: it takes one message and one
receiver on the same name. -/
theorem communication_in_fragment (channel : Term sig context Srt.nm)
    (payload : Term sig context Srt.pr) (body : Term sig (Srt.nm :: context) Srt.pr) :
    ChannelCommunication (instanceRule (communicationRoot channel payload body)) ∧
      ((instanceRule (communicationRoot channel payload body)).take : Multiset (Process context)) =
        {outputClass (project channel) (project payload)} + {inputClass (project channel) (project body)} := by
  refine ⟨compiled_in_fragment ⟨_, rfl⟩, ?_⟩
  rw [instance_take, communication_source, normalized_join, normalized_output, normalized_input]

/-! ## The fragment, read intrinsically -/

/-- Every communication redex is one message and one receiver on the same name, and its result is
the receiver's continuation instantiated at the quoted payload. -/
theorem core_root_shape (root : ContextualCommunicationProfiles.Root RhoScopedParallelEvents.core context) :
    ∃ (name : Name context) (payload : Process context) (body : Process (Srt.nm :: context)),
      root.source = join (outputClass name payload) (inputClass name body) ∧
        root.target = receive (quote payload) body := by
  rcases root with ⟨⟨selected, permitted⟩, firing⟩
  cases selected with
  | communication =>
      exact ⟨_, _, _, RhoScopedInstanceReadout.Communication.source_class firing,
        RhoScopedInstanceReadout.Communication.target_class firing⟩
  | reflection => exact False.elim permitted

/-- **The channel-communication fragment, intrinsically**: a rule is in it exactly when it reads,
checks and tells nothing, takes one message `x!(q)` and one receiver `for(y <- x) K` on the same
name, and makes the components of `K` instantiated at `@q`. -/
theorem channelCommunication_iff (rule : RuleInstance (Process context)) :
    ChannelCommunication rule ↔ rule.read = [] ∧ rule.checks = [] ∧ rule.tell = [] ∧
      ∃ (name : Name context) (payload : Process context) (body : Process (Srt.nm :: context)),
        (rule.take : Multiset (Process context)) = {outputClass name payload} + {inputClass name body} ∧
          (rule.produce : Multiset (Process context)) = normalized (receive (quote payload) body) := by
  constructor
  · rintro ⟨noReads, noChecks, noTells, root, takes, makes⟩
    obtain ⟨name, payload, body, source, target⟩ := core_root_shape root
    refine ⟨noReads, noChecks, noTells, name, payload, body, ?_, ?_⟩
    · rw [takes, source, normalized_join, normalized_output, normalized_input]
    · rw [makes, target]
  · rintro ⟨noReads, noChecks, noTells, name, payload, body, takes, makes⟩
    induction name using Quotient.inductionOn with
    | _ channel =>
      induction payload using Quotient.inductionOn with
      | _ sent =>
        induction body using Quotient.inductionOn with
        | _ continuation =>
          refine ⟨noReads, noChecks, noTells, communicationRoot channel sent continuation, ?_, ?_⟩
          · rw [takes, communication_source, normalized_join, normalized_output, normalized_input]
            rfl
          · rw [makes, communication_target]
            rfl

/-! ## Just outside: reflection -/

/-- **Negative control.** With the reflection rule added, the step fires on a store representing
`*@0`; rho's communication has no step there, so neither has the fragment's step. -/
theorem reflection_outside_breaks :
    ∃ before after : Configuration (Process context) (Occurrence context),
      Represents before (drop (quote (zero context))) ∧
        InterpretedStep RhoScopedParallelEvents.withReflection (action context).identity before after ∧
        (∀ target, ¬ RhoStep (drop (quote (zero context))) target) ∧
        ∀ after', ¬ ChannelStep before after' := by
  obtain ⟨before, after, empty, source, executed, _⟩ :=
    ContextualCommunicationReflection.process_drop_has_occurrence_execution (zero context)
  have represented : Represents before (drop (quote (zero context))) := by
    refine ⟨?_, source⟩
    rw [empty]
    exact (action context).models_nil _
  refine ⟨before, after, represented, executed,
    fun target => ContextualCommunicationReflection.dropped_null_has_no_core_event target,
    fun after' step => ?_⟩
  obtain ⟨target, event, _⟩ := channel_fragment_bisimulation.1 represented step
  exact ContextualCommunicationReflection.dropped_null_has_no_core_event target event

#print axioms channelStep_iff_view
#print axioms channel_fragment_bisimulation
#print axioms represents_iff_view
#print axioms communication_in_fragment
#print axioms core_root_shape
#print axioms channelCommunication_iff
#print axioms reflection_outside_breaks

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.RhoChannelFragment
