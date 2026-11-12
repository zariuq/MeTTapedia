import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationPlugging
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

/-!
# Rho on the step: parallel composition is the union of the store

A rho process is represented by a store that holds one occurrence for each
prime parallel component (a *heated* store) and whose equations hold at the
identity (`ContextualCommunicationAdequacy.Represents`). Then `P | Q` is the
union of the two stores and `0` is the empty store; rho's structural
congruence is carried by the multiset laws
(`RhoScopedParallelInventory.processEquiv`). COMM is one firing that takes a
sender occurrence and a receiver occurrence on the same channel.

* `interpreted_step_has_source_step`: every interpreted firing from a heated
  store is a source reduction, and its result is again heated. A compiled
  root takes and produces prime components, so firing preserves heating.
* `represents_bisimulation`: representation is a strong bisimulation between
  the source reduction, modulo the source equations, and interpreted firings.
* `observe_functional_bisimulation`: rho is a narrowing of the whole-store
  step. On heated stores and compiled source firings, reading a store as one
  process is a functional bisimulation onto the source reduction, and onto
  every process. Only existence of lifts is asserted.
* `interpretedStep_iff_core`: those firings are exactly the admitted events
  of the first-order instance of the calculus core (`AnnotatedRuns.firstOrder`)
  whose firing is a compiled source root, with the identity model kept.
* `unheated_store_cannot_communicate`: a store that keeps a communication
  redex in one occurrence denotes the same process but cannot fire it,
  although the source steps. Heating is needed for the lift; a process
  constructor kept as one unit of the state blocks the joint firing.

Scope: the intrinsic source profile with ordinary substitution of
`ContextualCommunicationProfiles`, not the paper-faithful semantic-substitution
profile. Runs: `ContextualCommunicationAdequacy.source_path_iff_firings`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RhoStoreBisimulation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres
open RhoScopedParallelInventory RhoScopedEventPresheaf
open ContextualCommunicationProfiles ContextualCommunicationAdequacy
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {admitted : RhoScopedParallelEvents.SourceRule → Prop} {context : Ctx sig}

local instance : DecidableEq (Process context) := Classical.decEq _

/-! ## Heated stores -/

theorem normalized_component (prime : Prime context) :
    normalized (component prime) = {component prime} := by
  unfold normalized component
  rw [read_write, Multiset.map_singleton]

/-- Every listed component of a process is itself one component. -/
theorem normalized_of_mem_normalized {process part : Process context}
    (member : part ∈ normalized process) : normalized part = {part} := by
  obtain ⟨prime, _, rfl⟩ := Multiset.mem_map.mp member
  exact normalized_component prime

/-- A bag of components is the component list of the process it assembles. -/
theorem normalized_assemble {parts : Multiset (Process context)}
    (components : ∀ part ∈ parts, normalized part = {part}) :
    normalized (assemble parts) = parts := by
  induction parts using Multiset.induction_on with
  | empty =>
      rw [assemble_zero]
      simp only [normalized, read_zero, Multiset.map_zero]
  | cons first rest earlier =>
      rw [assemble_cons, normalized_join,
        components first (Multiset.mem_cons.mpr (Or.inl rfl)),
        earlier (fun part member => components part (Multiset.mem_cons.mpr (Or.inr member)))]
      exact Multiset.singleton_add first rest

/-! ## The bisimulation -/

/-- Firing from a heated store is a source reduction and keeps the store heated. -/
theorem interpreted_step_has_source_step {source : Process context}
    {before after : Configuration (Process context) (Occurrence context)}
    (represented : Represents before source)
    (executed : InterpretedStep admitted (action context).identity before after) :
    ∃ target : Process context,
      RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules)
        (admitted := admitted) source target ∧ Represents after target := by
  have model := executed.retains_model
  have event := executed.no_invention
  rw [observe_identity_of_normalized before.present source represented.2] at event
  refine ⟨observe (action context).identity after.present, event, model, ?_⟩
  obtain ⟨root, ⟨selection, valid, rfl⟩, solved⟩ := executed
  have labelsFixed : PositiveResourceProjection.realized (action context)
      (action context).identity (label (context := context)) = label := by
    funext occurrence
    exact (action context).apply_identity _
  have identity : (action context).apply (action context).identity = id := by
    funext process
    exact (action context).apply_identity process
  obtain ⟨frame, sourceRead, targetRead, _⟩ :=
    PositiveResourceProjection.observed_frame (action context) rfl valid solved
  rw [labelsFixed, identity, List.map_id, instance_take, represented.2] at sourceRead
  rw [labelsFixed, identity, List.map_id, instance_produce] at targetRead
  have parts : ∀ part ∈ frame + normalized root.target, normalized part = {part} := by
    intro part member
    rcases Multiset.mem_add.mp member with inFrame | inTarget
    · have inSource : part ∈ normalized source := by
        rw [sourceRead]
        exact Multiset.mem_add.mpr (Or.inl inFrame)
      exact normalized_of_mem_normalized inSource
    · exact normalized_of_mem_normalized inTarget
  unfold observe
  rw [labelsFixed, targetRead, normalized_assemble parts]

/-- **Representation is a strong bisimulation** between the source reduction
and interpreted firings on heated stores. -/
theorem represents_bisimulation :
    (∀ {source target : Process context} {before : Configuration (Process context) (Occurrence context)},
      Represents before source →
      RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules)
        (admitted := admitted) source target →
      ∃ after, InterpretedStep admitted (action context).identity before after ∧
        Represents after target) ∧
    (∀ {source : Process context} {before after : Configuration (Process context) (Occurrence context)},
      Represents before source → InterpretedStep admitted (action context).identity before after →
      ∃ target, RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules)
        (admitted := admitted) source target ∧ Represents after target) := by
  refine ⟨fun represented event => ?_,
    fun represented executed => interpreted_step_has_source_step represented executed⟩
  obtain ⟨after, executed, targetRead⟩ :=
    source_step_has_firing _ _ _ represented.1 represented.2 event
  exact ⟨after, executed, executed.retains_model, targetRead⟩

/-! ## Rho as a narrowing of the whole-store step

A store is heated when it holds exactly the components of the process it
denotes, with its equations true at the identity. The observation `observe`
reads a store as one rho process. Restricted to heated stores and to firings of
compiled source roots, `observe` is a functional bisimulation onto the source
reduction: it maps firings to source steps, every source step lifts, and every
process is observed. Lifts exist; they are not claimed unique, since a store
retains occurrence identities that the process forgets. No fibration or
adjunction is asserted here. -/

/-- The store holds exactly the components of the process it denotes. -/
def Heated (state : Configuration (Process context) (Occurrence context)) : Prop :=
  Represents state (observe (action context).identity state.present)

theorem represents_iff_heated {state : Configuration (Process context) (Occurrence context)}
    {process : Process context} :
    Represents state process ↔ Heated state ∧ observe (action context).identity state.present = process := by
  constructor
  · intro represented
    have observed := observe_identity_of_normalized state.present process represented.2
    refine ⟨?_, observed⟩
    unfold Heated
    rw [observed]
    exact represented
  · rintro ⟨heated, observed⟩
    unfold Heated at heated
    rw [observed] at heated
    exact heated

/-- **The observation is a functional bisimulation** from heated stores under compiled
source firings onto rho processes under the source reduction, and it is onto. -/
theorem observe_functional_bisimulation :
    (∀ {before after : Configuration (Process context) (Occurrence context)}, Heated before →
      InterpretedStep admitted (action context).identity before after →
      Heated after ∧ RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules)
        (admitted := admitted) (observe (action context).identity before.present)
        (observe (action context).identity after.present)) ∧
    (∀ {before : Configuration (Process context) (Occurrence context)} {target : Process context},
      Heated before → RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules)
        (admitted := admitted) (observe (action context).identity before.present) target →
      ∃ after, InterpretedStep admitted (action context).identity before after ∧ Heated after ∧
        observe (action context).identity after.present = target) ∧
    (∀ process : Process context, ∃ state : Configuration (Process context) (Occurrence context),
      Heated state ∧ observe (action context).identity state.present = process) := by
  refine ⟨fun heated executed => ?_, fun heated event => ?_, fun process => ?_⟩
  · obtain ⟨target, event, represented⟩ := interpreted_step_has_source_step heated executed
    obtain ⟨heatedAfter, observed⟩ := represents_iff_heated.mp represented
    exact ⟨heatedAfter, observed ▸ event⟩
  · obtain ⟨after, executed, represented⟩ := (represents_bisimulation (admitted := admitted)).1 heated event
    exact ⟨after, executed, represents_iff_heated.mp represented⟩
  · obtain ⟨world, components⟩ := every_source_class_has_occurrences process
    refine ⟨⟨[], world⟩, represents_iff_heated.mp ⟨(action context).models_nil _, components⟩⟩

/-! ## The calculus core -/

/-- Interpreted firings are the admitted events of the core's first-order
instance whose firing is a compiled source root. -/
theorem interpretedStep_iff_core {before after : Configuration (Process context) (Occurrence context)} :
    InterpretedStep admitted (action context).identity before after ↔
      ∃ (root : Root admitted context) (selection : Selection (Occurrence context))
        (permitted : (AnnotatedRuns.firstOrder (action context) (label (context := context))).Admits
          (s := before) (AnnotatedRuns.Firing.ofPlain (instanceRule root, selection))),
        (AnnotatedRuns.firstOrder (action context) label).result _ permitted = after ∧
          (action context).Models (action context).identity after.equations := by
  constructor
  · rintro ⟨root, ⟨selection, valid, rfl⟩, solved⟩
    exact ⟨root, selection,
      (AnnotatedRuns.Firing.valid_ofPlain_iff (action context) label _ before).mpr valid, rfl, solved⟩
  · rintro ⟨root, selection, permitted, rfl, solved⟩
    exact ⟨root, ⟨selection,
      (AnnotatedRuns.Firing.valid_ofPlain_iff (action context) label _ before).mp permitted, rfl⟩, solved⟩

/-! ## Heating is needed -/

open ContextualCommunicationPlugging in
/-- A single occurrence cannot supply the two distinct occurrences that a
communication root takes. -/
theorem unheated_store_cannot_communicate (channel : Term sig context Srt.nm)
    (payload : Term sig context Srt.pr) (body : Term sig (Srt.nm :: context) Srt.pr)
    {before after : Configuration (Process context) (Occurrence context)}
    (single : before.present.card = 1) :
    ¬ ConstraintMultisetRewriting.Step (action context) label
      (instanceRule (communicationRoot channel payload body)) before after := by
  rintro ⟨selection, valid, -⟩
  have two := communication_takes_two_occurrences channel payload body
  have counted : selection.taken.toFinset.card = 2 := by
    rw [List.toFinset_card_of_nodup valid.take_distinct, ← valid.take_length, two]
  have bounded : selection.taken.toFinset.card ≤ before.present.card :=
    Finset.card_le_card valid.occurrences.taken_subset
  omega

/-- The unheated store denotes the redex: one occurrence labelled by the
whole process, observed as that process. -/
theorem unheated_store_denotes (process : Process context) :
    ∃ world : Finset (Occurrence context), world.card = 1 ∧
      observe (action context).identity world = process := by
  obtain ⟨world, represented⟩ := IndexedOccurrences.realize ({process} : Multiset (Process context))
  refine ⟨world, ?_, ?_⟩
  · have cardinalities := congrArg Multiset.card represented
    simpa [labels] using cardinalities
  · have labelsFixed : PositiveResourceProjection.realized (action context)
        (action context).identity (label (context := context)) = label := by
      funext occurrence
      exact (action context).apply_identity _
    unfold observe
    rw [labelsFixed]
    change assemble (labels IndexedOccurrences.label world) = process
    rw [represented, assemble_singleton]

open ContextualCommunicationPlugging in
/-- **Control.** The communication redex steps at the source and fires on a
heated store, while no single-occurrence store can fire it. -/
theorem heating_is_needed (channel : Term sig context Srt.nm)
    (payload : Term sig context Srt.pr) (body : Term sig (Srt.nm :: context) Srt.pr) :
    RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules)
        (admitted := RhoScopedParallelEvents.core)
        (communicationRoot channel payload body).source (communicationRoot channel payload body).target ∧
      (∃ before after : Configuration (Process context) (Occurrence context),
        Represents before (communicationRoot channel payload body).source ∧
        InterpretedStep RhoScopedParallelEvents.core (action context).identity before after) ∧
      (∃ world : Finset (Occurrence context), world.card = 1 ∧
        observe (action context).identity world = (communicationRoot channel payload body).source) ∧
      ∀ before after : Configuration (Process context) (Occurrence context), before.present.card = 1 →
        ¬ ConstraintMultisetRewriting.Step (action context) label
          (instanceRule (communicationRoot channel payload body)) before after := by
  refine ⟨ContextualCommunicationReflection.root_has_declared_source_step _, ?_,
    unheated_store_denotes _, fun before after single =>
      unheated_store_cannot_communicate channel payload body single⟩
  obtain ⟨before, after, empty, sourceRead, executed, _⟩ :=
    every_source_step_has_occurrence_execution _ _
      (ContextualCommunicationReflection.root_has_declared_source_step
        (communicationRoot channel payload body))
  refine ⟨before, after, ⟨?_, sourceRead⟩, executed⟩
  rw [empty]
  exact (action context).models_nil _

#print axioms interpreted_step_has_source_step
#print axioms represents_bisimulation
#print axioms observe_functional_bisimulation
#print axioms interpretedStep_iff_core
#print axioms heating_is_needed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RhoStoreBisimulation
