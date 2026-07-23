import Mettapedia.Languages.MeTTa.PrimeNeedWorlds
import Mathlib.Data.Finset.Lattice.Basic

/-!
# Prime cell-causal application semantics

This module separates the producer of a delayed value from the sites that use
it.  A stable allocated cell owns one producer outcome.  Dynamic rule
occurrences subscribe to that producer and may observe its outcome; production
itself is global and has no candidate parameter.

The model deliberately distinguishes a concrete publication occurrence, which
has one actual dependency receipt, from the quotient by rule and answer, which
may retain several alternative explanations.  Residual explanations are all
inclusion-minimal members of a finite family, not merely the members of least
cardinality.
-/

namespace Mettapedia.Languages.MeTTa.PrimeCellCausalSemantics

/-! ## Independent identities -/

structure ProducerId (Lineage Cell Generation : Type*) where
  lineage : Lineage
  cell : Cell
  generation : Generation
deriving DecidableEq, Repr

theorem ProducerId.ne_of_generation_ne
    {Lineage Cell Generation : Type*}
    {lineage : Lineage} {cell : Cell} {left right : Generation}
    (different : left ≠ right) :
    ProducerId.mk lineage cell left ≠ ProducerId.mk lineage cell right := by
  intro equal
  exact different (congrArg ProducerId.generation equal)

structure SourceOccurrence (Application Position Path : Type*) where
  application : Application
  position : Position
  path : Path
deriving DecidableEq, Repr

structure RuleOccurrence (Application Rule : Type*) where
  application : Application
  rule : Rule
deriving DecidableEq, Repr

inductive DemandRole where
  | lhs
  | rhs
deriving DecidableEq, Repr

structure OutcomeEvent (Producer Occurrence Outcome : Type*) where
  producer : Producer
  occurrence : Occurrence
  outcome : Outcome
deriving DecidableEq, Repr

structure Subscription
    (Rule Source Producer ExpectedType : Type*) where
  rule : Rule
  source : Source
  producer : Producer
  role : DemandRole
  expectedType : ExpectedType
deriving DecidableEq, Repr

structure Observation
    (Rule Source Producer ExpectedType Occurrence Outcome : Type*) where
  subscription : Subscription Rule Source Producer ExpectedType
  event : OutcomeEvent Producer Occurrence Outcome
deriving DecidableEq, Repr

structure CandidateRoot (Rule Event : Type*) where
  rule : Rule
  event : Event
deriving DecidableEq, Repr

structure PublicationOccurrence
    (Publication Rule Event Answer : Type*) where
  occurrence : Publication
  rule : Rule
  answer : Answer
  receipt : Finset Event
deriving DecidableEq

def PublicationOccurrence.dependencyReceipt
    (publication : PublicationOccurrence Publication Rule Event Answer) :
    PrimeNeedWorlds.DependencyReceipt Event :=
  { roots := publication.receipt }

/-! ## Global producer/subscriber machine -/

structure Model
    (Producer Occurrence Outcome Event : Type*) where
  outcomeRoot : OutcomeEvent Producer Occurrence Outcome → Event

structure State
    (Rule Source Producer ExpectedType Occurrence Outcome Event
      Publication Answer : Type*) where
  produced : Finset (OutcomeEvent Producer Occurrence Outcome)
  subscriptions : Finset (Subscription Rule Source Producer ExpectedType)
  observations : Finset
    (Observation Rule Source Producer ExpectedType Occurrence Outcome)
  roots : Finset (CandidateRoot Rule Event)
  publications : Finset
    (PublicationOccurrence Publication Rule Event Answer)

variable
  {Rule Source Producer ExpectedType Occurrence Outcome Event Publication Answer : Type*}
  [DecidableEq Rule] [DecidableEq Source] [DecidableEq Producer]
  [DecidableEq ExpectedType] [DecidableEq Occurrence] [DecidableEq Outcome]
  [DecidableEq Event] [DecidableEq Publication] [DecidableEq Answer]

local notation "MachineState" =>
  State Rule Source Producer ExpectedType Occurrence Outcome Event
    Publication Answer

def ProducedFunctional
    (state : MachineState) : Prop :=
  ∀ ⦃left right⦄,
    left ∈ state.produced → right ∈ state.produced →
    left.producer = right.producer → left = right

def ObservationsSupported
    (state : MachineState) : Prop :=
  ∀ observation ∈ state.observations,
    observation.subscription ∈ state.subscriptions ∧
    observation.event ∈ state.produced ∧
    observation.subscription.producer = observation.event.producer

def PublicationsFunctional
    (state : MachineState) : Prop :=
  ∀ ⦃left right⦄,
    left ∈ state.publications → right ∈ state.publications →
    left.occurrence = right.occurrence → left = right

def rootsFor (state : MachineState) (rule : Rule) : Finset Event :=
  state.roots.biUnion fun root =>
    if root.rule = rule then {root.event} else ∅

def subscribeState
    (state : MachineState)
    (subscription : Subscription Rule Source Producer ExpectedType) :
    MachineState :=
  { state with
    subscriptions := insert subscription state.subscriptions }

def produceState
    (state : MachineState)
    (event : OutcomeEvent Producer Occurrence Outcome) : MachineState :=
  { state with produced := insert event state.produced }

def observeState
    (model : Model Producer Occurrence Outcome Event)
    (state : MachineState)
    (observation : Observation Rule Source Producer ExpectedType Occurrence Outcome) :
    MachineState :=
  { state with
    observations := insert observation state.observations
    roots := insert
      { rule := observation.subscription.rule
        event := model.outcomeRoot observation.event }
      state.roots }

def recordRootState
    (state : MachineState) (root : CandidateRoot Rule Event) : MachineState :=
  { state with roots := insert root state.roots }

def publishState
    (state : MachineState)
    (publication : PublicationOccurrence Publication Rule Event Answer) :
    MachineState :=
  { state with publications := insert publication state.publications }

/-- The primary transition relation.  The `produce` constructor is global: it
mentions an allocated producer and outcome occurrence, but no rule candidate. -/
inductive Step
    (model : Model Producer Occurrence Outcome Event) :
    MachineState → MachineState → Prop where
  | subscribe (state) (subscription) :
      Step model state (subscribeState state subscription)
  | produce (state) (event)
      (fresh : ∀ old ∈ state.produced, old.producer ≠ event.producer) :
      Step model state (produceState state event)
  | observe (state) (observation)
      (subscribed : observation.subscription ∈ state.subscriptions)
      (produced : observation.event ∈ state.produced)
      (aligned : observation.subscription.producer =
        observation.event.producer) :
      Step model state (observeState model state observation)
  | recordRoot (state) (root) :
      Step model state (recordRootState state root)
  | publish (state) (publication)
      (exact : publication.receipt = rootsFor state publication.rule)
      (fresh : ∀ old ∈ state.publications,
        old.occurrence ≠ publication.occurrence) :
      Step model state (publishState state publication)

inductive Trace
    (model : Model Producer Occurrence Outcome Event) :
    MachineState → MachineState → Prop where
  | refl (state) : Trace model state state
  | tail {first middle last} :
      Trace model first middle → Step model middle last → Trace model first last

theorem Trace.invariant
    {model : Model Producer Occurrence Outcome Event}
    (property : MachineState → Prop)
    (preserved : ∀ {before after},
      property before → Step model before after → property after)
    {first last : MachineState}
    (trace : Trace model first last)
    (initial : property first) : property last := by
  induction trace with
  | refl => exact initial
  | tail trace step ih => exact preserved ih step

/-! ## Preservation laws -/

theorem producedFunctional_step
    {model : Model Producer Occurrence Outcome Event}
    {before after : MachineState}
    (functional : ProducedFunctional before)
    (step : Step model before after) :
    ProducedFunctional after := by
  cases step with
  | subscribe => exact functional
  | produce event fresh =>
      intro left right hleft hright hproducer
      simp only [produceState, Finset.mem_insert] at hleft hright
      rcases hleft with rfl | hleft <;> rcases hright with rfl | hright
      · rfl
      · exact False.elim (fresh right hright hproducer.symm)
      · exact False.elim (fresh left hleft hproducer)
      · exact functional hleft hright hproducer
  | observe => exact functional
  | recordRoot => exact functional
  | publish => exact functional

theorem producedFunctional_trace
    {model : Model Producer Occurrence Outcome Event}
    {first last : MachineState}
    (functional : ProducedFunctional first)
    (trace : Trace model first last) :
    ProducedFunctional last :=
  trace.invariant ProducedFunctional
    (fun invariant step => producedFunctional_step invariant step) functional

theorem observationsSupported_step
    {model : Model Producer Occurrence Outcome Event}
    {before after : MachineState}
    (supported : ObservationsSupported before)
    (step : Step model before after) :
    ObservationsSupported after := by
  cases step with
  | subscribe subscription =>
      intro observation h
      rcases supported observation h with ⟨hsub, hout, halign⟩
      exact ⟨by simp [subscribeState, hsub], hout, halign⟩
  | produce event fresh =>
      intro observation h
      rcases supported observation h with ⟨hsub, hout, halign⟩
      exact ⟨hsub, by simp [produceState, hout], halign⟩
  | observe observation subscribed produced aligned =>
      intro current h
      simp only [observeState, Finset.mem_insert] at h
      rcases h with rfl | h
      · exact ⟨subscribed, produced, aligned⟩
      · exact supported current h
  | recordRoot => exact supported
  | publish => exact supported

theorem observationsSupported_trace
    {model : Model Producer Occurrence Outcome Event}
    {first last : MachineState}
    (supported : ObservationsSupported first)
    (trace : Trace model first last) :
    ObservationsSupported last :=
  trace.invariant ObservationsSupported
    (fun invariant step => observationsSupported_step invariant step) supported

theorem publicationsFunctional_step
    {model : Model Producer Occurrence Outcome Event}
    {before after : MachineState}
    (functional : PublicationsFunctional before)
    (step : Step model before after) :
    PublicationsFunctional after := by
  cases step with
  | subscribe => exact functional
  | produce => exact functional
  | observe => exact functional
  | recordRoot => exact functional
  | publish publication exact fresh =>
      intro left right hleft hright hoccurrence
      simp only [publishState, Finset.mem_insert] at hleft hright
      rcases hleft with rfl | hleft <;> rcases hright with rfl | hright
      · rfl
      · exact False.elim (fresh right hright hoccurrence.symm)
      · exact False.elim (fresh left hleft hoccurrence)
      · exact functional hleft hright hoccurrence

theorem publicationsFunctional_trace
    {model : Model Producer Occurrence Outcome Event}
    {first last : MachineState}
    (functional : PublicationsFunctional first)
    (trace : Trace model first last) :
    PublicationsFunctional last :=
  trace.invariant PublicationsFunctional
    (fun invariant step => publicationsFunctional_step invariant step) functional

theorem produce_preserves_candidate_data
    (model : Model Producer Occurrence Outcome Event)
    (state : MachineState)
    (event : OutcomeEvent Producer Occurrence Outcome)
    (fresh : ∀ old ∈ state.produced, old.producer ≠ event.producer) :
    let after := produceState state event
    Step model state after ∧
      after.subscriptions = state.subscriptions ∧
      after.observations = state.observations ∧
      after.roots = state.roots ∧
      after.publications = state.publications := by
  exact ⟨Step.produce state event fresh, rfl, rfl, rfl, rfl⟩

theorem observed_events_are_supported
    {model : Model Producer Occurrence Outcome Event}
    {before after : MachineState}
    (supported : ObservationsSupported before)
    (step : Step model before after)
    {observation :
      Observation Rule Source Producer ExpectedType Occurrence Outcome}
    (member : observation ∈ after.observations) :
    observation.subscription ∈ after.subscriptions ∧
    observation.event ∈ after.produced ∧
    observation.subscription.producer = observation.event.producer :=
  observationsSupported_step supported step observation member

/-! ## Aliasing and fresh generations -/

theorem aliased_subscribers_observe_one_outcome
    (model : Model Producer Occurrence Outcome Event)
    (state : MachineState)
    (left right : Subscription Rule Source Producer ExpectedType)
    (event : OutcomeEvent Producer Occurrence Outcome)
    (leftMember : left ∈ state.subscriptions)
    (rightMember : right ∈ state.subscriptions)
    (eventMember : event ∈ state.produced)
    (leftAlias : left.producer = event.producer)
    (rightAlias : right.producer = event.producer) :
    let leftObservation :=
      ({ subscription := left, event := event } :
        Observation Rule Source Producer ExpectedType Occurrence Outcome)
    let rightObservation :=
      ({ subscription := right, event := event } :
        Observation Rule Source Producer ExpectedType Occurrence Outcome)
    ∃ middle final,
      Step model state middle ∧
      Step model middle final ∧
      leftObservation ∈ final.observations ∧
      rightObservation ∈ final.observations := by
  let leftObservation :
      Observation Rule Source Producer ExpectedType Occurrence Outcome :=
    { subscription := left, event := event }
  let rightObservation :
      Observation Rule Source Producer ExpectedType Occurrence Outcome :=
    { subscription := right, event := event }
  let middle := observeState model state leftObservation
  let final := observeState model middle rightObservation
  refine ⟨middle, final, ?_, ?_, ?_, ?_⟩
  · exact Step.observe state leftObservation leftMember eventMember leftAlias
  · apply Step.observe middle rightObservation
    · simpa [middle, observeState] using rightMember
    · simpa [middle, observeState] using eventMember
    · exact rightAlias
  · simp [final, middle, observeState, leftObservation, rightObservation]
  · simp [final, observeState, rightObservation]

def OutcomeConflict
    (left right : OutcomeEvent Producer Occurrence Outcome) : Prop :=
  left.producer = right.producer ∧ left ≠ right

omit [DecidableEq Producer] [DecidableEq Occurrence] [DecidableEq Outcome] in
theorem distinct_producers_do_not_conflict
    {left right : OutcomeEvent Producer Occurrence Outcome}
    (distinct : left.producer ≠ right.producer) :
    ¬ OutcomeConflict left right := by
  exact fun conflict => distinct conflict.1

omit [DecidableEq Producer] in
theorem injective_persistence_preserves_aliases
    {Key : Type*} (rename : Producer → Key) (injective : Function.Injective rename)
    {left right : Producer} :
    rename left = rename right ↔ left = right := by
  exact ⟨fun equal => injective equal, fun equal => congrArg rename equal⟩

/-! ## Exact publications and explanation quotients -/

theorem publish_step_has_exact_receipt
    {model : Model Producer Occurrence Outcome Event}
    {before after : MachineState}
    {publication : PublicationOccurrence Publication Rule Event Answer}
    (step : Step model before after)
    (new : publication ∈ after.publications)
    (absent : publication ∉ before.publications) :
    publication.receipt = rootsFor before publication.rule := by
  cases step with
  | subscribe => exact False.elim (absent new)
  | produce => exact False.elim (absent new)
  | observe => exact False.elim (absent new)
  | recordRoot => exact False.elim (absent new)
  | publish published exact fresh =>
      simp only [publishState, Finset.mem_insert] at new
      rcases new with equal | old
      · subst publication
        exact exact
      · exact False.elim (absent old)

def explanationFamily
    (publications : Finset
      (PublicationOccurrence Publication Rule Event Answer))
    (rule : Rule) (answer : Answer) : Finset (Finset Event) :=
  (publications.filter fun publication =>
      publication.rule = rule ∧ publication.answer = answer).image
    PublicationOccurrence.receipt

def demoPublicationLeft : PublicationOccurrence Nat Nat Nat Nat :=
  { occurrence := 0, rule := 7, answer := 42, receipt := {10} }

def demoPublicationRight : PublicationOccurrence Nat Nat Nat Nat :=
  { occurrence := 1, rule := 7, answer := 42, receipt := {11} }

theorem same_rule_answer_can_have_alternative_explanations :
    demoPublicationLeft.rule = demoPublicationRight.rule ∧
    demoPublicationLeft.answer = demoPublicationRight.answer ∧
    demoPublicationLeft.occurrence ≠ demoPublicationRight.occurrence ∧
    demoPublicationLeft.receipt ≠ demoPublicationRight.receipt := by
  decide

/-! ## Complete inclusion-minimal residual families -/

def minimalSupports (family : Finset (Finset Event)) : Finset (Finset Event) :=
  family.filter fun support =>
    ∀ other ∈ family, other ⊆ support → support ⊆ other

theorem mem_minimalSupports_iff
    {family : Finset (Finset Event)} {support : Finset Event} :
    support ∈ minimalSupports family ↔
      support ∈ family ∧
      ∀ other ∈ family, other ⊆ support → support ⊆ other := by
  simp [minimalSupports]

theorem minimalSupports_complete
    {family : Finset (Finset Event)} {support : Finset Event}
    (member : support ∈ family)
    (minimal : ∀ other ∈ family, other ⊆ support → support ⊆ other) :
    support ∈ minimalSupports family :=
  mem_minimalSupports_iff.mpr ⟨member, minimal⟩

def SupportsAntichain (family : Finset (Finset Event)) : Prop :=
  ∀ ⦃left right⦄, left ∈ family → right ∈ family →
    left ⊆ right → left = right

theorem minimalSupports_antichain (family : Finset (Finset Event)) :
    SupportsAntichain (minimalSupports family) := by
  intro left right leftMember rightMember subset
  have rightMinimal := (mem_minimalSupports_iff.mp rightMember).2
  exact Finset.Subset.antisymm subset
    (rightMinimal left (mem_minimalSupports_iff.mp leftMember).1 subset)

def mixedResidualFamily : Finset (Finset Nat) :=
  {{0}, {0, 1}, {0, 2}, {1, 2}}

theorem mixed_cardinality_minimals_are_retained :
    minimalSupports mixedResidualFamily = {{0}, {1, 2}} := by
  decide

/-! ## Local order-invariance diamonds -/

omit [DecidableEq Occurrence] [DecidableEq Outcome] [DecidableEq Event]
    [DecidableEq Publication] [DecidableEq Answer] in
theorem subscribeState_comm
    (state : MachineState)
    (left right : Subscription Rule Source Producer ExpectedType) :
    subscribeState (subscribeState state left) right =
      subscribeState (subscribeState state right) left := by
  cases state
  simp [subscribeState, Finset.insert_comm]

omit [DecidableEq Rule] [DecidableEq Source] [DecidableEq ExpectedType]
    [DecidableEq Event] [DecidableEq Publication] [DecidableEq Answer] in
theorem produceState_comm
    (state : MachineState)
    (left right : OutcomeEvent Producer Occurrence Outcome) :
    produceState (produceState state left) right =
      produceState (produceState state right) left := by
  cases state
  simp [produceState, Finset.insert_comm]

omit [DecidableEq Event] [DecidableEq Publication] [DecidableEq Answer] in
theorem produce_subscribe_comm
    (state : MachineState)
    (event : OutcomeEvent Producer Occurrence Outcome)
    (subscription : Subscription Rule Source Producer ExpectedType) :
    subscribeState (produceState state event) subscription =
      produceState (subscribeState state subscription) event := by
  rfl

omit [DecidableEq Publication] [DecidableEq Answer] in
theorem observeState_comm
    (model : Model Producer Occurrence Outcome Event)
    (state : MachineState)
    (left right :
      Observation Rule Source Producer ExpectedType Occurrence Outcome) :
    observeState model (observeState model state left) right =
      observeState model (observeState model state right) left := by
  cases state
  simp [observeState, Finset.insert_comm]

theorem independent_productions_form_diamond
    (model : Model Producer Occurrence Outcome Event)
    (state : MachineState)
    (left right : OutcomeEvent Producer Occurrence Outcome)
    (leftFresh : ∀ old ∈ state.produced,
      old.producer ≠ left.producer)
    (rightFresh : ∀ old ∈ state.produced,
      old.producer ≠ right.producer)
    (distinct : left.producer ≠ right.producer) :
    let leftFirst := produceState state left
    let rightFirst := produceState state right
    ∃ final,
      Step model state leftFirst ∧ Step model leftFirst final ∧
      Step model state rightFirst ∧ Step model rightFirst final := by
  let leftFirst := produceState state left
  let rightFirst := produceState state right
  let final := produceState leftFirst right
  have rightFreshAfterLeft :
      ∀ old ∈ leftFirst.produced, old.producer ≠ right.producer := by
    intro old member
    simp only [leftFirst, produceState, Finset.mem_insert] at member
    rcases member with rfl | member
    · exact distinct
    · exact rightFresh old member
  have leftFreshAfterRight :
      ∀ old ∈ rightFirst.produced, old.producer ≠ left.producer := by
    intro old member
    simp only [rightFirst, produceState, Finset.mem_insert] at member
    rcases member with rfl | member
    · exact distinct.symm
    · exact leftFresh old member
  refine ⟨final, Step.produce state left leftFresh,
    Step.produce leftFirst right rightFreshAfterLeft,
    Step.produce state right rightFresh, ?_⟩
  rw [show final = produceState rightFirst left by
    exact produceState_comm state left right]
  exact Step.produce rightFirst left leftFreshAfterRight

end Mettapedia.Languages.MeTTa.PrimeCellCausalSemantics
