import Mettapedia.GSLT.Logic.ObservationSpans
import Mettapedia.GSLT.Topos.PresheafEventModalControls

/-!
# Controls for observing reduction spans

The cyclic positive example forgets a state tag while matching both outgoing
and incoming endpoints. The negative example has the same futures but different
pasts. A further control distinguishes modal adequacy from preservation of
event occurrences: adding an event with existing endpoints is invisible to
state modalities and visible to an event-sensitive consumer.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ObservationSpans.Controls

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence

namespace TaggedCycle

abbrev State := Bool × Bool
abbrev Event := Bool × Bool × Bool

/-- An event retains its stage, source tag and target tag independently. -/
def authored : ReductionSpan State where
  Edge := Event
  source event := (event.1, event.2.1)
  target event := (!event.1, event.2.2)

def observed : ReductionSpan Bool where
  Edge := Bool
  source stage := stage
  target stage := !stage

def observation : SpanMap authored observed where
  states := Prod.fst
  events := Prod.fst
  source_comm _ := rfl
  target_comm _ := rfl

theorem sourceLifts : observation.SourceLifts := by
  intro state event endpointEq
  refine ⟨(state.1, state.2, false), rfl, ?_⟩
  change Bool.not state.1 = Bool.not event
  exact congrArg Bool.not endpointEq.symm

theorem targetLifts : observation.TargetLifts := by
  intro state event endpointEq
  refine ⟨(event, false, state.2), ?_, rfl⟩
  exact Prod.ext endpointEq rfl

/-- Both modal directions hold for this genuinely merging observation. -/
theorem modal_comparison (predicate : Bool → Prop) (state : State) :
    (derivedDiamond observed predicate state.1 ↔
      derivedDiamond authored (predicate ∘ Prod.fst) state) ∧
    (derivedBox observed predicate state.1 ↔
      derivedBox authored (predicate ∘ Prod.fst) state) :=
  ⟨observation.diamond_pullback sourceLifts predicate state,
    observation.box_pullback targetLifts predicate state⟩

theorem merges_distinct_states :
    observation.states (false, false) = observation.states (false, true) ∧
      (false, false) ≠ (false, true) :=
  ⟨rfl, by decide⟩

def stageEquations : Setoid State := Setoid.ker Prod.fst

/-- State quotienting retains two distinct event occurrences with the same
observed source and target. Endpoint equality does not identify the events. -/
theorem retained_occurrences :
    (false, false, false) ≠ (false, false, true) ∧
      (quotientSpan authored stageEquations).source (false, false, false) =
        (quotientSpan authored stageEquations).source (false, false, true) ∧
      (quotientSpan authored stageEquations).target (false, false, false) =
        (quotientSpan authored stageEquations).target (false, false, true) :=
  ⟨by decide, rfl, Quotient.sound rfl⟩

theorem event_tag_does_not_descend :
    ¬ PredicateDescends observation.events (fun event => event.2.2 = true) := by
  intro descends
  have constant := (predicateDescends_iff _ _).mp descends
  have impossible := Mettapedia.GSLT.Scope.ConstantOnFibers.iff constant
    (a := (false, false, true)) (b := (false, false, false)) rfl
  exact Bool.noConfusion (impossible.mp rfl)

end TaggedCycle

namespace DifferentPasts

inductive State where
  | predecessor
  | entered
  | isolated
  deriving DecidableEq

open State

def step (source target : State) : Prop :=
  source = predecessor ∧ target = entered

abbrev theory : GSLT := equalityGSLT State step

/-- This example deliberately admits only identity contexts, so its saturated
equivalence tests exactly these reductions rather than a hidden larger class. -/
def rules : ContextualRules theory where
  Context := Unit
  identity := ()
  compose _ _ := ()
  plug _ state := state
  plug_identity _ := rfl
  plug_compose _ _ _ := rfl
  plug_resp _ := by intro _ _ related; exact related
  Rule := Unit
  fires _ := step
  fires_resp_left := by
    intro _ _ _ _ equal fires
    cases equal
    exact ⟨_, fires, rfl⟩
  fires_resp_right := by
    intro _ _ _ _ fires equal
    cases equal
    exact fires
  fires_step fires := fires

def admissible : AdmissibleClass rules where
  Admissible _ := True
  identity_mem := trivial
  compose_mem _ _ := trivial

def observations : ContextualRules.Observations theory where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom _ := atom.elim

/-- The observation merges the two terminal states, but keeps their source
apart. It supplies a concrete bisimulation, not an assumed modal equality. -/
def view : State → Bool
  | predecessor => false
  | entered => true
  | isolated => true

theorem view_bisimulation : theory.IsBisimulation (fun left right => view left = view right) := by
  constructor
  · intro left right related next reduction
    obtain ⟨rfl, rfl⟩ := reduction
    cases right with
    | predecessor => exact ⟨entered, ⟨rfl, rfl⟩, rfl⟩
    | entered => exact Bool.noConfusion related
    | isolated => exact Bool.noConfusion related
  · intro left right related next reduction
    obtain ⟨rfl, rfl⟩ := reduction
    cases left with
    | predecessor => exact ⟨entered, ⟨rfl, rfl⟩, rfl⟩
    | entered => exact Bool.noConfusion related
    | isolated => exact Bool.noConfusion related

theorem same_saturated_futures : admissible.RelEquiv observations entered isolated := by
  apply admissible.relEquiv_of_isReductionBisimulation observations
    (relation := fun left right => view left = view right)
  · exact ⟨view_bisimulation, by intro _ _ _ atom; exact atom.elim⟩
  · intro _ _ _ _ related
    exact related
  · rfl

theorem observed_terminals_equal :
    relativeObserve admissible observations entered = relativeObserve admissible observations isolated :=
  Quotient.sound same_saturated_futures

theorem isolated_has_no_predecessor : ¬ ∃ source, theory.Step source isolated := by
  rintro ⟨source, _, impossible⟩
  exact State.noConfusion impossible

theorem same_future_diamonds (predicate : State → Prop) :
    gsltDiamond theory predicate entered ↔ gsltDiamond theory predicate isolated := by
  constructor
  · intro holds
    obtain ⟨_, ⟨impossible, _⟩, _⟩ := (gsltDiamond_spec theory predicate entered).mp holds
    exact State.noConfusion impossible
  · intro holds
    obtain ⟨_, ⟨impossible, _⟩, _⟩ := (gsltDiamond_spec theory predicate isolated).mp holds
    exact State.noConfusion impossible

theorem past_box_distinguishes :
    gsltBox theory (fun _ => False) isolated ∧ ¬ gsltBox theory (fun _ => False) entered := by
  constructor
  · apply (gsltBox_spec theory _ isolated).mpr
    intro _ reduction
    exact State.noConfusion reduction.2
  · intro allIncoming
    exact (gsltBox_spec theory _ entered).mp allIncoming predecessor ⟨rfl, rfl⟩

def entryEvent : (gsltSpan theory).Edge := ⟨predecessor, entered, ⟨rfl, rfl⟩⟩

/-- Independently existentially observed endpoints admit an incoming edge at
the class of the isolated terminal. They cannot lift it to that representative. -/
theorem quotient_incoming_without_native_incoming :
    (∃ event : (relativeSpan admissible observations).Edge,
      (relativeSpan admissible observations).target event =
        relativeObserve admissible observations isolated) ∧
      ¬ ∃ source, theory.Step source isolated :=
  ⟨⟨entryEvent, observed_terminals_equal⟩, isolated_has_no_predecessor⟩

theorem no_target_lifting : ¬ (relativeMap admissible observations).TargetLifts := by
  intro lifts
  obtain ⟨lift, target, _⟩ := lifts isolated entryEvent observed_terminals_equal
  apply isolated_has_no_predecessor
  exact ⟨lift.source, target ▸ lift.step⟩

theorem no_past_matching :
    ¬ PastMatching (gsltSpan theory) (relativeSetoid admissible observations) := by
  intro matching
  exact no_target_lifting ((quotient_targetLifts_iff _ _).mpr matching)

theorem quotient_box_not_natural :
    gsltBox theory (fun _ => False) isolated ∧
      ¬ derivedBox (relativeSpan admissible observations) (fun _ => False)
        (relativeObserve admissible observations isolated) :=
  ⟨past_box_distinguishes.1, fun allIncoming => allIncoming entryEvent observed_terminals_equal⟩

theorem native_terminal_test_does_not_descend :
    ¬ PredicateDescends (relativeObserve admissible observations) (fun state => state = entered) := by
  intro descends
  have constant := (predicateDescends_iff _ _).mp descends
  have impossible := Mettapedia.GSLT.Scope.ConstantOnFibers.iff constant observed_terminals_equal
  exact State.noConfusion (impossible.mp rfl)

/-- The rejected test is still a legitimate native predicate of the authored
theory. Native equation invariance is weaker than behavioural descent. -/
theorem authored_native_terminal_test :
    EquationInvariant theory (fun state => state = entered) := by
  intro _ _ equivalent
  cases equivalent
  exact Iff.rfl

end DifferentPasts

namespace AddedOccurrence

def authored : ReductionSpan Bool where
  Edge := Bool
  source stage := stage
  target stage := !stage

/-- The second event coordinate is an extra occurrence at existing endpoints. -/
def enlarged : ReductionSpan Bool where
  Edge := Bool × Bool
  source event := event.1
  target event := !event.1

def inclusion : SpanMap authored enlarged where
  states := id
  events stage := (stage, false)
  source_comm _ := rfl
  target_comm _ := rfl

theorem sourceLifts : inclusion.SourceLifts := by
  intro state event endpointEq
  exact ⟨state, rfl, congrArg Bool.not endpointEq.symm⟩

theorem targetLifts : inclusion.TargetLifts := by
  intro _ event endpointEq
  exact ⟨event.1, endpointEq, rfl⟩

theorem no_occurrence_source_lifting : ¬ inclusion.SourceOccurrenceLifts := by
  intro lifts
  obtain ⟨lift, _, impossible⟩ := lifts false (false, true) rfl
  exact Bool.noConfusion (congrArg Prod.snd impossible)

theorem no_occurrence_target_lifting : ¬ inclusion.TargetOccurrenceLifts := by
  intro lifts
  obtain ⟨lift, _, impossible⟩ := lifts true (false, true) rfl
  exact Bool.noConfusion (congrArg Prod.snd impossible)

/-- Both state modalities commute even though the target adds a new event. -/
theorem modalities_cannot_detect_added_occurrence (predicate : Bool → Prop) (state : Bool) :
    (derivedDiamond enlarged predicate state ↔ derivedDiamond authored predicate state) ∧
      (derivedBox enlarged predicate state ↔ derivedBox authored predicate state) :=
  ⟨inclusion.diamond_pullback sourceLifts predicate state,
    inclusion.box_pullback targetLifts predicate state⟩

theorem extra_event_not_in_image : ¬ ∃ event, inclusion.events event = (false, true) := by
  rintro ⟨_, impossible⟩
  exact Bool.noConfusion (congrArg Prod.snd impossible)

end AddedOccurrence

namespace RestrictedTaggedEvents

open CategoryTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open Mettapedia.GSLT.Topos.PresheafEventModalities
open scoped Mettapedia.GSLT.Topos.ConstructivePresheaf

abbrev sourceEvents := Mettapedia.GSLT.Topos.PresheafEventModalities.Controls.eventSections
abbrev sourceGraph := Mettapedia.GSLT.Topos.PresheafEventModalities.Controls.growing

def vertices : ℕ ⥤ Type where
  obj _ := Bool × Bool
  map _ := TypeCat.ofHom id

def events : ℕ ⥤ Type where
  obj n := sourceEvents.obj n × Bool × Bool
  map restriction := TypeCat.ofHom (fun event =>
    (sourceEvents.map restriction event.1, event.2))
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro event
    exact Prod.ext (sourceEvents.map_id_apply _ event.1) rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro event
    exact Prod.ext (sourceEvents.map_comp_apply first second event.1) rfl

/-- Tags are retained, and an event becomes available only at positive stages.
The event presheaf is not a constant wrapper. -/
def authored : EventGraph ℕ where
  vertex := vertices
  edge := events
  source :=
    { app _ := TypeCat.ofHom (fun event => (false, event.2.1))
      naturality _ _ _ := rfl }
  target :=
    { app _ := TypeCat.ofHom (fun event => (true, event.2.2))
      naturality _ _ _ := rfl }

def observation : Presheaf.EventObservation authored sourceGraph where
  states :=
    { app _ := TypeCat.ofHom Prod.fst
      naturality _ _ _ := rfl }
  events :=
    { app _ := TypeCat.ofHom Prod.fst
      naturality _ _ _ := rfl }
  source_comm _ _ := rfl
  target_comm _ _ := rfl

theorem sourceLifts : observation.SourceLifts := by
  intro _ state event endpointEq
  exact ⟨(event, state.2, false), Prod.ext endpointEq rfl, rfl⟩

theorem targetLifts : observation.TargetLifts := by
  intro _ state event endpointEq
  exact ⟨(event, false, state.2), Prod.ext endpointEq rfl, rfl⟩

theorem modal_comparison (predicate : Subfunctor sourceGraph.vertex)
    (stage : ℕ) (state : authored.vertex.obj stage) :
    (observation.states.app stage state ∈ (diamond sourceGraph predicate).obj stage ↔
      state ∈ (diamond authored (preimage observation.states predicate)).obj stage) ∧
    (observation.states.app stage state ∈ (box sourceGraph predicate).obj stage ↔
      state ∈ (box authored (preimage observation.states predicate)).obj stage) :=
  ⟨observation.diamond_pullback sourceLifts predicate stage state,
    observation.box_pullback targetLifts predicate stage state⟩

theorem no_current_event_at_zero : ¬ Nonempty (authored.edge.obj 0) := by
  rintro ⟨event⟩
  exact Nat.not_lt_zero 0 event.1.down

theorem pointwise_box_at_zero :
    ∀ event : authored.edge.obj 0, authored.target.app 0 event = (true, false) → False := by
  intro event
  exact (Nat.not_lt_zero 0 event.1.down).elim

/-- The real box rejects the earlier state despite its empty current event
fibre, because a restriction exposes an actual incoming event. -/
theorem internal_box_rejects_zero :
    (true, false) ∉
      (box authored (preimage observation.states (⊥ : Subfunctor sourceGraph.vertex))).obj 0 := by
  intro holds
  have observed := (observation.box_pullback targetLifts _ 0 (true, false)).mpr holds
  exact Mettapedia.GSLT.Topos.PresheafEventModalities.Controls.internal_box_rejects_zero observed

def tagPredicate : Subfunctor authored.vertex where
  obj _ := {state | state.2 = true}
  map _ _ holds := holds

theorem tag_predicate_does_not_descend :
    ¬ Presheaf.PredicateDescends observation tagPredicate := by
  intro descends
  have constant := (Presheaf.predicateDescends_iff _ _).mp descends 0
  have impossible := Mettapedia.GSLT.Scope.ConstantOnFibers.iff constant
    (a := (false, true)) (b := (false, false)) rfl
  exact Bool.noConfusion (impossible.mp rfl)

end RestrictedTaggedEvents

end Mettapedia.GSLT.ObservationSpans.Controls
