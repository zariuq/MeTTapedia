import Mettapedia.GSLT.Logic.SaturatedRelativeBisimilarity
import Mettapedia.GSLT.Scope.PredicateDescent
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis
import Mettapedia.GSLT.Topos.PresheafEventModalities

/-!
# Observation of reduction spans

The state observation and the map of reduction occurrences are separate data.
Source endpoint lifting is exactly what future diamond needs; target endpoint
lifting is exactly what OSLF's predecessor-universal box needs. These modal
laws only compare observed endpoints, not the identities of event witnesses.

A quotient of states retains the original event carrier. Its future lifting
comes from bisimulation; past lifting requires an additional matching law.
Admissible contexts act on the relative quotient by the proved saturated
congruence, rather than by an assumed action on behavioural classes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ObservationSpans

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence

universe u v w e f g uContext uRule uAtom

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- An observation records its action on occurrences, not just a state map. -/
structure SpanMap (A : ReductionSpan.{u, e} X) (B : ReductionSpan.{v, f} Y) where
  states : X → Y
  events : A.Edge → B.Edge
  source_comm : ∀ event, B.source (events event) = states (A.source event)
  target_comm : ∀ event, B.target (events event) = states (A.target event)

namespace SpanMap

variable {A : ReductionSpan.{u, e} X} {B : ReductionSpan.{v, f} Y}
variable {C : ReductionSpan.{w, g} Z}

def identity (A : ReductionSpan.{u, e} X) : SpanMap A A where
  states := id
  events := id
  source_comm _ := rfl
  target_comm _ := rfl

def comp (second : SpanMap B C) (first : SpanMap A B) : SpanMap A C where
  states := second.states ∘ first.states
  events := second.events ∘ first.events
  source_comm event := (second.source_comm _).trans (congrArg second.states (first.source_comm event))
  target_comm event := (second.target_comm _).trans (congrArg second.states (first.target_comm event))

/-- Match an observed outgoing endpoint. The matching event need not have the
same observed event identity; this is exactly the state-predicate requirement. -/
def SourceLifts (map : SpanMap A B) : Prop :=
  ∀ (state : X) (event : B.Edge), B.source event = map.states state →
    ∃ lift : A.Edge, A.source lift = state ∧ map.states (A.target lift) = B.target event

/-- Match an observed incoming endpoint, needed by the step-past box. -/
def TargetLifts (map : SpanMap A B) : Prop :=
  ∀ (state : X) (event : B.Edge), B.target event = map.states state →
    ∃ lift : A.Edge, A.target lift = state ∧ map.states (A.source lift) = B.source event

/-- A stronger occurrence-level lifting law, deliberately distinct from modal
endpoint lifting. It is not implied by state modal naturality. -/
def SourceOccurrenceLifts (map : SpanMap A B) : Prop :=
  ∀ (state : X) (event : B.Edge), B.source event = map.states state →
    ∃ lift : A.Edge, A.source lift = state ∧ map.events lift = event

def TargetOccurrenceLifts (map : SpanMap A B) : Prop :=
  ∀ (state : X) (event : B.Edge), B.target event = map.states state →
    ∃ lift : A.Edge, A.target lift = state ∧ map.events lift = event

theorem sourceLifts_of_occurrence (map : SpanMap A B) (lifts : map.SourceOccurrenceLifts) :
    map.SourceLifts := by
  intro state event endpointEq
  obtain ⟨lift, source, observed⟩ := lifts state event endpointEq
  exact ⟨lift, source, (map.target_comm lift).symm.trans (congrArg B.target observed)⟩

theorem targetLifts_of_occurrence (map : SpanMap A B) (lifts : map.TargetOccurrenceLifts) :
    map.TargetLifts := by
  intro state event endpointEq
  obtain ⟨lift, target, observed⟩ := lifts state event endpointEq
  exact ⟨lift, target, (map.source_comm lift).symm.trans (congrArg B.source observed)⟩

theorem diamond_pullback (map : SpanMap A B) (lifts : map.SourceLifts)
    (predicate : Y → Prop) (state : X) :
    derivedDiamond B predicate (map.states state) ↔
      derivedDiamond A (predicate ∘ map.states) state := by
  constructor
  · rintro ⟨event, endpointEq, holds⟩
    obtain ⟨lift, source, target⟩ := lifts state event endpointEq
    refine ⟨lift, source, ?_⟩
    change predicate (map.states (A.target lift))
    exact target ▸ holds
  · rintro ⟨event, source, holds⟩
    refine ⟨map.events event, (map.source_comm event).trans (congrArg map.states source), ?_⟩
    change predicate (B.target (map.events event))
    exact (map.target_comm event).symm ▸ holds

theorem sourceLifts_iff_diamond (map : SpanMap A B) :
    map.SourceLifts ↔ ∀ (predicate : Y → Prop) (state : X),
      derivedDiamond B predicate (map.states state) ↔
        derivedDiamond A (predicate ∘ map.states) state := by
  constructor
  · exact map.diamond_pullback
  · intro natural state event endpointEq
    have witness : derivedDiamond B (fun target => target = B.target event) (map.states state) :=
      ⟨event, endpointEq, rfl⟩
    exact (natural _ state).mp witness

theorem box_pullback (map : SpanMap A B) (lifts : map.TargetLifts)
    (predicate : Y → Prop) (state : X) :
    derivedBox B predicate (map.states state) ↔
      derivedBox A (predicate ∘ map.states) state := by
  constructor
  · intro holds event target
    have observed := holds (map.events event)
      ((map.target_comm event).trans (congrArg map.states target))
    change predicate (map.states (A.source event))
    exact map.source_comm event ▸ observed
  · intro holds event endpointEq
    obtain ⟨lift, target, source⟩ := lifts state event endpointEq
    change predicate (B.source event)
    exact source ▸ holds lift target

/-- Necessity is constructive: test with the predicate consisting of the
observed sources of actual incoming events. No excluded middle is used. -/
theorem targetLifts_iff_box (map : SpanMap A B) :
    map.TargetLifts ↔ ∀ (predicate : Y → Prop) (state : X),
      derivedBox B predicate (map.states state) ↔
        derivedBox A (predicate ∘ map.states) state := by
  constructor
  · exact map.box_pullback
  · intro natural state event endpointEq
    let incoming : Y → Prop := fun source =>
      ∃ lift : A.Edge, A.target lift = state ∧ map.states (A.source lift) = source
    have allIncoming : derivedBox A (incoming ∘ map.states) state :=
      fun lift target => ⟨lift, target, rfl⟩
    exact (natural incoming state).mpr allIncoming event endpointEq

theorem identity_sourceLifts (A : ReductionSpan.{u, e} X) : (identity A).SourceLifts :=
  fun _ event endpointEq => ⟨event, endpointEq, rfl⟩

theorem identity_targetLifts (A : ReductionSpan.{u, e} X) : (identity A).TargetLifts :=
  fun _ event endpointEq => ⟨event, endpointEq, rfl⟩

theorem comp_sourceLifts (second : SpanMap B C) (first : SpanMap A B)
    (secondLifts : second.SourceLifts) (firstLifts : first.SourceLifts) :
    (second.comp first).SourceLifts := by
  intro state event endpointEq
  obtain ⟨middle, source, target⟩ := secondLifts (first.states state) event endpointEq
  obtain ⟨lift, source', target'⟩ := firstLifts state middle source
  exact ⟨lift, source', (congrArg second.states target').trans target⟩

theorem comp_targetLifts (second : SpanMap B C) (first : SpanMap A B)
    (secondLifts : second.TargetLifts) (firstLifts : first.TargetLifts) :
    (second.comp first).TargetLifts := by
  intro state event endpointEq
  obtain ⟨middle, target, source⟩ := secondLifts (first.states state) event endpointEq
  obtain ⟨lift, target', source'⟩ := firstLifts state middle target
  exact ⟨lift, target', (congrArg second.states source').trans source⟩

@[simp] theorem comp_states (second : SpanMap B C) (first : SpanMap A B) (state : X) :
    (second.comp first).states state = second.states (first.states state) := rfl

@[simp] theorem comp_events (second : SpanMap B C) (first : SpanMap A B) (event : A.Edge) :
    (second.comp first).events event = second.events (first.events event) := rfl

end SpanMap

/-! ## The exact predicate descent criterion -/

/-- Existence of an actual predicate on observations whose pullback is the
given predicate. This asks no witness-selection operation on state fibres. -/
def PredicateDescends (observe : X → Y) (predicate : X → Prop) : Prop :=
  ∃ observed : Y → Prop, ∀ state, observed (observe state) ↔ predicate state

theorem predicateDescends_iff (observe : X → Y) (predicate : X → Prop) :
    PredicateDescends observe predicate ↔ ConstantOnFibers observe predicate := by
  constructor
  · rintro ⟨observed, reflects⟩ left right same
    apply propext
    exact (reflects left).symm.trans (same ▸ reflects right)
  · intro constant
    refine ⟨di observe predicate, ?_⟩
    intro state
    constructor
    · rintro ⟨witness, same, holds⟩
      exact (Mettapedia.GSLT.Scope.ConstantOnFibers.iff constant same).mp holds
    · intro holds
      exact ⟨state, rfl, holds⟩

theorem predicateDescends_iff_image_subset_universal (observe : X → Y)
    (predicate : X → Prop) :
    PredicateDescends observe predicate ↔
      observe '' {state | predicate state} ⊆ Set.kernImage observe {state | predicate state} :=
  (predicateDescends_iff observe predicate).trans
    (Mettapedia.GSLT.Scope.constantOnFibers_iff_image_subset_kernImage observe predicate)

theorem descended_pullback (observe : X → Y) (predicate : X → Prop)
    (constant : ConstantOnFibers observe predicate) (state : X) :
    di observe predicate (observe state) ↔ predicate state := by
  constructor
  · rintro ⟨witness, same, holds⟩
    exact (Mettapedia.GSLT.Scope.ConstantOnFibers.iff constant same).mp holds
  · intro holds
    exact ⟨state, rfl, holds⟩

theorem descended_unique (observe : X → Y) (onto : Function.Surjective observe)
    {first second : Y → Prop}
    (same : ∀ state, first (observe state) ↔ second (observe state)) : first = second := by
  funext observed
  obtain ⟨state, rfl⟩ := onto observed
  exact propext (same state)

namespace SpanMap

variable {A : ReductionSpan.{u, e} X} {B : ReductionSpan.{v, f} Y}

theorem diamond_descends (map : SpanMap A B) (lifts : map.SourceLifts)
    (predicate : X → Prop) (descends : PredicateDescends map.states predicate) :
    PredicateDescends map.states (derivedDiamond A predicate) := by
  obtain ⟨observed, reflects⟩ := descends
  have same : observed ∘ map.states = predicate := funext (fun state => propext (reflects state))
  refine ⟨derivedDiamond B observed, ?_⟩
  intro state
  rw [← same]
  exact map.diamond_pullback lifts observed state

theorem box_descends (map : SpanMap A B) (lifts : map.TargetLifts)
    (predicate : X → Prop) (descends : PredicateDescends map.states predicate) :
    PredicateDescends map.states (derivedBox A predicate) := by
  obtain ⟨observed, reflects⟩ := descends
  have same : observed ∘ map.states = predicate := funext (fun state => propext (reflects state))
  refine ⟨derivedBox B observed, ?_⟩
  intro state
  rw [← same]
  exact map.box_pullback lifts observed state

end SpanMap

/-! ## State quotients retain reduction occurrences -/

/-- Only endpoints are quotiented. The event type, including any multiplicity
and provenance it contains, is preserved without selecting representatives. -/
def quotientSpan (A : ReductionSpan.{u, e} X) (equations : Setoid X) :
    ReductionSpan.{u, e} (Quotient equations) where
  Edge := A.Edge
  source event := Quotient.mk equations (A.source event)
  target event := Quotient.mk equations (A.target event)

def quotientMap (A : ReductionSpan.{u, e} X) (equations : Setoid X) :
    SpanMap A (quotientSpan A equations) where
  states := Quotient.mk equations
  events := id
  source_comm _ := rfl
  target_comm _ := rfl

def FutureMatching (A : ReductionSpan.{u, e} X) (equations : Setoid X) : Prop :=
  ∀ ⦃left right : X⦄, equations.r left right →
    ∀ event : A.Edge, A.source event = left →
      ∃ matched : A.Edge, A.source matched = right ∧
        equations.r (A.target event) (A.target matched)

def PastMatching (A : ReductionSpan.{u, e} X) (equations : Setoid X) : Prop :=
  ∀ ⦃left right : X⦄, equations.r left right →
    ∀ event : A.Edge, A.target event = left →
      ∃ matched : A.Edge, A.target matched = right ∧
        equations.r (A.source event) (A.source matched)

theorem quotient_sourceLifts_iff (A : ReductionSpan.{u, e} X) (equations : Setoid X) :
    (quotientMap A equations).SourceLifts ↔ FutureMatching A equations := by
  constructor
  · intro lifts left right related event source
    have endpointEq : (quotientSpan A equations).source event = Quotient.mk equations right :=
      (congrArg (Quotient.mk equations) source).trans (Quotient.sound related)
    obtain ⟨matched, source', target⟩ := lifts right event endpointEq
    exact ⟨matched, source', equations.symm (Quotient.exact target)⟩
  · intro matching state event endpointEq
    obtain ⟨matched, source, related⟩ := matching (Quotient.exact endpointEq) event rfl
    exact ⟨matched, source, (Quotient.sound related).symm⟩

theorem quotient_targetLifts_iff (A : ReductionSpan.{u, e} X) (equations : Setoid X) :
    (quotientMap A equations).TargetLifts ↔ PastMatching A equations := by
  constructor
  · intro lifts left right related event target
    have endpointEq : (quotientSpan A equations).target event = Quotient.mk equations right :=
      (congrArg (Quotient.mk equations) target).trans (Quotient.sound related)
    obtain ⟨matched, target', source⟩ := lifts right event endpointEq
    exact ⟨matched, target', equations.symm (Quotient.exact source)⟩
  · intro matching state event endpointEq
    obtain ⟨matched, target, related⟩ := matching (Quotient.exact endpointEq) event rfl
    exact ⟨matched, target, (Quotient.sound related).symm⟩

theorem quotient_predicateDescends_iff (equations : Setoid X) (predicate : X → Prop) :
    PredicateDescends (Quotient.mk equations) predicate ↔
      ∀ ⦃left right⦄, equations.r left right → (predicate left ↔ predicate right) := by
  rw [predicateDescends_iff]
  constructor
  · intro constant left right related
    exact Mettapedia.GSLT.Scope.ConstantOnFibers.iff constant (Quotient.sound related)
  · intro invariant left right same
    exact propext (invariant (Quotient.exact same))

/-! ## The actual saturated relative quotient and its contexts -/

section Relative

variable {S : GSLT.{u}} {rules : ContextualRules.{uContext, uRule} S}
variable (A : AdmissibleClass rules) (observations : ContextualRules.Observations.{uAtom} S)

def relativeSetoid : Setoid S.Term where
  r := A.RelEquiv observations
  iseqv := A.relEquiv_equivalence observations

abbrev RelativeState := Quotient (relativeSetoid A observations)

def relativeObserve : S.Term → RelativeState A observations :=
  Quotient.mk (relativeSetoid A observations)

def relativeSpan : ReductionSpan (RelativeState A observations) :=
  quotientSpan (gsltSpan S) (relativeSetoid A observations)

def relativeMap : SpanMap (gsltSpan S) (relativeSpan A observations) :=
  quotientMap (gsltSpan S) (relativeSetoid A observations)

theorem relative_predicateDescends_iff (predicate : S.Term → Prop) :
    PredicateDescends (relativeObserve A observations) predicate ↔
      ∀ ⦃left right⦄, A.RelEquiv observations left right → (predicate left ↔ predicate right) :=
  quotient_predicateDescends_iff (relativeSetoid A observations) predicate

/-- This proof obtains an actual reduction at the chosen source representative
from the saturated bisimulation, then retains its occurrence as a span edge. -/
theorem relative_futureMatching : FutureMatching (gsltSpan S) (relativeSetoid A observations) := by
  intro left right related event source
  have step : S.Step left event.target := source ▸ event.step
  obtain ⟨target, step', related'⟩ :=
    (A.isReductionBisimulation_relEquiv observations).1.1 related step
  exact ⟨⟨right, target, step'⟩, rfl, related'⟩

theorem relative_sourceLifts : (relativeMap A observations).SourceLifts :=
  (quotient_sourceLifts_iff _ _).mpr (relative_futureMatching A observations)

theorem relative_diamond (predicate : RelativeState A observations → Prop) (state : S.Term) :
    derivedDiamond (relativeSpan A observations) predicate (relativeObserve A observations state) ↔
      gsltDiamond S (predicate ∘ relativeObserve A observations) state :=
  (relativeMap A observations).diamond_pullback (relative_sourceLifts A observations) predicate state

/-- A quotient transition from the class of a particular source has an actual
reduction at that source, with its target related to the requested target.
It is stronger than independently witnessing the two endpoint classes. -/
theorem relative_transition_iff (source target : S.Term) :
    derivedDiamond (relativeSpan A observations)
        (fun observed => observed = relativeObserve A observations target)
        (relativeObserve A observations source) ↔
      ∃ target', S.Step source target' ∧ A.RelEquiv observations target' target := by
  rw [relative_diamond, gsltDiamond_spec]
  constructor
  · rintro ⟨target', reduction, same⟩
    exact ⟨target', reduction, Quotient.exact same⟩
  · rintro ⟨target', reduction, related⟩
    exact ⟨target', reduction, Quotient.sound related⟩

theorem relative_box (past : PastMatching (gsltSpan S) (relativeSetoid A observations))
    (predicate : RelativeState A observations → Prop) (state : S.Term) :
    derivedBox (relativeSpan A observations) predicate (relativeObserve A observations state) ↔
      gsltBox S (predicate ∘ relativeObserve A observations) state :=
  (relativeMap A observations).box_pullback ((quotient_targetLifts_iff _ _).mpr past) predicate state

/-- Construct the context action using the existing congruence proof. -/
def contextAction (context : rules.Context) (admissible : A.Admissible context) :
    RelativeState A observations → RelativeState A observations :=
  Quotient.map (rules.plug context) (fun _ _ related =>
    A.relEquiv_closedUnder observations admissible related)

@[simp] theorem contextAction_observe (context : rules.Context)
    (admissible : A.Admissible context) (state : S.Term) :
    contextAction A observations context admissible (relativeObserve A observations state) =
      relativeObserve A observations (rules.plug context state) := rfl

theorem contextAction_identity (state : RelativeState A observations) :
    contextAction A observations rules.identity A.identity_mem state = state := by
  induction state using Quotient.inductionOn with
  | _ term =>
    exact Quotient.sound (A.relEquiv_of_equiv observations (rules.plug_identity term))

theorem contextAction_compose (outer inner : rules.Context)
    (outerAdmissible : A.Admissible outer) (innerAdmissible : A.Admissible inner)
    (state : RelativeState A observations) :
    contextAction A observations (rules.compose outer inner)
        (A.compose_mem outerAdmissible innerAdmissible) state =
      contextAction A observations outer outerAdmissible
        (contextAction A observations inner innerAdmissible state) := by
  induction state using Quotient.inductionOn with
  | _ term =>
    exact Quotient.sound (A.relEquiv_of_equiv observations (rules.plug_compose outer inner term))

/-- Descend an actual substitution only when it respects the selected
equivalence. Substitutions that reveal a forgotten observation are excluded. -/
def quotientSubstitution (substitution : S.Term → S.Term)
    (respects : ∀ ⦃left right⦄, A.RelEquiv observations left right →
      A.RelEquiv observations (substitution left) (substitution right)) :
    RelativeState A observations → RelativeState A observations :=
  Quotient.map substitution (fun _ _ related => respects related)

@[simp] theorem quotientSubstitution_observe (substitution : S.Term → S.Term)
    (respects : ∀ ⦃left right⦄, A.RelEquiv observations left right →
      A.RelEquiv observations (substitution left) (substitution right)) (state : S.Term) :
    quotientSubstitution A observations substitution respects (relativeObserve A observations state) =
      relativeObserve A observations (substitution state) := rfl

theorem quotientSubstitution_identity (state : RelativeState A observations) :
    quotientSubstitution A observations id (by intro _ _ related; exact related) state = state := by
  induction state using Quotient.inductionOn with
  | _ term => rfl

theorem quotientSubstitution_comp (first second : S.Term → S.Term)
    (firstRespects : ∀ ⦃left right⦄, A.RelEquiv observations left right →
      A.RelEquiv observations (first left) (first right))
    (secondRespects : ∀ ⦃left right⦄, A.RelEquiv observations left right →
      A.RelEquiv observations (second left) (second right)) (state : RelativeState A observations) :
    quotientSubstitution A observations (second ∘ first)
        (by intro _ _ related; exact secondRespects (firstRespects related)) state =
      quotientSubstitution A observations second secondRespects
        (quotientSubstitution A observations first firstRespects state) := by
  induction state using Quotient.inductionOn with
  | _ term => rfl

theorem contextAction_substitution (context : rules.Context) (admissible : A.Admissible context)
    (substitution : S.Term → S.Term)
    (respects : ∀ ⦃left right⦄, A.RelEquiv observations left right →
      A.RelEquiv observations (substitution left) (substitution right))
    (commutes : ∀ state, S.Equiv (substitution (rules.plug context state))
      (rules.plug context (substitution state))) (state : RelativeState A observations) :
    quotientSubstitution A observations substitution respects
        (contextAction A observations context admissible state) =
      contextAction A observations context admissible
        (quotientSubstitution A observations substitution respects state) := by
  induction state using Quotient.inductionOn with
  | _ term =>
    exact Quotient.sound (A.relEquiv_of_equiv observations (commutes term))

end Relative

/-! ## Restriction-natural event observations

These comparisons use the actual presheaf modalities. In particular, the box
ranges over every restriction and its incoming events. Pointwise box would
omit that requirement.
-/

namespace Presheaf

open CategoryTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open Mettapedia.GSLT.Topos.PresheafEventModalities

variable {C : Type u} [Category.{v} C]

structure EventObservation (A B : EventGraph.{u, v, w} C) where
  states : NatTrans A.vertex B.vertex
  events : NatTrans A.edge B.edge
  source_comm : ∀ (X : C) (event : A.edge.obj X),
    B.source.app X (events.app X event) = states.app X (A.source.app X event)
  target_comm : ∀ (X : C) (event : A.edge.obj X),
    B.target.app X (events.app X event) = states.app X (A.target.app X event)

namespace EventObservation

variable {A B D : EventGraph.{u, v, w} C}

theorem states_restrict (observation : EventObservation A B) {X Y : C}
    (restriction : X ⟶ Y) (state : A.vertex.obj X) :
    observation.states.app Y (A.vertex.map restriction state) =
      B.vertex.map restriction (observation.states.app X state) :=
  congrArg (fun h : A.vertex.obj X ⟶ B.vertex.obj Y => h state)
    (observation.states.naturality restriction)

theorem events_restrict (observation : EventObservation A B) {X Y : C}
    (restriction : X ⟶ Y) (event : A.edge.obj X) :
    observation.events.app Y (A.edge.map restriction event) =
      B.edge.map restriction (observation.events.app X event) :=
  congrArg (fun h : A.edge.obj X ⟶ B.edge.obj Y => h event)
    (observation.events.naturality restriction)

def identity (A : EventGraph.{u, v, w} C) : EventObservation A A where
  states := { app := fun _ => TypeCat.ofHom id, naturality := by intro _ _ _; rfl }
  events := { app := fun _ => TypeCat.ofHom id, naturality := by intro _ _ _; rfl }
  source_comm _ _ := rfl
  target_comm _ _ := rfl

def comp (second : EventObservation B D) (first : EventObservation A B) :
    EventObservation A D where
  states :=
    { app := fun X => TypeCat.ofHom (second.states.app X ∘ first.states.app X)
      naturality := by
        intro X Y restriction
        ext state
        change second.states.app Y (first.states.app Y (A.vertex.map restriction state)) =
          D.vertex.map restriction (second.states.app X (first.states.app X state))
        rw [first.states_restrict restriction, second.states_restrict restriction] }
  events :=
    { app := fun X => TypeCat.ofHom (second.events.app X ∘ first.events.app X)
      naturality := by
        intro X Y restriction
        ext event
        change second.events.app Y (first.events.app Y (A.edge.map restriction event)) =
          D.edge.map restriction (second.events.app X (first.events.app X event))
        rw [first.events_restrict restriction, second.events_restrict restriction] }
  source_comm X event :=
    (second.source_comm X _).trans (congrArg (second.states.app X) (first.source_comm X event))
  target_comm X event :=
    (second.target_comm X _).trans (congrArg (second.states.app X) (first.target_comm X event))

def SourceLifts (observation : EventObservation A B) : Prop :=
  ∀ (X : C) (state : A.vertex.obj X) (event : B.edge.obj X),
    B.source.app X event = observation.states.app X state →
      ∃ lift : A.edge.obj X, A.source.app X lift = state ∧
        observation.states.app X (A.target.app X lift) = B.target.app X event

def TargetLifts (observation : EventObservation A B) : Prop :=
  ∀ (X : C) (state : A.vertex.obj X) (event : B.edge.obj X),
    B.target.app X event = observation.states.app X state →
      ∃ lift : A.edge.obj X, A.target.app X lift = state ∧
        observation.states.app X (A.source.app X lift) = B.source.app X event

theorem comp_sourceLifts (second : EventObservation B D) (first : EventObservation A B)
    (secondLifts : second.SourceLifts) (firstLifts : first.SourceLifts) :
    (second.comp first).SourceLifts := by
  intro X state event endpointEq
  obtain ⟨middle, source, target⟩ := secondLifts X (first.states.app X state) event endpointEq
  obtain ⟨lift, source', target'⟩ := firstLifts X state middle source
  exact ⟨lift, source', (congrArg (second.states.app X) target').trans target⟩

theorem comp_targetLifts (second : EventObservation B D) (first : EventObservation A B)
    (secondLifts : second.TargetLifts) (firstLifts : first.TargetLifts) :
    (second.comp first).TargetLifts := by
  intro X state event endpointEq
  obtain ⟨middle, target, source⟩ := secondLifts X (first.states.app X state) event endpointEq
  obtain ⟨lift, target', source'⟩ := firstLifts X state middle target
  exact ⟨lift, target', (congrArg (second.states.app X) source').trans source⟩

theorem diamond_pullback (observation : EventObservation A B) (lifts : observation.SourceLifts)
    (predicate : Subfunctor B.vertex) (X : C) (state : A.vertex.obj X) :
    observation.states.app X state ∈ (diamond B predicate).obj X ↔
      state ∈ (diamond A (preimage observation.states predicate)).obj X := by
  constructor
  · rintro ⟨event, holds, endpointEq⟩
    obtain ⟨lift, source, target⟩ := lifts X state event endpointEq
    refine ⟨lift, ?_, source⟩
    change observation.states.app X (A.target.app X lift) ∈ predicate.obj X
    exact target ▸ holds
  · rintro ⟨event, holds, source⟩
    refine ⟨observation.events.app X event, ?_,
      (observation.source_comm X event).trans (congrArg (observation.states.app X) source)⟩
    change B.target.app X (observation.events.app X event) ∈ predicate.obj X
    exact (observation.target_comm X event).symm ▸ holds

theorem box_pullback (observation : EventObservation A B) (lifts : observation.TargetLifts)
    (predicate : Subfunctor B.vertex) (X : C) (state : A.vertex.obj X) :
    observation.states.app X state ∈ (box B predicate).obj X ↔
      state ∈ (box A (preimage observation.states predicate)).obj X := by
  constructor
  · intro holds Y restriction event endpointEq
    have observedTarget : B.target.app Y (observation.events.app Y event) =
        B.vertex.map restriction (observation.states.app X state) :=
      ((observation.target_comm Y event).trans
        (congrArg (observation.states.app Y) endpointEq)).trans
          (observation.states_restrict restriction state)
    have observedSource := holds Y restriction (observation.events.app Y event) observedTarget
    change observation.states.app Y (A.source.app Y event) ∈ predicate.obj Y
    exact observation.source_comm Y event ▸ observedSource
  · intro holds Y restriction event endpointEq
    have observedTarget : B.target.app Y event =
        observation.states.app Y (A.vertex.map restriction state) :=
      endpointEq.trans (observation.states_restrict restriction state).symm
    obtain ⟨lift, target, source⟩ := lifts Y (A.vertex.map restriction state) event observedTarget
    change B.source.app Y event ∈ predicate.obj Y
    exact source ▸ holds Y restriction lift target

theorem diamond_preimage (observation : EventObservation A B) (lifts : observation.SourceLifts)
    (predicate : Subfunctor B.vertex) :
    preimage observation.states (diamond B predicate) =
      diamond A (preimage observation.states predicate) := by
  apply Subfunctor.ext
  funext X
  funext state
  exact propext (observation.diamond_pullback lifts predicate X state)

theorem box_preimage (observation : EventObservation A B) (lifts : observation.TargetLifts)
    (predicate : Subfunctor B.vertex) :
    preimage observation.states (box B predicate) =
      box A (preimage observation.states predicate) := by
  apply Subfunctor.ext
  funext X
  funext state
  exact propext (observation.box_pullback lifts predicate X state)

end EventObservation

/-- Descent includes the restriction law of the resulting predicate. -/
def PredicateDescends {A B : EventGraph.{u, v, w} C} (observation : EventObservation A B)
    (predicate : Subfunctor A.vertex) : Prop :=
  ∃ observed : Subfunctor B.vertex, ∀ (X : C) (state : A.vertex.obj X),
    observation.states.app X state ∈ observed.obj X ↔ state ∈ predicate.obj X

/-- The canonical existential image is already restriction-natural. Thus
pointwise fibre constancy is an exact criterion even for genuine subfunctors. -/
theorem predicateDescends_iff {A B : EventGraph.{u, v, w} C}
    (observation : EventObservation A B) (predicate : Subfunctor A.vertex) :
    PredicateDescends observation predicate ↔
      ∀ X, ConstantOnFibers (observation.states.app X) (predicate.obj X) := by
  constructor
  · rintro ⟨observed, reflects⟩ X
    exact (ObservationSpans.predicateDescends_iff _ _).mp ⟨observed.obj X, reflects X⟩
  · intro constant
    refine ⟨image observation.states predicate, ?_⟩
    intro X state
    constructor
    · rintro ⟨witness, holds, same⟩
      exact (Mettapedia.GSLT.Scope.ConstantOnFibers.iff (constant X) same).mp holds
    · intro holds
      exact ⟨state, holds, rfl⟩

theorem diamond_descends {A B : EventGraph.{u, v, w} C}
    (observation : EventObservation A B) (lifts : observation.SourceLifts)
    (predicate : Subfunctor A.vertex) (descends : PredicateDescends observation predicate) :
    PredicateDescends observation (diamond A predicate) := by
  obtain ⟨observed, reflects⟩ := descends
  have same : preimage observation.states observed = predicate := by
    apply Subfunctor.ext
    funext X
    funext state
    exact propext (reflects X state)
  refine ⟨diamond B observed, ?_⟩
  intro X state
  rw [← same]
  exact observation.diamond_pullback lifts observed X state

theorem box_descends {A B : EventGraph.{u, v, w} C}
    (observation : EventObservation A B) (lifts : observation.TargetLifts)
    (predicate : Subfunctor A.vertex) (descends : PredicateDescends observation predicate) :
    PredicateDescends observation (box A predicate) := by
  obtain ⟨observed, reflects⟩ := descends
  have same : preimage observation.states observed = predicate := by
    apply Subfunctor.ext
    funext X
    funext state
    exact propext (reflects X state)
  refine ⟨box B observed, ?_⟩
  intro X state
  rw [← same]
  exact observation.box_pullback lifts observed X state

end Presheaf

end Mettapedia.GSLT.ObservationSpans
