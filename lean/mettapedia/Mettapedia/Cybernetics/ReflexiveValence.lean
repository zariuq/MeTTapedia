import Mathlib.CategoryTheory.Category.Basic

/-!
# Reflexive valence as propagated separation and formation

This module gives a process-level formalization of a relational account of
pain and joy.  A separation or formation is initially only proto-valenced.
Pain or joy requires a nonempty propagation path into a reflexive
representation which itself separates or forms.  Suffering and happiness are
stronger again: they require a genuinely self-sustaining propagation carrier,
not merely several consecutive observations.

The definitions are deliberately structural.  They do not identify valence
with a scalar, model accuracy, duration, or any particular physical
substrate.  Morphisms preserve propagation, reflexive representation, and
both relational polarities; consequently they preserve pain, joy, suffering,
and happiness.  This makes the ontology transportable without making it
observer-independent or claiming that these necessary structural conditions
are a complete theory of experience.

The positive and negative examples distinguish:

* proto-pain from reflexively propagated pain;
* a finite run of separating events from an auto-propagating cascade;
* a separating loop from a forming loop.

Reference: "On the Ontology of Joy and Pain, Happiness and Suffering",
Garden of Minds.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.ReflexiveValence

open CategoryTheory

universe u

/-- A relational process substrate on which valence can be interpreted.
`propagates` records causal or representational transmission.  The two
polarities are not assumed to be exhaustive or disjoint. -/
structure System where
  Event : Type u
  propagates : Event -> Event -> Prop
  separates : Event -> Prop
  forms : Event -> Prop
  reflexiveRepresentation : Event -> Prop

/-- A nonempty, proof-relevant propagation path. -/
inductive PropagationPath (system : System.{u}) :
    system.Event -> system.Event -> Type u where
  | edge {source target : system.Event} :
      system.propagates source target -> PropagationPath system source target
  | trans {source middle target : system.Event} :
      PropagationPath system source middle ->
      PropagationPath system middle target ->
      PropagationPath system source target

namespace PropagationPath

variable {system : System.{u}} {source target : system.Event}

/-- Every nonempty path contains a genuine propagation edge. -/
theorem containsEdge (path : PropagationPath system source target) :
    exists first second, system.propagates first second := by
  induction path with
  | edge propagation => exact ⟨_, _, propagation⟩
  | trans _ _ firstPath _ => exact firstPath

end PropagationPath

/-- Proto-pain is the local polarity of a separation event. -/
def ProtoPain (system : System.{u}) (event : system.Event) : Prop :=
  system.separates event

/-- Proto-joy is the local polarity of a formation event. -/
def ProtoJoy (system : System.{u}) (event : system.Event) : Prop :=
  system.forms event

/-- Pain at `target` requires an originating separation, a nonempty
propagation path into a reflexive representation, and a new separation at
that representational level. -/
def PainAt (system : System.{u}) (target : system.Event) : Prop :=
  exists origin,
    ProtoPain system origin /\
    Nonempty (PropagationPath system origin target) /\
    system.reflexiveRepresentation target /\
    system.separates target

/-- Joy is the formation-polar dual of `PainAt`. -/
def JoyAt (system : System.{u}) (target : system.Event) : Prop :=
  exists origin,
    ProtoJoy system origin /\
    Nonempty (PropagationPath system origin target) /\
    system.reflexiveRepresentation target /\
    system.forms target

/-- A self-sustaining propagation carrier for a selected signal predicate.
Every event in the nonempty carrier bears the signal and has a successor in
the same carrier.  No arbitrary duration threshold is involved. -/
structure Cascade (system : System.{u})
    (signal : system.Event -> Prop) : Type u where
  carrier : Set system.Event
  inhabited : carrier.Nonempty
  advances : forall event, event ∈ carrier ->
    exists next, next ∈ carrier /\
      Nonempty (PropagationPath system event next)
  carries : forall event, event ∈ carrier -> signal event

/-- Suffering is the existence of a self-sustaining separation cascade. -/
def Suffering (system : System.{u}) : Prop :=
  Nonempty (Cascade system system.separates)

/-- Happiness is the existence of a self-sustaining formation cascade. -/
def Happiness (system : System.{u}) : Prop :=
  Nonempty (Cascade system system.forms)

/-! ## Structure-preserving maps -/

/-- A map of valence systems preserves the process relation, both polarities,
and the reflexive-representation boundary. -/
structure Hom (source target : System.{u}) where
  toFun : source.Event -> target.Event
  map_propagates : forall {first second}, source.propagates first second ->
    target.propagates (toFun first) (toFun second)
  map_separates : forall {event}, source.separates event ->
    target.separates (toFun event)
  map_forms : forall {event}, source.forms event ->
    target.forms (toFun event)
  map_reflexiveRepresentation : forall {event},
    source.reflexiveRepresentation event ->
    target.reflexiveRepresentation (toFun event)

@[ext]
theorem Hom.ext {source target : System.{u}} {left right : Hom source target}
    (equal : left.toFun = right.toFun) : left = right := by
  cases left
  cases right
  cases equal
  rfl

/-- Valence systems and structure-preserving maps form a category. -/
instance : Category.{u} (System.{u}) where
  Hom := Hom
  id system := {
    toFun := id
    map_propagates := fun propagation => propagation
    map_separates := fun separation => separation
    map_forms := fun formation => formation
    map_reflexiveRepresentation := fun reflexive => reflexive }
  comp first second := {
    toFun := second.toFun ∘ first.toFun
    map_propagates := fun propagation =>
      second.map_propagates (first.map_propagates propagation)
    map_separates := fun separation =>
      second.map_separates (first.map_separates separation)
    map_forms := fun formation =>
      second.map_forms (first.map_forms formation)
    map_reflexiveRepresentation := fun reflexive =>
      second.map_reflexiveRepresentation
        (first.map_reflexiveRepresentation reflexive) }
  id_comp := by intros; ext; rfl
  comp_id := by intros; ext; rfl
  assoc := by intros; ext; rfl

namespace PropagationPath

variable {source target : System.{u}} {first second : source.Event}

/-- Structure-preserving maps transport complete propagation histories. -/
def map (morphism : source ⟶ target) :
    {first second : source.Event} -> PropagationPath source first second ->
      PropagationPath target (morphism.toFun first) (morphism.toFun second)
  | _, _, .edge propagation =>
      .edge (morphism.map_propagates propagation)
  | _, _, .trans firstPath secondPath =>
      .trans (map morphism firstPath) (map morphism secondPath)

end PropagationPath

/-- Pain is invariant under structure-preserving interpretation. -/
theorem pain_map {source target : System.{u}} (morphism : source ⟶ target)
    {event : source.Event} (pain : PainAt source event) :
    PainAt target (morphism.toFun event) := by
  rcases pain with ⟨origin, originSeparates, ⟨path⟩,
    reflexive, targetSeparates⟩
  exact ⟨morphism.toFun origin,
    morphism.map_separates originSeparates,
    ⟨path.map morphism⟩,
    morphism.map_reflexiveRepresentation reflexive,
    morphism.map_separates targetSeparates⟩

/-- Joy is invariant under structure-preserving interpretation. -/
theorem joy_map {source target : System.{u}} (morphism : source ⟶ target)
    {event : source.Event} (joy : JoyAt source event) :
    JoyAt target (morphism.toFun event) := by
  rcases joy with ⟨origin, originForms, ⟨path⟩,
    reflexive, targetForms⟩
  exact ⟨morphism.toFun origin,
    morphism.map_forms originForms,
    ⟨path.map morphism⟩,
    morphism.map_reflexiveRepresentation reflexive,
    morphism.map_forms targetForms⟩

namespace Cascade

variable {source target : System.{u}} {signal : source.Event -> Prop}
  {targetSignal : target.Event -> Prop}

/-- A signal-preserving map transports a self-sustaining cascade. -/
def map (morphism : source ⟶ target) (cascade : Cascade source signal)
    (mapsSignal : forall {event}, signal event ->
      targetSignal (morphism.toFun event)) : Cascade target targetSignal where
  carrier := Set.image morphism.toFun cascade.carrier
  inhabited := by
    rcases cascade.inhabited with ⟨event, member⟩
    exact ⟨morphism.toFun event, ⟨event, member, rfl⟩⟩
  advances := by
    rintro _ ⟨event, member, rfl⟩
    rcases cascade.advances event member with
      ⟨next, nextMember, ⟨path⟩⟩
    exact ⟨morphism.toFun next, ⟨next, nextMember, rfl⟩,
      ⟨path.map morphism⟩⟩
  carries := by
    rintro _ ⟨event, member, rfl⟩
    exact mapsSignal (cascade.carries event member)

end Cascade

/-- Suffering cascades survive structure-preserving interpretation. -/
theorem suffering_map {source target : System.{u}} (morphism : source ⟶ target)
    (suffering : Suffering source) : Suffering target := by
  rcases suffering with ⟨cascade⟩
  exact ⟨cascade.map morphism (fun separation =>
    morphism.map_separates separation)⟩

/-- Happiness cascades survive structure-preserving interpretation. -/
theorem happiness_map {source target : System.{u}} (morphism : source ⟶ target)
    (happiness : Happiness source) : Happiness target := by
  rcases happiness with ⟨cascade⟩
  exact ⟨cascade.map morphism (fun formation =>
    morphism.map_forms formation)⟩

/-! ## Discriminating examples -/

namespace Canary

inductive PainEvent where
  | origin
  | signal
  | representation
  deriving DecidableEq

inductive painPropagation : PainEvent -> PainEvent -> Prop where
  | origin_signal : painPropagation .origin .signal
  | signal_representation : painPropagation .signal .representation

/-- A separation propagates through a signal into a reflexive separation. -/
def painSystem : System where
  Event := PainEvent
  propagates := painPropagation
  separates
    | .origin => True
    | .signal => False
    | .representation => True
  forms := fun _ => False
  reflexiveRepresentation
    | .representation => True
    | _ => False

/-- The source-faithful positive witness: reflexive propagation creates pain. -/
theorem pain_at_representation :
    PainAt painSystem .representation := by
  refine ⟨.origin, trivial, ⟨?path⟩, trivial, trivial⟩
  exact PropagationPath.trans
    (.edge painPropagation.origin_signal)
    (.edge painPropagation.signal_representation)

/-- An isolated separation is proto-pain but cannot be pain because nothing
propagates into its reflexive model. -/
def isolatedSeparation : System where
  Event := Unit
  propagates := fun _ _ => False
  separates := fun _ => True
  forms := fun _ => False
  reflexiveRepresentation := fun _ => True

theorem isolated_protoPain_but_not_pain :
    ProtoPain isolatedSeparation () /\
      ¬ PainAt isolatedSeparation () := by
  refine ⟨trivial, ?_⟩
  rintro ⟨_, _, ⟨path⟩, _, _⟩
  rcases path.containsEdge with ⟨first, second, propagation⟩
  exact propagation

/-- A one-event separating loop is a genuine auto-propagating suffering
cascade. -/
def separatingLoop : System where
  Event := Unit
  propagates := fun _ _ => True
  separates := fun _ => True
  forms := fun _ => False
  reflexiveRepresentation := fun _ => True

theorem separatingLoop_suffers : Suffering separatingLoop := by
  refine ⟨{
    carrier := fun _ => True
    inhabited := ⟨(show separatingLoop.Event from ()), trivial⟩
    advances := ?_
    carries := ?_ }⟩
  · intro event _
    exact ⟨event, trivial, ⟨.edge trivial⟩⟩
  · intro _ _
    trivial

/-- The formation-polar loop is happy and is not a suffering cascade. -/
def formingLoop : System where
  Event := Unit
  propagates := fun _ _ => True
  separates := fun _ => False
  forms := fun _ => True
  reflexiveRepresentation := fun _ => True

theorem formingLoop_happy_not_suffering :
    Happiness formingLoop /\ ¬ Suffering formingLoop := by
  constructor
  · refine ⟨{
      carrier := fun _ => True
      inhabited := ⟨(show formingLoop.Event from ()), trivial⟩
      advances := ?_
      carries := ?_ }⟩
    · intro event _
      exact ⟨event, trivial, ⟨.edge trivial⟩⟩
    · intro _ _
      trivial
  · rintro ⟨cascade⟩
    rcases cascade.inhabited with ⟨event, member⟩
    exact cascade.carries event member

/-- A finite separating process with a terminal event.  It can look like a
sustained run under a bounded observer, but it is not auto-propagating. -/
def terminalSeparation : System where
  Event := Bool
  propagates := fun source target => source = false /\ target = true
  separates := fun _ => True
  forms := fun _ => False
  reflexiveRepresentation := fun _ => True

theorem terminalSeparation_all_events_separate :
    forall event, terminalSeparation.separates event := by
  intro _
  trivial

theorem terminalSeparation_path_endpoints :
    {source target : Bool} ->
      PropagationPath terminalSeparation source target ->
        source = false /\ target = true
  | _, _, .edge propagation => propagation
  | _, _, .trans firstPath secondPath => by
      have firstEndpoints :=
        terminalSeparation_path_endpoints firstPath
      have secondEndpoints :=
        terminalSeparation_path_endpoints secondPath
      have impossible : true = false :=
        firstEndpoints.2.symm.trans secondEndpoints.1
      exact Bool.noConfusion impossible

theorem terminalSeparation_no_path_from_true {target : Bool}
    (path : PropagationPath terminalSeparation true target) : False := by
  exact Bool.noConfusion (terminalSeparation_path_endpoints path).1

theorem terminalSeparation_path_from_false_ends_true {target : Bool}
    (path : PropagationPath terminalSeparation false target) :
    target = true := by
  exact (terminalSeparation_path_endpoints path).2

theorem terminalSeparation_not_suffering :
    ¬ Suffering terminalSeparation := by
  rintro ⟨cascade⟩
  rcases cascade.inhabited with ⟨start, startMember⟩
  cases start with
  | false =>
      rcases cascade.advances false startMember with
        ⟨next, nextMember, ⟨path⟩⟩
      have nextIsTrue : next = true :=
        terminalSeparation_path_from_false_ends_true path
      subst next
      rcases cascade.advances true nextMember with
        ⟨after, _, ⟨terminalPath⟩⟩
      exact terminalSeparation_no_path_from_true terminalPath
  | true =>
      rcases cascade.advances true startMember with
        ⟨after, _, ⟨terminalPath⟩⟩
      exact terminalSeparation_no_path_from_true terminalPath

end Canary

end Mettapedia.Cybernetics.ReflexiveValence

#print axioms Mettapedia.Cybernetics.ReflexiveValence.pain_map
#print axioms Mettapedia.Cybernetics.ReflexiveValence.suffering_map
#print axioms Mettapedia.Cybernetics.ReflexiveValence.Canary.pain_at_representation
#print axioms Mettapedia.Cybernetics.ReflexiveValence.Canary.isolated_protoPain_but_not_pain
#print axioms Mettapedia.Cybernetics.ReflexiveValence.Canary.terminalSeparation_not_suffering
