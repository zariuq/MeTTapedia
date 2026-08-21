import Mettapedia.GSLT.Dynamics.CompositeObservationDiscipline
import Mettapedia.PLN.WorldModel.Semitopology.PLNSemitopology

/-!
# A counting × coalition composite observer

This module gives a small formal witness for the composite-observer example:

* the counting component retains a bag of card-rank occurrences, so
  multiplicity is not contracted away;
* the room-reading component retains the exact witnessed coalitions and uses
  the existing quorum semitopology to decide which are actionable;
* their parallel composite retains both coordinates over an interleaved
  history, and independent cross-component events commute observationally.

This is an observation-level construction, not a poker strategy or a proof
that the two collection monads support no distributive law.  The components are
composed as separate disciplines; they are not identified with a single
merged logic.
-/

namespace Mettapedia.PLN.Bridges.GSLT.CompositeObservationMind

open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.ObservationDiscipline
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.Semitopology

/-! ## The two event families -/

/-- Card ranks are enough for the counting half of the example. -/
abbrev CardEvent := Fin 13

/-- Three representative room observations from the established quorum
semitopology. -/
inductive RoomEvent where
  | coalition01
  | coalition02
  | singletonZero
  deriving DecidableEq, Repr

/-- Interpret a room event as the participant set it reports. -/
def RoomEvent.members : RoomEvent -> Set (Fin 3)
  | .coalition01 => Mettapedia.PLN.WorldModel.Semitopology.coalition01
  | .coalition02 => Mettapedia.PLN.WorldModel.Semitopology.coalition02
  | .singletonZero => {0}

/-- Computational actionable-coalition readout for the three fixtures. -/
def RoomEvent.isActionable : RoomEvent -> Bool
  | .coalition01 => true
  | .coalition02 => true
  | .singletonZero => false

/-- The Boolean room readout agrees with the existing semitopological
semantics on every fixture. -/
theorem roomEvent_isActionable_iff (event : RoomEvent) :
    event.isActionable = true ↔
      quorumSemitopology.actionable event.members := by
  cases event with
  | coalition01 =>
      simp [RoomEvent.isActionable, RoomEvent.members,
        quorumSemitopology_actionable_coalition01]
  | coalition02 =>
      simp [RoomEvent.isActionable, RoomEvent.members,
        quorumSemitopology_actionable_coalition02]
  | singletonZero =>
      simp [RoomEvent.isActionable, RoomEvent.members,
        quorumSemitopology_not_actionable_singleton_zero]

/-! ## Separate disciplines -/

/-- Linear counting retains a multiset: order is forgotten, multiplicity is
not. -/
def cardBagCollection : WitnessCollector CardEvent where
  Container := Multiset CardEvent
  collect := fun events => some (events : Multiset CardEvent)

/-- The full bag is retained as the value; later readouts may count any rank. -/
def cardBag : ObservationDiscipline CardEvent where
  collection := cardBagCollection
  Value := Multiset CardEvent
  readout := id

theorem cardBag_total : cardBag.collection.Total := by
  intro events
  exact ⟨(events : Multiset CardEvent), rfl⟩

/-- Room reading retains the exact sequence of witnessed coalition fixtures. -/
def roomWitnessCollection : WitnessCollector RoomEvent where
  Container := List RoomEvent
  collect := some

def roomWitness : ObservationDiscipline RoomEvent where
  collection := roomWitnessCollection
  Value := List RoomEvent
  readout := id

theorem roomWitness_total : roomWitness.collection.Total := by
  intro events
  exact ⟨events, rfl⟩

/-- A coarser control readout asks merely whether some witnessed coalition is
actionable.  The exact witnesses remain in `S`, even though `V` is Boolean. -/
def actionableRoom : ObservationDiscipline RoomEvent :=
  roomWitness.mapValue fun events => events.any RoomEvent.isActionable

@[simp] theorem actionableRoom_coalition01 :
    actionableRoom.observe [.coalition01] = some true :=
  rfl

@[simp] theorem actionableRoom_coalition02 :
    actionableRoom.observe [.coalition02] = some true :=
  rfl

@[simp] theorem actionableRoom_singletonZero :
    actionableRoom.observe [.singletonZero] = some false :=
  rfl

/-- The Boolean control readout deliberately forgets which actionable
coalition was witnessed. -/
theorem actionableRoom_isLossy : actionableRoom.Lossy := by
  apply ObservationDiscipline.lossy_of_collision
    (first := [RoomEvent.coalition01])
    (second := [RoomEvent.coalition02])
  · intro equal
    have equalHeads := congrArg List.head? equal
    simp at equalHeads
  · rfl

/-! ## The composite observer -/

/-- Counting and room reading run as separate disciplines over one interleaved
history. -/
def composite : ObservationDiscipline (Sum CardEvent RoomEvent) :=
  parallelComposite cardBag roomWitness

def ace : CardEvent := 0

def twoAces : Multiset CardEvent := ([ace, ace] : List CardEvent)

def pokerObservation : List (Sum CardEvent RoomEvent) :=
  [.inl ace, .inr .coalition01, .inl ace]

/-- Positive witness: the composite simultaneously retains card multiplicity
and the coalition observation. -/
@[simp] theorem composite_observe_pokerObservation :
    composite.observe pokerObservation =
      some (twoAces, [RoomEvent.coalition01]) :=
  rfl

/-- The bag really records two occurrences rather than contracting them. -/
@[simp] theorem pokerObservation_ace_count : twoAces.count ace = 2 := by
  decide

def room01History : List (Sum CardEvent RoomEvent) :=
  [.inl ace, .inr .coalition01]

def room02History : List (Sum CardEvent RoomEvent) :=
  [.inl ace, .inr .coalition02]

/-- Counting alone cannot distinguish two histories with the same card events
but different room observations. -/
theorem card_projection_identifies_room_change :
    cardBag.observe (leftProjection room01History) =
      cardBag.observe (leftProjection room02History) :=
  rfl

/-- The room component does distinguish those histories. -/
theorem room_projection_distinguishes_room_change :
    roomWitness.observe (rightProjection room01History) ≠
      roomWitness.observe (rightProjection room02History) := by
  simp [room01History, room02History, roomWitness,
    roomWitnessCollection, ObservationDiscipline.observe]

/-- Therefore the distinction survives in the composite observer. -/
theorem composite_distinguishes_room_change :
    composite.observe room01History ≠ composite.observe room02History :=
  parallelComposite_distinguishes_of_right cardBag roomWitness cardBag_total
    room_projection_distinguishes_room_change

def oneAceHistory : List (Sum CardEvent RoomEvent) :=
  [.inl ace, .inr .coalition01]

def twoAceHistory : List (Sum CardEvent RoomEvent) :=
  [.inl ace, .inl ace, .inr .coalition01]

/-- Room reading alone cannot see a change in card multiplicity. -/
theorem room_projection_identifies_card_change :
    roomWitness.observe (rightProjection oneAceHistory) =
      roomWitness.observe (rightProjection twoAceHistory) :=
  rfl

/-- The bag observer distinguishes one occurrence from two. -/
theorem card_projection_distinguishes_card_change :
    cardBag.observe (leftProjection oneAceHistory) ≠
      cardBag.observe (leftProjection twoAceHistory) := by
  change
    (some (([ace] : List CardEvent) : Multiset CardEvent)) ≠
      some (([ace, ace] : List CardEvent) : Multiset CardEvent)
  intro equal
  have equalBags := Option.some.inj equal
  have equalCards := congrArg Multiset.card equalBags
  norm_num at equalCards

/-- Therefore card multiplicity also survives in the composite. -/
theorem composite_distinguishes_card_change :
    composite.observe oneAceHistory ≠ composite.observe twoAceHistory :=
  parallelComposite_distinguishes_of_left cardBag roomWitness roomWitness_total
    card_projection_distinguishes_card_change

/-- Cross-component interleaving is observationally irrelevant because each
discipline retains its own projected order. -/
theorem card_and_room_event_commute :
    composite.observe [.inl ace, .inr .coalition01] =
      composite.observe [.inr .coalition01, .inl ace] := by
  exact parallelComposite_commutes_adjacent_cross_events
    cardBag roomWitness [] [] ace RoomEvent.coalition01

end Mettapedia.PLN.Bridges.GSLT.CompositeObservationMind
