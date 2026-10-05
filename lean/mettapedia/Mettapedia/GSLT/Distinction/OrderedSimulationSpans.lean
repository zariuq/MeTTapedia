import Mettapedia.GSLT.Distinction.OrderedSimulation
import Mettapedia.GSLT.Distinction.SpanTransport

/-!
# Ordered simulations as span relations

`OrderedSimulation` relates nondeterministic machines whose successors come
as ordered lists, position by position.  `ProductiveBlocks.CostSimulation`
relates deterministic machines that publish events, within a cost bound, and
its span reading is the segment relation of `SpanTransport`.  This module gives
the ordered relation the same reading, so that both relations are instances of
the source laws of `SpanTransport.SpanRelation` and inherit its transfer
theorems.

* **Successor occurrences** (`OrderedSystem.Occurrence`,
  `OrderedSystem.occurrenceSpan`).  An occurrence is a state and a position in
  its successor list; the occurrence span runs from the state to the successor
  at that position.  Labelled by positions, with halting as the atom, it is a
  `SpanTransport.Labelled` reduction span (`OrderedSystem.occurrences`).
* **The occurrence relation** (`occurrenceRelation`): occurrences at the same
  position from related states to related successors.  It keeps positions
  (`occurrenceRelation_keeps`), and the composite of two occurrence relations
  lies in the occurrence relation of the composite relation
  (`occurrenceRelation_comp_events`).
* **Fibre matching** (`OrderedSimulation.outFibresMatch`).  Position-by-position
  relation of successor lists is exactly a one-to-one correspondence of the
  outgoing occurrences, so an ordered simulation has both source laws
  (`OrderedSimulation.sourceForthOcc`, `OrderedSimulation.sourceBackOcc`),
  keeps the number of successor occurrences (`OrderedSimulation.successor_card_eq`),
  and preserves and reflects every future formula over positions and halting
  (`OrderedSimulation.future_related`).  A cost simulation each way gives the
  same two source laws on run segments (`CostSimulation.segment_sourceForthOcc`,
  `CostSimulation.segment_sourceBackOcc`), without fibre matching.

What is not unified.  `OrderedSimulation` advances every occurrence of a
frontier in lockstep; `CostSimulation` lets one source transition cost a
varying number of target transitions.  Matching each branch within a varying
number of target steps does not relate the frontiers position by position at
`cost` times the fuel (`OrderedSimulationSpansControls.stutter_misaligns`),
so a cost-bounded ordered simulation needs its own frontier semantics with a
clock per occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.Distinction.SpanTransport

universe u v w

namespace OrderedSystem

variable {State : Type u} (system : OrderedSystem State)

/-- **A successor occurrence**: a state and a position in its successor list. -/
structure Occurrence where
  state : State
  position : ℕ
  inRange : position < (system.step state).length

variable {system}

/-- The successor at an occurrence. -/
def Occurrence.next (occurrence : system.Occurrence) : State :=
  (system.step occurrence.state).get ⟨occurrence.position, occurrence.inRange⟩

variable (system)

/-- **The occurrence span**: from a state to the successor at each position. -/
def occurrenceSpan : ReductionSpan.{u, u} State where
  Edge := system.Occurrence
  source := Occurrence.state
  target := Occurrence.next

/-- The occurrence span labelled by positions, observing halting. -/
def occurrences : Labelled.{u, u} State Bool ℕ where
  span := system.occurrenceSpan
  read := Occurrence.position
  observes halted state := system.halted state = halted

end OrderedSystem

/-- **The occurrence relation of a state relation**: occurrences at one position
from related states to related successors. -/
def occurrenceRelation {S : Type u} {T : Type v} (source : OrderedSystem S) (target : OrderedSystem T)
    (related : S → T → Prop) : SpanRelation source.occurrenceSpan target.occurrenceSpan where
  states := related
  events first second := related first.state second.state ∧ first.position = second.position ∧
    related first.next second.next
  source_rel _ _ matched := matched.1
  target_rel _ _ matched := matched.2.2

section Occurrences

variable {S : Type u} {T : Type v} {W : Type w} {source : OrderedSystem S} {target : OrderedSystem T}
  {third : OrderedSystem W} {related : S → T → Prop} {next : T → W → Prop}

theorem occurrenceRelation_keeps :
    (occurrenceRelation source target related).Keeps OrderedSystem.Occurrence.position
      OrderedSystem.Occurrence.position :=
  fun _ _ matched => matched.2.1

/-- The composite of two occurrence relations relates occurrences of the
composite relation. -/
theorem occurrenceRelation_comp_events {first : source.Occurrence} {last : third.Occurrence}
    (matched : ((occurrenceRelation source target related).comp
      (occurrenceRelation target third next)).events first last) :
    (occurrenceRelation source third (Relation.Comp related next)).events first last := by
  obtain ⟨middle, ⟨starts, positions, nexts⟩, starts', positions', nexts'⟩ := matched
  exact ⟨⟨middle.state, starts, starts'⟩, positions.trans positions', ⟨middle.next, nexts, nexts'⟩⟩

namespace OrderedSimulation

/-- **Position-by-position relation of successor lists is a one-to-one
correspondence of outgoing occurrences.** -/
theorem outFibresMatch (simulation : OrderedSimulation source target related) :
    (occurrenceRelation source target related).OutFibresMatch := by
  intro state state' relatedStates
  have lists := simulation.step relatedStates
  have lengths := lists.length_eq
  refine ⟨{
    toFun := fun occurrence => ⟨⟨state', occurrence.1.position, by
        have inRange := occurrence.1.inRange
        have stateEq : occurrence.1.state = state := occurrence.2
        rw [stateEq, lengths] at inRange
        exact inRange⟩, rfl⟩
    invFun := fun occurrence => ⟨⟨state, occurrence.1.position, by
        have inRange := occurrence.1.inRange
        have stateEq : occurrence.1.state = state' := occurrence.2
        rw [stateEq, ← lengths] at inRange
        exact inRange⟩, rfl⟩
    left_inv := by
      rintro ⟨⟨_, position, inRange⟩, rfl⟩
      rfl
    right_inv := by
      rintro ⟨⟨_, position, inRange⟩, rfl⟩
      rfl }, ?_⟩
  rintro ⟨⟨_, position, inRange⟩, rfl⟩
  exact ⟨relatedStates, rfl, lists.get inRange _⟩

theorem sourceForthOcc (simulation : OrderedSimulation source target related) :
    (occurrenceRelation source target related).SourceForthOcc :=
  simulation.outFibresMatch.sourceForthOcc

theorem sourceBackOcc (simulation : OrderedSimulation source target related) :
    (occurrenceRelation source target related).SourceBackOcc :=
  simulation.outFibresMatch.sourceBackOcc

/-- **Related states have equally many successor occurrences at each
position.** -/
theorem successor_card_eq (simulation : OrderedSimulation source target related) {state : S}
    {state' : T} (relatedStates : related state state') (position : ℕ) :
    Nat.card {occurrence : source.Occurrence // occurrence.state = state ∧
        occurrence.position = position} =
      Nat.card {occurrence : target.Occurrence // occurrence.state = state' ∧
        occurrence.position = position} :=
  outgoing_card_eq (occurrenceRelation source target related) simulation.outFibresMatch
    occurrenceRelation_keeps relatedStates position

/-- **Every future formula over positions and halting agrees on related
states.** -/
theorem future_related (simulation : OrderedSimulation source target related)
    {formula : Tense Bool ℕ} (future : formula.IsFuture) :
    Related related (Tense.sat source.occurrences formula) (Tense.sat target.occurrences formula) :=
  sat_related_future source.occurrences target.occurrences (occurrenceRelation source target related)
    occurrenceRelation_keeps
    (fun halted _ _ relatedStates => by
      change source.halted _ = halted ↔ target.halted _ = halted
      rw [simulation.halted relatedStates])
    simulation.sourceForthOcc simulation.sourceBackOcc future

end OrderedSimulation

end Occurrences

end Mettapedia.GSLT.Distinction
