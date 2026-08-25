import Mathlib

/-!
# Stigmergic media

Generalized stigmergy is indirect coordination: an action changes a medium,
the change remains available as a trace, and that trace stimulates a later
action.  This module keeps the five components explicit--agent, action,
medium, trace, and coordination--and adds only the temporal and medium-evolution
structure needed to state delayed persistence.

The definition and component analysis follow Francis Heylighen.  The formal
relations, proof-relevant episode, and specificity control below are our
mathematical formulation.  In particular, the negative theorem is scoped to
the delayed trace-mediated protocol; it does not claim that every possible
kind of coordination requires a persistent trace.

References:

- F. Heylighen, *Stigmergy as a Universal Coordination Mechanism* (2015).
- P.-P. Grasse, *La reconstruction du nid et les coordinations
  interindividuelles chez Bellicositermes natalensis et Cubitermes sp. La
  theorie de la stigmergie: essai d'interpretation du comportement des
  termites constructeurs* (1959).
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.Stigmergy

universe uAgent uAction uState uTrace uTime uEvidence

/-- The five components of generalized stigmergy, together with the time and
medium-evolution relations needed to express a delayed episode.  All dynamic
relations are proof relevant. -/
structure Medium where
  Agent : Type uAgent
  Action : Type uAction
  MediumState : Type uState
  Trace : Type uTrace
  Time : Type uTime
  before : Time -> Time -> Prop
  performs : Agent -> Action -> Type uEvidence
  evolves : MediumState -> MediumState -> Type uEvidence
  leaves : Time -> Agent -> Action -> MediumState -> MediumState -> Trace -> Type uEvidence
  exposes : Time -> MediumState -> Trace -> Type uEvidence
  stimulates : Trace -> Agent -> Action -> Type uEvidence
  Coordination : Action -> Action -> Type uEvidence

/-- A complete delayed stigmergic episode.  The medium state at observation
time is explicitly connected to the post-action state by `evolves`; the later
exposure cannot be supplied by an unrelated state. -/
structure DelayedEpisode
    (medium : Medium.{uAgent, uAction, uState, uTrace, uTime, uEvidence}) where
  producer : medium.Agent
  consumer : medium.Agent
  firstAction : medium.Action
  laterAction : medium.Action
  beforeState : medium.MediumState
  depositedState : medium.MediumState
  observedState : medium.MediumState
  trace : medium.Trace
  depositedAt : medium.Time
  observedAt : medium.Time
  delayed : medium.before depositedAt observedAt
  producerPerforms : medium.performs producer firstAction
  consumerPerforms : medium.performs consumer laterAction
  leavesTrace : medium.leaves depositedAt producer firstAction beforeState
    depositedState trace
  stateEvolves : medium.evolves depositedState observedState
  exposesTrace : medium.exposes observedAt observedState trace
  traceStimulates : medium.stimulates trace consumer laterAction

namespace Medium

variable {medium : Medium.{uAgent, uAction, uState, uTrace, uTime, uEvidence}}

/-- The medium supports the selected stigmergic protocol when every complete
delayed episode yields coordination evidence for its two actions. -/
def Mediates
    (medium : Medium.{uAgent, uAction, uState, uTrace, uTime, uEvidence}) : Prop :=
  forall episode : DelayedEpisode medium,
    Nonempty (medium.Coordination episode.firstAction episode.laterAction)

/-- A medium cannot expose a persisted trace when every later evolved state
has an empty exposure fibre for that trace. -/
def CannotExposePersistedTrace
    (medium : Medium.{uAgent, uAction, uState, uTrace, uTime, uEvidence}) : Prop :=
  forall depositedAt observedAt depositedState observedState trace,
    medium.before depositedAt observedAt ->
    medium.evolves depositedState observedState ->
    IsEmpty (medium.exposes observedAt observedState trace)

/-- Trace-mediated coordination follows from a medium's mediation law while
retaining the complete episode as input evidence. -/
theorem trace_mediated_coordination
    (mediates : medium.Mediates) (episode : DelayedEpisode medium) :
    Nonempty (medium.Coordination episode.firstAction episode.laterAction) :=
  mediates episode

/-- **Trace-persistence specificity control.** A medium that cannot expose any
trace after a delayed evolution admits no complete episode of this protocol. -/
theorem no_delayedEpisode_of_cannotExposePersistedTrace
    (cannotExpose : medium.CannotExposePersistedTrace) :
    Not (Nonempty (DelayedEpisode medium)) := by
  rintro ⟨episode⟩
  exact (cannotExpose episode.depositedAt episode.observedAt
    episode.depositedState episode.observedState episode.trace
    episode.delayed episode.stateEvolves).elim episode.exposesTrace

end Medium

/-! ## Specificity canary -/

namespace Canary

/-- An ephemeral medium may have a direct coordination relation while being
unable to expose any trace after an action. -/
def ephemeral : Medium where
  Agent := Unit
  Action := Bool
  MediumState := Unit
  Trace := Unit
  Time := Nat
  before := (.<.)
  performs _ _ := Unit
  evolves _ _ := Unit
  leaves _ _ _ _ _ _ := Unit
  exposes _ _ _ := Empty
  stimulates _ _ _ := Unit
  Coordination _ _ := Unit

theorem ephemeral_cannotExposePersistedTrace :
    ephemeral.CannotExposePersistedTrace := by
  intro depositedAt observedAt depositedState observedState trace delayed evolved
  change IsEmpty Empty
  infer_instance

theorem ephemeral_has_direct_coordination :
    Nonempty (ephemeral.Coordination false true) :=
  ⟨()⟩

/-- Losing traces blocks this delayed stigmergic mechanism even though another,
direct coordination relation can remain available. -/
theorem ephemeral_has_no_delayedEpisode :
    Not (Nonempty (DelayedEpisode ephemeral)) :=
  ephemeral.no_delayedEpisode_of_cannotExposePersistedTrace
    ephemeral_cannotExposePersistedTrace

end Canary

end Mettapedia.Cybernetics.Stigmergy

#print axioms Mettapedia.Cybernetics.Stigmergy.Medium.trace_mediated_coordination
#print axioms Mettapedia.Cybernetics.Stigmergy.Medium.no_delayedEpisode_of_cannotExposePersistedTrace
#print axioms Mettapedia.Cybernetics.Stigmergy.Canary.ephemeral_has_no_delayedEpisode
