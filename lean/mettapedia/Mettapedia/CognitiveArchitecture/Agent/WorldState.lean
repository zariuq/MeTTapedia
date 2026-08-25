import Mathlib.Data.Fintype.Card

/-!
# Typed Agent World State and Context Abstraction

Source provenance: adapted from GödelClaw commit
`c7475e89c0d86a21d3d817b0e46281f47cc93dbb`; only module packaging and
taxonomy-facing names were changed during integration.

This file separates five kinds of state that coding agents often blur:

* exact operational state;
* evidence, with its revision discipline supplied by a downstream model;
* commitments and goals;
* the bounded view shown to a model;
* executable capabilities.

The separation matters because evidence may obey an additive world-model
revision law while file updates, instruction precedence, plans, and protocol
state may be ordered and noncommutative.  The PLN-specific additive theorem is
kept in `Agent.Bridges.PLN.WorldStateEvidence`, so the state and compaction
mathematics in this module do not depend on PLN.

The second part states the basic limitation on context compaction.  If a view
preserves every query from a family that separates concrete states, then the
view is injective.  A genuinely smaller finite view therefore cannot preserve
all state-separating queries.  Compaction contracts must name a relevant query
family instead of claiming universal semantic preservation.
-/

namespace Mettapedia.CognitiveArchitecture.Agent.WorldState

/-- The agent state is a typed product, not one undifferentiated belief store. -/
structure AgentState
    (Operational Evidence Commitment Context Capability : Type*) where
  operational : Operational
  evidence : Evidence
  commitments : Commitment
  context : Context
  capabilities : Capability

/-- Change exact operational state without silently changing any other layer. -/
def mapOperational
    {Operational₁ Operational₂ Evidence Commitment Context Capability : Type*}
    (f : Operational₁ → Operational₂)
    (s : AgentState Operational₁ Evidence Commitment Context Capability) :
    AgentState Operational₂ Evidence Commitment Context Capability :=
  { operational := f s.operational
    evidence := s.evidence
    commitments := s.commitments
    context := s.context
    capabilities := s.capabilities }

/-- Add evidence without rewriting operational facts, commitments, context, or
capabilities. -/
def reviseEvidence
    {Operational Evidence Commitment Context Capability : Type*}
    [Add Evidence]
    (s : AgentState Operational Evidence Commitment Context Capability)
    (delta : Evidence) :
    AgentState Operational Evidence Commitment Context Capability :=
  { s with evidence := s.evidence + delta }

@[simp] theorem reviseEvidence_operational
    {Operational Evidence Commitment Context Capability : Type*}
    [Add Evidence]
    (s : AgentState Operational Evidence Commitment Context Capability)
    (delta : Evidence) :
    (reviseEvidence s delta).operational = s.operational := by
  rfl

/-- Operational updates are deliberately allowed to be order-sensitive. -/
theorem operational_updates_need_not_commute :
    let s : AgentState Nat Unit Unit Unit Unit := ⟨1, (), (), (), ()⟩
    mapOperational (fun n => n * 2)
        (mapOperational (fun n => n + 1) s) ≠
      mapOperational (fun n => n + 1)
        (mapOperational (fun n => n * 2) s) := by
  simp [mapOperational]

/-! ## Availability is not negative evidence -/

/-- A source may be unreadable, or it may have been read and yielded either an
absent or present value. -/
inductive SourceObservation (α : Type*) where
  | unavailable
  | observed (value : Option α)
deriving DecidableEq

/-- Failure to observe a source is distinct from observing absence. -/
theorem unavailable_ne_observed_absent {α : Type*} :
    (SourceObservation.unavailable : SourceObservation α) ≠
      SourceObservation.observed (none : Option α) := by
  intro impossible
  cases impossible

/-! ## Query-relative context abstraction -/

/-- A query family separates concrete states when agreement on every answer
forces equality of the concrete states. -/
def QuerySeparating {State Query Answer : Type*}
    (answer : State → Query → Answer) : Prop :=
  ∀ ⦃left right : State⦄,
    (∀ q, answer left q = answer right q) → left = right

/-- A context view is complete for a query family when all answers can be
recovered from the view alone. -/
def QueryComplete {State Query Answer View : Type*}
    (answer : State → Query → Answer) (view : State → View) : Prop :=
  ∃ answerFromView : View → Query → Answer,
    ∀ state query, answerFromView (view state) query = answer state query

/-- Completeness for a state-separating query family forces the context view to
retain enough information to identify the entire concrete state. -/
theorem queryComplete_injective
    {State Query Answer View : Type*}
    {answer : State → Query → Answer} {view : State → View}
    (separating : QuerySeparating answer)
    (complete : QueryComplete answer view) :
    Function.Injective view := by
  obtain ⟨answerFromView, recovers⟩ := complete
  intro left right sameView
  apply separating
  intro query
  calc
    answer left query = answerFromView (view left) query :=
      (recovers left query).symm
    _ = answerFromView (view right) query := by rw [sameView]
    _ = answer right query := recovers right query

/-- Finite universal-lossless compaction is impossible whenever the view has
strictly fewer states than the concrete state space. -/
theorem no_universal_query_complete_compression
    {State Query Answer View : Type*}
    [Fintype State] [Fintype View]
    {answer : State → Query → Answer} {view : State → View}
    (separating : QuerySeparating answer)
    (smaller : Fintype.card View < Fintype.card State) :
    ¬ QueryComplete answer view := by
  intro complete
  have injective : Function.Injective view :=
    queryComplete_injective separating complete
  have card_le : Fintype.card State ≤ Fintype.card View :=
    Fintype.card_le_of_injective view injective
  exact (Nat.not_le_of_gt smaller) card_le

/-- A practical compaction contract preserves only a declared relevant query
family. -/
def PreservesRelevantQueries
    {State Query Answer View : Type*}
    (relevant : Query → Prop)
    (answer : State → Query → Answer)
    (view : State → View) : Prop :=
  ∃ answerFromView : View → Query → Answer,
    ∀ state query, relevant query →
      answerFromView (view state) query = answer state query

/-- Universal completeness is sufficient for every restricted contract. -/
theorem QueryComplete.preservesRelevant
    {State Query Answer View : Type*}
    {answer : State → Query → Answer} {view : State → View}
    (complete : QueryComplete answer view)
    (relevant : Query → Prop) :
    PreservesRelevantQueries relevant answer view := by
  obtain ⟨answerFromView, recovers⟩ := complete
  exact ⟨answerFromView, fun state query _ => recovers state query⟩

end Mettapedia.CognitiveArchitecture.Agent.WorldState

#print axioms Mettapedia.CognitiveArchitecture.Agent.WorldState.queryComplete_injective
#print axioms Mettapedia.CognitiveArchitecture.Agent.WorldState.no_universal_query_complete_compression
