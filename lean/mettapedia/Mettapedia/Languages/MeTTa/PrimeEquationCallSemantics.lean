import Mettapedia.Languages.MeTTa.PrimeCallSharingTournament

/-!
# Prime equation-call small-step semantics

This module gives the equation-sharing tournament an operational core without
postulating a universal call world.  Evaluation episodes, dynamic applications,
source arguments, cells, rule occurrences, lexical contexts, event occurrences,
and answer occurrences remain distinct parameters.

Candidate steps accumulate occurrence-tagged receipt roots.  Publication uses
`PrimeNeedWorlds.DependencyReceipt`, so causal closure, compatible joins, and
conflict are inherited from the existing world theory rather than redefined.
The native trace correspondence is intentionally separate: this module states
what an accepted decoded trace means, not that arbitrary C executions satisfy
it.
-/

namespace Mettapedia.Languages.MeTTa.PrimeEquationCallSemantics

open PrimeCallSharingTournament

/-! ## Independent occurrence identities -/

/-- A source argument belongs to one evaluation episode, one dynamic
application occurrence, and one argument position. -/
structure SourceArgumentOccurrence
    (Episode Application Position : Type*) where
  episode : Episode
  application : Application
  position : Position
deriving DecidableEq, Repr

/-- An admitted equation is identified by its occurrence in one application,
not by structural equality of its source text. -/
structure AdmittedRuleOccurrence (Application Rule : Type*) where
  application : Application
  rule : Rule
deriving DecidableEq, Repr

/-- Events used by equation-call receipts.  An outer `EventOccurrence` retains
identity when two events have equal payloads. -/
inductive EquationEvent
    (Source Cell Rule Observation Effect : Type*) where
  | cellEvaluated (source : Source) (cell : Cell)
  | cellObserved (source : Source) (cell : Cell)
      (observation : Observation)
  | originInspected (cell : Cell) (origin : Observation)
  | ruleMatched (rule : Rule)
  | rhsObserved (rule : Rule) (observation : Observation)
  | effect (effect : Effect)
  | resampled (origin : Observation)
deriving DecidableEq, Repr

abbrev EquationEventOccurrence Source Cell Rule Observation Effect :=
  EventOccurrence (EquationEvent Source Cell Rule Observation Effect)

abbrev EquationReceipt Source Cell Rule Observation Effect :=
  PrimeNeedWorlds.DependencyReceipt
    (EquationEventOccurrence Source Cell Rule Observation Effect)

/-- An answer occurrence preserves application, admitted rule occurrence,
dependency receipt, and result independently. -/
structure AnswerOccurrence
    (Application Rule Source Cell Observation Effect Answer : Type*) where
  application : Application
  rule : Rule
  receipt : EquationReceipt Source Cell Rule Observation Effect
  answer : Answer

/-! ## Candidate machine -/

inductive CandidatePhase where
  | unadmitted
  | demanding
  | forcing
  | matching
  | rhs
  | ready
  | pruned
  | published
deriving DecidableEq, Repr

/-- The authored support and occurrence identity of one admitted candidate. -/
structure OperationalCandidate
    (Argument Rule Context : Type*) where
  rule : Rule
  context : Context
  support : Finset Argument

/-- The operational state of one candidate.  `pending` and `observed` concern
argument support; `roots` additionally records matching, RHS, and effect events.
-/
structure CandidateState
    (Argument Source Cell Rule Observation Effect Answer : Type*) where
  phase : CandidatePhase
  pending : Finset Argument
  inFlight : Option Argument
  observed : Finset Argument
  roots : Finset
    (EquationEventOccurrence Source Cell Rule Observation Effect)
  answer : Option Answer

abbrev State Argument Source Cell Rule Observation Effect Answer :=
  CandidateState Argument Source Cell Rule Observation Effect Answer

def unadmittedState :
    State Argument Source Cell Rule Observation Effect Answer :=
  { phase := .unadmitted
    pending := ∅
    inFlight := none
    observed := ∅
    roots := ∅
    answer := none }

def admittedState [DecidableEq Argument]
    (candidate : OperationalCandidate Argument Rule Context) :
    State Argument Source Cell Rule Observation Effect Answer :=
  { phase := if candidate.support = ∅ then .matching else .demanding
    pending := candidate.support
    inFlight := none
    observed := ∅
    roots := ∅
    answer := none }

def demandState (state : State Argument Source Cell Rule Observation Effect Answer)
    (argument : Argument) :
    State Argument Source Cell Rule Observation Effect Answer :=
  { state with phase := .forcing, inFlight := some argument }

def addRoot
    [DecidableEq Source] [DecidableEq Cell] [DecidableEq Rule]
    [DecidableEq Observation] [DecidableEq Effect]
    (state : State Argument Source Cell Rule Observation Effect Answer)
    (event : EquationEventOccurrence Source Cell Rule Observation Effect) :
    State Argument Source Cell Rule Observation Effect Answer :=
  { state with roots := insert event state.roots }

def forceState
    [DecidableEq Argument] [DecidableEq Source] [DecidableEq Cell]
    [DecidableEq Rule] [DecidableEq Observation] [DecidableEq Effect]
    (state : State Argument Source Cell Rule Observation Effect Answer)
    (argument : Argument)
    (event : EquationEventOccurrence Source Cell Rule Observation Effect) :
    State Argument Source Cell Rule Observation Effect Answer :=
  let remaining := state.pending.erase argument
  { state with
    phase := if remaining = ∅ then .matching else .demanding
    pending := remaining
    inFlight := none
    observed := insert argument state.observed
    roots := insert event state.roots }

def phaseWithRoot
    [DecidableEq Source] [DecidableEq Cell] [DecidableEq Rule]
    [DecidableEq Observation] [DecidableEq Effect]
    (state : State Argument Source Cell Rule Observation Effect Answer)
    (phase : CandidatePhase)
    (event : EquationEventOccurrence Source Cell Rule Observation Effect) :
    State Argument Source Cell Rule Observation Effect Answer :=
  { state with phase := phase, roots := insert event state.roots }

/-- Transition labels keep support demand, producer observations, matching,
effects, and publication distinguishable in traces. -/
inductive CandidateAction
    (Argument Source Cell Observation Effect Answer : Type*) where
  | admit
  | demand (argument : Argument)
  | producer (source : Source) (cell : Cell) (occurrence : Nat)
  | force (argument : Argument) (source : Source) (cell : Cell)
      (observation : Observation) (occurrence : Nat)
  | prune
  | lhsMatched (occurrence : Nat)
  | rhsObserve (observation : Observation) (occurrence : Nat)
  | recordEffect (effect : Effect) (occurrence : Nat)
  | resample (origin : Observation) (occurrence : Nat)
  | rhsComplete (answer : Answer)
  | publish
deriving DecidableEq, Repr

/-- The primary candidate transition relation.  Different `force` observations
from one state are distinct nondeterministic successor worlds. -/
inductive CandidateStep
    [DecidableEq Argument] [DecidableEq Source] [DecidableEq Cell]
    [DecidableEq Rule] [DecidableEq Observation] [DecidableEq Effect]
    (candidate : OperationalCandidate Argument Rule Context) :
    State Argument Source Cell Rule Observation Effect Answer →
      CandidateAction Argument Source Cell Observation Effect Answer →
      State Argument Source Cell Rule Observation Effect Answer → Prop where
  | admit : CandidateStep candidate unadmittedState .admit
      (admittedState candidate)
  | demand (state) (argument : Argument)
      (phase : state.phase = .demanding)
      (pending : argument ∈ state.pending) :
      CandidateStep candidate state (.demand argument)
        (demandState state argument)
  | producer (state) (source : Source) (cell : Cell) (occurrence : Nat)
      (active : state.phase ≠ .pruned ∧ state.phase ≠ .published) :
      CandidateStep candidate state (.producer source cell occurrence)
        (addRoot state
          { occurrence := occurrence, payload := .cellEvaluated source cell })
  | force (state) (argument : Argument)
      (source : Source) (cell : Cell) (observation : Observation)
      (occurrence : Nat)
      (phase : state.phase = .forcing)
      (focused : state.inFlight = some argument) :
      CandidateStep candidate state
        (.force argument source cell observation occurrence)
        (forceState state argument
          { occurrence := occurrence
            payload := .cellObserved source cell observation })
  | prune (state)
      (active : state.phase ≠ .ready ∧ state.phase ≠ .published) :
      CandidateStep candidate state .prune
        { state with phase := .pruned, inFlight := none }
  | lhsMatched (state) (occurrence : Nat)
      (phase : state.phase = .matching) :
      CandidateStep candidate state (.lhsMatched occurrence)
        (phaseWithRoot state .rhs
          { occurrence := occurrence
            payload := .ruleMatched candidate.rule })
  | rhsObserve (state) (observation : Observation) (occurrence : Nat)
      (phase : state.phase = .rhs) :
      CandidateStep candidate state (.rhsObserve observation occurrence)
        (addRoot state
          { occurrence := occurrence
            payload := .rhsObserved candidate.rule observation })
  | recordEffect (state) (effect : Effect) (occurrence : Nat)
      (active : state.phase ≠ .pruned ∧ state.phase ≠ .published) :
      CandidateStep candidate state (.recordEffect effect occurrence)
        (addRoot state
          { occurrence := occurrence, payload := .effect effect })
  | resample (state) (origin : Observation) (occurrence : Nat)
      (active : state.phase ≠ .pruned ∧ state.phase ≠ .published) :
      CandidateStep candidate state (.resample origin occurrence)
        (addRoot state
          { occurrence := occurrence, payload := .resampled origin })
  | rhsComplete (state) (answer : Answer)
      (phase : state.phase = .rhs) :
      CandidateStep candidate state (.rhsComplete answer)
        { state with phase := .ready, answer := some answer }
  | publish (state) (phase : state.phase = .ready) :
      CandidateStep candidate state .publish
        { state with phase := .published }

/-- A candidate trace is the reflexive/transitive closure of the primary
small-step relation, retaining the intermediate action at each extension. -/
inductive CandidateTrace
    [DecidableEq Argument] [DecidableEq Source] [DecidableEq Cell]
    [DecidableEq Rule] [DecidableEq Observation] [DecidableEq Effect]
    (candidate : OperationalCandidate Argument Rule Context) :
    State Argument Source Cell Rule Observation Effect Answer →
      State Argument Source Cell Rule Observation Effect Answer → Prop where
  | refl (state) : CandidateTrace candidate state state
  | tail {first middle last}
      (trace : CandidateTrace candidate first middle)
      (step : CandidateStep candidate middle action last) :
      CandidateTrace candidate first last

theorem step_roots_mono
    [DecidableEq Argument] [DecidableEq Source] [DecidableEq Cell]
    [DecidableEq Rule] [DecidableEq Observation] [DecidableEq Effect]
    {candidate : OperationalCandidate Argument Rule Context}
    {before after : State Argument Source Cell Rule Observation Effect Answer}
    {action : CandidateAction Argument Source Cell Observation Effect Answer}
    (step : CandidateStep candidate before action after) :
    before.roots ⊆ after.roots := by
  cases step <;>
    simp [unadmittedState, admittedState, demandState, forceState,
      phaseWithRoot, addRoot]

theorem trace_roots_mono
    [DecidableEq Argument] [DecidableEq Source] [DecidableEq Cell]
    [DecidableEq Rule] [DecidableEq Observation] [DecidableEq Effect]
    {candidate : OperationalCandidate Argument Rule Context}
    {first last : State Argument Source Cell Rule Observation Effect Answer}
    (trace : CandidateTrace candidate first last) :
    first.roots ⊆ last.roots := by
  induction trace with
  | refl => exact Finset.Subset.rfl
  | tail trace step ih =>
      exact Finset.Subset.trans ih (step_roots_mono step)

def RuleMatchRecorded
    [DecidableEq Source] [DecidableEq Cell] [DecidableEq Rule]
    [DecidableEq Observation] [DecidableEq Effect]
    (candidate : OperationalCandidate Argument Rule Context)
    (state : State Argument Source Cell Rule Observation Effect Answer) : Prop :=
  ∃ occurrence : Nat,
    ({ occurrence := occurrence, payload := .ruleMatched candidate.rule } :
      EquationEventOccurrence Source Cell Rule Observation Effect) ∈ state.roots

def MatchRequiredPhase (phase : CandidatePhase) : Prop :=
  phase = .rhs ∨ phase = .ready ∨ phase = .published

def MatchInvariant
    [DecidableEq Source] [DecidableEq Cell] [DecidableEq Rule]
    [DecidableEq Observation] [DecidableEq Effect]
    (candidate : OperationalCandidate Argument Rule Context)
    (state : State Argument Source Cell Rule Observation Effect Answer) : Prop :=
  MatchRequiredPhase state.phase → RuleMatchRecorded candidate state

theorem unadmitted_matchInvariant
    [DecidableEq Source] [DecidableEq Cell] [DecidableEq Rule]
    [DecidableEq Observation] [DecidableEq Effect]
    (candidate : OperationalCandidate Argument Rule Context) :
    MatchInvariant candidate
      (unadmittedState :
        State Argument Source Cell Rule Observation Effect Answer) := by
  simp [MatchInvariant, MatchRequiredPhase, unadmittedState]

/-- Entering the RHS records the match occurrence; all later transitions
preserve it. -/
theorem matchInvariant_step
    [DecidableEq Argument] [DecidableEq Source] [DecidableEq Cell]
    [DecidableEq Rule] [DecidableEq Observation] [DecidableEq Effect]
    {candidate : OperationalCandidate Argument Rule Context}
    {before after : State Argument Source Cell Rule Observation Effect Answer}
    {action : CandidateAction Argument Source Cell Observation Effect Answer}
    (invariant : MatchInvariant candidate before)
    (step : CandidateStep candidate before action after) :
    MatchInvariant candidate after := by
  intro required
  cases step with
  | admit =>
      by_cases emptySupport : candidate.support = ∅ <;>
        simp [admittedState, MatchRequiredPhase, emptySupport] at required
  | demand state argument phase pending =>
      simp [demandState, MatchRequiredPhase] at required
  | producer state source cell occurrence active =>
      rcases invariant required with ⟨matchOccurrence, recorded⟩
      exact ⟨matchOccurrence, by simpa [addRoot] using recorded⟩
  | force state argument source cell observation occurrence phase focused =>
      by_cases noRemaining : Finset.erase before.pending argument = ∅ <;>
        simp [forceState, MatchRequiredPhase, noRemaining] at required
  | prune state active =>
      simp [MatchRequiredPhase] at required
  | lhsMatched state occurrence phase =>
      exact ⟨occurrence, by simp [phaseWithRoot]⟩
  | rhsObserve state observation occurrence phase =>
      rcases invariant (Or.inl phase) with ⟨matchOccurrence, recorded⟩
      exact ⟨matchOccurrence, by simpa [addRoot] using recorded⟩
  | recordEffect state effect occurrence active =>
      rcases invariant required with ⟨matchOccurrence, recorded⟩
      exact ⟨matchOccurrence, by simpa [addRoot] using recorded⟩
  | resample state origin occurrence active =>
      rcases invariant required with ⟨matchOccurrence, recorded⟩
      exact ⟨matchOccurrence, by simpa [addRoot] using recorded⟩
  | rhsComplete state answer phase =>
      exact invariant (Or.inl phase)
  | publish state phase =>
      exact invariant (Or.inr (Or.inl phase))

theorem trace_preserves_matchInvariant
    [DecidableEq Argument] [DecidableEq Source] [DecidableEq Cell]
    [DecidableEq Rule] [DecidableEq Observation] [DecidableEq Effect]
    {candidate : OperationalCandidate Argument Rule Context}
    {first last : State Argument Source Cell Rule Observation Effect Answer}
    (trace : CandidateTrace candidate first last)
    (initial : MatchInvariant candidate first) :
    MatchInvariant candidate last := by
  induction trace with
  | refl => exact initial
  | tail trace step ih => exact matchInvariant_step (ih initial) step

theorem trace_matchInvariant
    [DecidableEq Argument] [DecidableEq Source] [DecidableEq Cell]
    [DecidableEq Rule] [DecidableEq Observation] [DecidableEq Effect]
    {candidate : OperationalCandidate Argument Rule Context}
    {last : State Argument Source Cell Rule Observation Effect Answer}
    (trace : CandidateTrace candidate unadmittedState last) :
    MatchInvariant candidate last :=
  trace_preserves_matchInvariant trace (unadmitted_matchInvariant candidate)

/-- A reachable ready or published answer cannot omit its admitted
rule-occurrence event. -/
theorem reachable_answer_records_rule_match
    [DecidableEq Argument] [DecidableEq Source] [DecidableEq Cell]
    [DecidableEq Rule] [DecidableEq Observation] [DecidableEq Effect]
    {candidate : OperationalCandidate Argument Rule Context}
    {last : State Argument Source Cell Rule Observation Effect Answer}
    (trace : CandidateTrace candidate unadmittedState last)
    (ready : last.phase = .ready ∨ last.phase = .published) :
    RuleMatchRecorded candidate last := by
  apply trace_matchInvariant trace
  exact ready.elim (fun h => Or.inr (Or.inl h))
    (fun h => Or.inr (Or.inr h))

theorem force_step_records_observation
    [DecidableEq Argument] [DecidableEq Source] [DecidableEq Cell]
    [DecidableEq Rule] [DecidableEq Observation] [DecidableEq Effect]
    (state : State Argument Source Cell Rule Observation Effect Answer)
    (argument : Argument) (source : Source) (cell : Cell)
    (observation : Observation) (occurrence : Nat)
    (_phase : state.phase = .forcing)
    (_focused : state.inFlight = some argument) :
    let event : EquationEventOccurrence Source Cell Rule Observation Effect :=
      { occurrence := occurrence
        payload := .cellObserved source cell observation }
    event ∈ (forceState state argument event).roots := by
  simp [forceState]

theorem lhs_step_records_match
    [DecidableEq Argument] [DecidableEq Source] [DecidableEq Cell]
    [DecidableEq Rule] [DecidableEq Observation] [DecidableEq Effect]
    (state : State Argument Source Cell Rule Observation Effect Answer)
    (candidate : OperationalCandidate Argument Rule Context)
    (occurrence : Nat) (_phase : state.phase = .matching) :
    let event : EquationEventOccurrence Source Cell Rule Observation Effect :=
      { occurrence := occurrence, payload := .ruleMatched candidate.rule }
    event ∈ (phaseWithRoot state .rhs event).roots := by
  simp [phaseWithRoot]

theorem rhs_step_records_observation
    [DecidableEq Argument] [DecidableEq Source] [DecidableEq Cell]
    [DecidableEq Rule] [DecidableEq Observation] [DecidableEq Effect]
    (state : State Argument Source Cell Rule Observation Effect Answer)
    (candidate : OperationalCandidate Argument Rule Context)
    (observation : Observation) (occurrence : Nat)
    (_phase : state.phase = .rhs) :
    let event : EquationEventOccurrence Source Cell Rule Observation Effect :=
      { occurrence := occurrence
        payload := .rhsObserved candidate.rule observation }
    event ∈ (addRoot state event).roots := by
  simp [addRoot]

/-- Every RHS observation that occurred on a candidate trace remains in the
eventual answer receipt. -/
theorem rhs_observation_survives_trace
    [DecidableEq Argument] [DecidableEq Source] [DecidableEq Cell]
    [DecidableEq Rule] [DecidableEq Observation] [DecidableEq Effect]
    (candidate : OperationalCandidate Argument Rule Context)
    (state : State Argument Source Cell Rule Observation Effect Answer)
    (observation : Observation) (occurrence : Nat)
    (phase : state.phase = .rhs)
    {last : State Argument Source Cell Rule Observation Effect Answer}
    (rest : CandidateTrace candidate
      (addRoot state
        { occurrence := occurrence
          payload := .rhsObserved candidate.rule observation }) last) :
    ({ occurrence := occurrence
       payload := .rhsObserved candidate.rule observation } :
      EquationEventOccurrence Source Cell Rule Observation Effect) ∈
        last.roots := by
  apply trace_roots_mono rest
  exact rhs_step_records_observation state candidate observation occurrence phase

theorem effect_step_records_occurrence
    [DecidableEq Argument] [DecidableEq Source] [DecidableEq Cell]
    [DecidableEq Rule] [DecidableEq Observation] [DecidableEq Effect]
    (state : State Argument Source Cell Rule Observation Effect Answer)
    (effect : Effect) (occurrence : Nat) :
    let event : EquationEventOccurrence Source Cell Rule Observation Effect :=
      { occurrence := occurrence, payload := .effect effect }
    event ∈ (addRoot state event).roots := by
  simp [addRoot]

theorem no_demand_without_pending
    [DecidableEq Argument] [DecidableEq Source] [DecidableEq Cell]
    [DecidableEq Rule] [DecidableEq Observation] [DecidableEq Effect]
    (candidate : OperationalCandidate Argument Rule Context)
    (state : State Argument Source Cell Rule Observation Effect Answer)
    (argument : Argument) (notPending : argument ∉ state.pending) :
    ¬ ∃ after, CandidateStep candidate state (.demand argument) after := by
  rintro ⟨after, step⟩
  cases step with
  | demand _ _ _ pending => exact notPending pending

theorem publish_preserves_receipt
    [DecidableEq Argument] [DecidableEq Source] [DecidableEq Cell]
    [DecidableEq Rule] [DecidableEq Observation] [DecidableEq Effect]
    (state : State Argument Source Cell Rule Observation Effect Answer)
    (_ready : state.phase = .ready) :
    ({ state with phase := .published } :
      State Argument Source Cell Rule Observation Effect Answer).roots =
        state.roots :=
  rfl

/-! ## Answer and residual publication -/

structure PublicationState
    (Application Rule Source Cell Observation Effect Answer Residual : Type*) where
  answers : List
    (AnswerOccurrence Application Rule Source Cell Observation Effect Answer)
  residuals : List Residual

def initialPublicationState :
    PublicationState Application Rule Source Cell Observation Effect Answer Residual :=
  { answers := [], residuals := [] }

def answerFromReady
    (application : Application)
    (candidate : OperationalCandidate Argument Rule Context)
    (state : State Argument Source Cell Rule Observation Effect Answer)
    (answer : Answer) :
    AnswerOccurrence Application Rule Source Cell Observation Effect Answer :=
  { application := application
    rule := candidate.rule
    receipt := { roots := state.roots }
    answer := answer }

inductive PublicationStep
    (application : Application) (Context : Type*)
    (candidates : List
      (State Argument Source Cell Rule Observation Effect Answer)) :
    PublicationState Application Rule Source Cell Observation Effect Answer Residual →
      PublicationState Application Rule Source Cell Observation Effect Answer Residual →
      Prop where
  | answer (publication)
      (candidate : OperationalCandidate Argument Rule Context)
      (state : State Argument Source Cell Rule Observation Effect Answer)
      (answer : Answer)
      (ready : state.phase = .ready)
      (result : state.answer = some answer) :
      PublicationStep application Context candidates publication
        { publication with
          answers := publication.answers ++
            [answerFromReady application candidate state answer] }
  | residual (publication) (residual : Residual)
      (allPruned : ∀ state ∈ candidates, state.phase = .pruned) :
      PublicationStep application Context candidates publication
        { publication with residuals := publication.residuals ++ [residual] }

theorem answerFromReady_exact_roots
    (application : Application)
    (candidate : OperationalCandidate Argument Rule Context)
    (state : State Argument Source Cell Rule Observation Effect Answer)
    (answer : Answer) :
    (answerFromReady application candidate state answer).receipt.roots =
      state.roots :=
  rfl

theorem residual_requires_every_candidate_pruned
    {application : Application}
    {Context : Type*}
    {candidates : List
      (State Argument Source Cell Rule Observation Effect Answer)}
    {before after :
      PublicationState Application Rule Source Cell Observation Effect Answer Residual}
    (step : PublicationStep application Context candidates before after)
    (grewResiduals : after.residuals.length = before.residuals.length + 1) :
    ∀ state ∈ candidates, state.phase = .pruned := by
  cases step with
  | answer candidate state answer ready result =>
      simp at grewResiduals
  | residual residual allPruned =>
      exact allPruned

/-! ## Occurrence bags, freshness, and world publication -/

/-- List order is presentational; the multiset retains semantic multiplicity. -/
def answerBag
    (answers : List
      (AnswerOccurrence Application Rule Source Cell Observation Effect Answer)) :
    Multiset
      (AnswerOccurrence Application Rule Source Cell Observation Effect Answer) :=
  answers

theorem answerBag_order_invariant
    {left right : List
      (AnswerOccurrence Application Rule Source Cell Observation Effect Answer)}
    (permutation : left.Perm right) :
    answerBag left = answerBag right := by
  simpa [answerBag] using permutation

abbrev DemoAnswerOccurrence :=
  AnswerOccurrence Nat Nat Nat Nat Nat Nat Nat

def duplicateAnswerLeft : DemoAnswerOccurrence :=
  { application := 0, rule := 1, receipt := { roots := ∅ }, answer := 42 }

def duplicateAnswerRight : DemoAnswerOccurrence :=
  { application := 0, rule := 2, receipt := { roots := ∅ }, answer := 42 }

/-- Equal result payloads from distinct admitted rule occurrences remain two
semantic answer occurrences. -/
theorem duplicate_rules_retain_occurrence_multiplicity :
    (answerBag [duplicateAnswerLeft, duplicateAnswerRight]).card = 2 ∧
    duplicateAnswerLeft.answer = duplicateAnswerRight.answer ∧
    duplicateAnswerLeft.rule ≠ duplicateAnswerRight.rule := by
  decide

def correlatedPairs (outcomes : List Observation) :
    List (Observation × Observation) :=
  outcomes.map fun outcome => (outcome, outcome)

def freshPairs (outcomes : List Observation) :
    List (Observation × Observation) :=
  outcomes.flatMap fun left => outcomes.map fun right => (left, right)

inductive DemoObservation where
  | a
  | b
deriving DecidableEq, Repr

theorem delay_demo_is_correlated :
    correlatedPairs [DemoObservation.a, DemoObservation.b] =
      [(DemoObservation.a, DemoObservation.a),
       (DemoObservation.b, DemoObservation.b)] := by
  rfl

theorem resample_demo_is_cross_product :
    freshPairs [DemoObservation.a, DemoObservation.b] =
      [(DemoObservation.a, DemoObservation.a),
       (DemoObservation.a, DemoObservation.b),
       (DemoObservation.b, DemoObservation.a),
       (DemoObservation.b, DemoObservation.b)] := by
  rfl

theorem resample_fresh_cells_not_same
    {Cell : Type*} {left right : Cell} (fresh : left ≠ right) :
    ¬ PrimeDemandBoundary.sameSuspension left right :=
  fresh

/-- Least publication is inherited directly from the shared causal world
theory for the exact occurrence-tagged roots of an answer. -/
theorem answer_publication_least
    [DecidableEq Event]
    {basis : PrimeNeedWorlds.FiniteCausalBasis Event}
    {conflict : Event → Event → Prop}
    (receipt : PrimeNeedWorlds.DependencyReceipt Event)
    (valid : PrimeNeedWorlds.ConflictFree conflict (basis.close receipt.roots))
    (world : PrimeNeedWorlds.Configuration basis conflict)
    (containsRoots : receipt.roots ⊆ world.events) :
    receipt.publish valid ≤ world :=
  PrimeNeedWorlds.DependencyReceipt.publish_least
    receipt valid world containsRoots

theorem compatible_publications_have_least_join
    [DecidableEq Event]
    {basis : PrimeNeedWorlds.FiniteCausalBasis Event}
    {conflict : Event → Event → Prop}
    (left right : PrimeNeedWorlds.Configuration basis conflict)
    (compatible : PrimeNeedWorlds.Configuration.Compatible left right) :
    left ≤ PrimeNeedWorlds.Configuration.join left right compatible ∧
    right ≤ PrimeNeedWorlds.Configuration.join left right compatible ∧
    ∀ upper, left ≤ upper → right ≤ upper →
      PrimeNeedWorlds.Configuration.join left right compatible ≤ upper := by
  exact ⟨PrimeNeedWorlds.Configuration.left_le_join left right compatible,
    PrimeNeedWorlds.Configuration.right_le_join left right compatible,
    fun upper hLeft hRight =>
      PrimeNeedWorlds.Configuration.join_least
        left right upper hLeft hRight compatible⟩

theorem conflicting_publications_have_no_common_extension
    [DecidableEq Event]
    {basis : PrimeNeedWorlds.FiniteCausalBasis Event}
    {conflict : Event → Event → Prop}
    (left right : PrimeNeedWorlds.Configuration basis conflict)
    (incompatible :
      ¬ PrimeNeedWorlds.Configuration.Compatible left right) :
    ¬ ∃ upper : PrimeNeedWorlds.Configuration basis conflict,
        left ≤ upper ∧ right ≤ upper := by
  rwa [← PrimeNeedWorlds.Configuration.compatible_iff_common_extension]

/-! ## Positive and negative executable examples -/

def demoCandidate : OperationalCandidate Bool Nat Nat :=
  { rule := 7, context := 0, support := {true} }

example :
    (admittedState (Source := Nat) (Cell := Nat) (Observation := Nat)
      (Effect := Nat) (Answer := Nat) demoCandidate).phase = .demanding := by
  decide

example :
    (admittedState (Source := Nat) (Cell := Nat) (Observation := Nat)
      (Effect := Nat) (Answer := Nat) demoCandidate).pending = {true} := by
  decide

/-- Negative: the unused argument is absent from the admitted support and
therefore cannot be demanded by the candidate machine. -/
example :
    false ∉
      (admittedState (Source := Nat) (Cell := Nat) (Observation := Nat)
        (Effect := Nat) (Answer := Nat) demoCandidate).pending := by
  decide

end Mettapedia.Languages.MeTTa.PrimeEquationCallSemantics
