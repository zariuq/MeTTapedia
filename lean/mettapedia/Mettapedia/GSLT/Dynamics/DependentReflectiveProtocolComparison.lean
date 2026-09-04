import Mettapedia.GSLT.Core.SemanticTransport
import Mettapedia.GSLT.Dynamics.ExactCodeProtocolPolynomial

/-!
# Dependent reflective protocol comparison

This module combines five structures on one nontrivial protocol:

* an indexed polynomial whose responses select differently typed successors;
* a material, nonidentity code representation of commands;
* forward and backward operational realizations of the endpoint dynamics;
* exact transport of proof-relevant interaction events and dependent rounds;
* independent denotation, observation, and occurrence-sensitive cost layers.

The comparison separates their proof obligations.  Static beta is enough for
endpoint-step preservation, while beta and eta are both needed for exact
command, event, and complete-strategy transport.  Even exact code does not
make a coarse completion observer determine the successor-indexed result
family or response-sensitive work/span cost.

This is a comparison canary, not a language definition.  It does not choose a
native calculus, scheduler, evaluation order, process equivalence, or cost
algebra.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.DependentReflectiveProtocolComparison

open Mettapedia.Algebra
open Mettapedia.Computability.ReflectiveCode
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol.VaryingCanary
open Mettapedia.GSLT.Dynamics.ExactCodeProtocolPolynomial
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.ExactCodeModalityModel

/-! ## Exact command code -/

/-- One material code layer around each command available at a protocol
state.  Completed states have no commands and hence no codes. -/
abbrev CommandCode (state : Phase) :=
  ExactCodeIter 1 (Command query state)

/-- Quotation and splicing are indexed by the protocol state. -/
def representation : CommandInterface query CommandCode :=
  fun _state =>
    { quote := quoteIter 1
      drop := spliceIter 1 }

theorem representation_beta (state : Phase) :
    (representation state).StaticBeta :=
  splice_quote 1

theorem representation_eta (state : Phase) :
    (representation state).StaticEta :=
  quote_splice 1

/-- The coded query has codes as command shapes and retains the original
response and successor families through decoding. -/
abbrev codedQuery := coded query CommandCode representation

/-- The initial command really is wrapped rather than definitionally reused. -/
theorem quoted_ask_has_one_code_layer :
    (representation Phase.start).quote QueryCommand.ask =
      ExactCodeLayer.mk QueryCommand.ask :=
  rfl

/-! ## Endpoint realization in both directions -/

/-- Encoding realizes every source endpoint step by one coded endpoint step.
The term map is identity because command representation changes the edge
witness rather than the protocol state. -/
def encodingRealization :
    OperationalRealization (lts query) (lts codedQuery) where
  mapTerm := id
  mapEquiv := fun equal => equal
  mapStep := fun step =>
    .cons
      ⟨step_preserves query CommandCode representation
        representation_beta step⟩
      (.refl _)

/-- Decoding reflects every coded endpoint step to the source protocol. -/
def decodingRealization :
    OperationalRealization (lts codedQuery) (lts query) where
  mapTerm := id
  mapEquiv := fun equal => equal
  mapStep := fun step =>
    .cons ⟨step_reflects query CommandCode representation step⟩ (.refl _)

/-- The two endpoint transition relations agree exactly. -/
theorem endpoint_step_iff {source target : Phase} :
    (lts codedQuery).Step source target <->
      (lts query).Step source target :=
  step_iff query CommandCode representation representation_beta

/-! ## Independent denotation square -/

/-- A deliberately small invariant says only that both transition systems
remain within the same protocol.  It is independent of completion, result
type, event identity, and cost. -/
def sourceDenotation : SemanticInvariant (lts query) Unit where
  denote := fun _ => ()
  equation := fun _ => rfl
  rewrite := fun _ => rfl

def codedDenotation : SemanticInvariant (lts codedQuery) Unit where
  denote := fun _ => ()
  equation := fun _ => rfl
  rewrite := fun _ => rfl

/-- Encoding commutes with the independently selected denotation. -/
def encodingDenotationSquare :
    DenotationSquare encodingRealization sourceDenotation codedDenotation id where
  commutes := fun _ => rfl

/-- Decoding commutes with the same denotation in the reverse direction. -/
def decodingDenotationSquare :
    DenotationSquare decodingRealization codedDenotation sourceDenotation id where
  commutes := fun _ => rfl

/-! ## Exact dependent interaction transport -/

/-- Exact command code transports the complete response-indexed strategy. -/
def roundEquiv :
    OneRound query Result Phase.start ≃
      OneRound codedQuery Result Phase.start :=
  oneRoundEquiv query CommandCode representation representation_beta
    representation_eta Result Phase.start

/-- The source strategy transported through material command code. -/
def codedRound : OneRound codedQuery Result Phase.start :=
  roundEquiv round

/-- Exact code also transports the proof-relevant enabled-event fibre. -/
def eventEquiv :
    (interaction query).Enabled Phase.start ≃
      (interaction codedQuery).Enabled Phase.start :=
  enabledEventEquiv query CommandCode representation representation_beta
    representation_eta Phase.start

/-- Explicit response events in the coded protocol. -/
def unitEvent : (interaction codedQuery).Enabled Phase.start :=
  enabled codedQuery (quoteIter 1 QueryCommand.ask) false

def boolEvent : (interaction codedQuery).Enabled Phase.start :=
  enabled codedQuery (quoteIter 1 QueryCommand.ask) true

/-- Response selection still lands in the differently typed successor
fibres after command coding. -/
def unitOutcome : Sigma (fun event : (interaction codedQuery).Enabled Phase.start =>
    Result event.target) :=
  ⟨unitEvent, PUnit.unit⟩

def boolOutcome : Sigma (fun event : (interaction codedQuery).Enabled Phase.start =>
    Result event.target) :=
  ⟨boolEvent, false⟩

theorem coded_outcomes_have_expected_types :
    unitOutcome.1.target = Phase.unitDone /\
      boolOutcome.1.target = Phase.boolDone /\
      unitOutcome.2 = PUnit.unit /\
      boolOutcome.2 = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The exact event equivalence sends each source response occurrence to the
corresponding coded occurrence. -/
theorem event_equiv_maps_both_responses :
    eventEquiv
        IndexedPolynomialProtocol.VaryingCanary.unitOutcome.1 = unitEvent /\
      eventEquiv
        IndexedPolynomialProtocol.VaryingCanary.boolOutcome.1 = boolEvent :=
  ⟨rfl, rfl⟩

/-! ## Observation and cost remain independent structure -/

/-- Recover the response identity retained in a coded enabled event. -/
def responseTag (event : (interaction codedQuery).Enabled Phase.start) : Bool :=
  by
    obtain ⟨site, target, evidence⟩ := event
    cases site
    cases evidence with
    | fire code response =>
        cases code with
        | mk command =>
            cases command
            exact response

/-- The visible endpoint observer forgets which completed phase was reached. -/
def visibleCompletion
    (event : (interaction codedQuery).Enabled Phase.start) : Bool :=
  completion event.target

/-- A response-sensitive work/span valuation. -/
def workSpan (event : (interaction codedQuery).Enabled Phase.start) : WorkSpan :=
  if responseTag event then ⟨3, 2⟩ else ⟨1, 1⟩

@[simp] theorem unitEvent_responseTag : responseTag unitEvent = false :=
  rfl

@[simp] theorem boolEvent_responseTag : responseTag boolEvent = true :=
  rfl

@[simp] theorem unitEvent_visibleCompletion :
    visibleCompletion unitEvent = true :=
  rfl

@[simp] theorem boolEvent_visibleCompletion :
    visibleCompletion boolEvent = true :=
  rfl

@[simp] theorem unitEvent_workSpan : workSpan unitEvent = ⟨1, 1⟩ :=
  rfl

@[simp] theorem boolEvent_workSpan : workSpan boolEvent = ⟨3, 2⟩ :=
  rfl

/-- Completion cannot reconstruct response-sensitive cost, even though the
command representation is exact. -/
theorem workSpan_not_completion_determined :
    ¬ Factors visibleCompletion workSpan := by
  let fibre : NonTrivialFiber visibleCompletion workSpan :=
    { left := unitEvent
      right := boolEvent
      sameShadow := rfl
      differentValue := by decide }
  exact fibre.not_factors

/-- Exact command code does not repair information already erased by a
coarse state observer: the result family still cannot descend through
completion. -/
theorem result_not_completion_determined :
    ¬ Nonempty (FamilyFactorization completion Result) :=
  IndexedPolynomialProtocol.VaryingCanary.result_not_determined_by_completion

/-- Exact state is the positive observation control. -/
def result_exact_state_factorization : FamilyFactorization id Result :=
  FamilyFactorization.pullback id Result

/-- One theorem records the full comparison boundary: endpoint behavior,
dependent interaction, and exact-state observation are preserved, while
coarse completion determines neither the varying result family nor cost. -/
theorem dependent_reflective_protocol_boundary :
    (lts codedQuery).Step Phase.start unitEvent.target /\
      (lts codedQuery).Step Phase.start boolEvent.target /\
      Nonempty (OneRound codedQuery Result Phase.start) /\
      Nonempty (FamilyFactorization id Result) /\
      ¬ Nonempty (FamilyFactorization completion Result) /\
      ¬ Factors visibleCompletion workSpan :=
  ⟨unitEvent.step, boolEvent.step, ⟨codedRound⟩,
    ⟨result_exact_state_factorization⟩,
    result_not_completion_determined,
    workSpan_not_completion_determined⟩

/-! ## Axiom audit -/

#print axioms quoted_ask_has_one_code_layer
#print axioms endpoint_step_iff
#print axioms encodingDenotationSquare
#print axioms decodingDenotationSquare
#print axioms roundEquiv
#print axioms eventEquiv
#print axioms coded_outcomes_have_expected_types
#print axioms event_equiv_maps_both_responses
#print axioms workSpan_not_completion_determined
#print axioms result_not_completion_determined
#print axioms dependent_reflective_protocol_boundary

end Mettapedia.GSLT.Dynamics.DependentReflectiveProtocolComparison
