import Mettapedia.Logic.GovernanceReasoning.Subsumption

/-!
# Treaty Kernel: Proof-Carrying AI-to-AI Subcontracting

Minimal viable treaty kernel for AI agent subcontracting with
formal obligation fulfillment, prohibition breach detection, and
deadline semantics.

## Architecture

- §1 Treaty structures: clauses, events, traces
- §2 Temporal predicates: `occursWithin`, `eventOccursBy`
- §3 Obligation fulfillment and prohibition violation (separate predicates)
- §4 Deadline semantics
- §5 Core theorems
- §6 Concrete example: confidential subcall treaty

## Design Decisions

Following GPT-5.2 Pro review:
- Obligations and prohibitions are handled by **separate predicates**
  (`obligationFulfilled` / `prohibitionViolated`), not a generic `clauseFulfilled`.
- Named clauses instead of `get!` indexing.
- Event subsumption (`eventSubsumes`) used locally; existing `HasViolation`
  exact-match layer is untouched.

## References

- governance-reasoning-engine/reason/judgement_level.metta
- GPT-5.2 Pro review (2026-03-02)
-/

namespace Mettapedia.Logic.GovernanceReasoning.TreatyKernel

open Mettapedia.Logic.GovernanceReasoning.Core
open Mettapedia.Logic.GovernanceReasoning.Subsumption

/-! ## §1 Treaty Structures -/

/-- A treaty clause: a single obligation, prohibition, or permission
    in a bilateral agreement between two parties. -/
structure TreatyClause (CId Entity Pred Time Party : Type*) where
  /-- Clause identifier. -/
  id : CId
  /-- The party bearing the duty. -/
  obligor : Party
  /-- The party holding the right. -/
  obligee : Party
  /-- Deontic modality of the clause. -/
  modality : DeonticModality
  /-- The eventuality pattern this clause constrains. -/
  eventPattern : Eventuality Entity Pred
  /-- Optional deadline for compliance. -/
  deadline : Option Time := none
  /-- Pointer to a repair clause (CTD chain). -/
  repairClauseId : Option CId := none

/-- A timestamped event in a treaty trace. -/
structure TreatyEvent (Entity Pred Time Party : Type*) where
  /-- When the event occurred. -/
  timestamp : Time
  /-- The concrete eventuality. -/
  event : Eventuality Entity Pred
  /-- The party attesting this event. -/
  attestedBy : Party

/-- A treaty trace: ordered sequence of attested events. -/
abbrev TreatyTrace (Entity Pred Time Party : Type*) :=
  List (TreatyEvent Entity Pred Time Party)

/-! ## §2 Temporal Predicates -/

/-- An event occurs within a deadline (or vacuously if no deadline). -/
def occursWithin [LE Time]
    (deadline : Option Time)
    (te : TreatyEvent Entity Pred Time Party) : Prop :=
  match deadline with
  | none => True
  | some d => te.timestamp ≤ d

/-- An event matching the pattern occurs in the trace within the deadline. -/
def eventOccursBy [LE Time]
    (pattern : Eventuality Entity Pred)
    (deadline : Option Time)
    (trace : TreatyTrace Entity Pred Time Party) : Prop :=
  ∃ te ∈ trace,
    eventSubsumes pattern te.event ∧ occursWithin deadline te

/-! ## §3 Obligation Fulfillment and Prohibition Violation -/

/-- An obligatory clause is fulfilled: the clause is obligatory and
    a matching event occurs within the deadline. -/
def obligationFulfilled [LE Time]
    (clause : TreatyClause CId Entity Pred Time Party)
    (trace : TreatyTrace Entity Pred Time Party) : Prop :=
  clause.modality = .obligatory ∧
  eventOccursBy clause.eventPattern clause.deadline trace

/-- A forbidden clause is violated: the clause is forbidden and
    a matching event occurs (within the deadline if any). -/
def prohibitionViolated [LE Time]
    (clause : TreatyClause CId Entity Pred Time Party)
    (trace : TreatyTrace Entity Pred Time Party) : Prop :=
  clause.modality = .forbidden ∧
  eventOccursBy clause.eventPattern clause.deadline trace

/-! ## §4 Deadline Semantics -/

/-- An obligation's deadline has been missed: the deadline is past
    and no fulfilling event exists. -/
def deadlineMissed [LT Time] [LE Time]
    (clause : TreatyClause CId Entity Pred Time Party)
    (trace : TreatyTrace Entity Pred Time Party)
    (now : Time) : Prop :=
  clause.modality = .obligatory ∧
  ∃ d, clause.deadline = some d ∧ d < now ∧
    ¬ obligationFulfilled clause trace

/-! ## §5 Core Theorems -/

/-- A matching event fulfills an obligatory clause. -/
theorem obligationFulfilled_of_event [LE Time]
    {clause : TreatyClause CId Entity Pred Time Party}
    {trace : TreatyTrace Entity Pred Time Party}
    {te : TreatyEvent Entity Pred Time Party}
    (hmod : clause.modality = .obligatory)
    (hmem : te ∈ trace)
    (hsub : eventSubsumes clause.eventPattern te.event)
    (htime : occursWithin clause.deadline te) :
    obligationFulfilled clause trace :=
  ⟨hmod, ⟨te, hmem, hsub, htime⟩⟩

/-- A matching event violates a forbidden clause. -/
theorem prohibitionViolated_of_event [LE Time]
    {clause : TreatyClause CId Entity Pred Time Party}
    {trace : TreatyTrace Entity Pred Time Party}
    {te : TreatyEvent Entity Pred Time Party}
    (hmod : clause.modality = .forbidden)
    (hmem : te ∈ trace)
    (hsub : eventSubsumes clause.eventPattern te.event)
    (htime : occursWithin clause.deadline te) :
    prohibitionViolated clause trace :=
  ⟨hmod, ⟨te, hmem, hsub, htime⟩⟩

/-- A missed deadline implies the obligation is not fulfilled. -/
theorem deadlineMissed_not_fulfilled [LT Time] [LE Time]
    {clause : TreatyClause CId Entity Pred Time Party}
    {trace : TreatyTrace Entity Pred Time Party}
    {now : Time}
    (h : deadlineMissed clause trace now) :
    ¬ obligationFulfilled clause trace := by
  obtain ⟨_, _, _, _, hnot⟩ := h
  exact hnot

/-- Adding events to a trace preserves obligation fulfillment. -/
theorem obligationFulfilled_mono [LE Time]
    {clause : TreatyClause CId Entity Pred Time Party}
    {trace : TreatyTrace Entity Pred Time Party}
    {extra : TreatyTrace Entity Pred Time Party}
    (h : obligationFulfilled clause trace) :
    obligationFulfilled clause (trace ++ extra) := by
  obtain ⟨hmod, te, hmem, hsub, htime⟩ := h
  exact ⟨hmod, ⟨te, List.mem_append_left _ hmem, hsub, htime⟩⟩

/-- Adding events to a trace preserves prohibition violation. -/
theorem prohibitionViolated_mono [LE Time]
    {clause : TreatyClause CId Entity Pred Time Party}
    {trace : TreatyTrace Entity Pred Time Party}
    {extra : TreatyTrace Entity Pred Time Party}
    (h : prohibitionViolated clause trace) :
    prohibitionViolated clause (trace ++ extra) := by
  obtain ⟨hmod, te, hmem, hsub, htime⟩ := h
  exact ⟨hmod, ⟨te, List.mem_append_left _ hmem, hsub, htime⟩⟩

/-! ## §6 Concrete Example: Confidential Subcall Treaty

A three-clause treaty for an orchestrator O subcontracting specialist S:
1. `deliverBy10` — S must deliver result by timestamp 10 (obligatory)
2. `noDisclosure` — S must not disclose input (forbidden)
3. `refundOnBreach` — S must refund on breach (obligatory, repair clause)
-/

section ConcreteExample

/-- Predicates for the subcall treaty example. -/
inductive SubcallPred where
  | deliver | disclose | refund
  deriving DecidableEq, Repr

/-- Role assignment for the abstract delivery pattern. -/
def deliverPatternRoles : ThematicRole → Option String
  | .agent => some "specialist"
  | .beneficiary => some "orchestrator"
  | .theme => some "job:J"
  | _ => none

/-- Role assignment for a concrete delivery event (has extra `.result` role). -/
def concreteDeliveryRoles : ThematicRole → Option String
  | .agent => some "specialist"
  | .beneficiary => some "orchestrator"
  | .theme => some "job:J"
  | .result => some "hash:H1"
  | _ => none

/-- Abstract delivery pattern: deliver by specialist for orchestrator on job:J. -/
def deliverPattern : Eventuality String SubcallPred :=
  { predicate := .deliver, roles := deliverPatternRoles, polarity := true }

/-- Concrete delivery event: same as pattern but with result role filled. -/
def concreteDelivery : Eventuality String SubcallPred :=
  { predicate := .deliver, roles := concreteDeliveryRoles, polarity := true }

/-- The concrete delivery event subsumes (is complied with by) the abstract pattern:
    same predicate, same polarity, and every role in the pattern matches. -/
theorem concreteDelivery_matches_pattern :
    eventSubsumes deliverPattern concreteDelivery := by
  refine ⟨rfl, ?_, rfl⟩
  intro r a ha
  revert ha
  cases r <;> simp [deliverPattern, concreteDelivery, deliverPatternRoles, concreteDeliveryRoles]

/-- Role assignment for the abstract disclosure pattern. -/
def disclosePatternRoles : ThematicRole → Option String
  | .agent => some "specialist"
  | .theme => some "job:J"
  | _ => none

/-- Abstract nondisclosure pattern. -/
def disclosePattern : Eventuality String SubcallPred :=
  { predicate := .disclose, roles := disclosePatternRoles, polarity := true }

/-- Concrete disclosure event (leak with extra recipient role). -/
def concreteDisclosureRoles : ThematicRole → Option String
  | .agent => some "specialist"
  | .theme => some "job:J"
  | .beneficiary => some "adversary"
  | _ => none

def concreteDisclosure : Eventuality String SubcallPred :=
  { predicate := .disclose, roles := concreteDisclosureRoles, polarity := true }

/-- The concrete disclosure subsumes the abstract disclosure pattern. -/
theorem concreteDisclosure_matches_pattern :
    eventSubsumes disclosePattern concreteDisclosure := by
  refine ⟨rfl, ?_, rfl⟩
  intro r a ha
  revert ha
  cases r <;> simp [disclosePattern, concreteDisclosure, disclosePatternRoles, concreteDisclosureRoles]

/-- Clause 1: deliver result by timestamp 10. -/
def deliverBy10 : TreatyClause String String SubcallPred Nat String :=
  { id := "deliver-by-10"
    obligor := "specialist"
    obligee := "orchestrator"
    modality := .obligatory
    eventPattern := deliverPattern
    deadline := some 10
    repairClauseId := some "refund-on-breach" }

/-- Clause 2: no disclosure of input (forbidden). -/
def noDisclosure : TreatyClause String String SubcallPred Nat String :=
  { id := "no-disclosure"
    obligor := "specialist"
    obligee := "orchestrator"
    modality := .forbidden
    eventPattern := disclosePattern }

/-- Clause 3: refund on breach (repair clause). -/
def refundOnBreach : TreatyClause String String SubcallPred Nat String :=
  { id := "refund-on-breach"
    obligor := "specialist"
    obligee := "orchestrator"
    modality := .obligatory
    eventPattern := { predicate := .refund
                      roles := fun
                        | .agent => some "specialist"
                        | .beneficiary => some "orchestrator"
                        | _ => none
                      polarity := true } }

/-- The full treaty: three clauses. -/
def confidentialSubcallTreaty :
    List (TreatyClause String String SubcallPred Nat String) :=
  [deliverBy10, noDisclosure, refundOnBreach]

/-- A delivery event at timestamp 7 by the specialist. -/
def deliveryEvent : TreatyEvent String SubcallPred Nat String :=
  { timestamp := 7
    event := concreteDelivery
    attestedBy := "specialist" }

/-- A disclosure event at timestamp 5 (leak). -/
def disclosureEvent : TreatyEvent String SubcallPred Nat String :=
  { timestamp := 5
    event := concreteDisclosure
    attestedBy := "monitor" }

/-- The delivery event at timestamp 7 fulfills the deliver-by-10 clause. -/
theorem deliveryEvent_fulfills_deliverBy10 :
    obligationFulfilled deliverBy10 [deliveryEvent] := by
  exact ⟨rfl, ⟨deliveryEvent, List.mem_cons_self .., concreteDelivery_matches_pattern,
    by simp [occursWithin, deliverBy10, deliveryEvent]⟩⟩

/-- The disclosure event violates the no-disclosure clause. -/
theorem disclosureEvent_violates_noDisclosure :
    prohibitionViolated noDisclosure [disclosureEvent] := by
  exact ⟨rfl, ⟨disclosureEvent, List.mem_cons_self .., concreteDisclosure_matches_pattern,
    by simp [occursWithin, noDisclosure]⟩⟩

end ConcreteExample

end Mettapedia.Logic.GovernanceReasoning.TreatyKernel
