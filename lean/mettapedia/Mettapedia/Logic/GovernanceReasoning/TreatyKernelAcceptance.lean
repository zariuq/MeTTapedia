import Mettapedia.Logic.GovernanceReasoning.ActualityPolicy
import Mettapedia.Logic.GovernanceReasoning.OccurrenceMVP

/-!
# Treaty Kernel Acceptance: Provenance-First Admitted-Trace Demo

Extends the confidential-subcall treaty example from `TreatyKernel.lean`
with evidence-assessed events and provenance-aware acceptance filtering.

## Scenario

An orchestrator O subcontracts specialist S. Multiple candidate events
arrive from different sources with varying reliability:

| Event | Attestor | BinaryEvidence | Accepted? |
|-------|----------|----------|-----------|
| Self-claimed delivery | specialist | ⟨2,2⟩ | NO (self-report, weak) |
| Hash-verified delivery | hash-verifier | ⟨8,0⟩ | YES (strong, trusted) |
| Monitor-detected leak | monitor | ⟨5,1⟩ | YES (trusted source) |
| Gossip-reported leak | gossip | ⟨1,4⟩ | NO (untrusted) |

The acceptance rule is provenance-aware: only trusted attestors
(hash-verifier, monitor) with sufficient positive evidence (≥ 3)
and low negative evidence (≤ 1) are admitted.

## Architecture

- §1 Assessed treaty event wrapper
- §2 Concrete assessed events (4 events)
- §3 Provenance-aware acceptance rule
- §4 Acceptance decision theorems
- §5 Treaty compliance on accepted trace

## References

- GPT-5.2 Pro review (2026-03-02): provenance-first acceptance
- Jøsang (2016): subjective logic, evidence with uncertainty dimension
- Shafer (1976): belief functions, not just probability
-/

namespace Mettapedia.Logic.GovernanceReasoning.TreatyKernelAcceptance

open Mettapedia.Logic.GovernanceReasoning.Core
open Mettapedia.Logic.GovernanceReasoning.Subsumption
open Mettapedia.Logic.GovernanceReasoning.TreatyKernel
open Mettapedia.Logic.EvidenceQuantale

/-! ## §1 Assessed Treaty Event Wrapper

Wraps a `TreatyEvent` with an evidence assessment and identifier,
without mutating the core treaty type. Analogous to `IdStatementJudgment`
for statements. -/

/-- A treaty event with an evidence assessment attached.
    The `ev` field represents the assessed strength of evidence
    for this event from its attestor. -/
structure AssessedTreatyEvent (Entity Pred Time Party : Type*) where
  /-- Identifier for this assessed event. -/
  id : String
  /-- The underlying treaty event. -/
  base : TreatyEvent Entity Pred Time Party
  /-- BinaryEvidence assessment for this event. -/
  ev : BinaryEvidence

/-! ## §2 Concrete Assessed Events

Four candidate events for the confidential subcall treaty.
Two are from trusted sources with strong evidence, two are not. -/

section ConcreteAcceptanceExample

/-- Self-claimed delivery by the specialist. Weak evidence: only
    the specialist's own report, with equal contrary indicators. -/
def claimedDelivery : AssessedTreatyEvent String SubcallPred Nat String :=
  { id := "claimed-delivery"
    base := { timestamp := 7
              event := concreteDelivery
              attestedBy := "specialist" }
    ev := ⟨2, 2⟩ }

/-- Hash-verified delivery confirmed by an escrow oracle.
    Strong evidence: cryptographic hash match, no contrary indicators. -/
def verifiedDelivery : AssessedTreatyEvent String SubcallPred Nat String :=
  { id := "verified-delivery"
    base := { timestamp := 8
              event := concreteDelivery
              attestedBy := "hash-verifier" }
    ev := ⟨8, 0⟩ }

/-- Disclosure detected by a network monitor. Trusted source with
    strong positive signal and minimal noise. -/
def monitorLeak : AssessedTreatyEvent String SubcallPred Nat String :=
  { id := "monitor-leak"
    base := { timestamp := 5
              event := concreteDisclosure
              attestedBy := "monitor" }
    ev := ⟨5, 1⟩ }

/-- Unverified rumor of a disclosure from a gossip channel.
    Untrusted source, mostly negative (contradicted by other signals). -/
def rumorLeak : AssessedTreatyEvent String SubcallPred Nat String :=
  { id := "rumor-leak"
    base := { timestamp := 9
              event := concreteDisclosure
              attestedBy := "gossip" }
    ev := ⟨1, 4⟩ }

/-- The raw assessed trace: all four candidate events. -/
def rawAssessedTrace : List (AssessedTreatyEvent String SubcallPred Nat String) :=
  [claimedDelivery, verifiedDelivery, monitorLeak, rumorLeak]

/-! ## §3 Provenance-Aware Acceptance Rule

The acceptance rule combines two checks:
1. **Provenance gate**: only events from trusted attestors are considered.
2. **BinaryEvidence quality gate**: sufficient positive evidence (pos ≥ 3) and
   low negative evidence (neg ≤ 1).

Both gates must pass for an event to be admitted to the accepted trace.
The provenance gate is computable (string match); the evidence gate
operates on `ℝ≥0∞` and is therefore noncomputable (classical decide). -/

open scoped ENNReal

/-- Whether an attestor is trusted for this treaty.

    Trust assignments reflect underlying evidence quality:
    - "hash-verifier": cryptographic receipt (strong evidence ⟨8,0⟩)
    - "monitor": independent network observation (good evidence ⟨5,1⟩)
    - "specialist": self-report (weak, conflicted evidence ⟨2,2⟩)
    - "gossip": unreliable channel (poor evidence ⟨1,4⟩) -/
def trustedAttestor : String → Bool
  | "hash-verifier" => true
  | "monitor" => true
  | _ => false

/-- BinaryEvidence quality gate: positive evidence ≥ 3, negative evidence ≤ 1. -/
noncomputable def evidenceAcceptable (ev : BinaryEvidence) : Bool :=
  if (3 : ℝ≥0∞) ≤ ev.pos ∧ ev.neg ≤ 1 then true else false

/-- Acceptance predicate: trusted attestor AND acceptable evidence quality. -/
noncomputable def subcallAccepts
    (ae : AssessedTreatyEvent String SubcallPred Nat String) : Bool :=
  trustedAttestor ae.base.attestedBy && evidenceAcceptable ae.ev

/-- The accepted base trace: filter by acceptance, project to base events. -/
noncomputable def acceptedBaseTrace
    (xs : List (AssessedTreatyEvent String SubcallPred Nat String)) :
    TreatyTrace String SubcallPred Nat String :=
  (xs.filter fun ae => subcallAccepts ae).map AssessedTreatyEvent.base

/-! ## §4 Acceptance Decision Theorems -/

/-- Self-claimed delivery is NOT accepted: specialist is not a trusted attestor.
    Short-circuits: `false && _ = false`. -/
theorem claimedDelivery_not_accepted :
    subcallAccepts claimedDelivery = false := by
  simp [subcallAccepts, trustedAttestor, claimedDelivery]

/-- Gossip rumor is NOT accepted: gossip is not a trusted attestor.
    Short-circuits: `false && _ = false`. -/
theorem rumorLeak_not_accepted :
    subcallAccepts rumorLeak = false := by
  simp [subcallAccepts, trustedAttestor, rumorLeak]

private lemma evidenceAcceptable_8_0 :
    evidenceAcceptable ⟨8, 0⟩ = true := by
  simp only [evidenceAcceptable]
  norm_num

private lemma evidenceAcceptable_5_1 :
    evidenceAcceptable ⟨5, 1⟩ = true := by
  simp only [evidenceAcceptable]
  norm_num

/-- Hash-verified delivery IS accepted: trusted attestor with strong evidence ⟨8,0⟩. -/
theorem verifiedDelivery_accepted :
    subcallAccepts verifiedDelivery = true := by
  simp [subcallAccepts, trustedAttestor, verifiedDelivery, evidenceAcceptable_8_0]

/-- Monitor-detected leak IS accepted: trusted attestor with strong evidence ⟨5,1⟩. -/
theorem monitorLeak_accepted :
    subcallAccepts monitorLeak = true := by
  simp [subcallAccepts, trustedAttestor, monitorLeak, evidenceAcceptable_5_1]

/-- The accepted base trace contains exactly the two admitted events. -/
theorem acceptedBaseTrace_eq :
    acceptedBaseTrace rawAssessedTrace =
      [verifiedDelivery.base, monitorLeak.base] := by
  simp [acceptedBaseTrace, rawAssessedTrace, List.filter,
    subcallAccepts, trustedAttestor,
    claimedDelivery, verifiedDelivery, monitorLeak, rumorLeak,
    evidenceAcceptable_8_0, evidenceAcceptable_5_1]

/-! ## §5 Treaty Compliance on Accepted Trace -/

/-- The verified delivery fulfills the deliver-by-10 obligation
    on the accepted trace. Timestamp 8 ≤ 10, pattern matches. -/
theorem verifiedDelivery_fulfills :
    obligationFulfilled deliverBy10 (acceptedBaseTrace rawAssessedTrace) := by
  rw [acceptedBaseTrace_eq]
  exact ⟨rfl, verifiedDelivery.base, List.mem_cons_self ..,
    concreteDelivery_matches_pattern,
    by simp [occursWithin, deliverBy10, verifiedDelivery]⟩

/-- The monitor-detected leak violates the no-disclosure prohibition
    on the accepted trace. -/
theorem monitorLeak_violates :
    prohibitionViolated noDisclosure (acceptedBaseTrace rawAssessedTrace) := by
  rw [acceptedBaseTrace_eq]
  exact ⟨rfl, monitorLeak.base, by simp [List.mem_cons],
    concreteDisclosure_matches_pattern,
    by simp [occursWithin, noDisclosure]⟩

/-! ## §6 Admission Soundness -/

/-- Soundness: an accepted event's base appears in the accepted base trace. -/
theorem accepted_event_sound
    {ae : AssessedTreatyEvent String SubcallPred Nat String}
    {xs : List (AssessedTreatyEvent String SubcallPred Nat String)}
    (hmem : ae ∈ xs)
    (hacc : subcallAccepts ae = true) :
    ae.base ∈ acceptedBaseTrace xs := by
  simp only [acceptedBaseTrace]
  apply List.mem_map.mpr
  exact ⟨ae, List.mem_filter.mpr ⟨hmem, hacc⟩, rfl⟩

end ConcreteAcceptanceExample

end Mettapedia.Logic.GovernanceReasoning.TreatyKernelAcceptance
