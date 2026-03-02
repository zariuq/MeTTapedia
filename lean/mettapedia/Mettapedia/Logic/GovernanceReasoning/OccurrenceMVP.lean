import Mettapedia.Logic.GovernanceReasoning.TreatyKernel

/-!
# Occurrence MVP: Admitted Traces for Treaty Reasoning

Bridges the evidence/acceptance layer to the treaty kernel by introducing
**admitted traces**: the treaty kernel operates over events that pass an
admission predicate, while the WM/evidence layer decides which events
are admitted.

## Architecture

- §1 `occursAt`: time-indexed occurrence predicate
- §2 `admittedTrace`: trace filtered by admission predicate
- §3 Soundness: admitted events fulfill obligations / trigger violations

## Design

The key architectural insight is separation of concerns:
- WM/evidence/attestation layer decides which events are **admitted**
- Treaty layer stays crisp and classical over the **admitted trace**

This is the minimal event-calculus-lite bridge: `occursAt` replaces
timeless `rexist` with time-indexed occurrence, and `admittedTrace`
connects evidence-based acceptance to treaty compliance.

## References

- GPT-5.2 Pro review (2026-03-02): admitted-trace architecture
- Event Calculus: `happens(E,T)` style occurrence predicates
-/

namespace Mettapedia.Logic.GovernanceReasoning.OccurrenceMVP

open Mettapedia.Logic.GovernanceReasoning.Core
open Mettapedia.Logic.GovernanceReasoning.Subsumption
open Mettapedia.Logic.GovernanceReasoning.TreatyKernel

/-! ## §1 Time-Indexed Occurrence

A lightweight `happens(E,T)` predicate: an eventuality matching
the pattern occurs at a specific time in the trace. -/

/-- An eventuality matching `pattern` occurs at time `t` in the trace. -/
def occursAt
    (pattern : Eventuality Entity Pred)
    (t : Time)
    (trace : TreatyTrace Entity Pred Time Party) : Prop :=
  ∃ te ∈ trace,
    eventSubsumes pattern te.event ∧ te.timestamp = t

/-! ## §2 Admitted Traces

Filter a treaty trace by an admission predicate. The admission
predicate can encode acceptance-policy gating, attestation checks,
signature verification, or any other event-admission criterion. -/

/-- Filter a treaty trace to only admitted events. -/
def admittedTrace
    (adm : TreatyEvent Entity Pred Time Party → Bool)
    (trace : TreatyTrace Entity Pred Time Party) :
    TreatyTrace Entity Pred Time Party :=
  trace.filter adm

/-! ## §3 Admitted-Trace Soundness

If an admitted event fulfills an obligation or violates a prohibition,
the corresponding predicate holds on the admitted trace. -/

/-- An admitted event fulfills an obligatory clause on the admitted trace. -/
theorem obligationFulfilled_of_admitted_event [LE Time]
    {adm : TreatyEvent Entity Pred Time Party → Bool}
    {clause : TreatyClause CId Entity Pred Time Party}
    {trace : TreatyTrace Entity Pred Time Party}
    {te : TreatyEvent Entity Pred Time Party}
    (hmod : clause.modality = .obligatory)
    (hmem : te ∈ trace)
    (hadm : adm te = true)
    (hsub : eventSubsumes clause.eventPattern te.event)
    (htime : occursWithin clause.deadline te) :
    obligationFulfilled clause (admittedTrace adm trace) := by
  refine ⟨hmod, te, ?_, hsub, htime⟩
  exact List.mem_filter.mpr ⟨hmem, hadm⟩

/-- An admitted event violates a forbidden clause on the admitted trace. -/
theorem prohibitionViolated_of_admitted_event [LE Time]
    {adm : TreatyEvent Entity Pred Time Party → Bool}
    {clause : TreatyClause CId Entity Pred Time Party}
    {trace : TreatyTrace Entity Pred Time Party}
    {te : TreatyEvent Entity Pred Time Party}
    (hmod : clause.modality = .forbidden)
    (hmem : te ∈ trace)
    (hadm : adm te = true)
    (hsub : eventSubsumes clause.eventPattern te.event)
    (htime : occursWithin clause.deadline te) :
    prohibitionViolated clause (admittedTrace adm trace) := by
  refine ⟨hmod, te, ?_, hsub, htime⟩
  exact List.mem_filter.mpr ⟨hmem, hadm⟩

end Mettapedia.Logic.GovernanceReasoning.OccurrenceMVP
