import Mettapedia.Logic.GovernanceReasoning.Bridge

/-!
# Evidence-Graded Actuality and Acceptance Policy

Replaces the metaphysical "really exists" reading of `rexist` with a
two-layer semantics:

1. **Eventuality evidence** — graded evidence that an eventuality obtained
2. **Acceptance policy** — policy-relative categorical acceptance

## Architecture

- §1 Eventuality evidence (thin wrapper over `modalEvidence … .rexist`)
- §2 Projection evidence (alias for `groundEvidence`)
- §3 Acceptance policy and accepted occurrence/projection
- §4 Acceptance bridge: `RexistBridge → AcceptanceBridge`

## Design

The key insight is that `rexist` is best read as an **eventuality-occurrence
evidence channel**, not a binary "really exists" predicate. Categorical
"actuality for governance" is a downstream **acceptance policy**, not
certainty-1 truth. This follows the formal-belief literature's separation
of graded belief from categorical acceptance.

Three bridge strengths form a hierarchy:
- **Evidence equality** (`RexistBridge` / `WMQueryEq`) — strongest
- **Strength agreement** — intermediate (future work)
- **Acceptance agreement** (`AcceptanceBridge`) — weakest, most realistic

## References

- GPT-5.2 Pro review (2026-03-02): modal stripping and evidence-graded actuality
- Stanford Encyclopedia of Philosophy: "States of Affairs" (obtains/not obtains)
- Stanford Encyclopedia of Philosophy: "Formal Representations of Belief"
-/

namespace Mettapedia.Logic.GovernanceReasoning.ActualityPolicy

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.GovernanceReasoning.Core
open Mettapedia.Logic.GovernanceReasoning.Bridge
open scoped ENNReal

/-! ## §1 Eventuality Evidence

Thin wrappers giving the clean "occurrence / obtains" vocabulary
over the existing `modalEvidence … .rexist` channel. -/

variable {State Entity Pred Query : Type*}
  [EvidenceType State] [WorldModel State Query]

/-- Evidence that an eventuality obtained / occurred.

    Semantically: "how much evidence is there that this eventuality
    occurred in world-model state W?" This replaces the metaphysical
    "really exists" reading of `rexist`. -/
def eventualityEvidence
    (W : State) (enc : DeonticQueryEncoder Entity Pred Query)
    (e : Eventuality Entity Pred) : Evidence :=
  DeonticQueryEncoder.modalEvidence (State := State) W enc .rexist e

/-- Short alias for `eventualityEvidence`. -/
abbrev eventEvidence := @eventualityEvidence

/-! ## §2 Projection Evidence

Aliases giving the "projection" vocabulary over the existing
`groundEvidence` / `groundQuery` channel. A projection query asks:
"what structured fact-shadow of the eventuality is supported?" -/

/-- Evidence for a structured factual projection (CT-triple) of an eventuality. -/
def projectionEvidence
    (W : State) (enc : DeonticQueryEncoder Entity Pred Query)
    (t : CTTriple Entity Pred) : Evidence :=
  DeonticQueryEncoder.groundEvidence (State := State) W enc t

/-- Alias: projection query = ground query with cleaner semantics. -/
abbrev projectionQuery {Entity Pred Query : Type*}
    (enc : DeonticQueryEncoder Entity Pred Query) :=
  enc.groundQuery

/-! ## §3 Acceptance Policy

A policy-relative categorical acceptance layer. Instead of treating
evidence = 1 as "truth", governance systems specify an acceptance
policy that determines when graded evidence is sufficient for
categorical governance reasoning. -/

/-- An acceptance policy: determines when graded evidence is sufficient
    for categorical acceptance in governance reasoning. -/
structure AcceptancePolicy where
  /-- Whether the policy accepts the given evidence as sufficient. -/
  accepts : Evidence → Prop

/-- An eventuality is accepted as having occurred under policy `π`. -/
def acceptedOccurrence
    (π : AcceptancePolicy) (W : State)
    (enc : DeonticQueryEncoder Entity Pred Query)
    (e : Eventuality Entity Pred) : Prop :=
  π.accepts (eventualityEvidence (State := State) W enc e)

/-- Short alias for `acceptedOccurrence`. -/
abbrev eventAccepted := @acceptedOccurrence

/-- A projection (CT-triple) is accepted under policy `π`. -/
def acceptedProjection
    (π : AcceptancePolicy) (W : State)
    (enc : DeonticQueryEncoder Entity Pred Query)
    (t : CTTriple Entity Pred) : Prop :=
  π.accepts (projectionEvidence (State := State) W enc t)

/-! ## §4 Acceptance Bridge

The key theorem: the current `RexistBridge` (evidence equality between
occurrence and projection channels) implies acceptance agreement for
**any** policy. This shows the existing strong bridge is conservative
over the weaker acceptance-level bridge. -/

/-- Two queries agree at the acceptance level under policy `π`:
    accepted-occurrence ↔ accepted-projection in every WM state. -/
def AcceptanceBridge
    (π : AcceptancePolicy)
    (enc : DeonticQueryEncoder Entity Pred Query)
    (e : Eventuality Entity Pred)
    (t : CTTriple Entity Pred) : Prop :=
  ∀ W : State,
    acceptedOccurrence (State := State) π W enc e ↔
    acceptedProjection (State := State) π W enc t

/-- The current `RexistBridge` (evidence equality) implies `AcceptanceBridge`
    for any acceptance policy. This is the soundness theorem:
    stronger bridge ⇒ weaker bridge. -/
theorem acceptanceBridge_of_rexistBridge
    (π : AcceptancePolicy)
    (enc : DeonticQueryEncoder Entity Pred Query)
    {e : Eventuality Entity Pred}
    {t : CTTriple Entity Pred}
    (h : RexistBridge (State := State) enc e t) :
    AcceptanceBridge (State := State) π enc e t := by
  intro W
  simp only [acceptedOccurrence, acceptedProjection,
    eventualityEvidence, projectionEvidence,
    DeonticQueryEncoder.modalEvidence, DeonticQueryEncoder.groundEvidence,
    h W]

/-! ## §5 Support/Confidence Preorder Family

A parameterized preorder on `Evidence` that compares both support (strength)
and confidence simultaneously. Unlike the raw coordinatewise order `≤` on
Evidence (which includes more negative evidence), this preorder captures the
intended meaning: "at least as supported and at least as confident."

This is one member of a **family** of preorders, parameterized by a prior
context `ctx` and a confidence parameter `κ`. Different governance applications
may choose different (ctx, κ) pairs.

### Why not a global order on Evidence?

The coordinatewise order `e₁ ≤ e₂ ↔ pos₁ ≤ pos₂ ∧ neg₁ ≤ neg₂` is wrong
for strength-based acceptance: `⟨8,1⟩ ≤ ⟨8,100⟩` but the latter has much
worse strength. A strength-respecting order must be context-dependent
(parameterized by prior), so there is no single canonical "better evidence"
order. (Hawthorne, "The Lockean Thesis and the Logic of Belief";
Foley, "Degrees of Belief".) -/

/-- Support/confidence preorder: `e₂` has at least as much support and
    confidence as `e₁`, relative to prior context `ctx` and confidence
    parameter `κ`.  Equivalently, `e₁` is no stronger than `e₂`. -/
noncomputable def supportConfidenceLE
    (ctx : BinaryContext) (κ : ℝ≥0∞) (e₁ e₂ : Evidence) : Prop :=
  Evidence.strengthWith ctx e₁ ≤ Evidence.strengthWith ctx e₂ ∧
  Evidence.toConfidence κ e₁ ≤ Evidence.toConfidence κ e₂

theorem supportConfidenceLE_refl
    (ctx : BinaryContext) (κ : ℝ≥0∞) (e : Evidence) :
    supportConfidenceLE ctx κ e e :=
  ⟨le_refl _, le_refl _⟩

theorem supportConfidenceLE_trans
    (ctx : BinaryContext) (κ : ℝ≥0∞)
    {e₁ e₂ e₃ : Evidence}
    (h₁₂ : supportConfidenceLE ctx κ e₁ e₂)
    (h₂₃ : supportConfidenceLE ctx κ e₂ e₃) :
    supportConfidenceLE ctx κ e₁ e₃ :=
  ⟨le_trans h₁₂.1 h₂₃.1, le_trans h₁₂.2 h₂₃.2⟩

end Mettapedia.Logic.GovernanceReasoning.ActualityPolicy
