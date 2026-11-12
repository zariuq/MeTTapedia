import Mettapedia.Protocols.Agents.InputSettlement

/-!
# Evidence-first handoffs

A handoff carries work across a context boundary. A narrative can say "already
reviewed" about something that has changed since, and the resuming step has no
way to tell. This module states when a handoff can be resumed from without
re-inspecting everything and without trusting anything stale.

A claim is a property of one source's content, recorded with the version it was
established at: a content digest, a commit, a record revision. At resume the
substrate reads the current versions, which is cheap and is not re-inspection,
and sorts the claims. A claim whose source still has the recorded version is
fresh; any other claim is stale and is inspected again.

Proved here:

* Sufficiency. Every fresh claim holds now (`fresh_claim_holds`), and a claim is
  stale exactly when its source changed (`stale_iff_changed`). Resume splits the
  claims into trusted and stale (`resume_partition`, `resume_stale_iff`), and
  every trusted claim holds (`resume_trusted_hold`).
* Necessity. A claim that names what was reviewed but not which version cannot
  be resumed both soundly and completely by any rule that reads only current
  versions. Two consistent histories present the rule with the same narrative and
  the same current versions; the claim holds in one and not in the other
  (`narrative_unsound_or_incomplete`). The recorded version separates exactly
  these histories (`version_separates`).
* Novel input is not the handoff's to state. Resume shows the store's pending
  deliveries, the same for every handoff (`resume_pending_independent`). A fresh
  delivery is therefore shown however the handoff was written
  (`fresh_delivery_survives_handoff`).

The handoff's other fields, the active request, the next physical action and the
unresolved checks, are carried and not judged. Workflow state is read from the
ledger at resume, not from the handoff. A call identifier pins an observation,
not the current state of what was observed: provenance names the observed source
and its version. Versions are assumed to name contents, as digests and commits
do; the model does not cover a source whose content changes under one version.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.EvidenceHandoff

open Mettapedia.Protocols.Mail
open Mettapedia.Protocols.Agents.InputSettlement (fresh_delivery_wakes)

variable {Source Version Content : Type}

/-- What each version of each source denotes. -/
abbrev Denotation (Source Version Content : Type) := Source → Version → Content

/-- A claim with its provenance: a property of one source's content, and the version
it was established at. -/
structure Claim (Source Version Content : Type) where
  source : Source
  version : Version
  property : Content → Prop

namespace Claim

/-- The claim was true of the version it records. -/
def Established (den : Denotation Source Version Content) (c : Claim Source Version Content) :
    Prop :=
  c.property (den c.source c.version)

/-- The claim is true of the source's current version. -/
def Holds (den : Denotation Source Version Content) (now : Source → Version)
    (c : Claim Source Version Content) : Prop :=
  c.property (den c.source (now c.source))

/-- The source still has the recorded version. Only versions are read. -/
def fresh [DecidableEq Version] (now : Source → Version) (c : Claim Source Version Content) :
    Bool :=
  decide (now c.source = c.version)

end Claim

variable [DecidableEq Version]

theorem fresh_claim_holds {den : Denotation Source Version Content} {now : Source → Version}
    {c : Claim Source Version Content} (est : c.Established den) (h : c.fresh now = true) :
    c.Holds den now := by
  have hv : now c.source = c.version := by simpa [Claim.fresh] using h
  show c.property (den c.source (now c.source))
  rw [hv]
  exact est

theorem stale_iff_changed {now : Source → Version} {c : Claim Source Version Content} :
    c.fresh now = false ↔ now c.source ≠ c.version := by
  simp [Claim.fresh]

/-- What a step leaves for the next one. Pending input and workflow state are not fields:
they are read from the stores at resume. -/
structure Handoff (Request Action Check Source Version Content : Type) where
  /-- The request the next step serves, by its ledger identity. -/
  request : Option Request
  /-- The next physical action. -/
  next : Action
  /-- Checks still owed. -/
  checks : List Check
  /-- Every claim, with its provenance. -/
  claims : List (Claim Source Version Content)

/-- What the resuming step is shown. -/
structure Resumed (Source Version Content : Type) where
  trusted : List (Claim Source Version Content)
  stale : List (Claim Source Version Content)
  pending : List Message

variable {Request Action Check : Type}

def resume (h : Handoff Request Action Check Source Version Content) (now : Source → Version)
    (b : Mailbox) : Resumed Source Version Content :=
  ⟨h.claims.filter (·.fresh now), h.claims.filter (fun c => !c.fresh now), b.unread⟩

theorem resume_partition (h : Handoff Request Action Check Source Version Content)
    (now : Source → Version) (b : Mailbox) :
    (resume h now b).trusted.length + (resume h now b).stale.length = h.claims.length :=
  (List.length_eq_length_filter_add _).symm

theorem resume_stale_iff (h : Handoff Request Action Check Source Version Content)
    (now : Source → Version) (b : Mailbox) (c : Claim Source Version Content) :
    c ∈ (resume h now b).stale ↔ c ∈ h.claims ∧ now c.source ≠ c.version := by
  simp [resume, Claim.fresh]

/-- Resume trusts only claims that hold: with every claim established at its recorded
version, each trusted claim is true of the current sources. -/
theorem resume_trusted_hold {den : Denotation Source Version Content}
    (h : Handoff Request Action Check Source Version Content) (now : Source → Version)
    (b : Mailbox) (est : ∀ c ∈ h.claims, c.Established den) :
    ∀ c ∈ (resume h now b).trusted, c.Holds den now := by
  intro c hc
  simp only [resume, List.mem_filter] at hc
  exact fresh_claim_holds (est c hc.1) hc.2

/-- Necessity of the recorded version. A rule shown only the narrative claim (the source and
the property) and the current versions answers the same in two consistent histories: in one
the reviewed version was replaced by a bad one, in the other the current version is the one
reviewed. Trusting is unsound in the first; not trusting is incomplete in the second. -/
theorem narrative_unsound_or_incomplete
    (trust : Source → (Bool → Prop) → (Source → Version) → Bool) (s : Source)
    {v₁ v₂ : Version} (hne : v₁ ≠ v₂) :
    let now : Source → Version := fun _ => v₂
    let good : Bool → Prop := fun x => x = true
    let reviewedOld : Claim Source Version Bool := ⟨s, v₁, good⟩
    let reviewedNew : Claim Source Version Bool := ⟨s, v₂, good⟩
    let denOld : Denotation Source Version Bool := fun _ v => decide (v = v₁)
    let denNew : Denotation Source Version Bool := fun _ v => decide (v = v₂)
    reviewedOld.Established denOld ∧ reviewedNew.Established denNew ∧
      ((trust s good now = true ∧ ¬ reviewedOld.Holds denOld now) ∨
        (trust s good now = false ∧ reviewedNew.Holds denNew now)) := by
  intro now good reviewedOld reviewedNew denOld denNew
  refine ⟨by simp [Claim.Established, reviewedOld, denOld, good],
    by simp [Claim.Established, reviewedNew, denNew, good], ?_⟩
  cases ht : trust s good now
  · exact Or.inr ⟨rfl, by simp [Claim.Holds, reviewedNew, denNew, now, good]⟩
  · exact Or.inl ⟨rfl, by simp [Claim.Holds, reviewedOld, denOld, now, good, Ne.symm hne]⟩

/-- The recorded version separates the two histories: the replaced review is stale and the
current one is fresh. -/
theorem version_separates (s : Source) {v₁ v₂ : Version} (hne : v₁ ≠ v₂)
    (good : Bool → Prop) :
    let now : Source → Version := fun _ => v₂
    (⟨s, v₁, good⟩ : Claim Source Version Bool).fresh now = false ∧
      (⟨s, v₂, good⟩ : Claim Source Version Bool).fresh now = true := by
  intro now
  simp [Claim.fresh, now, Ne.symm hne]

/-- The pending deliveries shown at resume do not depend on the handoff. -/
theorem resume_pending_independent (h₁ h₂ : Handoff Request Action Check Source Version Content)
    (now : Source → Version) (b : Mailbox) :
    (resume h₁ now b).pending = (resume h₂ now b).pending :=
  rfl

/-- A delivery with a fresh identity is shown at resume, whatever the handoff says. -/
theorem fresh_delivery_survives_handoff {b : Mailbox} (hb : b.Valid) {m : Message}
    (fresh : m.id ∉ b.ids) (h : Handoff Request Action Check Source Version Content)
    (now : Source → Version) :
    m ∈ (resume h now (b.deliver m)).pending :=
  (fresh_delivery_wakes hb fresh).1

end Mettapedia.Protocols.Agents.EvidenceHandoff
