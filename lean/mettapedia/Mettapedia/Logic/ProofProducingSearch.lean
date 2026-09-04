import Mettapedia.Logic.DisplayedAnytimeEvidence
import Mettapedia.GSLT.LanguageDef.CertificateGSLTUltrainfinite

/-!
# Proof-producing search over an independent semantic authority

A theorem prover, model finder, program synthesizer, proof planner, or
inductive learner may all enumerate candidate artifacts.  Enumeration is not
semantic authority.  This file isolates their common interface:

* a producer emits a finite batch of claim/certificate pairs at every finite
  stage;
* batches accumulate without erasing duplicate occurrences or their origins;
* acceptance is determined only by an independently sound authority;
* accepted artifacts form proof-relevant monotone evidence for the authority's
  meaning;
* eventual completeness is an additional coverage theorem, never a consequence
  of finiteness, fairness, or continued execution alone.

The stage index is only an observation horizon.  The complete run may be
unbounded, and absence from any finite prefix does not establish negation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ProofProducingSearch

open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Logic.DisplayedAnytimeEvidence

universe uId uClaim uCertificate uOrigin

/-- One untrusted proposal.  `origin` can retain a strategy name, occurrence
identifier, learned-hypothesis route, or other provenance.  It is deliberately
not inspected by the semantic checker. -/
structure Proposal
    {AuthorityId : Type uId} {Claim : Type uClaim}
    (authority : SemanticAuthority.{uId, uClaim, uCertificate}
      AuthorityId Claim)
    (Origin : Type uOrigin) where
  claim : Claim
  certificate : authority.Certificate
  origin : Origin

/-- A producer supplies a finite delta at each natural-number stage.  No
termination or global finiteness claim is built into this interface. -/
structure StagedProducer
    {AuthorityId : Type uId} {Claim : Type uClaim}
    (authority : SemanticAuthority.{uId, uClaim, uCertificate}
      AuthorityId Claim)
    (Origin : Type uOrigin) where
  batch : Nat → List (Proposal authority Origin)

namespace StagedProducer

variable {AuthorityId : Type uId} {Claim : Type uClaim}
variable {authority : SemanticAuthority.{uId, uClaim, uCertificate}
  AuthorityId Claim}
variable {Origin : Type uOrigin}

/-- All proposal occurrences observed through a finite stage.  Appending the
new batch preserves chronology, multiplicity, certificates, and origins. -/
def through (producer : StagedProducer authority Origin) :
    Nat → List (Proposal authority Origin)
  | 0 => producer.batch 0
  | stage + 1 => producer.through stage ++ producer.batch (stage + 1)

@[simp] theorem through_zero (producer : StagedProducer authority Origin) :
    producer.through 0 = producer.batch 0 :=
  rfl

@[simp] theorem through_succ (producer : StagedProducer authority Origin)
    (stage : Nat) :
    producer.through (stage + 1) =
      producer.through stage ++ producer.batch (stage + 1) :=
  rfl

/-- Every earlier proposal occurrence remains present at the next stage. -/
theorem mem_through_succ
    (producer : StagedProducer authority Origin)
    {stage : Nat} {proposal : Proposal authority Origin}
    (member : proposal ∈ producer.through stage) :
    proposal ∈ producer.through (stage + 1) := by
  exact List.mem_append_left _ member

/-- Finite observations form a monotone chain. -/
theorem mem_through_mono
    (producer : StagedProducer authority Origin)
    {earlier later : Nat} (bounded : earlier ≤ later)
    {proposal : Proposal authority Origin}
    (member : proposal ∈ producer.through earlier) :
    proposal ∈ producer.through later := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le bounded
  clear bounded
  induction extra with
  | zero => simpa
  | succ extra inductionHypothesis =>
      rw [Nat.add_succ]
      exact producer.mem_through_succ inductionHypothesis

/-- An accepted occurrence retains the exact proposal, its position in the
observed prefix, and independent replay at the semantic authority. -/
structure AcceptedAt (producer : StagedProducer authority Origin)
    (stage : Nat) where
  proposal : Proposal authority Origin
  offered : proposal ∈ producer.through stage
  replay : authority.check proposal.claim proposal.certificate = true

namespace AcceptedAt

/-- Every accepted occurrence has the meaning assigned by the independent
authority, irrespective of its origin or production strategy. -/
theorem sound
    {producer : StagedProducer authority Origin} {stage : Nat}
    (accepted : producer.AcceptedAt stage) :
    authority.Meaning accepted.proposal.claim :=
  authority.sound accepted.replay

/-- Retain the same accepted occurrence at every larger observation horizon. -/
def persist
    {producer : StagedProducer authority Origin}
    {earlier later : Nat} (bounded : earlier ≤ later)
    (accepted : producer.AcceptedAt earlier) :
    producer.AcceptedAt later where
  proposal := accepted.proposal
  offered := producer.mem_through_mono bounded accepted.offered
  replay := accepted.replay

end AcceptedAt

/-- Proof-relevant evidence that a fixed query claim has been accepted by a
finite stage.  The equality is retained because one producer may enumerate
certificates for many claims. -/
structure EvidenceFor (producer : StagedProducer authority Origin)
    (claim : Claim) (stage : Nat) where
  accepted : producer.AcceptedAt stage
  targets : accepted.proposal.claim = claim

namespace EvidenceFor

/-- Fixed-claim evidence persists while retaining the original certificate,
origin, and occurrence. -/
def persist
    {producer : StagedProducer authority Origin} {claim : Claim}
    {earlier later : Nat} (bounded : earlier ≤ later)
    (evidence : producer.EvidenceFor claim earlier) :
    producer.EvidenceFor claim later where
  accepted := evidence.accepted.persist bounded
  targets := evidence.targets

/-- Replay of a fixed-claim evidence value entails that query's meaning. -/
theorem sound
    {producer : StagedProducer authority Origin} {claim : Claim}
    {stage : Nat} (evidence : producer.EvidenceFor claim stage) :
    authority.Meaning claim := by
  rw [← evidence.targets]
  exact evidence.accepted.sound

end EvidenceFor

/-- A staged producer induces displayed monotone evidence for every fixed
claim.  The thin observer says only that some accepted artifact has appeared;
the displayed fibre retains which one and where it came from. -/
def evidence
    (producer : StagedProducer authority Origin) (claim : Claim) :
    MonotoneEvidence (authority.Meaning claim) where
  EvidenceAt stage := producer.EvidenceFor claim stage
  persist bounded witness := witness.persist bounded
  sound witness := witness.sound

/-- A claim lies in the positive limit of a run when an accepted certificate
for it appears at some finite stage. -/
def EventuallyAccepts
    (producer : StagedProducer authority Origin) (claim : Claim) : Prop :=
  ∃ stage, Nonempty (producer.EvidenceFor claim stage)

theorem eventuallyAccepts_iff_certificate
    (producer : StagedProducer authority Origin) (claim : Claim) :
    producer.EventuallyAccepts claim ↔
      ∃ stage, (producer.evidence claim).toCertificate.acceptsAt stage :=
  by
    rfl

/-- Positive completeness is precisely coverage of every meaningful query by
some independently accepted finite proposal. -/
def CoversMeaning (producer : StagedProducer authority Origin) : Prop :=
  ∀ claim, authority.Meaning claim → producer.EventuallyAccepts claim

theorem coversMeaning_iff_eventuallyComplete
    (producer : StagedProducer authority Origin) :
    producer.CoversMeaning ↔
      ∀ claim, (producer.evidence claim).EventuallyComplete := by
  constructor
  · intro covers claim meaningful
    exact covers claim meaningful
  · intro complete claim meaningful
    exact complete claim meaningful

/-- Every limit acceptance is sound.  The theorem gives only the positive
direction; it cannot turn a missing finite artifact into refutation. -/
theorem EventuallyAccepts.sound
    {producer : StagedProducer authority Origin} {claim : Claim}
    (accepted : producer.EventuallyAccepts claim) :
    authority.Meaning claim := by
  obtain ⟨stage, ⟨evidence⟩⟩ := accepted
  exact evidence.sound

end StagedProducer

/-! ## Canaries: production, acceptance, and proof identity do not collapse -/

namespace Canary

inductive DemoClaim where
  | lampLit
deriving Repr, DecidableEq

inductive DemoCertificate where
  | honest
  | forged
deriving Repr, DecidableEq

inductive DemoOrigin where
  | forward
  | backward
  | guess
deriving Repr, DecidableEq

/-- The meaning is independently true; only the honest certificate is
accepted. -/
def demoAuthority : SemanticAuthority Unit DemoClaim where
  id := ()
  Certificate := DemoCertificate
  check _ certificate := certificate == .honest
  Meaning _ := True
  sound := by
    intro claim certificate accepted
    exact True.intro

def forwardProposal : Proposal demoAuthority DemoOrigin :=
  ⟨.lampLit, .honest, .forward⟩

def backwardProposal : Proposal demoAuthority DemoOrigin :=
  ⟨.lampLit, .honest, .backward⟩

def forgedProposal : Proposal demoAuthority DemoOrigin :=
  ⟨.lampLit, .forged, .guess⟩

/-- A deliberately mixed producer offers a forged candidate first and two
distinct honest routes later. -/
def demoProducer : StagedProducer demoAuthority DemoOrigin where
  batch
    | 0 => [forgedProposal]
    | 1 => [forwardProposal, backwardProposal]
    | _ => []

theorem forged_is_offered_but_not_accepted :
    forgedProposal ∈ demoProducer.through 0 ∧
      demoAuthority.check forgedProposal.claim
        forgedProposal.certificate = false := by
  constructor
  · simp [demoProducer, StagedProducer.through, forgedProposal]
  · rfl

theorem two_origins_remain_distinct :
    forwardProposal ≠ backwardProposal := by
  intro equal
  have originEqual := congrArg (Proposal.origin) equal
  cases originEqual

def forwardAccepted : demoProducer.AcceptedAt 1 where
  proposal := forwardProposal
  offered := by simp [demoProducer, StagedProducer.through, forwardProposal]
  replay := by decide

def backwardAccepted : demoProducer.AcceptedAt 1 where
  proposal := backwardProposal
  offered := by simp [demoProducer, StagedProducer.through, backwardProposal]
  replay := by decide

/-- The same semantic claim has two distinguishable accepted route
occurrences.  The authority is proposition-valued, but the evidence fibre is
not thin. -/
theorem accepted_fibre_retains_parallel_origins :
    forwardAccepted.proposal.claim = backwardAccepted.proposal.claim ∧
      forwardAccepted.proposal ≠ backwardAccepted.proposal := by
  exact ⟨rfl, two_origins_remain_distinct⟩

/-- A meaningful claim can be absent at a finite stage.  The forged proposal
does not become evidence merely because the producer emitted it. -/
theorem finite_absence_is_not_refutation :
    demoAuthority.Meaning .lampLit ∧
      ¬ Nonempty (demoProducer.EvidenceFor .lampLit 0) := by
  constructor
  · trivial
  · rintro ⟨evidence⟩
    have replay := evidence.accepted.replay
    have onlyForged : evidence.accepted.proposal = forgedProposal := by
      simpa [demoProducer, StagedProducer.through] using
        evidence.accepted.offered
    rw [onlyForged] at replay
    simp [demoAuthority, forgedProposal] at replay

/-- At the next stage, honest replay supplies positive evidence. -/
theorem honest_eventually_accepted :
    demoProducer.EventuallyAccepts .lampLit := by
  refine ⟨1, ⟨?_⟩⟩
  exact
    { accepted := forwardAccepted
      targets := rfl }

end Canary

/-! ## Audited theorem crowns -/

#print axioms StagedProducer.mem_through_mono
#print axioms StagedProducer.AcceptedAt.sound
#print axioms StagedProducer.EventuallyAccepts.sound
#print axioms StagedProducer.coversMeaning_iff_eventuallyComplete
#print axioms Canary.forged_is_offered_but_not_accepted
#print axioms Canary.accepted_fibre_retains_parallel_origins
#print axioms Canary.finite_absence_is_not_refutation
#print axioms Canary.honest_eventually_accepted

end Mettapedia.Logic.ProofProducingSearch
