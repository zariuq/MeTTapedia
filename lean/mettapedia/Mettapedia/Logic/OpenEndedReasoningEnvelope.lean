import Mettapedia.Logic.HOL.HigherOrderAlgorithmProfiles
import Mettapedia.TypeTheory.InfinitaryProofAndObservationBoundary

/-!
# Open-ended reasoning with finite accelerators

A practical reasoner should be allowed to use bounded search, heuristics,
learned guidance, portfolios, and native code without making any of them the
definition of truth.  This module gives that policy a small theorem-level
interface.

A staged producer is a finite accelerator at every observation horizon.  Its
accepted outputs are sound immediately because acceptance belongs to an
independent semantic authority.  Coverage is optional and separately stated;
therefore a finite miss is never promoted to refutation.  Two producers can be
combined while retaining the origin of every proposal, and a complete producer
can be replaced by another complete producer without changing limit meaning.

The final section connects this interface to genuinely infinitary rules.  An
indexed derivation may have countably many immediate premises and hence need
not occur at any finite stage of a directed rule approximation.  The same
authority shape can state its meaning, but the reference certificate there is
not claimed to be a finite wire object.  A native implementation must instead
earn a finite global certificate, a productivity argument, or an explicit
residual outcome.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.OpenEndedReasoningEnvelope

open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Logic.ProofProducingSearch
open Mettapedia.TypeTheory.InfinitaryProofAndObservationBoundary

universe uId uClaim uCertificate uLeftOrigin uRightOrigin

/-! ## Origin-preserving portfolios -/

namespace Proposal

variable {AuthorityId : Type uId} {Claim : Type uClaim}
variable {authority : SemanticAuthority.{uId, uClaim, uCertificate}
  AuthorityId Claim}

/-- Change only the provenance vocabulary of a proposal.  Its claim and
certificate remain byte-for-byte the same logical payload. -/
def mapOrigin {Origin : Type uLeftOrigin} {TargetOrigin : Type uRightOrigin}
    (map : Origin → TargetOrigin) (proposal : Proposal authority Origin) :
    Proposal authority TargetOrigin where
  claim := proposal.claim
  certificate := proposal.certificate
  origin := map proposal.origin

@[simp] theorem mapOrigin_claim
    {Origin : Type uLeftOrigin} {TargetOrigin : Type uRightOrigin}
    (map : Origin → TargetOrigin) (proposal : Proposal authority Origin) :
    (mapOrigin map proposal).claim = proposal.claim :=
  rfl

@[simp] theorem mapOrigin_certificate
    {Origin : Type uLeftOrigin} {TargetOrigin : Type uRightOrigin}
    (map : Origin → TargetOrigin) (proposal : Proposal authority Origin) :
    (mapOrigin map proposal).certificate = proposal.certificate :=
  rfl

end Proposal

namespace StagedProducer

variable {AuthorityId : Type uId} {Claim : Type uClaim}
variable {authority : SemanticAuthority.{uId, uClaim, uCertificate}
  AuthorityId Claim}
variable {LeftOrigin : Type uLeftOrigin} {RightOrigin : Type uRightOrigin}

/-- Run two finite candidate generators at every stage.  `Sum` records which
generator produced each occurrence; duplicates are deliberately retained. -/
def portfolio (left : StagedProducer authority LeftOrigin)
    (right : StagedProducer authority RightOrigin) :
    StagedProducer authority (Sum LeftOrigin RightOrigin) where
  batch stage :=
    (left.batch stage).map (Proposal.mapOrigin Sum.inl) ++
      (right.batch stage).map (Proposal.mapOrigin Sum.inr)

/-- Every left-hand proposal occurrence embeds into the portfolio at the same
observation horizon. -/
theorem mem_portfolio_of_left
    (left : StagedProducer authority LeftOrigin)
    (right : StagedProducer authority RightOrigin)
    {stage : Nat} {proposal : Proposal authority LeftOrigin}
    (member : proposal ∈ left.through stage) :
    Proposal.mapOrigin Sum.inl proposal ∈
      (portfolio left right).through stage := by
  induction stage with
  | zero =>
      exact List.mem_append_left _ (List.mem_map.mpr ⟨proposal, member, rfl⟩)
  | succ stage inductionHypothesis =>
      rw [Mettapedia.Logic.ProofProducingSearch.StagedProducer.through_succ]
        at member
      rw [Mettapedia.Logic.ProofProducingSearch.StagedProducer.through_succ]
      rcases List.mem_append.mp member with old | fresh
      · exact List.mem_append_left _ (inductionHypothesis old)
      · apply List.mem_append_right
        exact List.mem_append_left _
          (List.mem_map.mpr ⟨proposal, fresh, rfl⟩)

/-- Every right-hand proposal occurrence embeds into the portfolio at the same
observation horizon. -/
theorem mem_portfolio_of_right
    (left : StagedProducer authority LeftOrigin)
    (right : StagedProducer authority RightOrigin)
    {stage : Nat} {proposal : Proposal authority RightOrigin}
    (member : proposal ∈ right.through stage) :
    Proposal.mapOrigin Sum.inr proposal ∈
      (portfolio left right).through stage := by
  induction stage with
  | zero =>
      exact List.mem_append_right _
        (List.mem_map.mpr ⟨proposal, member, rfl⟩)
  | succ stage inductionHypothesis =>
      rw [Mettapedia.Logic.ProofProducingSearch.StagedProducer.through_succ]
        at member
      rw [Mettapedia.Logic.ProofProducingSearch.StagedProducer.through_succ]
      rcases List.mem_append.mp member with old | fresh
      · exact List.mem_append_left _ (inductionHypothesis old)
      · apply List.mem_append_right
        exact List.mem_append_right _
          (List.mem_map.mpr ⟨proposal, fresh, rfl⟩)

/-- Lift an exact accepted occurrence from the left producer. -/
def liftAcceptedLeft
    {left : StagedProducer authority LeftOrigin}
    {right : StagedProducer authority RightOrigin}
    {stage : Nat} (accepted : left.AcceptedAt stage) :
    (portfolio left right).AcceptedAt stage where
  proposal := Proposal.mapOrigin Sum.inl accepted.proposal
  offered := mem_portfolio_of_left left right accepted.offered
  replay := accepted.replay

/-- Lift an exact accepted occurrence from the right producer. -/
def liftAcceptedRight
    {left : StagedProducer authority LeftOrigin}
    {right : StagedProducer authority RightOrigin}
    {stage : Nat} (accepted : right.AcceptedAt stage) :
    (portfolio left right).AcceptedAt stage where
  proposal := Proposal.mapOrigin Sum.inr accepted.proposal
  offered := mem_portfolio_of_right left right accepted.offered
  replay := accepted.replay

/-- Fixed-claim evidence from the left producer embeds without changing its
certificate or target claim. -/
def liftEvidenceLeft
    {left : StagedProducer authority LeftOrigin}
    {right : StagedProducer authority RightOrigin}
    {claim : Claim} {stage : Nat} (evidence : left.EvidenceFor claim stage) :
    (portfolio left right).EvidenceFor claim stage where
  accepted := liftAcceptedLeft evidence.accepted
  targets := by
    change evidence.accepted.proposal.claim = claim
    exact evidence.targets

/-- Fixed-claim evidence from the right producer embeds without changing its
certificate or target claim. -/
def liftEvidenceRight
    {left : StagedProducer authority LeftOrigin}
    {right : StagedProducer authority RightOrigin}
    {claim : Claim} {stage : Nat} (evidence : right.EvidenceFor claim stage) :
    (portfolio left right).EvidenceFor claim stage where
  accepted := liftAcceptedRight evidence.accepted
  targets := by
    change evidence.accepted.proposal.claim = claim
    exact evidence.targets

theorem eventuallyAccepts_portfolio_of_left
    (left : StagedProducer authority LeftOrigin)
    (right : StagedProducer authority RightOrigin) {claim : Claim}
    (accepted : left.EventuallyAccepts claim) :
    (portfolio left right).EventuallyAccepts claim := by
  obtain ⟨stage, ⟨evidence⟩⟩ := accepted
  exact ⟨stage, ⟨liftEvidenceLeft evidence⟩⟩

theorem eventuallyAccepts_portfolio_of_right
    (left : StagedProducer authority LeftOrigin)
    (right : StagedProducer authority RightOrigin) {claim : Claim}
    (accepted : right.EventuallyAccepts claim) :
    (portfolio left right).EventuallyAccepts claim := by
  obtain ⟨stage, ⟨evidence⟩⟩ := accepted
  exact ⟨stage, ⟨liftEvidenceRight evidence⟩⟩

/-- One complete member makes the whole portfolio complete; the other member
may remain heuristic or deliberately incomplete. -/
theorem portfolio_coversMeaning_of_left
    (left : StagedProducer authority LeftOrigin)
    (right : StagedProducer authority RightOrigin)
    (covers : left.CoversMeaning) :
    (portfolio left right).CoversMeaning := by
  intro claim meaningful
  exact eventuallyAccepts_portfolio_of_left left right
    (covers claim meaningful)

theorem portfolio_coversMeaning_of_right
    (left : StagedProducer authority LeftOrigin)
    (right : StagedProducer authority RightOrigin)
    (covers : right.CoversMeaning) :
    (portfolio left right).CoversMeaning := by
  intro claim meaningful
  exact eventuallyAccepts_portfolio_of_right left right
    (covers claim meaningful)

/-- Two positively complete accelerators over the same authority agree at the
limit even when their schedules, heuristics, and proof origins differ. -/
theorem complete_accelerators_agree
    (left : StagedProducer authority LeftOrigin)
    (right : StagedProducer authority RightOrigin)
    (leftCovers : left.CoversMeaning) (rightCovers : right.CoversMeaning)
    (claim : Claim) :
    left.EventuallyAccepts claim ↔ right.EventuallyAccepts claim := by
  constructor
  · intro accepted
    exact rightCovers claim accepted.sound
  · intro accepted
    exact leftCovers claim accepted.sound

end StagedProducer

/-! ## Finite observation is acceleration, not a semantic guard -/

namespace FiniteCanary

open Mettapedia.Logic.ProofProducingSearch.Canary

/-- The same true claim is absent from the first finite observation and
accepted later.  No completeness assumption is used for soundness. -/
theorem finite_miss_then_later_success :
    demoAuthority.Meaning .lampLit ∧
      ¬ Nonempty (demoProducer.EvidenceFor .lampLit 0) ∧
      demoProducer.EventuallyAccepts .lampLit :=
  ⟨finite_absence_is_not_refutation.1,
    finite_absence_is_not_refutation.2,
    honest_eventually_accepted⟩

end FiniteCanary

/-! ## A semantic authority for indexed derivations -/

universe uJudgment uPremise

/-- A reference proof object for an indexed rule system.  When the premise
index is infinite, this value is semantic evidence rather than a claim of
finite serializability. -/
structure IndexedDerivationCertificate
    {Judgment : Type uJudgment}
    (rules : PremiseFamily.{uJudgment, uPremise} Judgment →
      Judgment → Prop) where
  conclusion : Judgment
  derivation : IndexedDerives rules conclusion

/-- Indexed derivability packaged behind the same independent-checker shape as
finitary proof search. -/
def indexedDerivationAuthority
    {Judgment : Type uJudgment} [DecidableEq Judgment]
    (rules : PremiseFamily.{uJudgment, uPremise} Judgment →
      Judgment → Prop) :
    SemanticAuthority Unit Judgment where
  id := ()
  Certificate := IndexedDerivationCertificate rules
  check claim certificate := decide (certificate.conclusion = claim)
  Meaning claim := IndexedDerives rules claim
  sound := by
    intro claim certificate accepted
    have equal : certificate.conclusion = claim := by
      simpa using accepted
    subst claim
    exact certificate.derivation

namespace InfinitaryCanary

open OmegaCanary

def omegaCertificate :
    IndexedDerivationCertificate (UnionIndexedRules StageRules) where
  conclusion := none
  derivation := unionDerivesGoal

theorem omegaCertificate_accepted :
    (indexedDerivationAuthority (UnionIndexedRules StageRules)).check
      none omegaCertificate = true := by
  rfl

/-- The limit judgment has sound indexed evidence while every finite rule
stage misses it.  This is the exact point where an infinitary profile needs
global evidence or a residual result rather than a fabricated finite proof. -/
theorem limit_meaning_without_finite_stage :
    (indexedDerivationAuthority
        (UnionIndexedRules StageRules)).Meaning none ∧
      ∀ stage, ¬ IndexedDerives (StageRules stage) none :=
  ⟨(indexedDerivationAuthority
      (UnionIndexedRules StageRules)).sound omegaCertificate_accepted,
    stage_does_not_derive_goal⟩

end InfinitaryCanary

/-! ## Audited theorem crowns -/

#print axioms StagedProducer.mem_portfolio_of_left
#print axioms StagedProducer.mem_portfolio_of_right
#print axioms StagedProducer.eventuallyAccepts_portfolio_of_left
#print axioms StagedProducer.eventuallyAccepts_portfolio_of_right
#print axioms StagedProducer.portfolio_coversMeaning_of_left
#print axioms StagedProducer.portfolio_coversMeaning_of_right
#print axioms StagedProducer.complete_accelerators_agree
#print axioms FiniteCanary.finite_miss_then_later_success
#print axioms indexedDerivationAuthority
#print axioms InfinitaryCanary.omegaCertificate_accepted
#print axioms InfinitaryCanary.limit_meaning_without_finite_stage

end Mettapedia.Logic.OpenEndedReasoningEnvelope
