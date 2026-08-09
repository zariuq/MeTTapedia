import Mettapedia.GSLT.LanguageDef.CertifiedMask
import Mettapedia.GSLT.LanguageDef.ProofGSLTUltrainfinite

/-!
# Search guidance under a semantic authority

This module connects the generic certified-pruning interface to the generic
semantic-authority interface.  It does not add a Gauthier-specific type
system, evaluator, or score.  A downstream language supplies only a map from
completed programs to claims.

Hard pruning is licensed against the authority's semantic `Meaning`, not
against a heuristic score and not merely against the certificates currently
found by one producer.  An accepted envelope entails that meaning and hence
its trace is retained.  Conversely, operational failure or universal
certificate rejection cannot manufacture accepted evidence.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT.SearchAuthority

open Mettapedia.GSLT.LanguageDef.CertifiedMask
open Mettapedia.GSLT.LanguageDef.RefinementInterface

universe uId uClaim uCertificate uProgram

/-- A program has authority-tagged evidence for the claim assigned to it. -/
def HasAcceptedEvidence
    {AuthorityId : Type uId} {Claim : Type uClaim}
    [DecidableEq AuthorityId]
    (authority : SemanticAuthority.{uId, uClaim, uCertificate}
      AuthorityId Claim)
    (claimOf : Program → Claim) (program : Program) : Prop :=
  ∃ envelope : EvidenceEnvelope AuthorityId authority.Certificate,
    authority.checkEnvelope (claimOf program) envelope = true

/-- Semantic success is the property against which hard pruning should be
certified.  It is independent of how evidence is searched for. -/
def HasAuthoritativeMeaning
    {AuthorityId : Type uId} {Claim : Type uClaim}
    (authority : SemanticAuthority.{uId, uClaim, uCertificate}
      AuthorityId Claim)
    (claimOf : Program → Claim) (program : Program) : Prop :=
  authority.Meaning (claimOf program)

/-- Positive evidence enters the semantic lane only through authority replay. -/
theorem acceptedEvidence_sound
    {AuthorityId : Type uId} {Claim : Type uClaim}
    [DecidableEq AuthorityId]
    (authority : SemanticAuthority.{uId, uClaim, uCertificate}
      AuthorityId Claim)
    (claimOf : Program → Claim) {program : Program}
    (accepted : HasAcceptedEvidence authority claimOf program) :
    HasAuthoritativeMeaning authority claimOf program := by
  rcases accepted with ⟨envelope, accepted⟩
  exact authority.envelope_sound accepted

/-- An explicitly accepted envelope supplies the positive search property. -/
theorem acceptedEnvelope_hasEvidence
    {AuthorityId : Type uId} {Claim : Type uClaim}
    [DecidableEq AuthorityId]
    (authority : SemanticAuthority.{uId, uClaim, uCertificate}
      AuthorityId Claim)
    (claimOf : Program → Claim) (program : Program)
    (envelope : EvidenceEnvelope AuthorityId authority.Certificate)
    (accepted : authority.checkEnvelope (claimOf program) envelope = true) :
    HasAcceptedEvidence authority claimOf program :=
  ⟨envelope, accepted⟩

/-- Negative boundary: if every envelope is rejected, accepted evidence does
not exist.  This says nothing about the truth of the claim unless authority
completeness is supplied separately. -/
theorem noAcceptedEvidence_of_all_rejected
    {AuthorityId : Type uId} {Claim : Type uClaim}
    [DecidableEq AuthorityId]
    (authority : SemanticAuthority.{uId, uClaim, uCertificate}
      AuthorityId Claim)
    (claimOf : Program → Claim) (program : Program)
    (rejected : ∀ envelope :
      EvidenceEnvelope AuthorityId authority.Certificate,
      authority.checkEnvelope (claimOf program) envelope = false) :
    ¬ HasAcceptedEvidence authority claimOf program := by
  rintro ⟨envelope, accepted⟩
  rw [rejected envelope] at accepted
  contradiction

/-- Completeness of an authority is an explicit, source-specific obligation;
it is not bundled into soundness. -/
def EvidenceComplete
    {AuthorityId : Type uId} {Claim : Type uClaim}
    (authority : SemanticAuthority.{uId, uClaim, uCertificate}
      AuthorityId Claim) : Prop :=
  ∀ claim, authority.Meaning claim →
    ∃ certificate, authority.check claim certificate = true

/-- Under the additional completeness obligation, certificate existence and
semantic meaning coincide. -/
theorem acceptedEvidence_iff_meaning_of_complete
    {AuthorityId : Type uId} {Claim : Type uClaim}
    [DecidableEq AuthorityId]
    (authority : SemanticAuthority.{uId, uClaim, uCertificate}
      AuthorityId Claim)
    (complete : EvidenceComplete authority)
    (claimOf : Program → Claim) (program : Program) :
    HasAcceptedEvidence authority claimOf program ↔
      HasAuthoritativeMeaning authority claimOf program := by
  constructor
  · exact acceptedEvidence_sound authority claimOf
  · intro meaningful
    obtain ⟨certificate, accepted⟩ := complete (claimOf program) meaningful
    refine ⟨⟨authority.id, certificate⟩, ?_⟩
    simp [SemanticAuthority.checkEnvelope, accepted]

/-- A mask certified against semantic meaning retains every trace whose
completed program carries accepted evidence.  Search scores and operational
status do not enter the statement. -/
theorem certifiedHardMask_preserves_acceptedEvidence_trace
    {root : RefinementInterface} {AuthorityId : Type uId}
    {Claim : Type uClaim} [DecidableEq AuthorityId]
    (authority : SemanticAuthority.{uId, uClaim, uCertificate}
      AuthorityId Claim)
    (claimOf : root.Program → Claim)
    {hardMask : SearchNode root → Prop}
    (certified : CertifiedHardMask
      (HasAuthoritativeMeaning authority claimOf) hardMask)
    {budget : Nat} {trace : List root.Action} {program : root.Program}
    (accepts : root.Accepts budget trace program)
    (evidence : HasAcceptedEvidence authority claimOf program) :
    EveryPrefixRetained hardMask budget trace :=
  certifiedHardMask_preserves_accepted_trace certified accepts
    (acceptedEvidence_sound authority claimOf evidence)

/-- The Boolean sufficient-test form of the same boundary: a node containing
an accepted-evidence completion cannot test as prunable. -/
theorem certifiedStateTest_preserves_acceptedEvidence_path
    {root : RefinementInterface} {AuthorityId : Type uId}
    {Claim : Type uClaim} [DecidableEq AuthorityId]
    (authority : SemanticAuthority.{uId, uClaim, uCertificate}
      AuthorityId Claim)
    (claimOf : root.Program → Claim)
    (stateTest : CertifiedStateTest
      (HasAuthoritativeMeaning authority claimOf))
    {node : SearchNode root} {program : root.Program}
    (completes : node.Completes program)
    (evidence : HasAcceptedEvidence authority claimOf program) :
    stateTest.test node = false :=
  certifiedStateTest_preserves_property_path stateTest completes
    (acceptedEvidence_sound authority claimOf evidence)

#print axioms acceptedEvidence_sound
#print axioms noAcceptedEvidence_of_all_rejected
#print axioms acceptedEvidence_iff_meaning_of_complete
#print axioms certifiedHardMask_preserves_acceptedEvidence_trace
#print axioms certifiedStateTest_preserves_acceptedEvidence_path

end Mettapedia.GSLT.LanguageDef.ProofGSLT.SearchAuthority
