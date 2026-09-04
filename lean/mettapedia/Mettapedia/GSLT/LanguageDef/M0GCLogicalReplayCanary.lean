import Mettapedia.GSLT.LanguageDef.InferenceCompiledPlanLowering
import Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay

/-!
# Discriminating examples for M0GC logical replay

The fixture uses a real validated source calculus with one binary rule.  Its
M0GC certificate contains three ground-term nodes and one explicit rule
application.  The positive example crosses the complete encode/decode,
materialization, and ordinary CertificateGSLT replay boundary.  Negative
examples independently exercise claim pinning, rule fingerprints, profile
identity, term chronology and arity, explicit conclusions, and proof
chronology.
-/

namespace Mettapedia.GSLT.LanguageDef.M0GCLogicalReplayCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.InferenceCompiledPlanLowering
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay

def definition : ValidatedCalculusLanguageDef :=
  ⟨binaryDefinition, binaryDefinition_valid⟩

def profileDigest : List UInt8 := List.replicate digestWidth 17

def sourceDigest : List UInt8 := List.replicate digestWidth 29

def ruleFingerprint : UInt64 := 917431

def pairRuleProfile : RuleProfile :=
  { ruleId := ⟨"pair"⟩
    argumentCount := 2
    premiseCount := 0
    fingerprint := ruleFingerprint }

def profile : RuntimeProfile :=
  { profileDigest
    sourceDigest
    symbols :=
      #[ { name := "left", arity := 0 }
       , { name := "right", arity := 0 }
       , { name := "pair", arity := 2 } ]
    rules := #[pairRuleProfile] }

def left : Pattern := .apply "left" []

def right : Pattern := .apply "right" []

def pair : Pattern := .apply "pair" [left, right]

def leftHash : UInt64 := structuralTermHash 0 0 []

def rightHash : UInt64 := structuralTermHash 1 0 []

def pairHash : UInt64 := structuralTermHash 2 2 [leftHash, rightHash]

def leftNode : TermNode :=
  { symbol := 0
    arity := 0
    childStart := 0
    reserved := 0
    termHash := leftHash }

def rightNode : TermNode :=
  { symbol := 1
    arity := 0
    childStart := 0
    reserved := 0
    termHash := rightHash }

def pairNode : TermNode :=
  { symbol := 2
    arity := 2
    childStart := 0
    reserved := 0
    termHash := pairHash }

def proofNode : ProofNode :=
  { opcode := applyOpcode
    rule := 0
    argumentCount := 2
    premiseCount := 0
    argumentStart := 0
    premiseStart := 0
    resultTerm := 2
    reserved := 0
    ruleFingerprint }

def certificate : Certificate :=
  { flags := 0
    terms := [leftNode, rightNode, pairNode]
    children := [0, 1]
    proofs := [proofNode]
    arguments := [0, 1]
    premises := []
    goalTerm := 2
    profileDigest
    sourceDigest }

def article : WireArticle :=
  { version := wireArticleVersion
    nodes :=
      [{ id := 0
         ruleInstance := { ruleId := ⟨"pair"⟩, arguments := [left, right] }
         children := [] }]
    rootId := 0
    target := pair }

@[simp] theorem pair_instantiates :
    instantiateRule? definition
        { ruleId := ⟨"pair"⟩, arguments := [left, right] } =
      some ([], pair) := by
  simp [instantiateRule?, definition, binaryDefinition, binaryRule,
    CalculusLanguageDef.extend, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, argumentValidAt, RuleSchema.sideConditionsHold,
    lookupArgumentAt?, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, left, right, pair]

@[simp] theorem concrete_pair_instantiates :
    instantiateRule? definition
        { ruleId := ⟨"pair"⟩
          arguments :=
            [.apply "left" [], .apply "right" []] } =
      some
        ([], .apply "pair" [.apply "left" [], .apply "right" []]) := by
  simpa [left, right, pair] using pair_instantiates

theorem certificate_encodable : certificate.Encodable := by
  simp [Certificate.Encodable, certificate, profileDigest, sourceDigest,
    digestWidth]
  decide

def termState : TermState :=
  { patterns := #[left, right, pair]
    hashes := #[leftHash, rightHash, pairHash] }

def leftState : TermState :=
  { patterns := #[left]
    hashes := #[leftHash] }

def rightState : TermState :=
  { patterns := #[left, right]
    hashes := #[leftHash, rightHash] }

theorem left_term_step :
    materializeTermsLoop profile [0, 1]
        [leftNode, rightNode, pairNode] {} =
      materializeTermsLoop profile [0, 1]
        [rightNode, pairNode] leftState := by
  refine materializeTermsLoop_cons_of
    (symbol := { name := "left", arity := 0 })
    (childIds := []) (childPatterns := []) (childHashes := [])
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals rfl

theorem right_term_step :
    materializeTermsLoop profile [0, 1]
        [rightNode, pairNode] leftState =
      materializeTermsLoop profile [0, 1] [pairNode] rightState := by
  refine materializeTermsLoop_cons_of
    (symbol := { name := "right", arity := 0 })
    (childIds := []) (childPatterns := []) (childHashes := [])
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals rfl

theorem pair_term_step :
    materializeTermsLoop profile [0, 1] [pairNode] rightState =
      materializeTermsLoop profile [0, 1] [] termState := by
  refine materializeTermsLoop_cons_of
    (symbol := { name := "pair", arity := 2 })
    (childIds := [0, 1]) (childPatterns := [left, right])
    (childHashes := [leftHash, rightHash]) ?_ ?_ ?_ ?_ ?_ ?_
  all_goals rfl

theorem terms_materialize :
    materializeTerms? profile certificate = some termState := by
  change materializeTermsLoop profile [0, 1]
    [leftNode, rightNode, pairNode] {} = some termState
  rw [left_term_step, right_term_step, pair_term_step]
  rfl

def proofState : ProofState :=
  { nodes := article.nodes.toArray
    results := #[pair] }

theorem proof_step :
    materializeProofsLoop definition profile termState.patterns [0, 1] []
        [proofNode] {} =
      materializeProofsLoop definition profile termState.patterns [0, 1] []
        [] proofState := by
  refine materializeProofsLoop_cons_of
    (rule := pairRuleProfile) (argumentIds := [0, 1]) (premiseIds := [])
    (ruleArguments := [left, right]) (premiseResults := [])
    (explicitResult := pair) (expectedPremises := [])
    (expectedConclusion := pair)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact pair_instantiates
  · rfl
  · rfl

theorem proofs_materialize :
    materializeProofs? definition profile termState.patterns certificate =
      some proofState := by
  change materializeProofsLoop definition profile termState.patterns [0, 1]
    [] [proofNode] {} = some proofState
  rw [proof_step]
  rfl

theorem exact_materialization :
    materializeArticle? definition profile certificate = some article := by
  unfold materializeArticle?
  rw [if_pos (by simp [profile, profileDigest, digestWidth])]
  rw [if_pos (by simp [profile, sourceDigest, digestWidth])]
  rw [if_pos (by rfl)]
  rw [if_pos (by rfl)]
  rw [terms_materialize]
  dsimp
  rw [proofs_materialize]
  rfl

def pairDerivation : Derivation definition pair :=
  .byRule { ruleId := ⟨"pair"⟩, arguments := [left, right] }
    (instantiateRule?_eq_some_iff_application.mp pair_instantiates) .nil

theorem article_is_linearized :
    articleOfDerivation pairDerivation = article := by
  rfl

theorem article_accepts : checkWireArticle definition article = true := by
  rw [← article_is_linearized]
  exact checkWireArticle_articleOfDerivation pairDerivation

theorem decoded_certificate_accepts :
    checkCertificate definition profile pair certificate = true := by
  unfold checkCertificate
  rw [exact_materialization]
  dsimp
  rw [show decide (article.target = pair) = true by rfl]
  exact article_accepts

theorem encoded_bytes_accept :
    checkBytes definition profile pair (encodeCertificate certificate) = true := by
  unfold checkBytes
  rw [decodeCertificate?_encodeCertificate certificate certificate_encodable]
  exact decoded_certificate_accepts

def unrelatedClaim : Pattern := .apply "unrelated" []

theorem wrong_submitted_claim_rejected :
    checkCertificate definition profile unrelatedClaim certificate = false := by
  unfold checkCertificate
  rw [exact_materialization]
  simp [article, pair, unrelatedClaim]

def wrongFingerprintCertificate : Certificate :=
  { certificate with
    proofs := [{ proofNode with ruleFingerprint := ruleFingerprint + 1 }] }

theorem wrong_rule_fingerprint_rejected :
    checkCertificate definition profile pair wrongFingerprintCertificate = false := by
  decide

def wrongProfileCertificate : Certificate :=
  { certificate with
    profileDigest := List.replicate digestWidth 18 }

theorem wrong_profile_rejected :
    checkCertificate definition profile pair wrongProfileCertificate = false := by
  decide

def forwardChildCertificate : Certificate :=
  { certificate with children := [2, 1] }

theorem forward_term_child_rejected :
    checkCertificate definition profile pair forwardChildCertificate = false := by
  decide

def wrongArityCertificate : Certificate :=
  { certificate with
    terms := [leftNode, rightNode, { pairNode with arity := 1 }] }

theorem profile_arity_mismatch_rejected :
    checkCertificate definition profile pair wrongArityCertificate = false := by
  decide

def forgedProofNode : ProofNode := { proofNode with resultTerm := 0 }

def forgedConclusionCertificate : Certificate :=
  { certificate with
    proofs := [forgedProofNode]
    goalTerm := 0 }

theorem pair_ne_left : pair ≠ left := by
  decide

theorem forged_proof_loop_rejects :
    materializeProofsLoop definition profile termState.patterns [0, 1] []
      [forgedProofNode] {} = none := by
  refine materializeProofsLoop_conclusion_mismatch
    (rule := pairRuleProfile) (argumentIds := [0, 1]) (premiseIds := [])
    (ruleArguments := [left, right]) (premiseResults := [])
    (explicitResult := left) (expectedPremises := [])
    (expectedConclusion := pair)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact pair_instantiates
  · rfl
  · exact pair_ne_left

theorem forged_proofs_reject :
    materializeProofs? definition profile termState.patterns
      forgedConclusionCertificate = none := by
  exact forged_proof_loop_rejects

theorem forged_article_rejects :
    materializeArticle? definition profile forgedConclusionCertificate = none := by
  unfold materializeArticle?
  rw [if_pos (by simp [profile, profileDigest, digestWidth])]
  rw [if_pos (by simp [profile, sourceDigest, digestWidth])]
  rw [if_pos (by rfl)]
  rw [if_pos (by rfl)]
  rw [show materializeTerms? profile forgedConclusionCertificate =
      some termState by exact terms_materialize]
  dsimp
  rw [forged_proofs_reject]
  rfl

theorem forged_explicit_conclusion_rejected :
    checkCertificate definition profile left forgedConclusionCertificate = false := by
  unfold checkCertificate
  rw [forged_article_rejects]

def futurePremiseProfile : RuntimeProfile :=
  { profile with
    rules :=
      #[ { ruleId := ⟨"pair"⟩
           argumentCount := 2
           premiseCount := 1
           fingerprint := ruleFingerprint } ] }

def futurePremiseCertificate : Certificate :=
  { certificate with
    proofs := [{ proofNode with premiseCount := 1 }]
    premises := [0] }

theorem current_proof_as_premise_rejected :
    checkCertificate definition futurePremiseProfile pair
      futurePremiseCertificate = false := by
  decide

#print axioms exact_materialization
#print axioms decoded_certificate_accepts
#print axioms encoded_bytes_accept
#print axioms wrong_submitted_claim_rejected
#print axioms wrong_rule_fingerprint_rejected
#print axioms wrong_profile_rejected
#print axioms forward_term_child_rejected
#print axioms profile_arity_mismatch_rejected
#print axioms forged_explicit_conclusion_rejected
#print axioms current_proof_as_premise_rejected

end Mettapedia.GSLT.LanguageDef.M0GCLogicalReplayCanary
