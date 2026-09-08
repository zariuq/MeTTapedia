import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RawInferenceService
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILCheckedNativePrograms
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveMIL

/-!
# Raw inference requests with a proof-relevant MIL consumer

The existing learned relation calculus supplies ordinary raw proof data and
independent rule meanings. Runtime packet checking reconstructs the identical
raw derivation, which then supplies its native hypothesis and relational
evidence. Refined native admission uses separately proved quotation-leaf and
context formation obligations; it is not inferred from raw typing.

Checking and wire data are executable. The existing semantic reconstruction
of an accepted derivation uses noncomputable choice. No executable native
hypothesis materializer or general learned-rule soundness is asserted here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace RawInferenceMILWorkload

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceCettaWire
open Mettapedia.GSLT.LanguageDef.InferenceLanguageWire
open Presentation MILCheckedNativePrograms

variable {n : Nat} {context : Tower.Ctx n}

/-- Closed payloads are the runtime's independently checked vocabulary
condition. The accepted chain uses only the three declared entities. -/
theorem grandparent_payloads_valid :
    (RuntimeInferenceLanguage.ofDefinition MILCheckedChain.learned.target.1).proofPayloadsValid
      MILCheckedChain.grandparentProof = true := by
  simp only [MILCheckedChain.grandparentProof, MILCheckedChain.motherProof,
    MILCheckedChain.fatherProof, RuntimeInferenceLanguage.proofPayloadsValid,
    RuntimeInferenceLanguage.proofPayloadListsValid,
    RuntimeInferenceLanguage.fixedConstructorListsValid,
    MILCheckedChain.alice, MILCheckedChain.bob, MILCheckedChain.carol,
    RuntimeInferenceLanguage.fixedConstructorsValid]
  decide

theorem mother_payloads_valid :
    (RuntimeInferenceLanguage.ofDefinition MILCheckedChain.learned.target.1).proofPayloadsValid
      MILCheckedChain.motherProof = true := by
  simp [MILCheckedChain.motherProof, RuntimeInferenceLanguage.proofPayloadsValid,
    RuntimeInferenceLanguage.proofPayloadListsValid,
    RuntimeInferenceLanguage.fixedConstructorListsValid]

/-- The malformed chain has valid data vocabulary. Its rejection is about
its premise/argument alignment, not unsupported payload constructors. -/
theorem wrong_middle_payloads_valid :
    (RuntimeInferenceLanguage.ofDefinition MILCheckedChain.learned.target.1).proofPayloadsValid
      MILCheckedChain.wrongMiddleProof = true := by
  simp only [MILCheckedChain.wrongMiddleProof, MILCheckedChain.motherProof,
    MILCheckedChain.fatherProof, RuntimeInferenceLanguage.proofPayloadsValid,
    RuntimeInferenceLanguage.proofPayloadListsValid,
    RuntimeInferenceLanguage.fixedConstructorListsValid,
    MILCheckedChain.alice, MILCheckedChain.bob, MILCheckedChain.carol,
    RuntimeInferenceLanguage.fixedConstructorsValid]
  decide

theorem grandparent_packet_accepted :
    checkPacket (encodeDefinition MILCheckedChain.learned.target.1)
      (encodePattern (MILCheckedChain.relates MILCheckedChain.alice MILCheckedChain.carol))
      (encodeRawProof MILCheckedChain.grandparentProof) = some true := by
  rw [InferenceCettaWire.encodeDefinition, checkPacket_encode]
  exact congrArg some (RuntimeInferenceLanguage.checkRaw_complete _ _ _
    MILCheckedChain.grandparentProof_checked grandparent_payloads_valid)

theorem mother_packet_accepted :
    checkPacket (encodeDefinition MILCheckedChain.learned.target.1)
      (encodePattern (MILCheckedChain.relates MILCheckedChain.alice MILCheckedChain.bob))
      (encodeRawProof MILCheckedChain.motherProof) = some true := by
  rw [InferenceCettaWire.encodeDefinition, checkPacket_encode]
  apply congrArg some
  have lookup : (RuntimeInferenceLanguage.ofDefinition MILCheckedChain.learned.target.1).lookupRule?
      MILCheckedChain.motherRule.id = some MILCheckedChain.motherRule := by decide
  simp only [MILCheckedChain.motherProof, RuntimeInferenceLanguage.checkRaw,
    RuntimeInferenceLanguage.instantiateRule?, lookup]
  simp [RuntimeInferenceLanguage.checkRawChildren,
    MILCheckedChain.motherRule, RuntimeInferenceLanguage.argumentsValidAt,
    InferenceChecker.instantiateSchema?, InferenceChecker.instantiateSchemaAt?,
    InferenceChecker.instantiateSchemas?, InferenceChecker.instantiateSchemasAt?,
    RuleSchema.sideConditionsHold, MILCheckedChain.relates,
    MILCheckedChain.alice, MILCheckedChain.bob]

theorem wrong_middle_packet_rejected :
    checkPacket (encodeDefinition MILCheckedChain.learned.target.1)
      (encodePattern (MILCheckedChain.relates MILCheckedChain.alice MILCheckedChain.bob))
      (encodeRawProof MILCheckedChain.wrongMiddleProof) = some false := by
  rw [InferenceCettaWire.encodeDefinition, checkPacket_encode]
  apply congrArg some
  cases checked : (RuntimeInferenceLanguage.ofDefinition MILCheckedChain.learned.target.1).checkRaw
      (MILCheckedChain.relates MILCheckedChain.alice MILCheckedChain.bob)
      MILCheckedChain.wrongMiddleProof with
  | false => rfl
  | true =>
      have generic := RuntimeInferenceLanguage.checkRaw_sound MILCheckedChain.learned.target
        _ _ checked
      rw [MILCheckedChain.wrongMiddleProof_rejected] at generic
      cases generic

/-- The exact same goal has an accepted proof and a rejected candidate. -/
theorem rejected_candidate_not_refuted_goal :
    checkPacket (encodeDefinition MILCheckedChain.learned.target.1)
        (encodePattern (MILCheckedChain.relates MILCheckedChain.alice MILCheckedChain.bob))
        (encodeRawProof MILCheckedChain.wrongMiddleProof) = some false ∧
      checkPacket (encodeDefinition MILCheckedChain.learned.target.1)
        (encodePattern (MILCheckedChain.relates MILCheckedChain.alice MILCheckedChain.bob))
        (encodeRawProof MILCheckedChain.motherProof) = some true :=
  ⟨wrong_middle_packet_rejected, mother_packet_accepted⟩

/-- Every successful canonical MIL packet reconstructs its own raw proof,
not some other derivation of the same goal. No vocabulary premise is needed
for this soundness direction. -/
theorem packet_reconstructs_native (quotation : HostedQuotation context)
    (source target : Pattern) (raw : RawProof)
    (accepted : checkPacket (encodeDefinition MILCheckedChain.learned.target.1)
      (encodePattern (MILCheckedChain.relates source target)) (encodeRawProof raw) = some true) :
    Nonempty (CheckedRawNativeProgram quotation source target raw) := by
  obtain ⟨derivation, erases⟩ := checkPacket_encode_acceptance_sound
    MILCheckedChain.learned.target (MILCheckedChain.relates source target) raw accepted
  exact ⟨⟨derivation, erases⟩⟩

/-- Refined admission is obtained from the constructor program and the four
independent refined leaf judgments, not its existing raw `HasType` field. -/
theorem native_judgment_of_quotation
    {quotation : HostedQuotation context} {source target : Pattern} {raw : RawProof}
    (program : CheckedRawNativeProgram quotation source target raw)
    (leaves : FormationSensitiveMIL.QuotationTyping quotation.toTypedVocabularyQuotation)
    (formed : FormationSensitive.ContextFormation IntrinsicMILHypothesis.rules context) :
    FormationSensitive.Judgment IntrinsicMILHypothesis.rules context
      program.toChecked.nativeTerm.code (quotation.hypothesisType () ()).code := by
  exact program.toChecked.intrinsicProgram.formationSensitiveJudgment leaves formed

/-- The pre-existing concrete quotation really satisfies the refined leaf
interface. The two different primitive witnesses remain different slots. -/
theorem quotation_typed :
    FormationSensitiveMIL.QuotationTyping
      FormedQuotationCanary.quotation.toTypedVocabularyQuotation where
  sortsTyping := .var 4
  primitivesTyping := .var 3
  sortCodeTyping := fun _ => .var 2
  primitiveCodeTyping := by
    intro source target symbol
    cases symbol with
    | mother => exact .var 1
    | father => exact .var 0

theorem quotation_context_formed :
    FormationSensitive.ContextFormation IntrinsicMILHypothesis.rules
      FormedQuotationCanary.contextSPSMF := by
  have contextS : FormationSensitive.ContextFormation IntrinsicMILHypothesis.rules
      IntrinsicMILHypothesis.contextS :=
    .snoc .nil (.headType (.sort IntrinsicMILHypothesis.sortLevel))
      (.sort (.succ IntrinsicMILHypothesis.sortLevel))
  have contextSP : FormationSensitive.ContextFormation IntrinsicMILHypothesis.rules
      IntrinsicMILHypothesis.contextSP :=
    .snoc contextS FormationSensitiveMIL.primitiveFamilyType_hasType
      (.sort IntrinsicMILHypothesis.primitiveFamilyTypeLevel)
  have contextSPS : FormationSensitive.ContextFormation IntrinsicMILHypothesis.rules
      FormedQuotationCanary.contextSPS :=
    .snoc contextSP (.var 1) (.sort IntrinsicMILHypothesis.sortLevel)
  have contextSPSM : FormationSensitive.ContextFormation IntrinsicMILHypothesis.rules
      FormedQuotationCanary.contextSPSM :=
    .snoc contextSPS
      (FormationSensitiveMIL.primitiveFamilyApp_hasType (.var 1) (.var 0) (.var 0))
      (.sort IntrinsicMILHypothesis.primitiveLevel)
  exact .snoc contextSPSM
    (FormationSensitiveMIL.primitiveFamilyApp_hasType (.var 2) (.var 1) (.var 1))
    (.sort IntrinsicMILHypothesis.primitiveLevel)

/-- The checked program and its two-premise meaning cross the refined native
boundary in the actual five-slot quotation context. -/
theorem concrete_grandparent_refined_and_relational :
    FormationSensitive.Judgment IntrinsicMILHypothesis.rules
        FormedQuotationCanary.contextSPSMF
        (grandparent FormedQuotationCanary.quotation).toChecked.nativeTerm.code
        (FormedQuotationCanary.quotation.hypothesisType () ()).code ∧
      Nonempty ((grandparent FormedQuotationCanary.quotation).toChecked.intrinsicProgram.denotation.evidence
        MILCheckedChain.alice MILCheckedChain.carol) :=
  ⟨native_judgment_of_quotation _ quotation_typed quotation_context_formed,
    ⟨(grandparent FormedQuotationCanary.quotation).toChecked.nativeEvidence⟩⟩

/-! ## The ordinary raw service request and its independent native consumer -/

def request (scope : RawInferenceService.Scope) (source target : Pattern) :
    RawInferenceService.Request :=
  ⟨scope, encodePattern (MILCheckedChain.relates source target)⟩

def candidate (scope : RawInferenceService.Scope) (source target : Pattern) (raw : RawProof) :
    RawInferenceService.Candidate :=
  RawInferenceService.canonicalCandidate scope (MILCheckedChain.relates source target) raw

/-- Raw service evaluation checks the actual selected MIL language at the
exact supplied relational goal and proof tree. -/
theorem check_candidate (scope : RawInferenceService.Scope)
    (source target : Pattern) (raw : RawProof) :
    RawInferenceService.check MILCheckedChain.learned.target scope
      (candidate scope source target raw) =
        .checked ((RuntimeInferenceLanguage.ofDefinition MILCheckedChain.learned.target.1).checkRaw
          (MILCheckedChain.relates source target) raw) :=
  RawInferenceService.check_canonical _ _ _ _

/-- For every relational goal, a validated raw reply retains the exact
decoded article and supplies the independent proof-relevant native meaning.
The reply itself carries no proof or native-admission field. -/
theorem validated_native_program (quotation : HostedQuotation context)
    (scope : RawInferenceService.Scope) (source target : Pattern)
    (reply : RawInferenceService.Reply)
    (accepted : RawInferenceService.validate MILCheckedChain.learned.target scope
      (request scope source target) reply = true) :
    ∃ raw, decodeRawProof reply.candidate.article = some raw ∧
      ∃ program : CheckedRawNativeProgram quotation source target raw,
        Nonempty (MILLearnedProofRelevantAdmission.Reach source target) ∧
        Nonempty (program.toChecked.intrinsicProgram.denotation.evidence source target) := by
  obtain ⟨_, goal, raw, goalDecoded, rawDecoded, derivation, erases⟩ :=
    RawInferenceService.validate_sound MILCheckedChain.learned.target scope
      (request scope source target) reply accepted
  have goal_eq : MILCheckedChain.relates source target = goal := by
    simpa only [request, decodePattern_encodePattern, Option.some.injEq] using goalDecoded
  subst goal
  let program : CheckedRawNativeProgram quotation source target raw := ⟨derivation, erases⟩
  exact ⟨raw, rawDecoded, program, ⟨program.toChecked.relationalEvidence⟩,
    ⟨program.toChecked.nativeEvidence⟩⟩

/-- The raw-service theorem also reaches the refined native judgment when
the quotation's independent formation obligations have been discharged. -/
theorem validated_refined_program (quotation : HostedQuotation context)
    (leaves : FormationSensitiveMIL.QuotationTyping quotation.toTypedVocabularyQuotation)
    (formed : FormationSensitive.ContextFormation IntrinsicMILHypothesis.rules context)
    (scope : RawInferenceService.Scope) (source target : Pattern)
    (reply : RawInferenceService.Reply)
    (accepted : RawInferenceService.validate MILCheckedChain.learned.target scope
      (request scope source target) reply = true) :
    ∃ raw, decodeRawProof reply.candidate.article = some raw ∧
      ∃ program : CheckedRawNativeProgram quotation source target raw,
        FormationSensitive.Judgment IntrinsicMILHypothesis.rules context
          program.toChecked.nativeTerm.code (quotation.hypothesisType () ()).code ∧
        Nonempty (MILLearnedProofRelevantAdmission.Reach source target) ∧
        Nonempty (program.toChecked.intrinsicProgram.denotation.evidence source target) := by
  obtain ⟨raw, decoded, program, relational, native⟩ :=
    validated_native_program quotation scope source target reply accepted
  exact ⟨raw, decoded, program, native_judgment_of_quotation program leaves formed,
    relational, native⟩

theorem grandparent_service_accepted (scope : RawInferenceService.Scope) :
    RawInferenceService.validate MILCheckedChain.learned.target scope
      (request scope MILCheckedChain.alice MILCheckedChain.carol)
      (RawInferenceService.evaluate MILCheckedChain.learned.target scope
        (candidate scope MILCheckedChain.alice MILCheckedChain.carol
          MILCheckedChain.grandparentProof)) = true := by
  apply (RawInferenceService.validate_evaluated _ _ _).mpr
  rw [check_candidate]
  exact congrArg RawInferenceService.Verdict.checked
    (RuntimeInferenceLanguage.checkRaw_complete _ _ _
      MILCheckedChain.grandparentProof_checked grandparent_payloads_valid)

theorem mother_service_accepted (scope : RawInferenceService.Scope) :
    RawInferenceService.validate MILCheckedChain.learned.target scope
      (request scope MILCheckedChain.alice MILCheckedChain.bob)
      (RawInferenceService.evaluate MILCheckedChain.learned.target scope
        (candidate scope MILCheckedChain.alice MILCheckedChain.bob
          MILCheckedChain.motherProof)) = true := by
  apply (RawInferenceService.validate_evaluated _ _ _).mpr
  rw [check_candidate]
  have accepted := mother_packet_accepted
  rw [InferenceCettaWire.encodeDefinition, checkPacket_encode] at accepted
  exact congrArg RawInferenceService.Verdict.checked (Option.some.inj accepted)

/-- Rechecking rejects an invented acceptance tag even though a different
proof of this exact goal is accepted by the same service. -/
theorem forged_wrong_middle_rejected (scope : RawInferenceService.Scope) :
    RawInferenceService.validate MILCheckedChain.learned.target scope
      (request scope MILCheckedChain.alice MILCheckedChain.bob)
      ⟨candidate scope MILCheckedChain.alice MILCheckedChain.bob MILCheckedChain.wrongMiddleProof,
        .checked true⟩ = false := by
  apply RawInferenceService.forged_acceptance_rejected
  rw [check_candidate]
  have rejected := wrong_middle_packet_rejected
  rw [InferenceCettaWire.encodeDefinition, checkPacket_encode] at rejected
  rw [Option.some.inj rejected]
  decide

/-- This accepted reply has no postulated proof-bearing payload: its native
admission and evidence are reconstructed from the actual checker verdict. -/
theorem grandparent_service_refined (scope : RawInferenceService.Scope) :
    ∃ program : CheckedRawNativeProgram FormedQuotationCanary.quotation
        MILCheckedChain.alice MILCheckedChain.carol MILCheckedChain.grandparentProof,
      FormationSensitive.Judgment IntrinsicMILHypothesis.rules FormedQuotationCanary.contextSPSMF
        program.toChecked.nativeTerm.code
        (FormedQuotationCanary.quotation.hypothesisType () ()).code ∧
      Nonempty (MILLearnedProofRelevantAdmission.Reach MILCheckedChain.alice MILCheckedChain.carol) ∧
      Nonempty (program.toChecked.intrinsicProgram.denotation.evidence
        MILCheckedChain.alice MILCheckedChain.carol) := by
  obtain ⟨raw, decoded, program, admitted, relational, native⟩ :=
    validated_refined_program FormedQuotationCanary.quotation quotation_typed
      quotation_context_formed scope MILCheckedChain.alice MILCheckedChain.carol _
      (grandparent_service_accepted scope)
  have raw_eq : MILCheckedChain.grandparentProof = raw := by
    simpa only [RawInferenceService.evaluate, candidate, RawInferenceService.canonicalCandidate,
      decodeRawProof_encodeRawProof,
      Option.some.injEq] using decoded
  subst raw
  exact ⟨program, admitted, relational, native⟩

#print axioms grandparent_payloads_valid
#print axioms grandparent_packet_accepted
#print axioms rejected_candidate_not_refuted_goal
#print axioms packet_reconstructs_native
#print axioms native_judgment_of_quotation
#print axioms quotation_typed
#print axioms quotation_context_formed
#print axioms concrete_grandparent_refined_and_relational
#print axioms check_candidate
#print axioms validated_native_program
#print axioms validated_refined_program
#print axioms grandparent_service_accepted
#print axioms mother_service_accepted
#print axioms forged_wrong_middle_rejected
#print axioms grandparent_service_refined

end RawInferenceMILWorkload
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
