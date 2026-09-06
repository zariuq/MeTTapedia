import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedInferenceService
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RawInferenceMILWorkload

/-!
# Executed raw MIL checking and request-specific native use

The source program binds the actual checker reply and uses it as data in a
second operation. The existing Need machine allocates, forces and caches
that reply. Its observed admission is connected to the independently
interpreted MIL derivation, with its exact raw erasure and refined native
quotation qualification. No proof is stored in the input or returned data.

This is a concrete source-level mathematical-service boundary, not an
executable replacement for the existing noncomputable native materializer,
a new learning algorithm, or a union of native computation-rule packages.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace PolarizedNeedInferenceWorkload

open Presentation PrimeNeedReference
open Presentation.PolarizedNeedMachine
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceCettaWire
open Mettapedia.OSLF.MeTTaIL.Syntax
open PolarizedNeedInferenceService

def world : NeedWorld Tower.Head Operation Nat Empty Empty 0 :=
  ⟨0, [], .empty, .empty, 0, 0⟩

def initial (expected : Request) (candidate : Candidate) :
    NeedMachine Tower.Head Operation Nat Empty Empty 0 :=
  ⟨world, .run (.evaluate (sourceClosure expected candidate) .done) [], {}⟩

def acceptedOutcome : Outcome Tower.Head Operation Nat Empty Empty 0 :=
  replyOutcome (admissionVerdict (some true))

def refusedOutcome : Outcome Tower.Head Operation Nat Empty Empty 0 :=
  replyOutcome (admissionVerdict (some false))

def answers (scope : Scope) (expected : Request) (candidate : Candidate) (fuel : Nat) :=
  PrimeNeedLocalSteps.answers (extension (primitive MILCheckedChain.learned.target scope)) fuel
    (initial expected candidate)

/-- Every supplied candidate reaches its actual qualification result. This
is finite execution of the checker, not termination of proof search. -/
theorem eventually_result (scope : Scope) (expected : Request) (candidate : Candidate) :
    ∃ fuel, replyOutcome (qualificationResult MILCheckedChain.learned.target scope expected candidate)
      ∈ answers scope expected candidate fuel := by
  obtain ⟨final, run⟩ := checkThenQualify_runs_from_empty MILCheckedChain.learned.target scope
    expected candidate world rfl
  exact run.answers {}

theorem grandparent_eventually_admitted (scope : Scope) :
    ∃ fuel, acceptedOutcome ∈ answers scope
      (RawInferenceMILWorkload.request scope MILCheckedChain.alice MILCheckedChain.carol)
      (RawInferenceMILWorkload.candidate scope MILCheckedChain.alice MILCheckedChain.carol
        MILCheckedChain.grandparentProof) fuel := by
  have result := eventually_result scope
    (RawInferenceMILWorkload.request scope MILCheckedChain.alice MILCheckedChain.carol)
    (RawInferenceMILWorkload.candidate scope MILCheckedChain.alice MILCheckedChain.carol
      MILCheckedChain.grandparentProof)
  have admitted := (qualificationResult_admitted_iff _ _ _ _).mpr
    (RawInferenceMILWorkload.grandparent_service_accepted scope)
  simpa only [admitted, acceptedOutcome] using result

theorem mother_eventually_admitted (scope : Scope) :
    ∃ fuel, acceptedOutcome ∈ answers scope
      (RawInferenceMILWorkload.request scope MILCheckedChain.alice MILCheckedChain.bob)
      (RawInferenceMILWorkload.candidate scope MILCheckedChain.alice MILCheckedChain.bob
        MILCheckedChain.motherProof) fuel := by
  have result := eventually_result scope
    (RawInferenceMILWorkload.request scope MILCheckedChain.alice MILCheckedChain.bob)
    (RawInferenceMILWorkload.candidate scope MILCheckedChain.alice MILCheckedChain.bob
      MILCheckedChain.motherProof)
  have admitted := (qualificationResult_admitted_iff _ _ _ _).mpr
    (RawInferenceMILWorkload.mother_service_accepted scope)
  simpa only [admitted, acceptedOutcome] using result

theorem wrong_request_eventually_refused (scope : Scope) (expected : Request)
    (candidate : Candidate) (different : candidate.request ≠ expected) :
    ∃ fuel, refusedOutcome ∈ answers scope expected candidate fuel := by
  have result := eventually_result scope expected candidate
  simpa only [wrong_request_result _ _ _ _ different, refusedOutcome] using result

theorem zero_fuel_is_unfinished (scope : Scope) (expected : Request) (candidate : Candidate) :
    answers scope expected candidate 0 = [] := rfl

/-- The observation comes from this actual source invocation. A raw marker
created by any other program is not a premise of this theorem. -/
theorem observed_admission_refined {n : Nat} {context : Tower.Ctx n}
    (quotation : MILCheckedNativePrograms.HostedQuotation context)
    (leaves : FormationSensitiveMIL.QuotationTyping quotation.toTypedVocabularyQuotation)
    (formed : FormationSensitive.ContextFormation IntrinsicMILHypothesis.rules context)
    (scope : Scope) (source target : Pattern) (candidate : Candidate) {fuel : Nat}
    (observed : acceptedOutcome ∈ answers scope
      (RawInferenceMILWorkload.request scope source target) candidate fuel) :
    ∃ raw, decodeRawProof candidate.article = some raw ∧
      ∃ program : MILCheckedNativePrograms.CheckedRawNativeProgram quotation source target raw,
        FormationSensitive.Judgment IntrinsicMILHypothesis.rules context
          program.toChecked.nativeTerm.code (quotation.hypothesisType () ()).code ∧
        Nonempty (MILLearnedProofRelevantAdmission.Reach source target) ∧
        Nonempty (program.toChecked.intrinsicProgram.denotation.evidence source target) := by
  have validated := source_admission_validates MILCheckedChain.learned.target scope
    (RawInferenceMILWorkload.request scope source target) candidate world rfl {} observed
  exact RawInferenceMILWorkload.validated_refined_program quotation leaves formed scope source target
    (RawInferenceService.evaluate MILCheckedChain.learned.target scope candidate) validated

/-- The two-premise relation and refined native artifact are consequences of
the executed source's admission, not unrelated witnesses paired with a run. -/
theorem grandparent_executed_native (scope : Scope) :
    ∃ fuel, acceptedOutcome ∈ answers scope
      (RawInferenceMILWorkload.request scope MILCheckedChain.alice MILCheckedChain.carol)
      (RawInferenceMILWorkload.candidate scope MILCheckedChain.alice MILCheckedChain.carol
        MILCheckedChain.grandparentProof) fuel ∧
      ∃ program : MILCheckedNativePrograms.CheckedRawNativeProgram
        MILCheckedNativePrograms.FormedQuotationCanary.quotation
        MILCheckedChain.alice MILCheckedChain.carol MILCheckedChain.grandparentProof,
        FormationSensitive.Judgment IntrinsicMILHypothesis.rules
          MILCheckedNativePrograms.FormedQuotationCanary.contextSPSMF
          program.toChecked.nativeTerm.code
          (MILCheckedNativePrograms.FormedQuotationCanary.quotation.hypothesisType () ()).code ∧
        Nonempty (program.toChecked.intrinsicProgram.denotation.evidence
          MILCheckedChain.alice MILCheckedChain.carol) := by
  obtain ⟨fuel, observed⟩ := grandparent_eventually_admitted scope
  obtain ⟨raw, decoded, program, typed, _, meaning⟩ :=
    observed_admission_refined MILCheckedNativePrograms.FormedQuotationCanary.quotation
      RawInferenceMILWorkload.quotation_typed RawInferenceMILWorkload.quotation_context_formed
      scope MILCheckedChain.alice MILCheckedChain.carol _ observed
  have raw_eq : MILCheckedChain.grandparentProof = raw := by
    simpa only [RawInferenceMILWorkload.candidate, RawInferenceService.canonicalCandidate,
      decodeRawProof_encodeRawProof, Option.some.injEq] using decoded
  subst raw
  exact ⟨fuel, observed, program, typed, meaning⟩

theorem wrong_middle_never_admitted (scope : Scope) (fuel : Nat) :
    acceptedOutcome ∉ answers scope
      (RawInferenceMILWorkload.request scope MILCheckedChain.alice MILCheckedChain.bob)
      (RawInferenceMILWorkload.candidate scope MILCheckedChain.alice MILCheckedChain.bob
        MILCheckedChain.wrongMiddleProof) fuel := by
  intro observed
  have validated := source_admission_validates MILCheckedChain.learned.target scope
    (RawInferenceMILWorkload.request scope MILCheckedChain.alice MILCheckedChain.bob)
    (RawInferenceMILWorkload.candidate scope MILCheckedChain.alice MILCheckedChain.bob
      MILCheckedChain.wrongMiddleProof) world rfl {} observed
  have checked := (RawInferenceService.validate_evaluated _ _ _).mp validated
  rw [RawInferenceMILWorkload.check_candidate] at checked
  have generic := Mettapedia.GSLT.LanguageDef.InferenceLanguageWire.RuntimeInferenceLanguage.checkRaw_sound
    MILCheckedChain.learned.target _ _ (RawInferenceService.Verdict.checked.inj checked)
  rw [MILCheckedChain.wrongMiddleProof_rejected] at generic
  cases generic

theorem wrong_middle_eventually_refused (scope : Scope) :
    ∃ fuel, refusedOutcome ∈ answers scope
      (RawInferenceMILWorkload.request scope MILCheckedChain.alice MILCheckedChain.bob)
      (RawInferenceMILWorkload.candidate scope MILCheckedChain.alice MILCheckedChain.bob
        MILCheckedChain.wrongMiddleProof) fuel := by
  have result := eventually_result scope
    (RawInferenceMILWorkload.request scope MILCheckedChain.alice MILCheckedChain.bob)
    (RawInferenceMILWorkload.candidate scope MILCheckedChain.alice MILCheckedChain.bob
      MILCheckedChain.wrongMiddleProof)
  cases checked : RawInferenceService.validate MILCheckedChain.learned.target scope
      (RawInferenceMILWorkload.request scope MILCheckedChain.alice MILCheckedChain.bob)
      (RawInferenceService.evaluate MILCheckedChain.learned.target scope
        (RawInferenceMILWorkload.candidate scope MILCheckedChain.alice MILCheckedChain.bob
          MILCheckedChain.wrongMiddleProof)) with
  | false => simpa only [qualificationResult, checked, refusedOutcome] using result
  | true =>
      obtain ⟨fuel, observed⟩ := result
      rw [qualificationResult, checked] at observed
      exact False.elim (wrong_middle_never_admitted scope fuel observed)

theorem wrong_expected_never_admitted (scope : Scope) (expected : Request) (candidate : Candidate)
    (different : candidate.request ≠ expected) (fuel : Nat) :
    acceptedOutcome ∉ answers scope expected candidate fuel := by
  intro observed
  have validated := source_admission_validates MILCheckedChain.learned.target scope
    expected candidate world rfl {} observed
  rw [RawInferenceService.wrong_request_rejected _ _ _ _ different] at validated
  cases validated

theorem stale_expected_never_admitted (scope : Scope) (expected : Request) (candidate : Candidate)
    (stale : expected.scope ≠ scope) (fuel : Nat) :
    acceptedOutcome ∉ answers scope expected candidate fuel := by
  intro observed
  have validated := source_admission_validates MILCheckedChain.learned.target scope
    expected candidate world rfl {} observed
  rw [RawInferenceService.stale_scope_rejected _ _ _ _ stale] at validated
  cases validated

/-- A program can return this ordinary native data without checking anything.
The operation-specific observed-admission premise cannot be dropped. -/
theorem freely_formed_marker :
    FormationSensitive.Judgment NativeWireData.rules .nil
      (NativeWireData.encode (n := 0) (admissionVerdict (some true))) NativeWireData.dataType :=
  NativeWireData.encode_judgment .nil _

#print axioms eventually_result
#print axioms grandparent_eventually_admitted
#print axioms mother_eventually_admitted
#print axioms wrong_request_eventually_refused
#print axioms zero_fuel_is_unfinished
#print axioms observed_admission_refined
#print axioms grandparent_executed_native
#print axioms wrong_middle_never_admitted
#print axioms wrong_middle_eventually_refused
#print axioms wrong_expected_never_admitted
#print axioms stale_expected_never_admitted
#print axioms freely_formed_marker

end PolarizedNeedInferenceWorkload
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
