import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedFunctionPassing
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedInferenceFunction
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILNativeMaterialization

/-!
# Higher-order checker use and executable native materialization

An ordinary computation thunk carries the checker to a value-level caller,
which forces it and supplies raw proof data. Completed execution retains the
exact request, lexical checker origin and final world. An observed admission
then selects the submitted proof's native artifact by the executable MIL
materializer. Its formation and relational meaning are independently proved.

The checker returns data, not a trusted proof field. Materialization is a
separate executable Lean operation, not a newly installed machine primitive.
The statements do not claim a C realization, learning or proof-search
termination, a union of native rule packages, or totality at every fuel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace PolarizedNeedHigherOrderInference

open Presentation PrimeNeedReference
open Presentation.PolarizedNeed Presentation.PolarizedNeedMachine
open Presentation.PolarizedNeedNaturalSemantics
open Presentation.PolarizedNeedFunctionPassing
open PolarizedNeedInferenceService PolarizedNeedInferenceFunction
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceCettaWire
open Mettapedia.OSLF.MeTTaIL.Syntax

variable {Effect : Type} {m : Nat}

def passedSource (expected : Request) (input : Wire) :
    Computation Tower.Head Operation Effect 0 0 0 :=
  passAndApply (checkFunction expected) (NativeWireData.encode input)

def passedClosure (expected : Request) (input : Wire) :
    Closure Tower.Head Operation Effect m :=
  ⟨0, 0, 0, passedSource expected input, Fin.elim0, Fin.elim0, Fin.elim0⟩

def passedMachine (expected : Request) (input : Wire)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty m) (work : Work) :
    NeedMachine Tower.Head Operation Effect Empty Empty m :=
  ⟨world, .run (.evaluate (passedClosure expected input) .done) [], work⟩

def passedAnswers (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (input : Wire)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty m) (work : Work) (fuel : Nat) :=
  PrimeNeedLocalSteps.answers (extension (primitive definition scope)) fuel
    (passedMachine expected input world work)

/-- Data formation precedes and is independent of any checker verdict. -/
theorem passedSource_typed (expected : Request) (input : Wire) :
    ComputationTyping NativeWireData.rules signature .nil Fin.elim0 Fin.elim0
      (passedSource (Effect := Effect) expected input) (.returns (.native NativeWireData.dataType)) := by
  have formed : ComputationFormation NativeWireData.rules (.nil : Tower.Ctx 0) functionType :=
    .nativePi ⟨.sort Tower.zero, Tower.IsUniverse.sort _, NativeWireData.dataType_formed _⟩
      (.returns (.native ⟨.sort Tower.zero, Tower.IsUniverse.sort _, NativeWireData.dataType_formed _⟩))
  have resultFormed : ComputationFormation NativeWireData.rules (.nil : Tower.Ctx 0)
      (.returns (.native NativeWireData.dataType)) :=
    .returns (.native ⟨.sort Tower.zero, Tower.IsUniverse.sort _, NativeWireData.dataType_formed _⟩)
  simpa only [passedSource, functionType, CTy.instantiate, CTy.substitute, VTy.substitute,
    NativeWireData.dataType, subst] using
    (passAndApply_typed formed resultFormed
      (checkFunction_typed (Effect := Effect) .nil Fin.elim0 Fin.elim0 expected)
      (NativeWireData.encode_typing .nil input))

theorem passed_runs_iff (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (input : Wire)
    (world final : NeedWorld Tower.Head Operation Effect Empty Empty m)
    (outcome : Outcome Tower.Head Operation Effect Empty Empty m) :
    RunSegment (primitive definition scope) world
      (.run (.evaluate (passedClosure expected input) .done) []) final (.halted outcome) ↔
    RunSegment (primitive definition scope) world
      (.run (.evaluate (functionClosure expected input Fin.elim0 Fin.elim0 Fin.elim0) .done) [])
      final (.halted outcome) :=
  passAndApply_runs_iff (checkFunction expected) (NativeWireData.encode input) .done world final outcome

/-- Every finite raw input has a completed result in a slot-bounded world;
the theorem constructs the run without an acceptance premise. -/
theorem passed_answer_exists (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (input : Wire)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty m)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work) :
    ∃ fuel, replyOutcome (rawQualificationResult definition scope expected input) ∈
      passedAnswers definition scope expected input world work fuel := by
  obtain ⟨final, _, run⟩ := function_runs_of_slotBound definition scope expected input
    Fin.elim0 Fin.elim0 Fin.elim0 world bounded
  exact ((passed_runs_iff definition scope expected input world final _).mpr run).answers work

theorem passed_halted_exact (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (input : Wire)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty m)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work)
    {fuel : Nat} {final : NeedMachine Tower.Head Operation Effect Empty Empty m}
    {outcome : Outcome Tower.Head Operation Effect Empty Empty m}
    (member : final ∈ PrimeNeedLocalSteps.runFrontier (extension (primitive definition scope)) fuel
      [passedMachine expected input world work])
    (halted : haltedOutcome final = some outcome) :
    outcome = replyOutcome (rawQualificationResult definition scope expected input) ∧
      PrimeNeedAllocationBound.SlotBound final.world ∧
      ∃ allocated cell,
        world.allocate? (functionCheckOrigin input Fin.elim0 Fin.elim0 Fin.elim0) = some (allocated, cell) ∧
        final.world = replyWorld allocated cell
          (functionCheckOrigin input Fin.elim0 Fin.elim0 Fin.elim0) (rawCheckedReply definition scope input) := by
  have original := frontier_halt_has_natural_derivation (primitive definition scope) member halted
  obtain ⟨evaluation⟩ := (passAndApply_eval_iff (checkFunction expected) (NativeWireData.encode input)
    world final.world outcome).mp original
  obtain ⟨allocated, allocation⟩ := bounded.allocate_succeeds
    (functionCheckOrigin input Fin.elim0 Fin.elim0 Fin.elim0) 0
  obtain ⟨result, finalWorld⟩ := function_evaluation_exact definition scope expected input
    Fin.elim0 Fin.elim0 Fin.elim0 allocation evaluation
  refine ⟨result, ?_, allocated, _, allocation, finalWorld⟩
  rw [finalWorld]
  exact replyWorld_slotBound (bounded.allocate allocation) (World.allocate?_lookup_same allocation) _

theorem passed_answer_exact (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (input : Wire)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty m)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work)
    {fuel : Nat} {outcome : Outcome Tower.Head Operation Effect Empty Empty m}
    (observed : outcome ∈ passedAnswers definition scope expected input world work fuel) :
    outcome = replyOutcome (rawQualificationResult definition scope expected input) := by
  obtain ⟨final, member, halted⟩ := List.mem_filterMap.mp observed
  exact (passed_halted_exact definition scope expected input world bounded work member halted).1

theorem passed_admission_validates (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty m)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work) {fuel : Nat}
    (observed : replyOutcome (admissionVerdict (some true)) ∈ passedAnswers definition scope expected
      (RawInferenceService.encodeCandidate candidate) world work fuel) :
    RawInferenceService.validate definition scope expected (RawInferenceService.evaluate definition scope candidate) = true := by
  have same := passed_answer_exact definition scope expected (RawInferenceService.encodeCandidate candidate)
    world bounded work observed
  rw [rawQualificationResult_candidate] at same
  have wireSame : admissionVerdict (some true) = qualificationResult definition scope expected candidate :=
    NativeWireData.encode_injective (RuntimeValue.native.inj (Answer.returned.inj (Produced.value.inj same)))
  exact (qualificationResult_admitted_iff definition scope expected candidate).mp wireSame.symm

/-- Executed higher-order admission yields the computable artifact of the
submitted tree, with independently qualified native typing and meaning. -/
theorem observed_materializes {n : Nat} {context : Tower.Ctx n}
    (quotation : MILCheckedNativePrograms.HostedQuotation context)
    (leaves : FormationSensitiveMIL.QuotationTyping quotation.toTypedVocabularyQuotation)
    (formed : FormationSensitive.ContextFormation IntrinsicMILHypothesis.rules context)
    (scope : Scope) (source target : Pattern) (candidate : Candidate)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty m)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work) {fuel : Nat}
    (observed : replyOutcome (admissionVerdict (some true)) ∈
      passedAnswers MILCheckedChain.learned.target scope (RawInferenceMILWorkload.request scope source target)
        (RawInferenceService.encodeCandidate candidate) world work fuel) :
    ∃ raw, decodeRawProof candidate.article = some raw ∧
      ∃ program : MILCheckedNativePrograms.CheckedRawNativeProgram quotation source target raw,
        MILNativeMaterialization.materialize? quotation source target raw = some program.toChecked.nativeTerm.code ∧
        FormationSensitive.Judgment IntrinsicMILHypothesis.rules context
          program.toChecked.nativeTerm.code (quotation.hypothesisType () ()).code ∧
        Nonempty (MILLearnedProofRelevantAdmission.Reach source target) ∧
        Nonempty (program.toChecked.intrinsicProgram.denotation.evidence source target) := by
  have validated := passed_admission_validates MILCheckedChain.learned.target scope
    (RawInferenceMILWorkload.request scope source target) candidate world bounded work observed
  obtain ⟨raw, decoded, program, typed, reached, meaning⟩ :=
    RawInferenceMILWorkload.validated_refined_program quotation leaves formed scope source target
      (RawInferenceService.evaluate MILCheckedChain.learned.target scope candidate) validated
  exact ⟨raw, decoded, program, MILNativeMaterialization.materialize_checked program, typed, reached, meaning⟩

namespace Controls

def emptyWorld : NeedWorld Tower.Head Operation Nat Empty Empty 0 :=
  ⟨0, [], .empty, .empty, 0, 0⟩

theorem emptyWorld_bounded : PrimeNeedAllocationBound.SlotBound emptyWorld := by
  intro cell entry lookup
  cases lookup

theorem grandparent_eventually_admitted (scope : Scope) :
    ∃ fuel, replyOutcome (admissionVerdict (some true)) ∈
      passedAnswers MILCheckedChain.learned.target scope
        (RawInferenceMILWorkload.request scope MILCheckedChain.alice MILCheckedChain.carol)
        (RawInferenceService.encodeCandidate (RawInferenceMILWorkload.candidate scope
          MILCheckedChain.alice MILCheckedChain.carol MILCheckedChain.grandparentProof)) emptyWorld {} fuel := by
  have result := passed_answer_exists MILCheckedChain.learned.target scope
    (RawInferenceMILWorkload.request scope MILCheckedChain.alice MILCheckedChain.carol)
    (RawInferenceService.encodeCandidate (RawInferenceMILWorkload.candidate scope
      MILCheckedChain.alice MILCheckedChain.carol MILCheckedChain.grandparentProof)) emptyWorld emptyWorld_bounded {}
  have admitted := (qualificationResult_admitted_iff _ _ _ _).mpr
    (RawInferenceMILWorkload.grandparent_service_accepted scope)
  simpa only [rawQualificationResult_candidate, admitted] using result

theorem grandparent_executed_materialization (scope : Scope) :
    ∃ fuel, replyOutcome (admissionVerdict (some true)) ∈
      passedAnswers MILCheckedChain.learned.target scope
        (RawInferenceMILWorkload.request scope MILCheckedChain.alice MILCheckedChain.carol)
        (RawInferenceService.encodeCandidate (RawInferenceMILWorkload.candidate scope
          MILCheckedChain.alice MILCheckedChain.carol MILCheckedChain.grandparentProof)) emptyWorld {} fuel ∧
      ∃ term,
        MILNativeMaterialization.materialize? MILCheckedNativePrograms.FormedQuotationCanary.quotation
          MILCheckedChain.alice MILCheckedChain.carol MILCheckedChain.grandparentProof = some term ∧
        FormationSensitive.Judgment IntrinsicMILHypothesis.rules
          MILCheckedNativePrograms.FormedQuotationCanary.contextSPSMF term
          (MILCheckedNativePrograms.FormedQuotationCanary.quotation.hypothesisType () ()).code ∧
        Nonempty (MILLearnedProofRelevantAdmission.Reach MILCheckedChain.alice MILCheckedChain.carol) := by
  obtain ⟨fuel, observed⟩ := grandparent_eventually_admitted scope
  obtain ⟨raw, decoded, program, computed, typed, reached, _⟩ :=
    observed_materializes MILCheckedNativePrograms.FormedQuotationCanary.quotation
      RawInferenceMILWorkload.quotation_typed RawInferenceMILWorkload.quotation_context_formed
      scope MILCheckedChain.alice MILCheckedChain.carol _ emptyWorld emptyWorld_bounded {} observed
  have same : MILCheckedChain.grandparentProof = raw := by
    simpa only [RawInferenceMILWorkload.candidate, RawInferenceService.canonicalCandidate,
      decodeRawProof_encodeRawProof, Option.some.injEq] using decoded
  subst raw
  exact ⟨fuel, observed, program.toChecked.nativeTerm.code, computed, typed, reached⟩

theorem wrong_request_never_admitted (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate) (different : candidate.request ≠ expected)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty m)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work) (fuel : Nat) :
    replyOutcome (admissionVerdict (some true)) ∉ passedAnswers definition scope expected
      (RawInferenceService.encodeCandidate candidate) world work fuel := by
  intro observed
  have validated := passed_admission_validates definition scope expected candidate world bounded work observed
  rw [RawInferenceService.wrong_request_rejected definition scope expected _ different] at validated
  cases validated

theorem stale_scope_never_admitted (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate) (stale : expected.scope ≠ scope)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty m)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work) (fuel : Nat) :
    replyOutcome (admissionVerdict (some true)) ∉ passedAnswers definition scope expected
      (RawInferenceService.encodeCandidate candidate) world work fuel := by
  intro observed
  have validated := passed_admission_validates definition scope expected candidate world bounded work observed
  rw [RawInferenceService.stale_scope_rejected definition scope expected _ stale] at validated
  cases validated

/-- Rejection of the submitted tree prevents its admission through the
higher-order caller even if another proof of the same goal exists. -/
theorem rejected_article_never_admitted (scope : Scope) (source target : Pattern) (raw : RawProof)
    (rejected : checkRaw MILCheckedChain.learned.target (MILCheckedChain.relates source target) raw = false)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty m)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work) (fuel : Nat) :
    replyOutcome (admissionVerdict (some true)) ∉
      passedAnswers MILCheckedChain.learned.target scope (RawInferenceMILWorkload.request scope source target)
        (RawInferenceService.encodeCandidate (RawInferenceMILWorkload.candidate scope source target raw))
        world work fuel := by
  intro observed
  have validated := passed_admission_validates MILCheckedChain.learned.target scope
    (RawInferenceMILWorkload.request scope source target) (RawInferenceMILWorkload.candidate scope source target raw)
    world bounded work observed
  have checked := (RawInferenceService.validate_evaluated _ _ _).mp validated
  rw [RawInferenceMILWorkload.check_candidate] at checked
  have accepted := InferenceLanguageWire.RuntimeInferenceLanguage.checkRaw_sound
    MILCheckedChain.learned.target _ _ (RawInferenceService.Verdict.checked.inj checked)
  rw [rejected] at accepted
  cases accepted

theorem wrong_middle_never_admitted (scope : Scope) (fuel : Nat) :
    replyOutcome (admissionVerdict (some true)) ∉
      passedAnswers MILCheckedChain.learned.target scope
        (RawInferenceMILWorkload.request scope MILCheckedChain.alice MILCheckedChain.bob)
        (RawInferenceService.encodeCandidate (RawInferenceMILWorkload.candidate scope
          MILCheckedChain.alice MILCheckedChain.bob MILCheckedChain.wrongMiddleProof)) emptyWorld {} fuel :=
  rejected_article_never_admitted scope _ _ _ MILCheckedChain.wrongMiddleProof_rejected
    emptyWorld emptyWorld_bounded {} fuel

theorem malformed_eventually_reported (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) :
    ∃ fuel, replyOutcome (admissionVerdict none) ∈ passedAnswers definition scope expected
      PolarizedNeedInferenceFunction.Controls.malformedInput emptyWorld {} fuel := by
  simpa only [PolarizedNeedInferenceFunction.Controls.malformed_result] using
    passed_answer_exists definition scope expected PolarizedNeedInferenceFunction.Controls.malformedInput
      emptyWorld emptyWorld_bounded {}

end Controls

#print axioms passedSource_typed
#print axioms passed_runs_iff
#print axioms passed_answer_exists
#print axioms passed_halted_exact
#print axioms passed_answer_exact
#print axioms passed_admission_validates
#print axioms observed_materializes
#print axioms Controls.emptyWorld_bounded
#print axioms Controls.grandparent_eventually_admitted
#print axioms Controls.grandparent_executed_materialization
#print axioms Controls.wrong_request_never_admitted
#print axioms Controls.stale_scope_never_admitted
#print axioms Controls.rejected_article_never_admitted
#print axioms Controls.wrong_middle_never_admitted
#print axioms Controls.malformed_eventually_reported

end PolarizedNeedHigherOrderInference
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
