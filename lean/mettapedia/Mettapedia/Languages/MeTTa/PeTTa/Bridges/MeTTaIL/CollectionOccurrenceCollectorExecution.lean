import Mettapedia.Languages.MeTTa.PeTTa.EquationEquality
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseMatchingExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceRuntime
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceReadout

/-!
# Native preparation and installation of newly matched occurrence allocations

The collector applies the existing local checks and presentation replay,
retains the original occurrence/allocation packet, and starts the existing
conditional continuation. It grants no new source admission authority.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceCollectorExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionOccurrenceBatch CollectionOccurrenceMatcher CanonicalCompare
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open CollectionOccurrenceRuntime
open scoped ProgramQuotation

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {sourcePattern : Pattern}

def source : ProgramQuotation.QuotedProgram :=
  CollectionOccurrenceSearchExecution.SelectedNativeSource.collectorSource

def library : Library :=
  CollectionOccurrenceSearchExecution.SelectedNativeSource.library

theorem checked : library.check = true := CollectionOccurrenceSearchExecution.SelectedNativeSource.checked

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceCollectorExecution


namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise ScopedRuleMatching
open CollectionOccurrenceHandoff CollectionOccurrenceBatch CollectionOccurrenceMatcher
open SpaceSemantics Eval BridgeKit WireKit


namespace CollectionOccurrenceCollectorExecution.Interpreted

def originTerm (job : CollectionOccurrenceHandoff.Job) : Term :=
  .application "RecursiveOccurrenceJob" [ScopedRuleJobReadoutExecution.jobTerm job.origin,
    CollectionContextExecution.variantTerm job.variant]

/-- A source-derived view of the one allocation row and its inert wire constructors. -/
def metadataLibrary : Library :=
  ⟨{equations := [], declarations := []},
    ((((RuleExecutionProgram.callFragment ["gslt:premise:binding-admitted", "gslt:premise:open-well-sorted"]
        RuleExecutionProgram.scopedProgram).append
      (RuleExecutionProgram.callFragment ["gslt:collection-handoff:prepare"]
        (RuleExecutionProgram.interpretedPremiseSupportSources[12]'(by decide +kernel)).program)).append
      (RuleExecutionProgram.callFragment ["gslt:occurrence-batch:frame-begin"]
        (RuleExecutionProgram.interpretedPremiseSupportSources[14]'(by decide +kernel)).program)).append
      (RuleExecutionProgram.callFragment ["gslt:occurrence-collector:allocate"] CollectionOccurrenceSearchExecution.SelectedNativeSource.collectorSource.program)).append
      (RuleExecutionProgram.callFragment ["gslt:premise:matching-environment"] RuleExecutionProgram.scopedProgram),
    ["gslt:occurrence-collector:allocate", "gslt:premise:matching-environment",
      "gslt:premise:binding-admitted", "gslt:premise:open-well-sorted", "gslt:collection-handoff:prepare",
      "gslt:occurrence-batch:frame-begin", "OccurrenceAllocationInput", "RecursiveOccurrenceJob", "RuleJob",
      "CollectionSiteVariant", "RuleJobSite", "ScopedMatcherRequest", "PremiseEnvironment", "None", "Some",
      "RecursiveCollectionOrigin"]⟩
def metadataHeads := metadataLibrary.owns
theorem metadata_checked : metadataLibrary.check = true := by decide +kernel

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {matcher : MatchingExecution}

/-- The collector's positive branch composes its actual lower operations.
The seed initializer is post-match work with no supplied premise outcome. -/
theorem allocated_returns_with (program : Program)
    (agreement : ProgramAgreementOn metadataHeads metadataLibrary.runtime program)
    (host : Effects.State) (names footprint : List String)
    (environmentWire : Term) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (profile : SeedProfile matcher plan bound expected source)
    (job : CollectionOccurrenceHandoff.Job) (licensed : job.Valid plan bound expected source)
    (work depth : Nat) (answer : RecursiveCollectionMachine.Answer)
    (published : Published job work answer)
    (inside : ∀ name ∈ job.variant.site.focus.freeFvarNames, name ∈ footprint)
    (allocation : Allocation plan bound expected source)
    (made : allocate? job licensed work answer published depth = some allocation)
    (metadata : PureReturns program [] host
      (apply "gslt:premise:matching-environment" [encoded environmentWire]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm
        (GeneralPlanEnvironment.environment plan) ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint))))
    (admission : PureReturns program [] host
      (apply "gslt:premise:binding-admitted"
        [encoded (InferenceCettaWire.AuthoredRule.rewriteTerm job.origin.declaration.rule),
          encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm job.origin.declaration.binding.spec)]) host
      (Effects.boolean (RuleBinding.admittedFor job.origin.declaration.rule job.origin.declaration.binding.spec)))
    (sorting : PureReturns program [] host
      (apply "gslt:premise:open-well-sorted"
        [encoded (encodeList InferenceCettaWire.AuthoredRule.typingDeclarationTerm
          (GeneralPlanEnvironment.environment plan).language.terms),
          encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm
            ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint)),
          encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm job.variant.site.focusBound),
          encoded (InferenceCettaWire.AuthoredRule.typeTerm job.variant.site.focusType),
          encoded (InferenceCettaWire.encodePattern job.variant.site.focus)]) host
      (Effects.boolean (Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted
        (GeneralPlanEnvironment.environment plan).language
        (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList
          ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint))
        job.variant.site.focusBound job.variant.site.focusType job.variant.site.focus)))
    (prepared : PureReturns program [] host
      (apply "gslt:collection-handoff:prepare"
        [encoded (encodeList Term.string names),
          encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm job.request),
          encoded (RecursiveCollectionExecution.answerTerm answer)]) host
      (encoded (encodeOption RecursiveCollectionHandoffExecution.preparedTerm
        (RecursiveCollectionHandoff.prepare job.request answer))))
    (begun : PureReturns program [] host
      (apply "gslt:occurrence-batch:frame-begin"
        [encoded (CollectionOccurrenceBatchExecution.originTerm allocation.job allocation.answer),
          encoded environmentWire, number allocation.request.depth,
          encoded (CompleteExecution.DescentCodec.typesTerm allocation.request.bound),
          encoded (InferenceCettaWire.AuthoredRule.typeTerm allocation.request.type),
          number allocation.request.index,
          encoded (InferenceCettaWire.AuthoredRule.rewriteTerm allocation.request.rule),
          encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm allocation.request.spec),
          encoded (RecursiveCollectionHandoffExecution.preparedTerm allocation.request.prepared)]) host
      (encoded (CollectionOccurrenceBatchExecution.frameTermWith codec (Frame.initialWith profile allocation)))) :
    PureReturns program [] host
      (apply "gslt:occurrence-collector:allocate"
        [encoded (encodeList Term.string names), encoded environmentWire, number depth,
          encoded (originTerm job), encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm job.request),
          encoded (RecursiveCollectionExecution.answerTerm answer)]) host
      (encoded (.application "Some"
        [CollectionOccurrenceBatchExecution.frameTermWith codec (Frame.initialWith profile allocation)])) := by
  obtain ⟨sameJob, sameAnswer, sameDepth, computed⟩ := allocate_readout job licensed work depth answer published made
  have checkedLocal := allocation.static_checked
  rw [sameJob] at checkedLocal
  rw [computed] at prepared
  have snapshot := WellSorted.check_open_pattern_snapshot (GeneralPlanEnvironment.environment plan).language
    (GeneralPlanEnvironment.environment plan).free job.variant.site.focusBound job.variant.site.focusType
    job.variant.site.focus footprint inside
  obtain ⟨requestDepth, requestBound, requestType, requestSource, requestIndex,
    requestRule, requestSpec, requestAnswer⟩ := allocation.request_fields
  simp only [allocation.request_origin.2, requestDepth, requestBound, requestType, requestIndex,
    requestRule, requestSpec, sameJob, sameAnswer, sameDepth] at begun
  metta_call_in metadata_checked using agreement
  metta_eval [metadata, admission, sorting, prepared, begun] with metadata_checked in agreement unfolding
    [checkedLocal.1, checkedLocal.2, snapshot, originTerm, CollectionOccurrenceHandoff.Job.request,
      CollectionOccurrenceBatchExecution.originTerm, CollectionContextExecution.variantTerm,
      ScopedRuleJobReadoutExecution.jobTerm, ScopedRuleJobReadoutExecution.siteTerm,
      RuleInstantiationExecution.GeneralExecution.matcherRequestTerm,
      PremiseOperationsExecution.GeneralExecution.environmentTerm,
      CompleteExecution.DescentCodec.typesTerm, CompleteExecution.DescentCodec.typeTerm,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, encodeOption,
      CettaWireAtom.encode, CettaWireAtom.encodeMany]

#print axioms metadata_checked
#print axioms allocated_returns_with
end CollectionOccurrenceCollectorExecution.Interpreted
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL


namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceCollectorExecution.Selected
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open SpaceSemantics Eval BridgeKit WireKit

private local instance equationEq : DecidableEq SpaceSemantics.Equation :=
  SpaceSemantics.Equation.decideEq

/-- The finite allocation metadata view retains the actual selected source rows and order. -/
theorem metadata_agreement : ProgramAgreementOn Interpreted.metadataHeads Interpreted.metadataLibrary.runtime
    CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

theorem scoped_supported (head : String) (active : RetainedMatchingWire.scopedPrimitiveHeads head = true) :
    CollectionOccurrenceSearchExecution.SelectedNativeSource.lowerHeads head = true := by
  have probe : head.startsWith "native-probe:" = false := by
    have parts := active
    simp only [RetainedMatchingWire.scopedPrimitiveHeads, Bool.and_eq_true, Bool.not_eq_true'] at parts
    exact parts.1.2
  have outside : CollectionOccurrenceSearchExecution.SelectedNativeSource.excluded.all (fun name => !RetainedMatchingWire.scopedPrimitiveHeads name) = true :=
    by decide +kernel
  cases found : CollectionOccurrenceSearchExecution.SelectedNativeSource.excluded.contains head with
  | false => simp only [CollectionOccurrenceSearchExecution.SelectedNativeSource.lowerHeads, found, Bool.not_false, Bool.true_and, probe]
  | true =>
    have member : head ∈ CollectionOccurrenceSearchExecution.SelectedNativeSource.excluded := by simpa only [List.contains_iff_mem] using found
    have rejected := List.all_eq_true.mp outside head member
    rw [active] at rejected
    cases rejected

/-- Existing proved scoped computations are retained in the actual three-slot source. -/
theorem scoped_agreement : ProgramAgreementOn RetainedMatchingWire.scopedPrimitiveHeads
    RuleExecutionProgram.scopedMachineProgram CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime :=
  agreement_trans RetainedMatchingWire.scopedPrimitive_agreement
    (agreement_mono scoped_supported CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement)

theorem admission_returns (host : Effects.State) (rule : RewriteRule) (spec : RuleBindingSpec) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:premise:binding-admitted"
        [encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule),
          encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)]) host
      (Effects.boolean (RuleBinding.admittedFor rule spec)) := by
  refine transport_call RetainedMatchingWire.scopedPrimitive_closed scoped_agreement
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
    ["rule", "spec"] (by decide) (by rfl) ?_
    (PremiseOperationsExecution.GeneralExecution.AdmissionLower.Assembly.admitted_returns host rule spec)
  intro index bounded
  have small : index < 2 := by simpa using bounded
  interval_cases index <;> decide +kernel

theorem sorting_returns (host : Effects.State) (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (type : TypeExpr) (pattern : Pattern) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:premise:open-well-sorted"
        [encoded (encodeList InferenceCettaWire.AuthoredRule.typingDeclarationTerm language.terms),
          encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm free),
          encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm bound),
          encoded (InferenceCettaWire.AuthoredRule.typeTerm type), encoded (InferenceCettaWire.encodePattern pattern)]) host
      (Effects.boolean (WellSorted.checkOpenPatternWellSorted language
        (WellSorted.FreeTypeContext.ofList free) bound type pattern)) := by
  refine transport_call RetainedMatchingWire.scopedPrimitive_closed scoped_agreement
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
    ["declarations", "free", "bound", "type", "pattern"] (by decide) (by rfl) ?_
    (PremiseOperationsExecution.GeneralExecution.MatcherFrames.Checkers.sorted_returns [] host language free bound
      type pattern _ _ _ _ _ (by simp))
  intro index bounded
  have small : index < 5 := by simpa using bounded
  interval_cases index <;> decide +kernel

#print axioms metadata_agreement
#print axioms scoped_supported
#print axioms scoped_agreement
#print axioms admission_returns
#print axioms sorting_returns
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceCollectorExecution.Selected


namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceCollectorExecution.Selected
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open SpaceSemantics Eval BridgeKit WireKit

theorem canonical_environment_returns (host : Effects.State) (names : List String) (core : Term) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:premise:matching-environment"
        [encoded (RetainedMatchingWire.interpretedEnvironmentTerm names core)]) host (encoded core) := by
  metta_call_in Interpreted.metadata_checked using metadata_agreement
  metta_eval with Interpreted.metadata_checked in metadata_agreement unfolding
    [RetainedMatchingWire.interpretedEnvironmentTerm,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
      CettaWireAtom.encode, CettaWireAtom.encodeMany]

theorem ordinary_environment_returns (host : Effects.State) (environment : GeneralPremise.Environment)
    (table : List (String × TypeExpr)) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:premise:matching-environment"
        [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment table)]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment table)) := by
  metta_call_in Interpreted.metadata_checked using metadata_agreement
  metta_eval with Interpreted.metadata_checked in metadata_agreement unfolding
    [PremiseOperationsExecution.GeneralExecution.environmentTerm,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
      CettaWireAtom.encode, CettaWireAtom.encodeMany]

#print axioms canonical_environment_returns
#print axioms ordinary_environment_returns
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceCollectorExecution.Selected


namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceCollectorExecution.Selected
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise CanonicalCompare CollectionOccurrenceBatch CollectionOccurrenceMatcher
open SpaceSemantics Eval BridgeKit WireKit

private local instance allocationEquationEq : DecidableEq SpaceSemantics.Equation :=
  SpaceSemantics.Equation.decideEq

/-- Batch bodies are unchanged when the declared continuation profile is selected. -/
theorem canonical_batch_body_agreement : ProgramAgreementOn CollectionOccurrenceBatchExecution.batchBodyHeads
    CollectionOccurrenceBatchExecution.batchBodyLibrary.runtime
    CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

private theorem canonical_begin_dispatch :
    (ioHead "gslt:collection-continuation:begin" || StdLib.known "gslt:collection-continuation:begin" ||
      CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime.equations.any
        (·.head == "gslt:collection-continuation:begin")) = true := by
  rw [← RecursiveCollectionContinuationExecution.Canonical.SelectedPostmatch.view_agreement.dispatch _ (by decide +kernel)]
  decide +kernel

private theorem canonical_begin_raw : ∀ index < 8,
    argumentIsRaw CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime
      "gslt:collection-continuation:begin" index = true := by
  intro index bounded
  rw [← RecursiveCollectionContinuationExecution.Canonical.SelectedPostmatch.view_agreement.demand _ index (by decide +kernel)]
  interval_cases index <;> decide +kernel

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}

/-- The shared batch initializer consumes the original producer's canonical seed. -/
theorem canonical_frame_begin_returns (host : Effects.State)
    (allocation : Allocation plan bound expected (CanonicalBags.canon source))
    (names footprint : List String)
    (inside : ∀ name ∈ allocation.request.source.freeFvarNames, name ∈ footprint) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-batch:frame-begin"
        [encoded (CollectionOccurrenceBatchExecution.originTerm allocation.job allocation.answer),
          encoded (RecursiveCollectionContinuationExecution.Canonical.SelectedPostmatch.environmentTerm
            allocation.request names footprint), number allocation.request.depth,
          encoded (CompleteExecution.DescentCodec.typesTerm allocation.request.bound),
          encoded (CompleteExecution.DescentCodec.typeTerm allocation.request.type), number allocation.request.index,
          encoded (InferenceCettaWire.AuthoredRule.rewriteTerm allocation.request.rule),
          encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm allocation.request.spec),
          encoded (RecursiveCollectionHandoffExecution.preparedTerm allocation.request.prepared)]) host
      (encoded (CollectionOccurrenceBatchExecution.frameTermWith RetainedMatchingWire.canonicalCodec
        (Frame.initialWith (canonicalSeedProfile plan bound expected source) allocation))) := by
  have seeded := RecursiveCollectionContinuationExecution.Canonical.SelectedPostmatch.begin_returns host
    allocation.request RetainedMatchingWire.canonicalCodec rfl names footprint inside allocation.canonical_seed
  apply CollectionOccurrenceBatchExecution.frame_begin_with_returns _ canonical_batch_body_agreement host
    (RecursiveCollectionContinuationExecution.Canonical.SelectedPostmatch.environmentTerm allocation.request names footprint)
    RetainedMatchingWire.canonicalCodec (canonicalSeedProfile plan bound expected source) allocation
    canonical_begin_dispatch canonical_begin_raw
  simpa only [Frame.initialWith_canonical, Frame.initialCanonical,
    RecursiveCollectionContinuationExecution.Canonical.SelectedPostmatch.frameTermWith] using seeded

/-- Preparation replays the real published allocation in the selected runtime. -/
theorem prepared_published_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (job : CollectionOccurrenceHandoff.Job) (work : Nat) (answer : RecursiveCollectionMachine.Answer)
    (published : Published job work answer) (covered : Covered names job.request.target) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:collection-handoff:prepare" [encoded (encodeList Term.string names),
        encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm job.request),
        encoded (RecursiveCollectionExecution.answerTerm answer)]) host
      (encoded (encodeOption RecursiveCollectionHandoffExecution.preparedTerm
        (RecursiveCollectionHandoff.prepare job.request answer))) := by
  have preparationAgreement := RecursiveCollectionHandoffExecution.handoffProof_agreement
  simp only [RecursiveCollectionHandoffExecution.library, RetainedMatchingWire.interpreted_runtime] at preparationAgreement
  apply transport_call CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_closed
    CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement
    (by decide +kernel) (by decide)
    (by rw [← preparationAgreement.dispatch _ (by decide +kernel)]; decide +kernel)
    (by decide) ["names", "request", "answer"] (by decide) (by rfl)
    (by
      intro index bounded
      have small : index < 3 := by simpa using bounded
      rw [← preparationAgreement.demand _ index (by decide +kernel)]
      interval_cases index <;> decide +kernel)
  simpa only [RecursiveCollectionHandoffExecution.library, RetainedMatchingWire.interpreted_runtime] using
    RecursiveCollectionHandoffExecution.prepare_returns host names ordered job.request answer
      (RecursiveCollectionMachine.published_trace_valid job.request work published) covered

/-- Every positive collector operation is realized from its actual publication,
local checks, exact preparation, and original canonical seed. -/
theorem allocated_canonical_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (footprint : List String) (job : CollectionOccurrenceHandoff.Job)
    (licensed : job.Valid plan bound expected (CanonicalBags.canon source))
    (work depth : Nat) (answer : RecursiveCollectionMachine.Answer) (published : Published job work answer)
    (inside : ∀ name ∈ job.variant.site.focus.freeFvarNames, name ∈ footprint)
    (covered : Covered names job.request.target)
    (allocation : Allocation plan bound expected (CanonicalBags.canon source))
    (made : allocate? job licensed work answer published depth = some allocation) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-collector:allocate"
        [encoded (encodeList Term.string names),
          encoded (RetainedMatchingWire.interpretedEnvironmentTerm names
            (PremiseOperationsExecution.GeneralExecution.environmentTerm (GeneralPlanEnvironment.environment plan)
              ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint))),
          number depth, encoded (Interpreted.originTerm job),
          encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm job.request),
          encoded (RecursiveCollectionExecution.answerTerm answer)]) host
      (encoded (.application "Some" [CollectionOccurrenceBatchExecution.frameTermWith
        RetainedMatchingWire.canonicalCodec
          (Frame.initialWith (canonicalSeedProfile plan bound expected source) allocation)])) := by
  have sameJob := (allocate_readout job licensed work depth answer published made).1
  obtain ⟨requestDepth, requestBound, requestType, requestSource, requestIndex,
    requestRule, requestSpec, requestAnswer⟩ := allocation.request_fields
  have requestInside : ∀ name ∈ allocation.request.source.freeFvarNames, name ∈ footprint := by
    intro name member
    rw [requestSource, sameJob] at member
    exact inside name member
  have begun := canonical_frame_begin_returns host allocation names footprint requestInside
  apply Interpreted.allocated_returns_with _ metadata_agreement host names footprint
    (RetainedMatchingWire.interpretedEnvironmentTerm names
      (PremiseOperationsExecution.GeneralExecution.environmentTerm (GeneralPlanEnvironment.environment plan)
        ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint)))
    RetainedMatchingWire.canonicalCodec (canonicalSeedProfile plan bound expected source)
    job licensed work depth answer published inside allocation made
  · exact canonical_environment_returns host names _
  · exact admission_returns host job.origin.declaration.rule job.origin.declaration.binding.spec
  · exact sorting_returns host (GeneralPlanEnvironment.environment plan).language
      ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint)
      job.variant.site.focusBound job.variant.site.focusType job.variant.site.focus
  · exact prepared_published_returns host names ordered job work answer published covered
  · simpa only [RecursiveCollectionContinuationExecution.Canonical.SelectedPostmatch.environmentTerm,
      allocation.request_origin.1] using begun

#print axioms canonical_batch_body_agreement
#print axioms canonical_begin_dispatch
#print axioms canonical_begin_raw
#print axioms canonical_frame_begin_returns
#print axioms prepared_published_returns
#print axioms allocated_canonical_returns
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceCollectorExecution.Selected


namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceCollectorExecution.Selected.Canonical
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise CanonicalCompare CollectionOccurrenceBatch CollectionOccurrenceMatcher
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics Eval BridgeKit WireKit

private local instance collectorEquationEq : DecidableEq SpaceSemantics.Equation :=
  SpaceSemantics.Equation.decideEq

private def loopMetadataBase : Program :=
  (RuleExecutionProgram.callFragment ["gslt:automata:append"] RuleExecutionProgram.scopedProgram).append
    (RuleExecutionProgram.callFragment ["gslt:occurrence-matcher:advance"]
      (RuleExecutionProgram.interpretedPremiseSupportSources[16]'(by decide +kernel)).program)

def loopLibrary : Library := ⟨loopMetadataBase, CollectionOccurrenceSearchExecution.SelectedNativeSource.collectorSource.program,
  ["gslt:occurrence-collector:"]⟩
def loopHeads (head : String) : Bool := !head.startsWith "gslt:" || loopLibrary.owns head ||
  ["gslt:automata:append", "gslt:occurrence-matcher:advance"].contains head

theorem loop_checked : loopLibrary.check = true := by decide +kernel

theorem loop_agreement : ProgramAgreementOn loopHeads loopLibrary.runtime
    CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

private theorem matchValue_variable (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (name : String) (value : Atom) :
    matchValue bindings (.var name) value = Mettapedia.Languages.ProcessCalculi.MORK.matchAtom bindings (.var name) value := by
  cases value <;> simp only [matchValue]

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr} {expected : TypeExpr} {sourcePattern : Pattern}

def environmentTerm (plan : GeneralExecutionAdmission.Plan) (names footprint : List String) : Term :=
  RetainedMatchingWire.interpretedEnvironmentTerm names
    (PremiseOperationsExecution.GeneralExecution.environmentTerm (GeneralPlanEnvironment.environment plan)
      ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint))

def frameTerm (frame : Frame plan bound expected sourcePattern RecursiveCollectionHandoff.canonicalMatchingExecution) : Term :=
  CollectionOccurrenceBatchExecution.frameTermWith RetainedMatchingWire.canonicalCodec frame

syntax "canonical_collector_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| canonical_collector_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in loop_checked using loop_agreement; metta_eval [$facts,*] with loop_checked in loop_agreement unfolding
      [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, encodeList,
        frameTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany, matchValue_variable, $extra,*]))

theorem collected_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (footprint : List String) (job : CollectionOccurrenceHandoff.Job)
    (licensed : job.Valid plan bound expected (CanonicalBags.canon sourcePattern))
    (work depth : Nat) (answers : List RecursiveCollectionMachine.Answer)
    (published : ∀ answer ∈ answers, Published job work answer)
    (covered : Covered names job.request.target)
    (inside : ∀ name ∈ job.variant.site.focus.freeFvarNames, name ∈ footprint)
    (admitted : RuleBinding.admittedFor job.origin.declaration.rule job.origin.declaration.binding.spec = true)
    (sorted : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language (GeneralPlanEnvironment.environment plan).free
      job.variant.site.focusBound job.variant.site.focusType job.variant.site.focus) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-collector:collect"
        [encoded (encodeList Term.string names), encoded (environmentTerm plan names footprint), number depth,
          encoded (Interpreted.originTerm job),
          encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm job.request),
          encoded (encodeList RecursiveCollectionExecution.answerTerm answers)]) host
      (encoded (encodeList frameTerm ((collect job licensed work depth answers published).map Frame.initialCanonical))) := by
  induction answers with
  | nil => canonical_collector_eval unfolding [CollectionOccurrenceMatcher.collect]
  | cons answer answers ih =>
    have firstPublished := published answer List.mem_cons_self
    obtain ⟨allocation, made, _, _⟩ := allocate_published_exists job licensed work depth answer firstPublished admitted sorted
    have first := allocated_canonical_returns host names ordered footprint job licensed work depth answer firstPublished
      inside covered allocation made
    have rest := ih (fun next member => published next (List.mem_cons_of_mem _ member))
    simp only [Frame.initialWith_canonical] at first
    canonical_collector_eval [first, rest] unfolding
      [CollectionOccurrenceMatcher.collect, made, Option.toList_some, List.singleton_append, List.map_cons, environmentTerm]

structure LaneReady (names footprint : List String)
    (lane : Lane plan bound expected sourcePattern) : Prop where
  state : RecursiveCollectionMachine.StateCovered names lane.state
  target : Covered names lane.job.request.target
  free : ∀ name ∈ lane.job.variant.site.focus.freeFvarNames, name ∈ footprint
  admitted : RuleBinding.admittedFor lane.job.origin.declaration.rule lane.job.origin.declaration.binding.spec = true
  sorted : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
    (GeneralPlanEnvironment.environment plan).language (GeneralPlanEnvironment.environment plan).free
    lane.job.variant.site.focusBound lane.job.variant.site.focusType lane.job.variant.site.focus

private theorem matcher_advance_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (lane : Lane plan bound expected sourcePattern) (covered : RecursiveCollectionMachine.StateCovered names lane.state) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-matcher:advance" [encoded (encodeList Term.string names),
        encoded (CollectionOccurrenceMatcherExecution.laneTerm lane)]) host
      (encoded (CollectionOccurrenceMatcherExecution.advancedTerm lane)) := by
  have metadata := CollectionOccurrenceMatcherExecution.matcherProof_agreement
  simp only [CollectionOccurrenceMatcherExecution.library, RetainedMatchingWire.interpreted_runtime] at metadata
  apply transport_call CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_closed
    CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement (by decide +kernel) (by decide)
    (by rw [← metadata.dispatch _ (by decide +kernel)]; decide +kernel) (by decide)
    ["names", "lane"] (by decide) (by rfl)
    (by intro index bounded; have small : index < 2 := by simpa using bounded
        rw [← metadata.demand _ index (by decide +kernel)]; interval_cases index <;> decide +kernel)
  simpa only [CollectionOccurrenceMatcherExecution.library, RetainedMatchingWire.interpreted_runtime] using
    CollectionOccurrenceMatcherExecution.advance_returns host names ordered lane covered

theorem advance_lane_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (footprint : List String) (lane : Lane plan bound expected (CanonicalBags.canon sourcePattern)) (depth : Nat)
    (ready : LaneReady names footprint lane) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-collector:advance-lane" [encoded (encodeList Term.string names),
        encoded (environmentTerm plan names footprint), number depth,
        encoded (CollectionOccurrenceMatcherExecution.laneTerm lane)]) host
      (encoded (.application "RecursiveOccurrenceLaneAllocations"
        [CollectionOccurrenceMatcherExecution.laneTerm (lane.resume 1),
          encodeList frameTerm ((lane.allocations depth).map Frame.initialCanonical)])) := by
  have advanced := matcher_advance_returns host names ordered lane ready.state
  have collected := collected_returns host names ordered footprint lane.job lane.licensed (lane.spent + 1) depth lane.fresh
    (fun answer member => (lane.resume 1).published answer (List.mem_of_mem_drop member))
    ready.target ready.free ready.admitted ready.sorted
  canonical_collector_eval [advanced, collected] unfolding
    [CollectionOccurrenceMatcherExecution.laneTerm, CollectionOccurrenceMatcherExecution.advancedTerm,
      Lane.allocations, Interpreted.originTerm, CollectionOccurrenceMatcherExecution.originTerm]

private theorem append_returns {α : Type} (encoder : α → Term) (host : Effects.State) (left right : List α) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:automata:append" [encoded (encodeList encoder left), encoded (encodeList encoder right)]) host
      (encoded (encodeList encoder (left ++ right))) := by
  have metadata := CollectionOccurrenceBatchExecution.batchPrimitive_agreement
  apply transport_call CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_closed
    CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement (by decide +kernel) (by decide)
    (by rw [← metadata.dispatch _ (by decide +kernel)]; decide +kernel)
    (by decide) ["left", "right"] (by decide) (by rfl)
    (by intro index bounded; have small : index < 2 := by simpa using bounded
        rw [← metadata.demand _ index (by decide +kernel)]
        interval_cases index <;> decide +kernel)
  exact CollectionSelectionExecution.scoped_append_returns encoder host left right

def advancedLanesTerm (depth : Nat) (lanes : List (Lane plan bound expected (CanonicalBags.canon sourcePattern))) : Term :=
  .application "RecursiveOccurrenceLanesAllocations"
    [encodeList CollectionOccurrenceMatcherExecution.laneTerm (lanes.map (Lane.resume 1)),
      encodeList frameTerm ((lanes.flatMap (Lane.allocations depth)).map Frame.initialCanonical)]

theorem advance_lanes_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (footprint : List String) (depth : Nat) :
    ∀ lanes : List (Lane plan bound expected (CanonicalBags.canon sourcePattern)),
    (∀ lane ∈ lanes, LaneReady names footprint lane) →
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-collector:advance-lanes" [encoded (encodeList Term.string names),
        encoded (environmentTerm plan names footprint), number depth,
        encoded (encodeList CollectionOccurrenceMatcherExecution.laneTerm lanes)]) host
      (encoded (advancedLanesTerm depth lanes))
  | [], _ => by canonical_collector_eval unfolding [advancedLanesTerm]
  | lane :: lanes, ready => by
    have first := advance_lane_returns host names ordered footprint lane depth (ready lane List.mem_cons_self)
    have later := advance_lanes_returns host names ordered footprint depth lanes
      (fun next member => ready next (List.mem_cons_of_mem _ member))
    have joined := append_returns frameTerm host ((lane.allocations depth).map Frame.initialCanonical)
      ((lanes.flatMap (Lane.allocations depth)).map Frame.initialCanonical)
    simp only [advancedLanesTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] at later
    canonical_collector_eval [first, later, joined] unfolding
      [advancedLanesTerm, List.flatMap_cons, List.map_append]

#print axioms loop_checked
#print axioms loop_agreement
#print axioms collected_returns
#print axioms matcher_advance_returns
#print axioms advance_lane_returns
#print axioms append_returns
#print axioms advance_lanes_returns
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceCollectorExecution.Selected.Canonical


namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceCollectorExecution
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax CollectionOccurrenceBatch CollectionOccurrenceMatcher CanonicalCompare
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics Eval BridgeKit WireKit CollectionOccurrenceRuntime
variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
  {expected : TypeExpr} {sourcePattern : Pattern}
syntax "collector_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| collector_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| canonical_collector_eval [$facts,*] unfolding
      [CompleteExecution.environmentValue, CollectionOccurrenceBatchExecution.frameTerm, $extra,*])


/-- Every successful mathematical allocation is realized by the native
collector. `made` is the actual producer computation, not a supplied target
execution or source-completeness premise. -/
@[metta_head "gslt:occurrence-collector:allocate"]
theorem allocated_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (footprint : List String) (job : CollectionOccurrenceHandoff.Job)
    (licensed : job.Valid plan bound expected sourcePattern)
    (work depth : Nat) (answer : RecursiveCollectionMachine.Answer)
    (published : Published job work answer)
    (covered : Covered names job.request.target)
    (inside : ∀ name ∈ job.variant.site.focus.freeFvarNames, name ∈ footprint)
    (allocation : Allocation plan bound expected sourcePattern)
    (made : allocate? job licensed work answer published depth = some allocation) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-collector:allocate"
        [encoded (encodeList Term.string names),
          CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
            ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number depth, encoded (CollectionOccurrenceMatcherExecution.originTerm job),
          encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm job.request),
          encoded (RecursiveCollectionExecution.answerTerm answer)])
      host (encoded (.application "Some" [CollectionOccurrenceBatchExecution.frameTerm (Frame.initial allocation)])) := by
  have sameJob := (allocate_readout job licensed work depth answer published made).1
  have requestInside : ∀ name ∈ allocation.request.source.freeFvarNames, name ∈ footprint := by
    intro name member
    rw [allocation.request_fields.2.2.2.1, sameJob] at member
    exact inside name member
  have begun := CollectionOccurrenceBatchExecution.frame_begin_returns host allocation footprint requestInside
  have result := Interpreted.allocated_returns_with _ Selected.metadata_agreement host names footprint
    (PremiseOperationsExecution.GeneralExecution.environmentTerm (GeneralPlanEnvironment.environment plan)
      ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint))
    RetainedMatchingWire.ordinaryCodec (ordinarySeedProfile plan bound expected sourcePattern)
    job licensed work depth answer published inside allocation made
    (Selected.ordinary_environment_returns host _ _)
    (Selected.admission_returns host job.origin.declaration.rule job.origin.declaration.binding.spec)
    (Selected.sorting_returns host (GeneralPlanEnvironment.environment plan).language
      ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint)
      job.variant.site.focusBound job.variant.site.focusType job.variant.site.focus)
    (Selected.prepared_published_returns host names ordered job work answer published covered)
    (by
      simpa only [Frame.initialWith_ordinary, CollectionOccurrenceBatchExecution.frameTermWith_ordinary,
        allocation.request_origin.1, CompleteExecution.environmentValue,
        CollectionOccurrenceBatchExecution.library,
        CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime_same] using begun)
  simpa only [Frame.initialWith_ordinary, CollectionOccurrenceBatchExecution.frameTermWith_ordinary,
    CompleteExecution.environmentValue, Interpreted.originTerm,
    CollectionOccurrenceMatcherExecution.originTerm, library,
    CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime_same] using result

/-- Collecting a published answer suffix realizes the mathematical account
in its original order. Local source admission guarantees that every valid
answer enters its own retained continuation. -/
@[metta_head "gslt:occurrence-collector:collect"]
theorem collected_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (footprint : List String) (job : CollectionOccurrenceHandoff.Job)
    (licensed : job.Valid plan bound expected sourcePattern)
    (work depth : Nat) (answers : List RecursiveCollectionMachine.Answer)
    (published : ∀ answer ∈ answers, Published job work answer)
    (covered : Covered names job.request.target)
    (inside : ∀ name ∈ job.variant.site.focus.freeFvarNames, name ∈ footprint)
    (admitted : RuleBinding.admittedFor job.origin.declaration.rule
      job.origin.declaration.binding.spec = true)
    (sorted : WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language (GeneralPlanEnvironment.environment plan).free
      job.variant.site.focusBound job.variant.site.focusType job.variant.site.focus) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-collector:collect"
        [encoded (encodeList Term.string names),
          CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
            ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number depth, encoded (CollectionOccurrenceMatcherExecution.originTerm job),
          encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm job.request),
          encoded (encodeList RecursiveCollectionExecution.answerTerm answers)])
      host (encoded (encodeList CollectionOccurrenceBatchExecution.frameTerm
        ((collect job licensed work depth answers published).map Frame.initial))) := by
  rw [library, CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime_same]
  induction answers with
  | nil => collector_eval unfolding [CollectionOccurrenceMatcher.collect, CettaWire.encodeList]
  | cons answer answers ih =>
    have firstPublished := published answer List.mem_cons_self
    obtain ⟨allocation, made, _, _⟩ := allocate_published_exists job licensed work depth
      answer firstPublished admitted sorted
    have first := allocated_returns host names ordered footprint job licensed work depth
      answer firstPublished covered inside allocation made
    have rest := ih (fun next member => published next (List.mem_cons_of_mem _ member))
    collector_eval [first, rest] unfolding
      [CollectionOccurrenceMatcher.collect, made, Option.toList_some, List.singleton_append, List.map_cons, CettaWire.encodeList]

/-- One native matching quantum returns the resumed lane and precisely the
fresh allocation frames. Existing continuation states are not reconstructed. -/
@[metta_head "gslt:occurrence-collector:advance-lane"]
theorem advance_lane_returns (host : Effects.State) (names : List String)
    (ordered : NameOrdered names) (footprint : List String)
    (lane : Lane plan bound expected sourcePattern) (depth : Nat)
    (stateCovered : RecursiveCollectionMachine.StateCovered names lane.state)
    (targetCovered : Covered names lane.job.request.target)
    (inside : ∀ name ∈ lane.job.variant.site.focus.freeFvarNames, name ∈ footprint)
    (admitted : RuleBinding.admittedFor lane.job.origin.declaration.rule
      lane.job.origin.declaration.binding.spec = true)
    (sorted : WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language (GeneralPlanEnvironment.environment plan).free
      lane.job.variant.site.focusBound lane.job.variant.site.focusType lane.job.variant.site.focus) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-collector:advance-lane"
        [encoded (encodeList Term.string names),
          CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
            ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number depth, encoded (CollectionOccurrenceMatcherExecution.laneTerm lane)])
      host (encoded (.application "RecursiveOccurrenceLaneAllocations"
        [CollectionOccurrenceMatcherExecution.laneTerm (lane.resume 1),
          encodeList CollectionOccurrenceBatchExecution.frameTerm
            ((lane.allocations depth).map Frame.initial)])) := by
  rw [library, CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime_same]
  have advanced := occurrence_from_matcher% ["names", "lane"]
    (CollectionOccurrenceMatcherExecution.advance_returns host names ordered lane stateCovered)
  have collected := collected_returns host names ordered footprint lane.job lane.licensed
    (lane.spent + 1) depth lane.fresh
    (fun answer member => (lane.resume 1).published answer (List.mem_of_mem_drop member))
    targetCovered inside admitted sorted
  collector_eval [advanced, collected] unfolding
    [CollectionOccurrenceMatcherExecution.laneTerm,
      CollectionOccurrenceMatcherExecution.advancedTerm, Lane.allocations]

/-- Finite codec coverage and the same local checks used by allocation.
These are representation preconditions, not successor-coverage assumptions. -/
structure LaneReady (names footprint : List String)
    (lane : Lane plan bound expected sourcePattern) : Prop where
  state : RecursiveCollectionMachine.StateCovered names lane.state
  target : Covered names lane.job.request.target
  free : ∀ name ∈ lane.job.variant.site.focus.freeFvarNames, name ∈ footprint
  admitted : RuleBinding.admittedFor lane.job.origin.declaration.rule
    lane.job.origin.declaration.binding.spec = true
  sorted : WellSorted.OpenPatternWellSorted
    (GeneralPlanEnvironment.environment plan).language (GeneralPlanEnvironment.environment plan).free
    lane.job.variant.site.focusBound lane.job.variant.site.focusType lane.job.variant.site.focus

private theorem append_returns {α : Type} (encoder : α → Term) (host : Effects.State)
    (left right : List α) :
    PureReturns library.runtime [] host
      (apply "gslt:automata:append"
        [encoded (encodeList encoder left), encoded (encodeList encoder right)])
      host (encoded (encodeList encoder (left ++ right))) := by
  exact occurrence_batch_from_lower% ["left", "right"]
    (CollectionSelectionExecution.scoped_append_returns encoder host left right)

def advancedLanesTerm (depth : Nat) (lanes : List (Lane plan bound expected sourcePattern)) : Term :=
  .application "RecursiveOccurrenceLanesAllocations"
    [encodeList CollectionOccurrenceMatcherExecution.laneTerm (lanes.map (Lane.resume 1)),
      encodeList CollectionOccurrenceBatchExecution.frameTerm
        ((lanes.flatMap (Lane.allocations depth)).map Frame.initial)]

/-- The native list traversal preserves the authored lane order and the
complete fresh allocation account before installation into retained work. -/
@[metta_head "gslt:occurrence-collector:advance-lanes"]
theorem advance_lanes_returns (host : Effects.State) (names : List String)
    (ordered : NameOrdered names) (footprint : List String) (depth : Nat) :
    ∀ lanes : List (Lane plan bound expected sourcePattern),
      (∀ lane ∈ lanes, LaneReady names footprint lane) →
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-collector:advance-lanes"
        [encoded (encodeList Term.string names),
          CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
            ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number depth, encoded (encodeList CollectionOccurrenceMatcherExecution.laneTerm lanes)])
      host (encoded (advancedLanesTerm depth lanes))
  | [], _ => by collector_eval unfolding [advancedLanesTerm, encodeList]
  | lane :: lanes, ready => by
    have firstReady := ready lane List.mem_cons_self
    have first := advance_lane_returns host names ordered footprint lane depth
      firstReady.state firstReady.target firstReady.free firstReady.admitted firstReady.sorted
    have rest := advance_lanes_returns host names ordered footprint depth lanes
      (fun next member => ready next (List.mem_cons_of_mem _ member))
    have joined := append_returns CollectionOccurrenceBatchExecution.frameTerm host
      ((lane.allocations depth).map Frame.initial)
      ((lanes.flatMap (Lane.allocations depth)).map Frame.initial)
    collector_eval [first, rest, joined] unfolding
      [advancedLanesTerm, List.flatMap_cons, List.map_append, List.map_cons, encodeList]

#print axioms allocated_returns
#print axioms collected_returns
#print axioms advance_lane_returns
#print axioms append_returns
#print axioms advance_lanes_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceCollectorExecution
