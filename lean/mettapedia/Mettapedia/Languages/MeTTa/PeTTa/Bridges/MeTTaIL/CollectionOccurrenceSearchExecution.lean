import Mettapedia.Languages.MeTTa.PeTTa.BridgeTransport
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.StandardWire
import Mettapedia.OSLF.MeTTaIL.GeneralTypedSitesFocus
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataInventoryExecution
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrencePublication
import Mettapedia.OSLF.MeTTaIL.Complete.ClassesReady
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceDiscoveryExecution

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompletePlanWire
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
/-- The environment metadata is selected explicitly; all other plan fields
come from the same plan and retain their declaration order. -/
def planTermWithEnvironment (plan : GeneralExecutionAdmission.Plan) (environment : Term)
    (bound : List TypeExpr) (expected : TypeExpr) : Term :=
  .application "CompletePlan"
    [environment,
     InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites,
     CettaWire.encodeList InferenceCettaWire.AuthoredRule.typeTerm bound,
     InferenceCettaWire.AuthoredRule.typeTerm expected,
     CettaWire.encodeList ScopedRuleJobReadoutExecution.rulePlanTerm plan.rules,
     CettaWire.encodeList (equationDeclarationTerm plan) plan.equations.zipIdx,
     admittedTerm (StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan))]


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompletePlanWire

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.Interpreted

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise ScopedRuleMatching GeneralRuleJobs
open CollectionOccurrenceBatch CollectionOccurrenceHandoff
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics Eval BridgeKit WireKit

syntax "readout_eval" " using " "(" term ")" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| readout_eval using ($agreement) $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic|
      (metta_call_in metadata_checked using $agreement
       metta_eval [$facts,*] with metadata_checked in $agreement unfolding
        [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
          Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, $extra,*]))

private def fillSupport (head : String) : Bool :=
  ScopedRuleJobReadoutExecution.executionHeads head &&
    head != "gslt:rule:job-finish-root" && head != "gslt:rule:site-replacement-represented"

private theorem fill_closed : ProgramClosed fillSupport RuleExecutionProgram.program := by
  exact BridgeKit.closed_of_all _ _ (by decide +kernel) (by decide +kernel)

private theorem fill_job_agreement :
    ProgramAgreementOn fillSupport RuleExecutionProgram.program ScopedRuleJobReadoutExecution.runtime := by
  apply appended_program_agreement
  · intro equation member
    have checked : ScopedRuleJobReadoutExecution.sourceProgram.equations.all
        (fun equation => !fillSupport equation.head) = true := by decide +kernel
    have row := List.all_eq_true.mp checked equation member
    cases selected : fillSupport equation.head with
    | false => rfl
    | true => simp [selected] at row
  · intro name types member
    have checked : ScopedRuleJobReadoutExecution.sourceProgram.declarations.all (fun declaration => match declaration with
        | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] => !fillSupport head
        | _ => true) = true := by decide +kernel
    have row := List.all_eq_true.mp checked
      (.expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]) member
    cases selected : fillSupport name with
    | false => rfl
    | true => simp [selected] at row

variable (program : Program)
    (agreement : ProgramAgreementOn metadataHeads metadataLibrary.runtime program)
    (primitiveAgreement : ProgramAgreementOn ScopedRuleJobReadoutExecution.executionHeads
      ScopedRuleJobReadoutExecution.runtime program)

include primitiveAgreement in
theorem fill_returns (host : Effects.State) (context : GeneralTypedSites.SiteData) (pattern : Pattern) :
    PureReturns program [] host
      (apply "gslt:rule:scope-fill"
        [encoded (InferenceCettaWire.ContextObservation.contextTerm context.context),
          encoded (InferenceCettaWire.encodePattern pattern)])
      host (encoded (InferenceCettaWire.encodePattern (context.context.fill pattern))) := by
  have within : ∀ head, fillSupport head = true → ScopedRuleJobReadoutExecution.executionHeads head = true := by
    intro head supported
    simp only [fillSupport, Bool.and_eq_true] at supported
    exact supported.1.1
  have agreed := agreement_trans fill_job_agreement (agreement_mono within primitiveAgreement)
  refine transport_call fill_closed agreed (head := "gslt:rule:scope-fill")
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
    ["context", "pattern"] (by decide) (by rfl) ?_
    (RuleInstantiationExecution.ContextObservation.fill_returns host context.context pattern)
  intro index bounded
  have small : index < 2 := by simpa using bounded
  interval_cases index <;> decide +kernel

include primitiveAgreement in
theorem finish_root_returns {Choice : Type}
    (choiceTerm : Choice → Term) (meaning : MatchingInterpretation Choice)
    (host : Effects.State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (footprint : List String) (trace : List Choice) (captured completed : Assignment)
    (history : List (GeneralPremise.Event Choice)) (localTarget : Pattern)
    (valid : GeneralPremise.Interpreted.RootFiring meaning request.environment request.job.site.focusBound
      request.job.site.focusType request.job.site.focus request.job.ordinal
      trace captured completed history localTarget)
    (covered : ∀ name ∈ (request.job.site.context.fill localTarget).freeFvarNames, name ∈ footprint) :
    PureReturns program [] host
      (ScopedRuleJobReadoutExecution.finishRootQueryWith choiceTerm request footprint trace captured completed history localTarget)
      host (encoded (encodeOption (ScopedRuleJobReadoutExecution.receiptTermWith choiceTerm)
        (GeneralRuleJobs.finish? request.plan request.bound request.expected request.job trace captured completed history))) := by
  refine transport_call ScopedRuleJobReadoutExecution.runtime_closed primitiveAgreement
    (head := "gslt:rule:job-finish-root") (by decide +kernel) (by decide)
    (by decide +kernel) (by decide) ["request", "result"] (by decide) (by rfl) ?_
    (ScopedRuleJobReadoutExecution.finish_root_interpreted_readout_returns choiceTerm meaning host request licensed
      footprint trace captured completed history localTarget valid covered)
  intro index bounded
  have small : index < 2 := by simpa using bounded
  interval_cases index <;> decide +kernel

include agreement in
theorem canonical_environment_returns (host : Effects.State) (names : List String) (core : Term) :
    PureReturns program [] host
      (apply "gslt:premise:matching-environment"
        [encoded (RetainedMatchingWire.interpretedEnvironmentTerm names core)]) host (encoded core) := by
  readout_eval using (agreement) unfolding [RetainedMatchingWire.interpretedEnvironmentTerm]

include agreement in
theorem ordinary_environment_returns (host : Effects.State) (environment : GeneralPremise.Environment)
    (table : List (String × TypeExpr)) :
    PureReturns program [] host
      (apply "gslt:premise:matching-environment"
        [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment table)])
      host (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment table)) := by
  readout_eval using (agreement) unfolding [PremiseOperationsExecution.GeneralExecution.environmentTerm]

#print axioms metadata_checked
#print axioms fill_returns
#print axioms finish_root_returns
#print axioms canonical_environment_returns
#print axioms ordinary_environment_returns
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.Interpreted


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.Interpreted

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise ScopedRuleMatching GeneralRuleJobs
open CollectionOccurrenceBatch CollectionOccurrenceHandoff CollectionCommittedObservation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics Eval BridgeKit WireKit

variable (program : Program)
    (agreement : ProgramAgreementOn metadataHeads metadataLibrary.runtime program)
    (primitiveAgreement : ProgramAgreementOn ScopedRuleJobReadoutExecution.executionHeads
      ScopedRuleJobReadoutExecution.runtime program)
variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr} {expected : TypeExpr}

def interpretedPlanTerm (names : List String) (plan : GeneralExecutionAdmission.Plan)
    (footprint : List String) (bound : List TypeExpr) (expected : TypeExpr) : Term :=
  CompletePlanWire.planTermWithEnvironment plan
    (RetainedMatchingWire.interpretedEnvironmentTerm names
      (PremiseOperationsExecution.GeneralExecution.environmentTerm (GeneralPlanEnvironment.environment plan)
        (plan.snapshot.free.entriesOn footprint))) bound expected

include agreement primitiveAgreement in
theorem canonical_finish_returns (host : Effects.State) (names footprint : List String)
    (packet : Publication EquationalScopedReceipts.Event)
    (ready : packet.FinishReadyIn RecursiveCollectionHandoff.canonicalMatchingInterpretation plan bound expected
      packet.answer.trace packet.answer.assignment)
    (covered : ∀ name ∈ (packet.job.variant.site.context.fill packet.outcome.target).freeFvarNames,
      name ∈ footprint) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:finish"
        [encoded (interpretedPlanTerm names plan footprint bound expected),
          encoded (CollectionOccurrenceBatchExecution.publicationTermWith RecursiveCollectionExecution.eventTerm packet)])
      host (encoded (encodeOption (ScopedRuleJobReadoutExecution.receiptTermWith RecursiveCollectionExecution.eventTerm)
        (packet.finishCanonical? plan bound expected))) := by
  let request : GeneralRuleJobExecution.Request :=
    ⟨plan, bound, expected, packet.job.presentedSource packet.prepared, packet.job.preparedJob packet.prepared⟩
  let core := PremiseOperationsExecution.GeneralExecution.environmentTerm (GeneralPlanEnvironment.environment plan)
    (plan.snapshot.free.entriesOn footprint)
  have valid : GeneralPremise.Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation
      request.environment request.job.site.focusBound request.job.site.focusType request.job.site.focus request.job.ordinal
      packet.answer.trace packet.answer.assignment packet.outcome.completed packet.outcome.history packet.outcome.target := ready.2
  have filled := fill_returns program primitiveAgreement host packet.job.variant.site packet.prepared.source
  have view := canonical_environment_returns program agreement host names core
  readout_eval using (agreement) [filled, view] unfolding
    [interpretedPlanTerm, CompletePlanWire.planTermWithEnvironment,
      CollectionOccurrenceBatchExecution.publicationTermWith, CollectionOccurrenceBatchExecution.originTerm,
      CollectionContextExecution.variantTerm, RecursiveCollectionHandoffExecution.preparedTerm,
      RecursiveCollectionExecution.answerTerm, CompleteExecution.firingTermWith,
      RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm,
      ScopedRuleJobReadoutExecution.jobTerm, ScopedRuleJobReadoutExecution.siteTerm,
      ScopedRuleJobReadoutExecution.requestProjectionTerm, ScopedRuleJobReadoutExecution.rootResultTermWith,
      CollectionOccurrenceHandoff.Job.preparedJob, CollectionOccurrenceHandoff.Job.presentedSource,
      CollectionSelection.refocus, GeneralRuleJobExecution.Request.environment, GeneralRuleJobExecution.Request.goal,
      PremiseOperationsExecution.GeneralExecution.goalTerm, RetainedMatchingWire.interpretedEnvironmentTerm,
      request, core]
  apply ScopedRuleJobReadoutExecution.finish_root_interpreted_captured_returns_in_extension
    RecursiveCollectionExecution.eventTerm RecursiveCollectionHandoff.canonicalMatchingInterpretation program primitiveAgreement _ host request ready.1 footprint
    packet.answer.trace packet.answer.assignment packet.outcome.completed packet.outcome.history packet.outcome.target
    valid covered "request" "result"
  simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
    Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
    Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
    ScopedRuleJobReadoutExecution.requestProjectionTerm, ScopedRuleJobReadoutExecution.rootResultTermWith,
    ScopedRuleJobReadoutExecution.jobTerm, ScopedRuleJobReadoutExecution.siteTerm,
    CollectionOccurrenceHandoff.Job.preparedJob, CollectionOccurrenceHandoff.Job.presentedSource,
    CollectionSelection.refocus, GeneralRuleJobExecution.Request.environment, GeneralRuleJobExecution.Request.goal,
    PremiseOperationsExecution.GeneralExecution.goalTerm, PremiseOperationsExecution.GeneralExecution.Base.typesTerm,
    CompleteExecution.DescentCodec.assignmentTerm, CompleteExecution.DescentCodec.patternTerm,
    request, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  rfl

include agreement primitiveAgreement in
theorem ordinary_finish_returns (host : Effects.State) (footprint : List String) (packet : Publication)
    (ready : packet.FinishReady plan bound expected)
    (covered : ∀ name ∈ (packet.job.variant.site.context.fill packet.outcome.target).freeFvarNames,
      name ∈ footprint) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:finish"
        [encoded (CompletePlanWire.planTerm plan (plan.snapshot.free.entriesOn footprint) bound expected),
          encoded (CollectionOccurrenceBatchExecution.publicationTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm packet)])
      host (encoded (encodeOption (ScopedRuleJobReadoutExecution.receiptTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm)
        (packet.finish? plan bound expected))) := by
  let request : GeneralRuleJobExecution.Request :=
    ⟨plan, bound, expected, packet.job.presentedSource packet.prepared, packet.job.preparedJob packet.prepared⟩
  have valid : GeneralPremise.RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal packet.prepared.ordinary.trace packet.prepared.ordinary.assignment
      packet.outcome.completed packet.outcome.history packet.outcome.target := ready.2
  have filled := fill_returns program primitiveAgreement host packet.job.variant.site packet.prepared.source
  have view := ordinary_environment_returns program agreement host (GeneralPlanEnvironment.environment plan)
    (plan.snapshot.free.entriesOn footprint)
  readout_eval using (agreement) [filled, view] unfolding
    [CompletePlanWire.planTerm, CompletePlanWire.planTermWithEnvironment,
      CollectionOccurrenceBatchExecution.publicationTermWith, CollectionOccurrenceBatchExecution.originTerm,
      CollectionContextExecution.variantTerm, RecursiveCollectionHandoffExecution.preparedTerm,
      RecursiveCollectionExecution.answerTerm, CompleteExecution.firingTermWith,
      RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm,
      ScopedRuleJobReadoutExecution.jobTerm, ScopedRuleJobReadoutExecution.siteTerm,
      ScopedRuleJobReadoutExecution.requestProjectionTerm, ScopedRuleJobReadoutExecution.rootResultTermWith,
      CollectionOccurrenceHandoff.Job.preparedJob, CollectionOccurrenceHandoff.Job.presentedSource,
      CollectionSelection.refocus, GeneralRuleJobExecution.Request.environment, GeneralRuleJobExecution.Request.goal,
      PremiseOperationsExecution.GeneralExecution.goalTerm, PremiseOperationsExecution.GeneralExecution.environmentTerm,
      request]
  apply ScopedRuleJobReadoutExecution.finish_root_interpreted_captured_returns_in_extension
    RetainedMatchingWire.ordinaryCodec.choiceTerm ordinaryInterpretation program primitiveAgreement _ host request ready.1 footprint
    packet.prepared.ordinary.trace packet.prepared.ordinary.assignment packet.outcome.completed packet.outcome.history packet.outcome.target
    valid covered "request" "result"
  simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
    Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
    Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
    ScopedRuleJobReadoutExecution.requestProjectionTerm, ScopedRuleJobReadoutExecution.rootResultTermWith,
    ScopedRuleJobReadoutExecution.jobTerm, ScopedRuleJobReadoutExecution.siteTerm,
    CollectionOccurrenceHandoff.Job.preparedJob, CollectionOccurrenceHandoff.Job.presentedSource,
    CollectionSelection.refocus, GeneralRuleJobExecution.Request.environment, GeneralRuleJobExecution.Request.goal,
    PremiseOperationsExecution.GeneralExecution.goalTerm, PremiseOperationsExecution.GeneralExecution.Base.typesTerm,
    CompleteExecution.DescentCodec.assignmentTerm, CompleteExecution.DescentCodec.patternTerm,
    request, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  exact ⟨rfl, rfl⟩

include agreement in
theorem read_log_returns_with {Choice : Type} (choiceTerm : Choice → Term)
    (planWire : Term) (finish : Publication Choice → Option (Receipt Choice)) (host : Effects.State) :
    ∀ packets : List (Publication Choice),
      (∀ packet ∈ packets, PureReturns program [] host
        (apply "gslt:occurrence-search:finish"
          [encoded planWire, encoded (CollectionOccurrenceBatchExecution.publicationTermWith choiceTerm packet)])
        host (encoded (encodeOption (ScopedRuleJobReadoutExecution.receiptTermWith choiceTerm) (finish packet)))) →
      PureReturns program [] host (apply "gslt:occurrence-search:read-log"
        [encoded planWire, encoded (encodeList (CollectionOccurrenceBatchExecution.publicationTermWith choiceTerm) packets)])
        host (encoded (encodeList (ScopedRuleJobReadoutExecution.receiptTermWith choiceTerm) (packets.filterMap finish)))
  | [], _ => by readout_eval using (agreement) unfolding [encodeList]
  | packet :: packets, ready => by
    have first := ready packet List.mem_cons_self
    have later := read_log_returns_with choiceTerm planWire finish host packets
      (fun next member => ready next (List.mem_cons_of_mem _ member))
    cases finished : finish packet <;>
      readout_eval using (agreement) [first, later] unfolding [List.filterMap_cons, finished, encodeList, encodeOption]

include agreement in
theorem read_committed_returns_with {Choice : Type} (choiceTerm : Choice → Term)
    (planWire : Term) (finish : Publication Choice → Option (Receipt Choice)) (host : Effects.State) :
    ∀ packets : List (Publication Choice),
      (∀ packet ∈ packets, PureReturns program [] host
        (apply "gslt:occurrence-search:finish"
          [encoded planWire, encoded (CollectionOccurrenceBatchExecution.publicationTermWith choiceTerm packet)])
        host (encoded (encodeOption (ScopedRuleJobReadoutExecution.receiptTermWith choiceTerm) (finish packet)))) →
      PureReturns program [] host (apply "gslt:occurrence-search:read-committed"
        [encoded planWire, encoded (encodeList (CollectionOccurrenceBatchExecution.publicationTermWith choiceTerm) packets)])
        host (encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith choiceTerm)
          (retainedWith finish packets)))
  | [], _ => by readout_eval using (agreement) unfolding [retainedWith, encodeList]
  | packet :: packets, ready => by
    have first := ready packet List.mem_cons_self
    have later := read_committed_returns_with choiceTerm planWire finish host packets
      (fun next member => ready next (List.mem_cons_of_mem _ member))
    cases finished : finish packet <;>
      readout_eval using (agreement) [first, later] unfolding
        [retainedWith, commitWith?, List.filterMap_cons, finished, encodeList, encodeOption,
          CollectionOccurrenceBatchExecution.committedTermWith]

#print axioms canonical_finish_returns
#print axioms ordinary_finish_returns
#print axioms read_log_returns_with
#print axioms read_committed_returns_with
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.Interpreted


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.Interpreted

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise ScopedRuleMatching GeneralRuleJobs
open CollectionOccurrenceBatch CollectionOccurrenceHandoff CollectionCommittedObservation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics Eval BridgeKit WireKit

variable (program : Program)
    (agreement : ProgramAgreementOn metadataHeads metadataLibrary.runtime program)
    (primitiveAgreement : ProgramAgreementOn ScopedRuleJobReadoutExecution.executionHeads
      ScopedRuleJobReadoutExecution.runtime program)
variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}

include agreement primitiveAgreement in
theorem canonical_read_log_returns (host : Effects.State) (names footprint : List String)
    (state : State plan bound expected (CanonicalBags.canon source)
      RecursiveCollectionHandoff.canonicalMatchingExecution)
    (balanced : state.Balanced) (declared : Complete.Footprint.Declared plan footprint) :
    PureReturns program [] host (apply "gslt:occurrence-search:read-log"
      [encoded (interpretedPlanTerm names plan footprint bound expected),
        encoded (encodeList (CollectionOccurrenceBatchExecution.publicationTermWith RecursiveCollectionExecution.eventTerm)
          state.log)]) host
      (encoded (encodeList (ScopedRuleJobReadoutExecution.receiptTermWith RecursiveCollectionExecution.eventTerm)
        (state.log.filterMap fun packet => packet.finishCanonical? plan bound expected))) := by
  apply read_log_returns_with program agreement RecursiveCollectionExecution.eventTerm
    (interpretedPlanTerm names plan footprint bound expected)
    (fun packet => packet.finishCanonical? plan bound expected) host state.log
  intro packet member
  have ready := state.publication_canonical_finish_ready balanced member
  exact canonical_finish_returns program agreement primitiveAgreement host names footprint packet ready
    (packet.finish_target_free_within_in RecursiveCollectionHandoff.canonicalMatchingInterpretation
      packet.answer.trace packet.answer.assignment footprint declared ready)

include agreement primitiveAgreement in
theorem canonical_read_committed_returns (host : Effects.State) (names footprint : List String)
    (state : State plan bound expected (CanonicalBags.canon source)
      RecursiveCollectionHandoff.canonicalMatchingExecution)
    (balanced : state.Balanced) (declared : Complete.Footprint.Declared plan footprint) :
    PureReturns program [] host (apply "gslt:occurrence-search:read-committed"
      [encoded (interpretedPlanTerm names plan footprint bound expected),
        encoded (encodeList (CollectionOccurrenceBatchExecution.publicationTermWith RecursiveCollectionExecution.eventTerm)
          state.log)]) host
      (encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith RecursiveCollectionExecution.eventTerm)
        (retainedCanonical plan bound expected state.log))) := by
  apply read_committed_returns_with program agreement RecursiveCollectionExecution.eventTerm
    (interpretedPlanTerm names plan footprint bound expected)
    (fun packet => packet.finishCanonical? plan bound expected) host state.log
  intro packet member
  have ready := state.publication_canonical_finish_ready balanced member
  exact canonical_finish_returns program agreement primitiveAgreement host names footprint packet ready
    (packet.finish_target_free_within_in RecursiveCollectionHandoff.canonicalMatchingInterpretation
      packet.answer.trace packet.answer.assignment footprint declared ready)

include agreement primitiveAgreement in
theorem ordinary_read_log_returns (host : Effects.State) (footprint : List String)
    (state : State plan bound expected source) (balanced : state.Balanced)
    (declared : Complete.Footprint.Declared plan footprint) :
    PureReturns program [] host (apply "gslt:occurrence-search:read-log"
      [encoded (CompletePlanWire.planTerm plan (plan.snapshot.free.entriesOn footprint) bound expected),
        encoded (encodeList (CollectionOccurrenceBatchExecution.publicationTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm)
          state.log)]) host
      (encoded (encodeList (ScopedRuleJobReadoutExecution.receiptTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm)
        (state.log.filterMap fun packet => packet.finish? plan bound expected))) := by
  apply read_log_returns_with program agreement RetainedMatchingWire.ordinaryCodec.choiceTerm
    (CompletePlanWire.planTerm plan (plan.snapshot.free.entriesOn footprint) bound expected)
    (fun packet => packet.finish? plan bound expected) host state.log
  intro packet member
  have ready := state.publication_finish_ready balanced member
  exact ordinary_finish_returns program agreement primitiveAgreement host footprint packet ready
    (packet.finish_target_free_within footprint declared ready)

include agreement primitiveAgreement in
theorem ordinary_read_committed_returns (host : Effects.State) (footprint : List String)
    (state : State plan bound expected source) (balanced : state.Balanced)
    (declared : Complete.Footprint.Declared plan footprint) :
    PureReturns program [] host (apply "gslt:occurrence-search:read-committed"
      [encoded (CompletePlanWire.planTerm plan (plan.snapshot.free.entriesOn footprint) bound expected),
        encoded (encodeList (CollectionOccurrenceBatchExecution.publicationTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm)
          state.log)]) host
      (encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm)
        (retained plan bound expected state.log))) := by
  apply read_committed_returns_with program agreement RetainedMatchingWire.ordinaryCodec.choiceTerm
    (CompletePlanWire.planTerm plan (plan.snapshot.free.entriesOn footprint) bound expected)
    (fun packet => packet.finish? plan bound expected) host state.log
  intro packet member
  have ready := state.publication_finish_ready balanced member
  exact ordinary_finish_returns program agreement primitiveAgreement host footprint packet ready
    (packet.finish_target_free_within footprint declared ready)

include agreement primitiveAgreement in
theorem canonical_committed_reflection (host : Effects.State) (names footprint : List String)
    (state : State plan bound expected (CanonicalBags.canon source)
      RecursiveCollectionHandoff.canonicalMatchingExecution)
    (balanced : state.Balanced) (declared : Complete.Footprint.Declared plan footprint)
    (committed : List (Committed EquationalScopedReceipts.Event))
    (observed : ∃ fuel, run program fuel {state := host, control := (.evaluate []
      (apply "gslt:occurrence-search:read-committed"
        [encoded (interpretedPlanTerm names plan footprint bound expected),
          encoded (encodeList (CollectionOccurrenceBatchExecution.publicationTermWith RecursiveCollectionExecution.eventTerm)
            state.log)]))} = .complete host
              [encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith RecursiveCollectionExecution.eventTerm)
                committed)] [] []) :
    committed = retainedCanonical plan bound expected state.log := by
  have fact := canonical_read_committed_returns program agreement primitiveAgreement host names footprint state balanced declared
  have returned := (pure_returns_completed_iff program [] host host _ _ fact host
    [encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith RecursiveCollectionExecution.eventTerm) committed)]
    [] []).mp observed
  have same := (List.cons.inj returned.2.1).1
  have terms := CettaWireAtom.encode_injective _ _ same
  exact CollectionOccurrenceBatchExecution.committedListWith_encoding_injective
    RecursiveCollectionExecution.eventTerm RecursiveCollectionExecution.decodeEvent?
    RecursiveCollectionExecution.decodeEvent?_eventTerm terms

include agreement primitiveAgreement in
theorem canonical_committed_valid (host : Effects.State) (names footprint : List String)
    (state : State plan bound expected (CanonicalBags.canon source)
      RecursiveCollectionHandoff.canonicalMatchingExecution)
    (balanced : state.Balanced) (declared : Complete.Footprint.Declared plan footprint)
    (committed : List (Committed EquationalScopedReceipts.Event))
    (observed : ∃ fuel, run program fuel {state := host, control := (.evaluate []
      (apply "gslt:occurrence-search:read-committed"
        [encoded (interpretedPlanTerm names plan footprint bound expected),
          encoded (encodeList (CollectionOccurrenceBatchExecution.publicationTermWith RecursiveCollectionExecution.eventTerm)
            state.log)]))} = .complete host
              [encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith RecursiveCollectionExecution.eventTerm)
                committed)] [] []) :
    ∀ pair ∈ committed,
      pair.2.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation DynamicProvider.empty
        plan bound expected (pair.1.job.presentedSource pair.1.prepared) ∧
      CanonicalBags.Same source (pair.1.job.presentedSource pair.1.prepared) := by
  rw [canonical_committed_reflection program agreement primitiveAgreement host names footprint state balanced declared
    committed observed]
  intro pair member
  obtain ⟨logged, finished⟩ := retainedCanonical_keeps_packet plan bound expected state.log member
  obtain ⟨frame, _, published⟩ := List.mem_flatMap.mp (balanced.subset logged)
  exact Frame.publication_canonical_valid frame published finished

#print axioms canonical_read_log_returns
#print axioms canonical_read_committed_returns
#print axioms ordinary_read_log_returns
#print axioms ordinary_read_committed_returns
#print axioms canonical_committed_reflection
#print axioms canonical_committed_valid
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.Interpreted

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.SelectedNativeSource
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics Eval BridgeKit

private theorem primitive_names_lower :
    ScopedRuleJobReadoutExecution.executionHeadNames.all lowerHeads = true := by decide +kernel
private theorem primitive_lower (head : String)
    (kept : ScopedRuleJobReadoutExecution.executionHeads head = true) : lowerHeads head = true :=
  List.all_eq_true.mp primitive_names_lower head
    (by simpa only [ScopedRuleJobReadoutExecution.executionHeads, List.contains_iff_mem] using kept)

private def support : Program :=
  {equations := RuleExecutionProgram.interpretedPremiseSupportSources.flatMap (fun part => part.program.equations),
   declarations := RuleExecutionProgram.interpretedPremiseSupportSources.flatMap (fun part => part.program.declarations)}

private theorem support_equations_fresh :
    support.equations.all (fun row => !ScopedRuleJobReadoutExecution.executionHeads row.head) = true := by
  decide +kernel
private theorem support_declarations_fresh :
    support.declarations.all (fun row => match row with
      | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] =>
          !ScopedRuleJobReadoutExecution.executionHeads head
      | _ => true) = true := by decide +kernel

private theorem scoped_appended_agreement :
    ProgramAgreementOn ScopedRuleJobReadoutExecution.executionHeads RuleExecutionProgram.scopedProgram
      (RuleExecutionProgram.scopedProgram.append support) := by
  apply appended_program_agreement
  · intro row member
    have fresh := List.all_eq_true.mp support_equations_fresh row member
    cases kept : ScopedRuleJobReadoutExecution.executionHeads row.head with
    | false => rfl
    | true => simp only [kept, Bool.not_true, Bool.false_eq_true] at fresh
  · intro head types member
    have fresh := List.all_eq_true.mp support_declarations_fresh
      (.expression [.symbol ":", .symbol head, .expression (.symbol "->" :: types)]) member
    cases kept : ScopedRuleJobReadoutExecution.executionHeads head with
    | false => rfl
    | true => simp only [kept, Bool.not_true, Bool.false_eq_true] at fresh

private theorem appended_physical_agreement :
    ProgramAgreementOn (fun _ => true) (RuleExecutionProgram.scopedProgram.append support)
      (RuleExecutionProgram.interpretedPremiseSupportSources.foldl
        (fun loaded part => loaded.append part.program) RuleExecutionProgram.scopedProgram) := by
  apply programAgreementOn_of_retained_rows
  · have rows := (CompleteExecution.PhysicalSourceAgreement.fold_equations
      RuleExecutionProgram.interpretedPremiseSupportSources RuleExecutionProgram.scopedProgram).symm
    exact congrArg (List.filter (fun _ => true)) rows
  · have rows := (CompleteExecution.PhysicalSourceAgreement.fold_declarations
      RuleExecutionProgram.interpretedPremiseSupportSources RuleExecutionProgram.scopedProgram).symm
    exact congrArg (List.filter (retainedCallDeclaration (fun _ => true))) rows

theorem primitive_agreement :
    ProgramAgreementOn ScopedRuleJobReadoutExecution.executionHeads
      ScopedRuleJobReadoutExecution.runtime runtime := by
  have physical := agreement_trans scoped_appended_agreement
    (agreement_mono (fun _ _ => rfl) appended_physical_agreement)
  have old := agreement_trans physical
    (agreement_mono (fun _ _ => rfl) CompleteExecution.PhysicalSourceAgreement.physical_interpreted_agreement)
  exact agreement_trans PremiseOperationsExecution.GeneralExecution.CompletedAssembly.readout_agreement
    (agreement_trans old (agreement_mono primitive_lower lower_agreement))

#print axioms primitive_names_lower
#print axioms support_equations_fresh
#print axioms support_declarations_fresh
#print axioms scoped_appended_agreement
#print axioms appended_physical_agreement
#print axioms primitive_agreement
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.SelectedNativeSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.SelectedNativeSource
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise ScopedRuleMatching GeneralRuleJobs
open CollectionOccurrenceBatch CollectionOccurrenceHandoff CollectionCommittedObservation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics Eval BridgeKit WireKit
variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}

theorem canonical_read_log_returns (host : Effects.State) (names footprint : List String)
    (state : State plan bound expected (CanonicalBags.canon source)
      RecursiveCollectionHandoff.canonicalMatchingExecution)
    (balanced : state.Balanced) (declared : Complete.Footprint.Declared plan footprint) :
    PureReturns runtime [] host (apply "gslt:occurrence-search:read-log"
      [encoded (CollectionOccurrenceSearchExecution.Interpreted.interpretedPlanTerm names plan footprint bound expected),
        encoded (encodeList (CollectionOccurrenceBatchExecution.publicationTermWith RecursiveCollectionExecution.eventTerm)
          state.log)]) host
      (encoded (encodeList (ScopedRuleJobReadoutExecution.receiptTermWith RecursiveCollectionExecution.eventTerm)
        (state.log.filterMap fun packet => packet.finishCanonical? plan bound expected))) := by
  exact CollectionOccurrenceSearchExecution.Interpreted.canonical_read_log_returns runtime metadata_agreement primitive_agreement host names footprint state balanced declared

theorem canonical_read_committed_returns (host : Effects.State) (names footprint : List String)
    (state : State plan bound expected (CanonicalBags.canon source)
      RecursiveCollectionHandoff.canonicalMatchingExecution)
    (balanced : state.Balanced) (declared : Complete.Footprint.Declared plan footprint) :
    PureReturns runtime [] host (apply "gslt:occurrence-search:read-committed"
      [encoded (CollectionOccurrenceSearchExecution.Interpreted.interpretedPlanTerm names plan footprint bound expected),
        encoded (encodeList (CollectionOccurrenceBatchExecution.publicationTermWith RecursiveCollectionExecution.eventTerm)
          state.log)]) host
      (encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith RecursiveCollectionExecution.eventTerm)
        (retainedCanonical plan bound expected state.log))) := by
  exact CollectionOccurrenceSearchExecution.Interpreted.canonical_read_committed_returns runtime metadata_agreement primitive_agreement host names footprint state balanced declared

theorem ordinary_read_log_returns (host : Effects.State) (footprint : List String)
    (state : State plan bound expected source) (balanced : state.Balanced)
    (declared : Complete.Footprint.Declared plan footprint) :
    PureReturns runtime [] host (apply "gslt:occurrence-search:read-log"
      [encoded (CompletePlanWire.planTerm plan (plan.snapshot.free.entriesOn footprint) bound expected),
        encoded (encodeList (CollectionOccurrenceBatchExecution.publicationTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm)
          state.log)]) host
      (encoded (encodeList (ScopedRuleJobReadoutExecution.receiptTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm)
        (state.log.filterMap fun packet => packet.finish? plan bound expected))) := by
  exact CollectionOccurrenceSearchExecution.Interpreted.ordinary_read_log_returns runtime metadata_agreement primitive_agreement host footprint state balanced declared

theorem ordinary_read_committed_returns (host : Effects.State) (footprint : List String)
    (state : State plan bound expected source) (balanced : state.Balanced)
    (declared : Complete.Footprint.Declared plan footprint) :
    PureReturns runtime [] host (apply "gslt:occurrence-search:read-committed"
      [encoded (CompletePlanWire.planTerm plan (plan.snapshot.free.entriesOn footprint) bound expected),
        encoded (encodeList (CollectionOccurrenceBatchExecution.publicationTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm)
          state.log)]) host
      (encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm)
        (retained plan bound expected state.log))) := by
  exact CollectionOccurrenceSearchExecution.Interpreted.ordinary_read_committed_returns runtime metadata_agreement primitive_agreement host footprint state balanced declared

theorem canonical_committed_reflection (host : Effects.State) (names footprint : List String)
    (state : State plan bound expected (CanonicalBags.canon source)
      RecursiveCollectionHandoff.canonicalMatchingExecution)
    (balanced : state.Balanced) (declared : Complete.Footprint.Declared plan footprint)
    (committed : List (Committed EquationalScopedReceipts.Event))
    (observed : ∃ fuel, run runtime fuel {state := host, control := (.evaluate []
      (apply "gslt:occurrence-search:read-committed"
        [encoded (CollectionOccurrenceSearchExecution.Interpreted.interpretedPlanTerm names plan footprint bound expected),
          encoded (encodeList (CollectionOccurrenceBatchExecution.publicationTermWith RecursiveCollectionExecution.eventTerm)
            state.log)]))} = .complete host
              [encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith RecursiveCollectionExecution.eventTerm)
                committed)] [] []) :
    committed = retainedCanonical plan bound expected state.log := by
  exact CollectionOccurrenceSearchExecution.Interpreted.canonical_committed_reflection runtime metadata_agreement primitive_agreement host names footprint state balanced declared committed observed

theorem canonical_committed_valid (host : Effects.State) (names footprint : List String)
    (state : State plan bound expected (CanonicalBags.canon source)
      RecursiveCollectionHandoff.canonicalMatchingExecution)
    (balanced : state.Balanced) (declared : Complete.Footprint.Declared plan footprint)
    (committed : List (Committed EquationalScopedReceipts.Event))
    (observed : ∃ fuel, run runtime fuel {state := host, control := (.evaluate []
      (apply "gslt:occurrence-search:read-committed"
        [encoded (CollectionOccurrenceSearchExecution.Interpreted.interpretedPlanTerm names plan footprint bound expected),
          encoded (encodeList (CollectionOccurrenceBatchExecution.publicationTermWith RecursiveCollectionExecution.eventTerm)
            state.log)]))} = .complete host
              [encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith RecursiveCollectionExecution.eventTerm)
                committed)] [] []) :
    ∀ pair ∈ committed,
      pair.2.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation DynamicProvider.empty
        plan bound expected (pair.1.job.presentedSource pair.1.prepared) ∧
      CanonicalBags.Same source (pair.1.job.presentedSource pair.1.prepared) := by
  exact CollectionOccurrenceSearchExecution.Interpreted.canonical_committed_valid runtime metadata_agreement primitive_agreement host names footprint state balanced declared committed observed

#print axioms canonical_read_log_returns
#print axioms canonical_read_committed_returns
#print axioms ordinary_read_log_returns
#print axioms ordinary_read_committed_returns
#print axioms canonical_committed_reflection
#print axioms canonical_committed_valid
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.SelectedNativeSource


/-! # Native retained runs and original completed receipt readout -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionOccurrenceBatch CollectionOccurrenceMatcher CollectionOccurrenceHandoff CanonicalCompare
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics Eval BridgeKit WireKit

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {sourcePattern : Pattern}

theorem begin_ready (names : List String) (named : StandardWire.TableFor plan names)
    (footprint : List String) (declared : Complete.Footprint.Declared plan footprint)
    (admitted : ∀ declaration ∈ plan.rules,
      RuleBinding.admittedFor declaration.rule declaration.binding.spec = true)
    (input : Pattern) (canonical : input.hasCanonicalBinderMetadata = true) :
    CollectionOccurrenceMachineExecution.Ready names footprint
      (CollectionOccurrenceMachine.begin plan bound expected input) := by
  constructor
  · intro lane member
    obtain ⟨selected, _, rfl⟩ := List.mem_map.mp member
    let job := selected.val
    have valid : job.Valid plan bound expected input := (jobs_exact _ _ _ _ _).mp selected.property
    have fields : job.variant.site.focus = job.origin.site.focus ∧
        job.variant.site.focusBound = job.origin.site.focusBound ∧
        job.variant.site.focusType = job.origin.site.focusType := by
      obtain ⟨context, _, same⟩ := List.mem_map.mp valid.2
      rw [← same]
      exact ⟨rfl,rfl,rfl⟩
    have sorted : WellSorted.OpenPatternWellSorted
        (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
        job.variant.site.focusBound job.variant.site.focusType job.variant.site.focus := by
      simpa only [fields.1, fields.2.1, fields.2.2] using valid.1.2.focus_sorted canonical
    have checked := WellSorted.checkOpenPatternWellSorted_complete sorted
    have target : CanonicalCompare.Covered names job.request.target := named.covered checked
    refine ⟨RecursiveCollectionMachine.start_covered names job.request target, target, ?_, ?_, sorted⟩
    · exact Complete.Footprint.sorted_within declared checked
    · exact admitted job.origin.declaration (List.fst_mem_of_mem_zipIdx valid.1.1)
  · intro frame member
    cases member

@[metta_head "gslt:occurrence-search:finish"]
theorem finish_returns (host : Effects.State) (footprint : List String) (packet : Publication)
    (ready : packet.FinishReady plan bound expected)
    (covered : ∀ name ∈ (packet.job.variant.site.context.fill packet.outcome.target).freeFvarNames,
      name ∈ footprint) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:finish"
        [encoded (CompletePlanWire.planTerm plan (plan.snapshot.free.entriesOn footprint) bound expected),
          encoded (CollectionOccurrenceBatchExecution.publicationTerm packet)])
      host (encoded (encodeOption ScopedRuleJobReadoutExecution.receiptTerm
        (packet.finish? plan bound expected))) := by
  have returned := Interpreted.ordinary_finish_returns library.runtime
    SelectedNativeSource.metadata_agreement SelectedNativeSource.primitive_agreement host footprint packet ready covered
  have packets : CollectionOccurrenceBatchExecution.publicationTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm =
      CollectionOccurrenceBatchExecution.publicationTerm :=
    funext CollectionOccurrenceBatchExecution.publicationTermWith_ordinary
  have receipts : ScopedRuleJobReadoutExecution.receiptTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm =
      ScopedRuleJobReadoutExecution.receiptTerm :=
    funext ScopedRuleJobReadoutExecution.receiptTermWith_ordinary
  simpa only [packets, receipts] using returned


def PacketReady (footprint : List String) (packet : Publication) : Prop :=
  packet.FinishReady plan bound expected ∧
    ∀ name ∈ (packet.job.variant.site.context.fill packet.outcome.target).freeFvarNames,
      name ∈ footprint

@[metta_head "gslt:occurrence-search:read-log"]
theorem read_log_returns (host : Effects.State) (footprint : List String) :
    ∀ packets : List Publication,
    (∀ packet ∈ packets, PacketReady (plan := plan) (bound := bound) (expected := expected) footprint packet) →
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:read-log"
        [encoded (CompletePlanWire.planTerm plan (plan.snapshot.free.entriesOn footprint) bound expected),
          encoded (encodeList CollectionOccurrenceBatchExecution.publicationTerm packets)])
      host (encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm
        (packets.filterMap fun packet => packet.finish? plan bound expected)))
  | packets, ready => by
    have packetTerms : CollectionOccurrenceBatchExecution.publicationTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm =
        CollectionOccurrenceBatchExecution.publicationTerm :=
      funext CollectionOccurrenceBatchExecution.publicationTermWith_ordinary
    have receiptTerms : ScopedRuleJobReadoutExecution.receiptTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm =
        ScopedRuleJobReadoutExecution.receiptTerm :=
      funext ScopedRuleJobReadoutExecution.receiptTermWith_ordinary
    have returned := Interpreted.read_log_returns_with library.runtime SelectedNativeSource.metadata_agreement
      RetainedMatchingWire.ordinaryCodec.choiceTerm
      (CompletePlanWire.planTerm plan (plan.snapshot.free.entriesOn footprint) bound expected)
      (fun packet => packet.finish? plan bound expected) host packets (by
        intro packet member
        simpa only [packetTerms, receiptTerms] using
          finish_returns host footprint packet (ready packet member).1 (ready packet member).2)
    simpa only [packetTerms, receiptTerms] using returned


theorem run_state_ready (names footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (depth work : Nat) (input : Pattern)
    (state : CollectionOccurrenceMachine.State plan bound expected input)
    (ready : CollectionOccurrenceMachineExecution.Ready names footprint state) :
    CollectionOccurrenceMachineExecution.Ready names footprint
      (CollectionOccurrenceMachine.run depth work state) := by
  induction work generalizing state with
  | zero => exact ready
  | succ work ih => exact ih _ (CollectionOccurrenceMachineExecution.round_ready
      names footprint finite provider depth state ready)

def Ready (names footprint : List String) (depth : Nat)
    (run : CollectionOccurrenceSearch.Run plan bound expected) : Prop :=
  CollectionOccurrenceMachineExecution.Ready names footprint run.state ∧
    CollectionOccurrenceMachine.Invariant depth run.state

theorem resume_ready (names footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (depth : Nat) (run : CollectionOccurrenceSearch.Run plan bound expected)
    (ready : Ready names footprint depth run) (work : Nat) :
    Ready names footprint depth
      ((CollectionOccurrenceSearch.search plan bound expected depth).resume run work) := by
  exact ⟨run_state_ready names footprint finite provider depth work _ run.state ready.1,
    CollectionOccurrenceMachine.run_invariant depth work ready.2⟩

theorem ready_packet (names footprint : List String) (depth : Nat)
    (declared : Complete.Footprint.Declared plan footprint)
    (run : CollectionOccurrenceSearch.Run plan bound expected) (ready : Ready names footprint depth run)
    {packet : CollectionOccurrenceBatch.Publication} (member : packet ∈ run.state.batch.log) :
    packet.FinishReady plan bound expected ∧
      ∀ name ∈ (packet.job.variant.site.context.fill packet.outcome.target).freeFvarNames,
        name ∈ footprint := by
  have finished := run.state.batch.publication_finish_ready ready.2.1 member
  exact ⟨finished, packet.finish_target_free_within footprint declared finished⟩

theorem run_ready (names : List String) (named : StandardWire.TableFor plan names)
    (footprint : List String) (scope : Complete.Footprint.Scope plan footprint)
    (admitted : ∀ declaration ∈ plan.rules,
      RuleBinding.admittedFor declaration.rule declaration.binding.spec = true)
    (depth : Nat) (input : Pattern) (checked : Complete.Classes.Checked plan bound expected input)
    (work : Nat) : Ready names footprint depth
      ((CollectionOccurrenceSearch.search plan bound expected depth).run input work) := by
  have typed := CanonicalBags.openPatternWellSorted_canon
    (WellSorted.checkOpenPatternWellSorted_sound checked)
  have begun := begin_ready (bound := bound) (expected := expected) names named footprint scope.declared admitted
    (CanonicalBags.canon input) typed.2.1
  exact ⟨run_state_ready names footprint scope.finite scope.provider depth work _ _ begun,
    CollectionOccurrenceMachine.run_invariant depth work (CollectionOccurrenceMachine.begin_invariant depth)⟩

theorem publication_checked (names footprint : List String) (depth : Nat)
    (run : CollectionOccurrenceSearch.Run plan bound expected) (ready : Ready names footprint depth run)
    {receipt : GeneralRuleJobs.Receipt}
    (member : receipt ∈ (CollectionOccurrenceSearch.search plan bound expected depth).publication run) :
    Complete.Classes.Checked plan bound expected receipt.target := by
  obtain ⟨packet, logged, finished⟩ := List.mem_filterMap.mp member
  have packetReady := run.state.batch.publication_finish_ready ready.2.1 logged
  have valid := packet.finished_valid packetReady finished
  exact WellSorted.checkOpenPatternWellSorted_complete valid.2.2.2.2


@[metta_head "gslt:occurrence-search:with-state"]
theorem with_state_returns (host : Effects.State) (footprint : List String)
    (run : CollectionOccurrenceSearch.Run plan bound expected)
    (ready : ∀ packet ∈ run.state.batch.log,
      PacketReady (plan := plan) (bound := bound) (expected := expected) footprint packet) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:with-state"
        [encoded (CompletePlanWire.planTerm plan (plan.snapshot.free.entriesOn footprint) bound expected),
          encoded (InferenceCettaWire.encodePattern run.source),
          encoded (CollectionOccurrenceMachineExecution.stateTerm run.state)])
      host (encoded (runTerm (plan.snapshot.free.entriesOn footprint) run)) := by
  have observed := read_log_returns host footprint run.state.batch.log ready
  occurrence_search_eval [observed] unfolding
    [runTerm, CollectionOccurrenceMachineExecution.stateTerm, CollectionOccurrenceBatchExecution.stateTerm]

@[metta_head "gslt:occurrence-search:publication"]
theorem publication_returns (host : Effects.State) (table : List (String × TypeExpr))
    (run : CollectionOccurrenceSearch.Run plan bound expected) (depth : Nat) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:publication" [encoded (runTerm table run)])
      host (encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm
        ((CollectionOccurrenceSearch.search plan bound expected depth).publication run))) := by
  occurrence_search_eval unfolding [runTerm, CollectionOccurrenceSearch.search]

@[metta_head "gslt:occurrence-search:resume"]
theorem resume_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (footprint : List String) (declared : Complete.Footprint.Declared plan footprint)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (depth work : Nat)
    (run : CollectionOccurrenceSearch.Run plan bound expected) (ready : Ready names footprint depth run) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:resume"
        [encoded (encodeList Term.string names), number depth,
          encoded (runTerm (plan.snapshot.free.entriesOn footprint) run), number work])
      host (encoded (runTerm (plan.snapshot.free.entriesOn footprint)
        ((CollectionOccurrenceSearch.search plan bound expected depth).resume run work))) := by
  have advanced := CollectionOccurrenceMachineExecution.run_returns host names ordered footprint finite provider depth
      work run.state ready.1
  have resumedReady := resume_ready names footprint finite provider depth run ready work
  have observed := with_state_returns host footprint
    ((CollectionOccurrenceSearch.search plan bound expected depth).resume run work)
    (fun packet member => ready_packet names footprint depth declared _ resumedReady member)
  have freeSame : (GeneralPlanEnvironment.environment plan).free = plan.snapshot.free := rfl
  occurrence_search_eval [advanced, observed] unfolding
    [runTerm, CompletePlanWire.planTerm, CollectionOccurrenceSearch.search,
      CompleteExecution.environmentValue, CollectionOccurrenceMachineExecution.stateTerm, freeSame]

@[metta_head "gslt:occurrence-search:run"]
theorem run_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (footprint : List String) (declared : Complete.Footprint.Declared plan footprint)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (depth work : Nat) (input : Pattern) (covered : Covered names input)
    (free : ∀ name ∈ (CanonicalBags.canon input).freeFvarNames, name ∈ footprint)
    (ready : CollectionOccurrenceMachineExecution.Ready names footprint
      (CollectionOccurrenceMachine.begin plan bound expected (CanonicalBags.canon input))) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:run"
        [encoded (encodeList Term.string names), number depth,
          encoded (CompletePlanWire.planTerm plan (plan.snapshot.free.entriesOn footprint) bound expected),
          encoded (InferenceCettaWire.encodePattern input), number work])
      host (encoded (runTerm (plan.snapshot.free.entriesOn footprint)
        ((CollectionOccurrenceSearch.search plan bound expected depth).run input work))) := by
  have canonical := canon_lower_returns host names ordered input covered
  have discovered := CollectionOccurrenceDiscoveryExecution.begin_returns host plan bound expected
    (CanonicalBags.canon input) footprint free
  have advanced := CollectionOccurrenceMachineExecution.run_returns host names ordered footprint finite provider depth work
      (CollectionOccurrenceMachine.begin plan bound expected (CanonicalBags.canon input)) ready
  have runReady : Ready names footprint depth
      ((CollectionOccurrenceSearch.search plan bound expected depth).run input work) :=
    ⟨run_state_ready names footprint finite provider depth work _ _ ready,
      CollectionOccurrenceMachine.run_invariant depth work (CollectionOccurrenceMachine.begin_invariant depth)⟩
  have observed := with_state_returns host footprint
    ((CollectionOccurrenceSearch.search plan bound expected depth).run input work)
    (fun packet member => ready_packet names footprint depth declared _ runReady member)
  have view := Interpreted.ordinary_environment_returns library.runtime SelectedNativeSource.metadata_agreement
    host (GeneralPlanEnvironment.environment plan) (plan.snapshot.free.entriesOn footprint)
  have freeSame : (GeneralPlanEnvironment.environment plan).free = plan.snapshot.free := rfl
  occurrence_search_eval [view, canonical, discovered, advanced, observed] unfolding
    [runTerm, CompletePlanWire.planTerm, PremiseOperationsExecution.GeneralExecution.environmentTerm,
      CollectionOccurrenceSearch.search, CompleteExecution.environmentValue, freeSame,
      PremiseOperationsExecution.DeclarationTyping.declarationsTerm,
      PremiseOperationsExecution.DeclarationTyping.freeContextTerm,
      PremiseOperationsExecution.DeclarationTyping.boundContextTerm, encodeList, InferenceCettaWire.encodeList,
      CompleteExecution.patternValue]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.Declared
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise CollectionCommittedObservation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics Eval BridgeKit WireKit
@[local simp] private theorem key_match_variable (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (name : String) (value : Atom) :
    SpaceSemantics.matchValue bindings (.var name) value =
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom bindings (.var name) value := by
  cases value <;> simp [SpaceSemantics.matchValue]

syntax "key_eval" " using " "(" term ")" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| key_eval using ($agreement) $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic|
      (metta_call_in key_checked using $agreement
       metta_eval [$facts,*] with key_checked in $agreement unfolding
        [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
          Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, key_match_variable, $extra,*]))

variable (program : Program) (agreement : ProgramAgreementOn keyHeads keyLibrary.runtime program)

include agreement
mutual
theorem key_event_returns {Choice : Type} (choiceTerm : Choice → Term)
    (host : Effects.State) (event : Event Choice) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-event" [encoded (RetainedMatchingWire.eventTerm choiceTerm event)])
      host (encoded (encodeOption (RetainedMatchingWire.eventTerm choiceTerm)
        (administrativeEvent? .factValidation event))) := by
  cases event with
  | query p q row origins =>
      key_eval using (agreement) unfolding
        [RetainedMatchingWire.eventTerm, administrativeEvent?, validationEventReadout, encodeOption]
  | freshness p q atom subject =>
      key_eval using (agreement) unfolding
        [RetainedMatchingWire.eventTerm, administrativeEvent?, validationEventReadout, encodeOption]
  | quantified p q kind elements =>
      have nested := key_elements_returns choiceTerm host elements
      key_eval using (agreement) [nested] unfolding
        [RetainedMatchingWire.eventTerm, administrativeEvent?, validationEventReadout, encodeOption]
  | child p q declaration bound source target trace targetTrace captured completed history =>
      have nested := key_history_returns choiceTerm host history
      key_eval using (agreement) [nested] unfolding
        [RetainedMatchingWire.eventTerm, administrativeEvent?, validationEventReadout, encodeOption]
termination_by sizeOf event

theorem key_history_returns {Choice : Type} (choiceTerm : Choice → Term)
    (host : Effects.State) (history : List (Event Choice)) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-history" [encoded (RetainedMatchingWire.eventsTerm choiceTerm history)])
      host (encoded (RetainedMatchingWire.eventsTerm choiceTerm
        (validationHistoryReadout history .factValidation))) := by
  cases history with
  | nil => key_eval using (agreement) unfolding [RetainedMatchingWire.eventsTerm, validationHistoryReadout]
  | cons event rest =>
      have first := key_event_returns choiceTerm host event
      have later := key_history_returns choiceTerm host rest
      rw [← administrative_history_filterMap]
      cases result : administrativeEvent? .factValidation event <;>
        key_eval using (agreement) [first,later] unfolding
          [RetainedMatchingWire.eventsTerm, List.filterMap_cons, result, encodeOption,
           administrative_history_filterMap]
termination_by sizeOf history

theorem key_elements_returns {Choice : Type} (choiceTerm : Choice → Term)
    (host : Effects.State) (elements : List (Nat × Pattern × List (Event Choice))) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-elements"
        [encoded (RetainedMatchingWire.quantifiedEventsTerm choiceTerm elements)])
      host (encoded (RetainedMatchingWire.quantifiedEventsTerm choiceTerm
        (validationElementsReadout elements .factValidation))) := by
  cases elements with
  | nil => key_eval using (agreement) unfolding [RetainedMatchingWire.quantifiedEventsTerm, validationElementsReadout]
  | cons entry rest =>
      rcases entry with ⟨index, element, history⟩
      have first := key_history_returns choiceTerm host history
      have later := key_elements_returns choiceTerm host rest
      key_eval using (agreement) [first,later] unfolding
        [RetainedMatchingWire.quantifiedEventsTerm, validationElementsReadout]
termination_by sizeOf elements
end
omit agreement

#print axioms key_checked
#print axioms key_body_count
#print axioms key_event_returns
#print axioms key_history_returns
#print axioms key_elements_returns

open ScopedRuleMatching RuleInstantiationExecution.ScopedCapture CanonicalBags
open InferenceCettaWire.AuthoredRule (contextualValueTerm)

include agreement in
theorem binding_returns (host : Effects.State) (name : String) (assignment : Assignment) :
    PureReturns program [] host
      (apply "gslt:automata:binding" [encoded (.string name), encoded (scopedAssignmentTerm assignment)])
      host (encoded (encodeOption contextualValueTerm (lookup assignment name))) := by
  induction assignment with
  | nil => key_eval using (agreement) unfolding
      [scopedAssignmentTerm, MatchAutomataBindingExecution.payloadBindingsTerm, MatchAutomataBindingExecution.payloadBindingTerm, lookup,
       encodeList, encodeOption]
  | cons entry rest ih =>
      rcases entry with ⟨key,value⟩
      by_cases same : name = key
      · subst key
        key_eval using (agreement) unfolding
          [scopedAssignmentTerm, MatchAutomataBindingExecution.payloadBindingsTerm, MatchAutomataBindingExecution.payloadBindingTerm, lookup,
           encodeList, encodeOption]
      · have looked : lookup ((key,value) :: rest) name = lookup rest name := by
          simp [lookup,Ne.symm same]
        rw [looked]
        key_eval using (agreement) [ih] unfolding
          [scopedAssignmentTerm, MatchAutomataBindingExecution.payloadBindingsTerm, MatchAutomataBindingExecution.payloadBindingTerm,
           encodeList,same]

/-- Only the existing pattern-canonicalization primitive is supplied. -/
structure CanonOperations (program : Program) (table : List String) : Prop where
  canon : ∀ host pattern, CanonicalCompare.Covered table pattern →
    PureReturns program [] host
      (apply "gslt:canon:canon" [CompleteExecution.tableValue table,
        encoded (InferenceCettaWire.encodePattern pattern)])
      host (encoded (InferenceCettaWire.encodePattern (CanonicalBags.canon pattern)))

/-- The actual canonical owner independently supplies the primitive on the lower reference. -/
theorem raw_canon_operations (table : List String) (ordered : CanonicalCompare.NameOrdered table) :
    CanonOperations RetainedMatchingWire.interpretedLibrary.runtime table :=
  ⟨fun host pattern covered => CompleteExecution.canon_returns host ordered pattern covered⟩

theorem selected_canon_operations (table : List String) (ordered : CanonicalCompare.NameOrdered table) :
    CanonOperations SelectedNativeSource.runtime table :=
  ⟨fun host pattern covered => canon_lower_returns host table ordered pattern covered⟩

#print axioms selected_canon_operations

include agreement in
theorem key_binding_returns (table : List String) (operations : CanonOperations program table)
    (host : Effects.State) (name : String) (assignment : Assignment)
    (covered : ∀ value, lookup assignment name = some value → CanonicalCompare.Covered table value.body) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-binding"
        [CompleteExecution.tableValue table, encoded (.string name), encoded (scopedAssignmentTerm assignment)])
      host (encoded (encodeOption contextualValueTerm ((lookup assignment name).map canonValue))) := by
  have binding := binding_returns program agreement host name assignment
  cases found : lookup assignment name with
  | none => key_eval using (agreement) [binding] unfolding [found, encodeOption]
  | some value =>
      have canonical := operations.canon host value.body (covered value found)
      key_eval using (agreement) [binding,canonical] unfolding
        [found, encodeOption, contextualValueTerm, canonValue]

include agreement in
theorem key_values_returns (table : List String) (operations : CanonOperations program table)
    (host : Effects.State) (assignment : Assignment) :
    ∀ names : List String,
    (∀ name ∈ names, ∀ value, lookup assignment name = some value → CanonicalCompare.Covered table value.body) →
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-values"
        [CompleteExecution.tableValue table, encoded (encodeList Term.string names), encoded (scopedAssignmentTerm assignment)])
      host (encoded (encodeList (encodeOption contextualValueTerm)
        (names.map fun name => (lookup assignment name).map canonValue)))
  | [], _ => by key_eval using (agreement) unfolding [encodeList]
  | name :: rest, covered => by
      have first := key_binding_returns program agreement table operations host name assignment
        (covered name List.mem_cons_self)
      have later := key_values_returns table operations host assignment rest
        (fun next member => covered next (List.mem_cons_of_mem _ member))
      key_eval using (agreement) [first,later] unfolding [encodeList]

#print axioms binding_returns
#print axioms raw_canon_operations
#print axioms key_binding_returns
#print axioms key_values_returns

/-- Data projection of a licensed site's typing spine; source payload stays in the pair. -/
def siteShapeTerm (site : GeneralTypedSites.SiteData) : Term :=
  .application "LogicalSiteShape"
    [encodeList Term.natural site.address, encodeList InferenceCettaWire.AuthoredRule.typeTerm site.focusBound,
      InferenceCettaWire.AuthoredRule.typeTerm site.focusType,
      encodeList ScopedRuleJobReadoutExecution.typingFrameTerm site.typingFrames]

def committedKeyTerm {Choice : Type} (choiceTerm : Choice → Term) (names : List String)
    (pair : Committed Choice) : Term :=
  .application "DeclaredFiringKey"
    [.natural pair.1.job.origin.ordinal, .natural pair.1.job.origin.declaration.declarationIndex,
      siteShapeTerm pair.1.job.origin.site,
      encodeList (encodeOption contextualValueTerm)
        (names.map fun name => (lookup pair.2.completed name).map canonValue),
      RetainedMatchingWire.eventsTerm choiceTerm (validationHistoryReadout pair.2.premiseHistory .factValidation)]

include agreement in
theorem key_extract_returns {Choice : Type} (choiceTerm : Choice → Term)
    (table : List String) (operations : CanonOperations program table) (names : List String)
    (host : Effects.State) (pair : Committed Choice)
    (covered : ∀ name ∈ names, ∀ value, lookup pair.2.completed name = some value →
      CanonicalCompare.Covered table value.body) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-extract"
        [CompleteExecution.tableValue table, encoded (encodeList Term.string names),
          encoded (CollectionOccurrenceBatchExecution.committedTermWith choiceTerm pair)])
      host (encoded (committedKeyTerm choiceTerm names pair)) := by
  have values := key_values_returns program agreement table operations host pair.2.completed names covered
  have history := key_history_returns program agreement choiceTerm host pair.2.premiseHistory
  simp only [CollectionOccurrenceBatchExecution.committedTermWith, CollectionOccurrenceBatchExecution.publicationTermWith,
    CollectionOccurrenceBatchExecution.originTerm, ScopedRuleJobReadoutExecution.receiptTermWith,
    ScopedRuleJobReadoutExecution.jobTerm, ScopedRuleJobReadoutExecution.rulePlanTerm,
    ScopedRuleJobReadoutExecution.siteTerm]
  key_eval using (agreement) [values,history] unfolding
    [CollectionOccurrenceBatchExecution.committedTermWith, CollectionOccurrenceBatchExecution.publicationTermWith,
      CollectionOccurrenceBatchExecution.originTerm, ScopedRuleJobReadoutExecution.receiptTermWith,
      ScopedRuleJobReadoutExecution.jobTerm, ScopedRuleJobReadoutExecution.rulePlanTerm,
      ScopedRuleJobReadoutExecution.siteTerm, committedKeyTerm, siteShapeTerm,
      RetainedMatchingWire.assignmentTerm]

  all_goals (try metta_select [key_match_variable,CettaWireAtom.encode,CettaWireAtom.encodeMany,encoded,
    CollectionOccurrenceBatchExecution.committedTermWith,CollectionOccurrenceBatchExecution.publicationTermWith,
    CollectionOccurrenceBatchExecution.originTerm,ScopedRuleJobReadoutExecution.receiptTermWith,
    ScopedRuleJobReadoutExecution.jobTerm,ScopedRuleJobReadoutExecution.rulePlanTerm,ScopedRuleJobReadoutExecution.siteTerm])
  all_goals
    try (apply pure_let_star_returns _ _ _ _ _ _ _ rfl)
    apply pure_let_returns _ _ _ _ _ _ _ _ (by rfl)
    · metta_capture_agreed agreement from values
    · apply pure_let_returns _ _ _ _ _ _ _ _ (by rfl)
      · metta_capture_agreed agreement from history
      · metta_eval with key_checked in agreement unfolding [committedKeyTerm,siteShapeTerm,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
          Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,List.find?,CettaWireAtom.encode,CettaWireAtom.encodeMany]

include agreement in
theorem key_project_returns {Choice : Type} (choiceTerm : Choice → Term)
    (table : List String) (operations : CanonOperations program table) (names : List String)
    (host : Effects.State) :
    ∀ pairs : List (Committed Choice),
    (∀ pair ∈ pairs, ∀ name ∈ names, ∀ value, lookup pair.2.completed name = some value →
      CanonicalCompare.Covered table value.body) →
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-project"
        [CompleteExecution.tableValue table, encoded (encodeList Term.string names),
          encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith choiceTerm) pairs)])
      host (encoded (encodeList id (pairs.map (committedKeyTerm choiceTerm names))))
  | [], _ => by key_eval using (agreement) unfolding [encodeList]
  | pair :: rest, covered => by
      have first := key_extract_returns program agreement choiceTerm table operations names host pair
        (covered pair List.mem_cons_self)
      have later := key_project_returns choiceTerm table operations names host rest
        (fun next member => covered next (List.mem_cons_of_mem _ member))
      key_eval using (agreement) [first,later] unfolding [encodeList]

private local instance keyEquationEq : DecidableEq SpaceSemantics.Equation := by
  intro left right
  apply decidable_of_iff (left.head = right.head ∧ left.arguments = right.arguments ∧ left.body = right.body)
  constructor
  · rintro ⟨head, arguments, body⟩
    cases left; cases right; cases head; cases arguments; cases body; rfl
  · intro same; cases same; exact ⟨rfl,rfl,rfl⟩

def keyPrimitiveHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || ["gslt:automata:binding", "gslt:automata:member",
    "gslt:automata:unique", "gslt:automata:unique-acc"].contains head

omit agreement in
theorem keyPrimitive_closed : ProgramClosed keyPrimitiveHeads MatchAutomataProgram.program := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked : MatchAutomataProgram.program.equations.all
        (fun row => !keyPrimitiveHeads row.head || codeWithin keyPrimitiveHeads row.body) = true := by decide +kernel
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row

omit agreement in
theorem keyPrimitive_metadata :
    ProgramAgreementOn keyPrimitiveHeads MatchAutomataProgram.program keyLibrary.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

include agreement in
theorem unique_returns (host : Effects.State) (terms : List Term) :
    PureReturns program [] host
      (apply "gslt:automata:unique" [encoded (encodeList id terms)])
      host (encoded (encodeList id terms.eraseDups)) := by
  have within : ∀ head, keyPrimitiveHeads head = true → keyHeads head = true := by
    intro head supported
    simp only [keyPrimitiveHeads, Bool.or_eq_true] at supported
    rcases supported with literal | selected
    · simp only [keyHeads, literal, Bool.true_or]
    · simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at selected
      rcases selected with same | same | same | same <;> subst head <;> decide +kernel
  have agreed := agreement_trans keyPrimitive_metadata (agreement_mono within agreement)
  refine transport_call keyPrimitive_closed agreed (head := "gslt:automata:unique")
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
    ["xs"] (by decide) (by rfl) ?_ (MatchAutomataInventoryExecution.unique_returns host terms)
  intro index bounded
  have zero : index = 0 := by simpa using bounded
  subst index
  decide +kernel

include agreement in
theorem key_unique_returns {Choice : Type} (choiceTerm : Choice → Term)
    (table : List String) (operations : CanonOperations program table) (names : List String)
    (host : Effects.State) (pairs : List (Committed Choice))
    (covered : ∀ pair ∈ pairs, ∀ name ∈ names, ∀ value, lookup pair.2.completed name = some value →
      CanonicalCompare.Covered table value.body) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-unique"
        [CompleteExecution.tableValue table, encoded (encodeList Term.string names),
          encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith choiceTerm) pairs)])
      host (encoded (encodeList id (pairs.map (committedKeyTerm choiceTerm names)).eraseDups)) := by
  have projected := key_project_returns program agreement choiceTerm table operations names host pairs covered
  have unique := unique_returns program agreement host (pairs.map (committedKeyTerm choiceTerm names))
  key_eval using (agreement) [projected,unique]

#print axioms key_extract_returns
#print axioms key_project_returns
#print axioms keyPrimitive_closed
#print axioms keyPrimitive_metadata
#print axioms unique_returns
#print axioms key_unique_returns

include agreement in
theorem key_binary_returns (host : Effects.State) (head : String) (selected authored : Nat)
    (site history : Term) (first intermediate last : Option RuleBinding.ContextualValue) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-binary" [encoded (.string head),
        encoded (.application "DeclaredFiringKey" [.natural selected, .natural authored, site,
          encodeList (encodeOption contextualValueTerm) [first,intermediate,last], history])])
      host (encoded (encodeOption InferenceCettaWire.encodePattern
        (do let first ← first; let last ← last; pure (.apply head [first.body,last.body])))) := by
  cases first <;> cases last <;>
    simp only [Option.bind_eq_bind,Option.bind_none,Option.bind_some] <;>
    key_eval using (agreement) unfolding [encodeList,encodeOption,contextualValueTerm,
      InferenceCettaWire.encodePattern,InferenceCettaWire.encodePatterns]

include agreement in
theorem key_conclusions_returns {Key : Type} (keyTerm : Key → Term) (conclusion : Key → Option Pattern)
    (host : Effects.State) (head : String) :
    ∀ keys : List Key,
    (∀ key ∈ keys, PureReturns program [] host
      (apply "gslt:occurrence-search:key-binary" [encoded (.string head),encoded (keyTerm key)])
      host (encoded (encodeOption InferenceCettaWire.encodePattern (conclusion key)))) →
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-conclusions" [encoded (.string head),encoded (encodeList keyTerm keys)])
      host (encoded (encodeList InferenceCettaWire.encodePattern (keys.filterMap conclusion)))
  | [], _ => by key_eval using (agreement) unfolding [encodeList]
  | key :: rest, primitive => by
      have first := primitive key List.mem_cons_self
      have later := key_conclusions_returns keyTerm conclusion host head rest
        (fun next member => primitive next (List.mem_cons_of_mem _ member))
      cases found : conclusion key <;>
        key_eval using (agreement) [first,later] unfolding [encodeList,encodeOption,List.filterMap_cons,found]

private theorem encoded_eraseDups_loop {Key : Type} [BEq Key] [LawfulBEq Key]
    (keyTerm : Key → Term) (faithful : Function.Injective keyTerm) (keys seen : List Key) :
    List.eraseDupsBy.loop (· == ·) (keys.map keyTerm) (seen.map keyTerm) =
      (List.eraseDupsBy.loop (· == ·) keys seen).map keyTerm := by
  induction keys generalizing seen with
  | nil => simp [List.eraseDupsBy.loop]
  | cons first rest ih =>
      have sameContains : (seen.map keyTerm).contains (keyTerm first) = seen.contains first := by
        apply Bool.eq_iff_iff.mpr
        simp [faithful.eq_iff]
      simp only [List.map_cons,List.eraseDupsBy.loop,List.any_beq,sameContains]
      cases present : seen.contains first
      · simpa [present,List.map_cons] using ih (first :: seen)
      · simpa [present] using ih seen

omit agreement in
theorem encoded_eraseDups {Key : Type} [BEq Key] [LawfulBEq Key]
    (keyTerm : Key → Term) (faithful : Function.Injective keyTerm) (keys : List Key) :
    (keys.map keyTerm).eraseDups = keys.eraseDups.map keyTerm :=
  encoded_eraseDups_loop keyTerm faithful keys []

include agreement in
theorem key_bag_returns {Choice Key : Type} [DecidableEq Key] (choiceTerm : Choice → Term)
    (table : List String) (operations : CanonOperations program table) (names : List String)
    (head : String) (keyTerm : Key → Term) (identity : Committed Choice → Key)
    (faithful : Function.Injective keyTerm)
    (coordinates : ∀ pair, committedKeyTerm choiceTerm names pair = keyTerm (identity pair))
    (conclusion : Key → Option Pattern) (host : Effects.State) (pairs : List (Committed Choice))
    (covered : ∀ pair ∈ pairs, ∀ name ∈ names, ∀ value, lookup pair.2.completed name = some value →
      CanonicalCompare.Covered table value.body)
    (primitive : ∀ key ∈ orderedCommittedKeys identity pairs, PureReturns program [] host
      (apply "gslt:occurrence-search:key-binary" [encoded (.string head),encoded (keyTerm key)])
      host (encoded (encodeOption InferenceCettaWire.encodePattern (conclusion key)))) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-bag"
        [CompleteExecution.tableValue table,encoded (encodeList Term.string names),encoded (.string head),
          encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith choiceTerm) pairs)])
      host (encoded (encodeList InferenceCettaWire.encodePattern
        ((orderedCommittedKeys identity pairs).filterMap conclusion))) := by
  have projected := key_unique_returns program agreement choiceTerm table operations names host pairs covered
  have encodedKeys : pairs.map (committedKeyTerm choiceTerm names) = (pairs.map identity).map keyTerm := by
    simp only [List.map_map]
    exact List.map_congr_left (fun pair _ => coordinates pair)
  have keyOutput : encodeList id (pairs.map (committedKeyTerm choiceTerm names)).eraseDups =
      encodeList keyTerm (orderedCommittedKeys identity pairs) := by
    rw [encodedKeys,encoded_eraseDups keyTerm faithful]
    simp only [encodeList_map,Function.id_comp]
    rfl
  rw [keyOutput] at projected
  have readout := key_conclusions_returns program agreement keyTerm conclusion host head
    (orderedCommittedKeys identity pairs) primitive
  key_eval using (agreement) [projected,readout]

include agreement in
theorem key_facts_returns {Choice Key : Type} [DecidableEq Key] (choiceTerm : Choice → Term)
    (table : List String) (operations : CanonOperations program table) (names : List String)
    (head : String) (keyTerm : Key → Term) (identity : Committed Choice → Key)
    (faithful : Function.Injective keyTerm)
    (coordinates : ∀ pair, committedKeyTerm choiceTerm names pair = keyTerm (identity pair))
    (conclusion : Key → Option Pattern) (host : Effects.State) (pairs : List (Committed Choice))
    (covered : ∀ pair ∈ pairs, ∀ name ∈ names, ∀ value, lookup pair.2.completed name = some value →
      CanonicalCompare.Covered table value.body)
    (primitive : ∀ key ∈ orderedCommittedKeys identity pairs, PureReturns program [] host
      (apply "gslt:occurrence-search:key-binary" [encoded (.string head),encoded (keyTerm key)])
      host (encoded (encodeOption InferenceCettaWire.encodePattern (conclusion key)))) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-facts"
        [CompleteExecution.tableValue table,encoded (encodeList Term.string names),encoded (.string head),
          encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith choiceTerm) pairs)])
      host (encoded (encodeList InferenceCettaWire.encodePattern
        ((orderedCommittedKeys identity pairs).filterMap conclusion).eraseDups)) := by
  have bag := key_bag_returns program agreement choiceTerm table operations names head keyTerm identity
    faithful coordinates conclusion host pairs covered primitive
  have unique := unique_returns program agreement host
    (((orderedCommittedKeys identity pairs).filterMap conclusion).map InferenceCettaWire.encodePattern)
  rw [encoded_eraseDups InferenceCettaWire.encodePattern InferenceCettaWire.encodePattern_injective] at unique
  simp only [encodeList_map,Function.id_comp] at unique
  key_eval using (agreement) [bag,unique]

#print axioms key_binary_returns
#print axioms key_conclusions_returns
#print axioms encoded_eraseDups
#print axioms key_bag_returns
#print axioms key_facts_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.Declared


namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.Canonical
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise CanonicalCompare CollectionOccurrenceBatch
open SpaceSemantics Eval BridgeKit WireKit

/-- Public execution projects all declared free types while covering every name in the actual input syntax. -/
def configForInput (plan : GeneralExecutionAdmission.Plan) (source : Pattern)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = []) :
    CollectionOccurrenceBatchExecution.Canonical.Config plan :=
  CollectionOccurrenceBatchExecution.Canonical.Config.forFootprint plan
    ((CanonicalBags.canon source).freeFvarNames ++
      (Complete.Footprint.declaredFootprint plan ++ providerFreeNames (GeneralPlanEnvironment.environment plan).provider))
    finite (fun _ member => List.mem_append_right _ (List.mem_append_right _ member))
    (CanonicalCompare.names source)

theorem configForInput_source_within (plan : GeneralExecutionAdmission.Plan) (source : Pattern)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = []) :
    ∀ name ∈ (CanonicalBags.canon source).freeFvarNames, name ∈ (configForInput plan source finite).footprint :=
  fun _ member => List.mem_append_left _ member

theorem configForInput_declared (plan : GeneralExecutionAdmission.Plan) (source : Pattern)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = []) :
    Complete.Footprint.Declared plan (configForInput plan source finite).footprint := by
  intro name type found
  exact List.mem_append_right _ (List.mem_append_left _ (Complete.Footprint.declared_footprint name type found))

theorem configForInput_covered (plan : GeneralExecutionAdmission.Plan) (source : Pattern)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = []) :
    Covered (configForInput plan source finite).names source := by
  intro name member
  exact StructuralDescent.Scheduled.NameSupport.environment_table_footprint _ _ name
    (List.mem_append_left _ member)

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}

theorem input_ready (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (admitted : ∀ declaration ∈ plan.rules,
      RuleBinding.admittedFor declaration.rule declaration.binding.spec = true)
    (canonical : (CanonicalBags.canon source).hasCanonicalBinderMetadata = true) :
    CollectionOccurrenceMachineExecution.Canonical.Ready (configForInput plan source finite)
      (CollectionOccurrenceSearch.beginWith RecursiveCollectionHandoff.canonicalMatchingExecution
        plan bound expected source).state :=
  CollectionOccurrenceMachineExecution.Canonical.begin_ready _ (configForInput_source_within _ _ _) admitted canonical

theorem run_ready (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (admitted : ∀ declaration ∈ plan.rules,
      RuleBinding.admittedFor declaration.rule declaration.binding.spec = true)
    (canonical : (CanonicalBags.canon source).hasCanonicalBinderMetadata = true) (depth work : Nat) :
    CollectionOccurrenceMachineExecution.Canonical.Ready (configForInput plan source finite)
      (CollectionOccurrenceSearch.runWith plan bound expected
        (fun source => canonicalSeedProfile plan bound expected source) depth source work).state :=
  CollectionOccurrenceMachineExecution.Canonical.run_ready _ depth work _ (input_ready finite admitted canonical)

theorem run_balanced (depth work : Nat) :
    (CollectionOccurrenceSearch.runWith plan bound expected
      (fun source => canonicalSeedProfile plan bound expected source) depth source work).state.batch.Balanced :=
  (CollectionOccurrenceMachine.runWith_invariant (canonicalSeedProfile plan bound expected source) depth work
    (CollectionOccurrenceMachine.beginWith_invariant RecursiveCollectionHandoff.canonicalMatchingExecution depth)).1

/-- The public input fixes the name table and initial typed jobs before any continuation outcome exists. -/
theorem run_machine_returns (host : Effects.State)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (admitted : ∀ declaration ∈ plan.rules,
      RuleBinding.admittedFor declaration.rule declaration.binding.spec = true)
    (canonical : (CanonicalBags.canon source).hasCanonicalBinderMetadata = true) (depth work : Nat) :
    let config := configForInput plan source finite
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-machine:run" [encoded (CettaWire.encodeList CettaWire.Term.string config.names),
        encoded (CollectionOccurrenceBatchExecution.Canonical.environmentTerm config), number depth, number work,
        encoded (CollectionOccurrenceMachineExecution.Canonical.stateTerm
          (CollectionOccurrenceSearch.beginWith RecursiveCollectionHandoff.canonicalMatchingExecution
            plan bound expected source).state)]) host
      (encoded (CollectionOccurrenceMachineExecution.Canonical.stateTerm
        (CollectionOccurrenceSearch.runWith plan bound expected
          (fun source => canonicalSeedProfile plan bound expected source) depth source work).state)) :=
  CollectionOccurrenceMachineExecution.Canonical.run_returns host _ depth work _ (input_ready finite admitted canonical)

#print axioms configForInput
#print axioms configForInput_source_within
#print axioms configForInput_declared
#print axioms configForInput_covered
#print axioms input_ready
#print axioms run_ready
#print axioms run_balanced
#print axioms run_machine_returns
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.Canonical


namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.Canonical
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise CanonicalCompare CollectionOccurrenceBatch
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics Eval BridgeKit WireKit

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr} {expected : TypeExpr}
local notation "CRun" => CollectionOccurrenceSearch.Run plan bound expected RecursiveCollectionHandoff.canonicalMatchingExecution

def runTerm (config : CollectionOccurrenceBatchExecution.Canonical.Config plan) (run : CRun) : Term :=
  runTermWith RetainedMatchingWire.canonicalCodec
    (Interpreted.interpretedPlanTerm config.names plan config.footprint bound expected)
    (fun packet => packet.finishCanonical? plan bound expected) run

/-- The canonical projection is a specialization of the shared complete run wire. -/
theorem runTerm_fields (config : CollectionOccurrenceBatchExecution.Canonical.Config plan) (run : CRun) :
    runTerm config run = .application "RecursiveOccurrenceRun"
      [Interpreted.interpretedPlanTerm config.names plan config.footprint bound expected,
        InferenceCettaWire.encodePattern run.source,
        CollectionOccurrenceMachineExecution.Canonical.stateTerm (sourcePattern := run.source) run.state,
        encodeList (ScopedRuleJobReadoutExecution.receiptTermWith RecursiveCollectionExecution.eventTerm)
          (CollectionOccurrenceSearch.publicationWith (fun packet => packet.finishCanonical? plan bound expected) run)] := by
  simp only [runTerm, runTermWith, CollectionOccurrenceBatchExecution.stateTermWith_canonical]
  rfl

/-- The published cache is computed from the original complete packet log by the actual checked finisher. -/
theorem with_state_returns (host : Effects.State) (config : CollectionOccurrenceBatchExecution.Canonical.Config plan)
    (run : CRun) (balanced : run.state.batch.Balanced)
    (declared : Complete.Footprint.Declared plan config.footprint) :
    PureReturns SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-search:with-state"
        [encoded (Interpreted.interpretedPlanTerm config.names plan config.footprint bound expected),
          encoded (InferenceCettaWire.encodePattern run.source),
          encoded (CollectionOccurrenceMachineExecution.Canonical.stateTerm (sourcePattern := run.source) run.state)])
      host (encoded (runTerm config run)) := by
  have publicationEncoder : CollectionOccurrenceBatchExecution.Canonical.publicationTerm =
      CollectionOccurrenceBatchExecution.publicationTermWith RecursiveCollectionExecution.eventTerm := rfl
  have observed := SelectedNativeSource.canonical_read_log_returns host config.names config.footprint
    (source := run.source) run.state.batch balanced declared
  rw [← publicationEncoder] at observed
  occurrence_search_eval unfolding
    [runTerm_fields, CollectionOccurrenceMachineExecution.Canonical.stateTerm,
      CollectionOccurrenceBatchExecution.Canonical.stateTerm,
      CollectionOccurrenceSearch.publicationWith, CollectionOccurrenceBatchExecution.Canonical.publicationTerm]
  apply pure_let_returns _ _ _ _ _ _ _ _ (by rfl)
  · refine PureData.raw_capture_returns _ [] _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ observed
    · rw [← proof_agreement.dispatch _ (by decide +kernel)]
      decide +kernel
    · intro index bounded
      rw [← proof_agreement.demand _ index (by decide +kernel)]
      simp only [List.length_cons, List.length_nil, Nat.zero_add] at bounded
      revert index
      decide +kernel
    · decide
    · simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,
        List.map_cons, List.map_nil, CettaWireAtom.applySubst_encode, encoded]; rfl
  · metta_eval with proof_checked in proof_agreement unfolding
      [runTerm_fields, CollectionOccurrenceSearch.publicationWith,
        CollectionOccurrenceMachineExecution.Canonical.stateTerm,
        CollectionOccurrenceBatchExecution.Canonical.stateTerm,
        CollectionOccurrenceBatchExecution.Canonical.publicationTerm]

/-- Public execution uses actual typed discovery, the original canonical seed and retained conditional execution. -/
theorem run_returns (host : Effects.State)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (admitted : ∀ declaration ∈ plan.rules,
      RuleBinding.admittedFor declaration.rule declaration.binding.spec = true)
    (input : Pattern) (canonical : (CanonicalBags.canon input).hasCanonicalBinderMetadata = true)
    (depth work : Nat) :
    let config := configForInput plan input finite
    PureReturns SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-search:run"
        [encoded (encodeList Term.string config.names), number depth,
          encoded (Interpreted.interpretedPlanTerm config.names plan config.footprint bound expected),
          encoded (InferenceCettaWire.encodePattern input), number work])
      host (encoded (runTerm config (CollectionOccurrenceSearch.runWith plan bound expected
        (fun source => canonicalSeedProfile plan bound expected source) depth input work))) := by
  let config := configForInput plan input finite
  let result := CollectionOccurrenceSearch.runWith plan bound expected
    (fun source => canonicalSeedProfile plan bound expected source) depth input work
  have canonicalized := canon_lower_returns host config.names config.ordered input (configForInput_covered _ _ _)
  have discovered := CollectionOccurrenceDiscoveryExecution.Canonical.begin_returns host plan bound expected input
    config.footprint (configForInput_source_within _ _ _)
  have advanced := run_machine_returns (plan := plan) (bound := bound) (expected := expected)
    (source := input) host finite admitted canonical depth work
  have observed := with_state_returns host config result (run_balanced depth work) (configForInput_declared _ _ _)
  have viewed := Interpreted.canonical_environment_returns SelectedNativeSource.runtime
    SelectedNativeSource.metadata_agreement host config.names
    (PremiseOperationsExecution.GeneralExecution.environmentTerm (GeneralPlanEnvironment.environment plan)
      (plan.snapshot.free.entriesOn config.footprint))
  have freeSame : (GeneralPlanEnvironment.environment plan).free = plan.snapshot.free := rfl
  have freeEncoding (table : List (String × TypeExpr)) :
      PremiseOperationsExecution.DeclarationTyping.freeContextTerm table =
        MatchAutomataBindingExecution.payloadBindingsTerm
          (table.map fun entry => (entry.1, InferenceCettaWire.AuthoredRule.typeTerm entry.2)) := rfl
  occurrence_search_eval unfolding
    [Interpreted.interpretedPlanTerm, CompletePlanWire.planTermWithEnvironment,
      CollectionOccurrenceBatchExecution.Canonical.environmentTerm,
      RetainedMatchingWire.interpretedEnvironmentTerm,
      CollectionOccurrenceSearch.runWith, CollectionOccurrenceSearch.beginWith,
      PremiseOperationsExecution.GeneralExecution.environmentTerm,
      CompleteExecution.environmentValue, freeSame, result,
      PremiseOperationsExecution.DeclarationTyping.declarationsTerm,
      PremiseOperationsExecution.DeclarationTyping.freeContextTerm,
      PremiseOperationsExecution.DeclarationTyping.boundContextTerm,
      encodeList, InferenceCettaWire.encodeList]
  apply pure_case_returns _ _ _ _ _ _ _ _ rfl
  · metta_capture_agreed proof_agreement from viewed unfolding
      [Interpreted.interpretedPlanTerm, CompletePlanWire.planTermWithEnvironment,
        RetainedMatchingWire.interpretedEnvironmentTerm,
        PremiseOperationsExecution.GeneralExecution.environmentTerm, config, freeEncoding]
  · metta_select [CettaWireAtom.encode, CettaWireAtom.encodeMany, encoded, number,
      PremiseOperationsExecution.GeneralExecution.environmentTerm]
  · intro selected body selection
    metta_select [CettaWireAtom.encode, CettaWireAtom.encodeMany, encoded, number,
      PremiseOperationsExecution.GeneralExecution.environmentTerm] at selection
    obtain ⟨bindings, branch⟩ := selection
    subst bindings
    subst branch
    apply pure_let_star_returns _ _ _ _ _ _ _ rfl
    apply pure_let_returns _ _ _ _ _ _ _ _ (by rfl)
    · metta_capture_agreed proof_agreement from canonicalized unfolding [config, InferenceCettaWire.encodeList]
    · apply pure_let_returns _ _ _ _ _ _ _ _ (by rfl)
      · metta_capture_agreed proof_agreement from discovered unfolding
          [PremiseOperationsExecution.DeclarationTyping.declarationsTerm,
            PremiseOperationsExecution.DeclarationTyping.freeContextTerm,
            PremiseOperationsExecution.DeclarationTyping.boundContextTerm,
            CollectionOccurrenceSearch.beginWith, encodeList, InferenceCettaWire.encodeList, freeEncoding]
      · apply pure_let_returns _ _ _ _ _ _ _ _ (by rfl)
        · metta_capture_agreed proof_agreement from advanced unfolding
            [CollectionOccurrenceSearch.beginWith, CollectionOccurrenceBatchExecution.Canonical.environmentTerm,
              RetainedMatchingWire.interpretedEnvironmentTerm, PremiseOperationsExecution.GeneralExecution.environmentTerm,
              freeSame, config, freeEncoding, InferenceCettaWire.encodeList]
        · metta_capture_agreed proof_agreement from observed unfolding
            [Interpreted.interpretedPlanTerm, CompletePlanWire.planTermWithEnvironment,
              RetainedMatchingWire.interpretedEnvironmentTerm, PremiseOperationsExecution.GeneralExecution.environmentTerm,
              CollectionOccurrenceSearch.runWith, result, freeSame, config, freeEncoding, InferenceCettaWire.encodeList]

/-- Resumption advances the same retained state and recomputes only its readout cache. -/
theorem resume_returns (host : Effects.State)
    (config : CollectionOccurrenceBatchExecution.Canonical.Config plan) (depth work : Nat)
    (run : CRun) (ready : CollectionOccurrenceMachineExecution.Canonical.Ready config run.state)
    (valid : CollectionOccurrenceMachine.Invariant depth run.state)
    (declared : Complete.Footprint.Declared plan config.footprint) :
    PureReturns SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-search:resume" [encoded (encodeList Term.string config.names), number depth,
        encoded (runTerm config run), number work]) host
      (encoded (runTerm config (CollectionOccurrenceSearch.resumeWith
        (fun source => canonicalSeedProfile plan bound expected source) depth run work))) := by
  have advanced := CollectionOccurrenceMachineExecution.Canonical.run_returns
    (sourcePattern := run.source) host config depth work run.state ready
  have balanced := (CollectionOccurrenceMachine.runWith_invariant
    (canonicalSeedProfile plan bound expected run.source) depth work valid).1
  have observed := with_state_returns host config
    (CollectionOccurrenceSearch.resumeWith (fun source => canonicalSeedProfile plan bound expected source) depth run work)
    balanced declared
  have freeSame : (GeneralPlanEnvironment.environment plan).free = plan.snapshot.free := rfl
  occurrence_search_eval [advanced, observed] unfolding
    [runTerm_fields, Interpreted.interpretedPlanTerm, CompletePlanWire.planTermWithEnvironment,
      CollectionOccurrenceBatchExecution.Canonical.environmentTerm,
      CollectionOccurrenceSearch.resumeWith, RetainedMatchingWire.interpretedEnvironmentTerm,
      PremiseOperationsExecution.GeneralExecution.environmentTerm,
      CompleteExecution.environmentValue, freeSame]

/-- Splitting the work budget preserves the whole run, including packet origins and all premise histories. -/
theorem resumed_run_returns (host : Effects.State)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (admitted : ∀ declaration ∈ plan.rules,
      RuleBinding.admittedFor declaration.rule declaration.binding.spec = true)
    (input : Pattern) (canonical : (CanonicalBags.canon input).hasCanonicalBinderMetadata = true)
    (depth first extra : Nat) :
    let config := configForInput plan input finite
    PureReturns SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-search:resume" [encoded (encodeList Term.string config.names), number depth,
        encoded (runTerm config (CollectionOccurrenceSearch.runWith plan bound expected
          (fun source => canonicalSeedProfile plan bound expected source) depth input first)), number extra]) host
      (encoded (runTerm config (CollectionOccurrenceSearch.runWith plan bound expected
        (fun source => canonicalSeedProfile plan bound expected source) depth input (first + extra)))) := by
  have ready := run_ready (plan := plan) (bound := bound) (expected := expected) (source := input)
    finite admitted canonical depth first
  have valid := CollectionOccurrenceMachine.runWith_invariant
    (canonicalSeedProfile plan bound expected input) depth first
    (CollectionOccurrenceMachine.beginWith_invariant RecursiveCollectionHandoff.canonicalMatchingExecution depth)
  have resumed := resume_returns host (configForInput plan input finite) depth extra
    (CollectionOccurrenceSearch.runWith plan bound expected
      (fun source => canonicalSeedProfile plan bound expected source) depth input first)
    ready valid (configForInput_declared _ _ _)
  simpa only [CollectionOccurrenceSearch.resumeWith_runWith] using resumed

/-- Reading the published view does not replay matching or premise validation. -/
theorem publication_returns (host : Effects.State) (config : CollectionOccurrenceBatchExecution.Canonical.Config plan)
    (run : CRun) :
    PureReturns SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-search:publication" [encoded (runTerm config run)]) host
      (encoded (encodeList (ScopedRuleJobReadoutExecution.receiptTermWith RecursiveCollectionExecution.eventTerm)
        (CollectionOccurrenceSearch.publicationWith (fun packet => packet.finishCanonical? plan bound expected) run))) := by
  rw [runTerm_fields]
  exact publication_wire_returns SelectedNativeSource.runtime proof_agreement host _ _ _ _


#print axioms runTerm_fields
#print axioms with_state_returns
#print axioms run_returns
#print axioms resume_returns
#print axioms resumed_run_returns
#print axioms publication_returns
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.Canonical

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.finish_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.read_log_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.with_state_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.publication_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.resume_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.run_returns
