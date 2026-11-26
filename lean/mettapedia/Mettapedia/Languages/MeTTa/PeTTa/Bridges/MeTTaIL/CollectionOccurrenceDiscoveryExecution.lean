import Mettapedia.Languages.MeTTa.PeTTa.EquationEquality
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceMachineExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContextExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralTypedSiteExecution.Traversal

/-!
# Native discovery of retained collection matcher lanes

Typed rule-job enumeration and residual-context variants produce the actual
initial matcher lanes. Ordinary and canonical execution share this traversal
and retain the complete job origins before any continuation is advanced.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceDiscoveryExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open GeneralPremise CanonicalCompare CollectionOccurrenceHandoff CollectionOccurrenceBatch CollectionOccurrenceMatcher
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics Eval BridgeKit WireKit
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_occurrence_discovery.metta"
    sha256 "e9a6245831dd80046f26c38e13509251840c3c5c4a6d7c5460e1fdab76fadcdc"


def library : Library := CollectionOccurrenceSearchExecution.SelectedNativeSource.library

theorem checked : library.check = true := CollectionOccurrenceSearchExecution.SelectedNativeSource.checked

private local instance discoveryEquationEq : DecidableEq SpaceSemantics.Equation :=
  SpaceSemantics.Equation.decideEq

private def discoveryMetadataBase : Program :=
  (((((RuleExecutionProgram.callFragment ["gslt:automata:append", "gslt:automata:length"]
        RuleExecutionProgram.scopedProgram).append
      (RuleExecutionProgram.callFragment ["gslt:sites:jobs"]
        (RuleExecutionProgram.interpretedPremiseSupportSources[0]'(by decide +kernel)).program)).append
      (RuleExecutionProgram.callFragment ["gslt:collection-search:elaborated-types"]
        (RuleExecutionProgram.interpretedPremiseSupportSources[7]'(by decide +kernel)).program)).append
      (RuleExecutionProgram.callFragment ["gslt:collection-context:site-variants"]
        (RuleExecutionProgram.interpretedPremiseSupportSources[9]'(by decide +kernel)).program)).append
      (RuleExecutionProgram.callFragment ["gslt:occurrence-matcher:begin"]
        (RuleExecutionProgram.interpretedPremiseSupportSources[16]'(by decide +kernel)).program)).append
      (RuleExecutionProgram.callFragment ["gslt:occurrence-machine:from-lanes"]
        (RuleExecutionProgram.interpretedPremiseSupportSources[18]'(by decide +kernel)).program)

def discoveryLibrary : Library := ⟨discoveryMetadataBase, source.program, ["gslt:occurrence-discovery:"]⟩
def discoveryHeads (head : String) : Bool := !head.startsWith "gslt:" || discoveryLibrary.owns head ||
  ["gslt:automata:append", "gslt:automata:length", "gslt:sites:jobs", "gslt:collection-search:elaborated-types",
    "gslt:collection-context:site-variants", "gslt:occurrence-matcher:begin", "gslt:occurrence-machine:from-lanes"].contains head

theorem discovery_checked : discoveryLibrary.check = true := by decide +kernel


theorem discovery_agreement : ProgramAgreementOn discoveryHeads discoveryLibrary.runtime
    CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel


private theorem raw_metadata : ProgramAgreementOn discoveryHeads discoveryLibrary.runtime
    RuleExecutionProgram.interpretedPremiseProgram := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel



theorem typed_jobs_agreement : ProgramAgreementOn GeneralTypedSiteExecution.executionHeads
    GeneralTypedSiteExecution.program CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime := by
  apply agreement_trans GeneralTypedSiteExecution.raw_agreement
  apply agreement_mono _ CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement
  intro head supported
  have checked : GeneralTypedSiteExecution.executionHeadNames.all
      CollectionOccurrenceSearchExecution.SelectedNativeSource.lowerHeads = true := by decide +kernel
  exact List.all_eq_true.mp checked head (List.contains_iff_mem.mp supported)

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr} {expected : TypeExpr} {sourcePattern : Pattern}

/-- Typed jobs are the actual generator output; source validity is not supplied as an execution oracle. -/
theorem typed_jobs_returns (host : Effects.State) (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (subject : Pattern) (footprint : List String)
    (covered : ∀ name ∈ subject.freeFvarNames, name ∈ footprint) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:sites:jobs"
        [encoded (PremiseOperationsExecution.DeclarationTyping.declarationsTerm (GeneralPlanEnvironment.environment plan).language.terms),
          encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm (plan.snapshot.free.entriesOn footprint)),
          encoded (InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites),
          encoded (PremiseOperationsExecution.DeclarationTyping.boundContextTerm bound),
          encoded (InferenceCettaWire.AuthoredRule.typeTerm expected), encoded (InferenceCettaWire.encodePattern subject),
          encoded (encodeList ScopedRuleJobReadoutExecution.rulePlanTerm plan.rules)]) host
      (encoded (encodeList ScopedRuleJobReadoutExecution.jobTerm (GeneralRuleJobs.jobs plan bound expected subject))) := by
  apply transport_call GeneralTypedSiteExecution.program_closed typed_jobs_agreement (by decide +kernel) (by decide)
    (by decide +kernel) (by decide) ["declarations", "free", "permissions", "bound", "expected", "source", "rules"]
    (by decide) (by rfl) (by decide +kernel)
  exact GeneralTypedSiteExecution.jobs_plan_returns host plan bound expected subject footprint covered

private theorem append_returns {α : Type} (encoder : α → Term) (host : Effects.State) (left right : List α) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:automata:append" [encoded (encodeList encoder left), encoded (encodeList encoder right)]) host
      (encoded (encodeList encoder (left ++ right))) := by
  apply transport_call CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_closed
    CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement (by decide +kernel) (by decide)
    (by rw [← raw_metadata.dispatch _ (by decide +kernel)]; decide +kernel) (by decide)
    ["left", "right"] (by decide) (by rfl)
    (by intro index bounded; have small : index < 2 := by simpa using bounded
        rw [← raw_metadata.demand _ index (by decide +kernel)]; interval_cases index <;> decide +kernel)
  exact CollectionSelectionExecution.scoped_append_returns encoder host left right

private theorem length_returns {α : Type} (encoder : α → Term) (host : Effects.State) (items : List α) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:automata:length" [encoded (encodeList encoder items)]) host (number items.length) := by
  apply transport_call CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_closed
    CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement (by decide +kernel) (by decide)
    (by rw [← raw_metadata.dispatch _ (by decide +kernel)]; decide +kernel) (by decide)
    ["items"] (by decide) (by rfl)
    (by intro index bounded; have small : index = 0 := by simpa using bounded
        subst index; rw [← raw_metadata.demand _ 0 (by decide +kernel)]; decide +kernel)
  exact CollectionSelectionExecution.scoped_length_returns encoder host items

private def elaborationLibrary : Library := ⟨
  RuleExecutionProgram.callFragment ["gslt:automata:append"] RuleExecutionProgram.scopedProgram,
  RuleExecutionProgram.callFragment ["gslt:collection-search:elaborated-types"]
    (RuleExecutionProgram.interpretedPremiseSupportSources[7]'(by decide +kernel)).program,
  ["gslt:collection-search:elaborated-types"]⟩
private def elaborationHeads (head : String) : Bool := !head.startsWith "gslt:" ||
  elaborationLibrary.owns head || head == "gslt:automata:append"
private theorem elaboration_checked : elaborationLibrary.check = true := by decide +kernel
private theorem elaboration_agreement : ProgramAgreementOn elaborationHeads elaborationLibrary.runtime
    CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

/-- The wire origin elaborates exactly the actual binding plan's implicit type declarations. -/
private theorem elaborated_types_returns (host : Effects.State) (types : List (String × TypeExpr))
    (binding : GeneralRuleBindingInference.BindingPlan) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:collection-search:elaborated-types"
        [encoded (encodeList InferenceCettaWire.AuthoredRule.typeBindingTerm types),
          encoded (ScopedRuleJobReadoutExecution.originTerm binding.origin)]) host
      (encoded (encodeList InferenceCettaWire.AuthoredRule.typeBindingTerm (types ++ binding.implicitTypes))) := by
  cases binding with
  | mk spec origin =>
    cases origin with
    | authored =>
      metta_call_in elaboration_checked using elaboration_agreement
      metta_eval with elaboration_checked in elaboration_agreement unfolding
        [ScopedRuleJobReadoutExecution.originTerm, GeneralRuleBindingInference.BindingPlan.implicitTypes,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst, Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,
          List.find?, CettaWireAtom.encode, CettaWireAtom.encodeMany]
    | inferredRootInputs =>
      metta_call_in elaboration_checked using elaboration_agreement
      metta_eval with elaboration_checked in elaboration_agreement unfolding
        [ScopedRuleJobReadoutExecution.originTerm, GeneralRuleBindingInference.BindingPlan.implicitTypes,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst, Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,
          List.find?, CettaWireAtom.encode, CettaWireAtom.encodeMany]
    | inferredGrammar implicitTypes =>
      have appended := append_returns InferenceCettaWire.AuthoredRule.typeBindingTerm host types implicitTypes
      metta_call_in elaboration_checked using elaboration_agreement
      metta_eval [appended] with elaboration_checked in elaboration_agreement unfolding
        [ScopedRuleJobReadoutExecution.originTerm, GeneralRuleBindingInference.BindingPlan.implicitTypes,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst, Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,
          List.find?, CettaWireAtom.encode, CettaWireAtom.encodeMany]

def begunTerm (job : Job) : Term := .application "RecursiveOccurrenceLane"
  [CollectionOccurrenceMatcherExecution.originTerm job,
    RuleInstantiationExecution.GeneralExecution.matcherRequestTerm job.request,
    RecursiveCollectionExecution.stateTerm (RecursiveCollectionMachine.start job.request), .natural 0]

private theorem matcher_agreement : ProgramAgreementOn CollectionOccurrenceMatcherExecution.matcherProofHeads
    CollectionOccurrenceMatcherExecution.matcherProofLibrary.runtime
    CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

private theorem start_returns (host : Effects.State) (request : RecursiveCollectionMachine.Request) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:recursive-collection:start" [encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm request)]) host
      (encoded (RecursiveCollectionExecution.stateTerm (RecursiveCollectionMachine.start request))) := by
  have metadata := RecursiveCollectionExecution.recursiveProof_agreement
  apply transport_call CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_closed
    CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement (by decide +kernel) (by decide)
    (by rw [← metadata.dispatch _ (by decide +kernel)]; decide +kernel) (by decide)
    ["request"] (by decide) (by rfl)
    (by intro index bounded; have small : index = 0 := by simpa using bounded
        subst index; rw [← metadata.demand _ 0 (by decide +kernel)]; decide +kernel)
  exact RecursiveCollectionExecution.start_returns host request

theorem begin_job_returns (host : Effects.State) (job : Job) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-matcher:begin" [encoded (CollectionOccurrenceMatcherExecution.originTerm job),
        encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm job.request)]) host
      (encoded (begunTerm job)) := by
  have begun := start_returns host job.request
  metta_call_in CollectionOccurrenceMatcherExecution.matcherProof_checked using matcher_agreement
  metta_eval [begun] with CollectionOccurrenceMatcherExecution.matcherProof_checked in matcher_agreement unfolding
    [begunTerm, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, CettaWireAtom.encode, CettaWireAtom.encodeMany]

private theorem context_variants_returns (host : Effects.State) (site : GeneralTypedSites.SiteData) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:collection-context:site-variants" [encoded (ScopedRuleJobReadoutExecution.siteTerm site)]) host
      (encoded (encodeList CollectionContextExecution.variantTerm (CollectionSelection.siteVariants site))) := by
  apply transport_call CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_closed
    CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement (by decide +kernel) (by decide)
    (by rw [← raw_metadata.dispatch _ (by decide +kernel)]; decide +kernel) (by decide)
    ["site"] (by decide) (by rfl)
    (by intro index bounded; have small : index = 0 := by simpa using bounded
        subst index; rw [← raw_metadata.demand _ 0 (by decide +kernel)]; decide +kernel)
  exact CollectionContextExecution.site_variants_returns host site

syntax "discovery_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| discovery_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in discovery_checked using discovery_agreement; metta_eval [$facts,*] with discovery_checked in discovery_agreement unfolding
      [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, $extra,*]))

@[metta_head "gslt:occurrence-discovery:variant"]
theorem variant_returns (host : Effects.State) (origin : GeneralRuleJobs.Job) (variant : CollectionSelection.SiteVariant) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-discovery:variant" [encoded (ScopedRuleJobReadoutExecution.jobTerm origin),
        encoded (CollectionContextExecution.variantTerm variant)]) host (encoded (begunTerm ⟨origin, variant⟩)) := by
  have elaborated := elaborated_types_returns host origin.declaration.authored.typeContext origin.declaration.binding
  have counted := length_returns InferenceCettaWire.AuthoredRule.typeTerm host variant.site.focusBound
  have begun := begin_job_returns host ⟨origin, variant⟩
  simp only [CollectionOccurrenceMatcherExecution.originTerm, Job.request,
    RuleInstantiationExecution.GeneralExecution.matcherRequestTerm, GeneralExecutionAdmission.RulePlan.rule,
    GeneralRuleBindingInference.BindingPlan.elaborate, InferenceCettaWire.AuthoredRule.rewriteTerm,
    InferenceCettaWire.AuthoredRule.optionalBindingTerm] at begun
  have emptyBindings : CettaWireAtom.encode (MatchAutomataBindingExecution.payloadBindingsTerm []) = Atom.symbol "LNil" := rfl
  discovery_eval [elaborated, counted, begun] unfolding
    [ScopedRuleJobReadoutExecution.jobTerm, ScopedRuleJobReadoutExecution.rulePlanTerm,
      ScopedRuleJobReadoutExecution.bindingPlanTerm, ScopedRuleJobReadoutExecution.siteTerm,
      CollectionContextExecution.variantTerm, InferenceCettaWire.AuthoredRule.rewriteTerm,
      CollectionOccurrenceMatcherExecution.originTerm, Job.request, begunTerm,
      RuleInstantiationExecution.GeneralExecution.matcherRequestTerm, GeneralExecutionAdmission.RulePlan.rule,
      GeneralRuleBindingInference.BindingPlan.elaborate, InferenceCettaWire.AuthoredRule.optionalBindingTerm,
      RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm, encodeList, InferenceCettaWire.encodeList,
      GeneralRuleBindingInference.BindingPlan.implicitTypes, emptyBindings]
  metta_capture_agreed discovery_agreement from begun unfolding
    [ScopedRuleJobReadoutExecution.jobTerm, ScopedRuleJobReadoutExecution.rulePlanTerm,
      ScopedRuleJobReadoutExecution.bindingPlanTerm, ScopedRuleJobReadoutExecution.siteTerm,
      CollectionContextExecution.variantTerm, InferenceCettaWire.AuthoredRule.rewriteTerm,
      InferenceCettaWire.AuthoredRule.optionalBindingTerm, InferenceCettaWire.AuthoredRule.siteTerm,
      RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
      GeneralRuleBindingInference.BindingPlan.implicitTypes, encodeList, InferenceCettaWire.encodeList, emptyBindings]

@[metta_head "gslt:occurrence-discovery:variants"]
theorem variants_returns (host : Effects.State) (origin : GeneralRuleJobs.Job) :
    ∀ variants : List CollectionSelection.SiteVariant,
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-discovery:variants" [encoded (ScopedRuleJobReadoutExecution.jobTerm origin),
        encoded (encodeList CollectionContextExecution.variantTerm variants)]) host
      (encoded (encodeList (fun variant => begunTerm ⟨origin, variant⟩) variants))
  | [] => by discovery_eval unfolding [encodeList]
  | variant :: variants => by
    have first := variant_returns host origin variant
    have later := variants_returns host origin variants
    discovery_eval [first, later] unfolding [encodeList]

@[metta_head "gslt:occurrence-discovery:jobs"]
theorem jobs_returns (host : Effects.State) : ∀ origins : List GeneralRuleJobs.Job,
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-discovery:jobs" [encoded (encodeList ScopedRuleJobReadoutExecution.jobTerm origins)]) host
      (encoded (encodeList begunTerm (origins.flatMap fun origin =>
        (CollectionSelection.siteVariants origin.site).map fun variant => ⟨origin, variant⟩)))
  | [] => by discovery_eval unfolding [encodeList]
  | origin :: origins => by
    have variants := context_variants_returns host origin.site
    have first := variants_returns host origin (CollectionSelection.siteVariants origin.site)
    have later := jobs_returns host origins
    have appended := append_returns begunTerm host
      ((CollectionSelection.siteVariants origin.site).map fun variant => ⟨origin, variant⟩)
      (origins.flatMap fun origin => (CollectionSelection.siteVariants origin.site).map fun variant => ⟨origin, variant⟩)
    simp only [encodeList_map, Function.comp_def] at appended
    discovery_eval [variants, first, later, appended] unfolding
      [ScopedRuleJobReadoutExecution.jobTerm, List.flatMap_cons, encodeList_map, Function.comp_def]

theorem lanes_encoding (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr) (subject : Pattern) :
    encodeList CollectionOccurrenceMatcherExecution.laneTerm (lanes plan bound expected subject) =
      encodeList begunTerm (CollectionOccurrenceHandoff.jobs plan bound expected subject) := by
  simp only [lanes, encodeList_map]
  change encodeList (fun selected => begunTerm selected.val) (CollectionOccurrenceHandoff.jobs plan bound expected subject).attach = _
  calc
    _ = encodeList begunTerm ((CollectionOccurrenceHandoff.jobs plan bound expected subject).attach.map Subtype.val) :=
      (encodeList_map begunTerm Subtype.val (CollectionOccurrenceHandoff.jobs plan bound expected subject).attach).symm
    _ = _ := congrArg (encodeList begunTerm) (List.attach_map_subtype_val _)
/-- The native factory discovers the actual typed jobs of its current source,
expands their residual contexts, and initializes precisely the retained joint
machine. The caller supplies only the finite free-context projection needed
by the existing typed-site generator. -/
@[metta_head "gslt:occurrence-discovery:begin"]
theorem begin_returns (host : Effects.State) (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (subject : Pattern)
    (footprint : List String) (covered : ∀ name ∈ subject.freeFvarNames, name ∈ footprint) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-discovery:begin"
        [encoded (PremiseOperationsExecution.DeclarationTyping.declarationsTerm
            (GeneralPlanEnvironment.environment plan).language.terms),
          encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm
            (plan.snapshot.free.entriesOn footprint)),
          encoded (InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites),
          encoded (PremiseOperationsExecution.DeclarationTyping.boundContextTerm bound),
          encoded (InferenceCettaWire.AuthoredRule.typeTerm expected),
          encoded (InferenceCettaWire.encodePattern subject),
          encoded (encodeList ScopedRuleJobReadoutExecution.rulePlanTerm plan.rules)])
      host (encoded (CollectionOccurrenceMachineExecution.stateTerm
        (CollectionOccurrenceMachine.begin plan bound expected subject))) := by
  have generated := typed_jobs_returns host plan bound expected subject footprint covered
  have discovered := jobs_returns host (GeneralRuleJobs.jobs plan bound expected subject)
  have initial := CollectionOccurrenceMachineExecution.from_lanes_returns
    (plan := plan) (bound := bound) (expected := expected) (sourcePattern := subject) host
  have started := initial
  rw [lanes_encoding] at started
  discovery_eval [generated, discovered, started] unfolding [CollectionOccurrenceHandoff.jobs]

namespace Canonical

theorem begin_returns (host : Effects.State) (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (subject : Pattern) (footprint : List String)
    (covered : ∀ name ∈ (CanonicalBags.canon subject).freeFvarNames, name ∈ footprint) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-discovery:begin"
        [encoded (PremiseOperationsExecution.DeclarationTyping.declarationsTerm (GeneralPlanEnvironment.environment plan).language.terms),
          encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm (plan.snapshot.free.entriesOn footprint)),
          encoded (InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites),
          encoded (PremiseOperationsExecution.DeclarationTyping.boundContextTerm bound),
          encoded (InferenceCettaWire.AuthoredRule.typeTerm expected), encoded (InferenceCettaWire.encodePattern (CanonicalBags.canon subject)),
          encoded (encodeList ScopedRuleJobReadoutExecution.rulePlanTerm plan.rules)]) host
      (encoded (CollectionOccurrenceMachineExecution.Canonical.stateTerm
        (CollectionOccurrenceMachine.beginWith RecursiveCollectionHandoff.canonicalMatchingExecution
          plan bound expected (CanonicalBags.canon subject)))) := by
  have generated := typed_jobs_returns host plan bound expected (CanonicalBags.canon subject) footprint covered
  have discovered := jobs_returns host (GeneralRuleJobs.jobs plan bound expected (CanonicalBags.canon subject))
  have started := CollectionOccurrenceMachineExecution.Canonical.from_lanes_returns
    (plan := plan) (bound := bound) (expected := expected) (sourcePattern := subject) host
  rw [lanes_encoding] at started
  discovery_eval [generated, discovered, started] unfolding [CollectionOccurrenceHandoff.jobs]

end Canonical

#print axioms discovery_checked
#print axioms discovery_agreement
#print axioms raw_metadata
#print axioms typed_jobs_agreement
#print axioms typed_jobs_returns
#print axioms append_returns
#print axioms length_returns
#print axioms elaboration_checked
#print axioms elaboration_agreement
#print axioms elaborated_types_returns
#print axioms matcher_agreement
#print axioms start_returns
#print axioms begin_job_returns
#print axioms context_variants_returns
#print axioms variant_returns
#print axioms variants_returns
#print axioms jobs_returns
#print axioms lanes_encoding
#print axioms begin_returns
#print axioms Canonical.begin_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceDiscoveryExecution
