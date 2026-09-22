import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentFragment
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServices
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServicePrograms
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceProgramAdmission
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceProgramOSLF
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentPublicContext
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNamedContext
import Mettapedia.TypeTheory.NamedContextDataflow
import Mettapedia.TypeTheory.MonoidIndexedTransportCoherence
import Mettapedia.TypeTheory.RetainedPresentationViews
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentIdentityRegions
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNamedIdentityRegions
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeHedberg
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeDecidableIdentity
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanNamedRegion
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentScopedIdentityQualification
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentProgramContexts
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentPolarizedServices
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceNaturality
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentDeclarationInterpretation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualComparison
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeFormedContextComparisonControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientCwf
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeQuotientCwfControls
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientUniverses
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentity
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentityGeometry
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentityInputCoherence
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentityNativeReindexing
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveContextSourceObstruction
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeIdentityLevelInstantiation
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentProofEvidence
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceRegistry
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentAssemblyServices
import Mettapedia.Logic.HOL.ProofSyntax
import Mettapedia.Logic.HOL.UniformListMapFusion
import Mettapedia.GSLT.LanguageDef.NIKServiceResumption
import Mettapedia.GSLT.LanguageDef.NIKPropositionBranching
import Mettapedia.GSLT.LanguageDef.NIKOutcomeViewControls
import Mettapedia.GSLT.LanguageDef.FiniteSetRepresentationService
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ScopedComputationEffectTree
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.UniformListCognitiveWorkload
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeWireDataDenotation

/-!
# Executable observations for the shared judgment fragment

These observations run the reference functions on accepted and altered input.
They supplement the generic qualification theorems; they do not establish
runtime refinement, arbitrary proof-byte checking, or a selected language.
Single-crossing service observations execute the authored contextual effect
backend after the actual request and payload-dependent continuation. Repeated
program observations execute the independently recursive source worlds; their
backend and generated OSLF meaning are separate proved correspondences.
-/

open Mettapedia.Machines.BranchLocalNeed

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

open Mettapedia.Languages.MeTTa
open TypeTheory.CumulativeTower
open Presentation Presentation.ScopedComputation
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

namespace JointExperiments

private def expect {α : Type} [BEq α] [ToString α]
    (label : String) (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw (IO.userError s!"{label}: observed {actual}; expected {expected}")
  IO.println s!"PASS {label}: {actual}"

def matching : IO Unit := do
  let request := PolarizedNeedMatchedIndex.Examples.canonical.request
  let wire := PolarizedNeedMatchedIndex.admittedWire
    PolarizedNeedMatchedIndex.Examples.canonical
  expect "match.valid.reconstructed"
    (PrimeCandidates.SharedJudgmentFragment.common.reconstructMatch request wire).isSome true
  expect "match.changed-output.reconstructed"
    (PrimeCandidates.SharedJudgmentFragment.common.reconstructMatch request
      (PolarizedNeedMatchedIndex.admittedWire
        PolarizedNeedMatchedIndex.Examples.changedOutput)).isSome false
  expect "match.changed-index-and-request.reconstructed"
    (PrimeCandidates.SharedJudgmentFragment.common.reconstructMatch
      MatchedIndexDependentTransport.Examples.changedIndex.request
      (PolarizedNeedMatchedIndex.admittedWire
        MatchedIndexDependentTransport.Examples.changedIndex)).isSome false
  expect "match.cross-occurrence.reconstructed"
    (PrimeCandidates.SharedJudgmentFragment.common.reconstructMatch
      (PolarizedNeedMatchedIndex.Examples.duplicateRequest 0)
      (PolarizedNeedMatchedIndex.admittedWire
        (PolarizedNeedMatchedIndex.Examples.duplicateReceipt 1))).isSome false
  match MatchedIndexDependentTransport.consume? request wire with
  | none => throw (IO.userError "The accepted match did not reach its independent consumer")
  | some transport =>
      expect "identity.actual-J-step"
        (NativeRelatorConversionChecking.checkStep transport.step transport.source transport.proof) true
      expect "identity.receipt-as-proof-step"
        (NativeRelatorConversionChecking.checkStep transport.step
          (NativeIndexedFamilies.Intrinsic.identityEliminateApp NativeWireData.dataType
            (MatchedIndexDependentTransport.nativePattern transport.selected)
            (MatchedIndexDependentTransport.motive transport.selected) transport.proof
            (MatchedIndexDependentTransport.nativePattern transport.receipt.output)
            (NativeWireData.encode wire)) transport.proof) false

def cognitive : IO Unit := do
  let request := UniformListChartNIKService.actualRequest []
  let environment := Mettapedia.Logic.HOL.UniformListInductionRevisionViews.Induction.initialEnvironment
  let samples := [UniformListCognitiveWorkload.emptySample,
    UniformListCognitiveWorkload.nonemptySample]
  let theory := Mettapedia.Logic.HOL.UniformListInduction.theory (Γ := [])
  let outcome generation recognition submitted revision :=
    (UniformListCognitiveWorkload.consume generation recognition samples .inputLength
      theory submitted revision).label
  IO.println s!"learning.empty-only: {repr (UniformListCognitiveWorkload.survivors 1
    [UniformListCognitiveWorkload.emptySample])}"
  IO.println s!"learning.nonempty-added: {repr (UniformListCognitiveWorkload.survivors 1 samples)}"
  IO.println s!"learning.imported: {repr ((UniformListCognitiveWorkload.learnAndImport 1 2 samples
    theory request environment).map fun result => (result.1, result.2.label))}"
  expect "proof.shared-producer"
    (PrimeCandidates.SharedJudgmentFragment.common.produceHOL [] request).isSome true
  expect "proof.current" (outcome 1 2 request environment) "current-proof"
  expect "proof.consulted-revision" (outcome 1 2 request (environment.update 0 1))
    "historical-proof"
  expect "proof.unrelated-revision" (outcome 1 2 request (environment.update 1 7))
    "current-proof"
  expect "proof.generation-bound" (outcome 0 2 request environment) "generation-miss"
  expect "proof.recognition-bound" (outcome 1 1 request environment) "recognition-miss"
  expect "proof.malformed-certificate"
    (outcome 1 2 { request with stepProof :=
      Mettapedia.Logic.HOL.UniformListInductionChart.malformedCertificate [] } environment)
    "proof-rejected"
  expect "sample.zero.empty"
    (UniformListCognitiveWorkload.fits .zero UniformListCognitiveWorkload.emptySample) true
  expect "sample.zero.nonempty"
    (UniformListCognitiveWorkload.fits .zero UniformListCognitiveWorkload.nonemptySample) false
  expect "proof.overfit-empty-sample"
    (UniformListCognitiveWorkload.consume 1 2 [UniformListCognitiveWorkload.emptySample]
      .zero theory { request with claim := (theory, UniformListCognitiveWorkload.hypothesis .zero) }
      environment).label "proof-rejected"
  let equations := Mettapedia.Logic.HOL.UniformListInduction.equations (Γ := [])
  expect "proof.induction-removed"
    (UniformListCognitiveWorkload.consume 1 2 samples .inputLength equations
      { request with claim := (equations, UniformListCognitiveWorkload.hypothesis .inputLength) }
      environment).label "proof-rejected"

def contextualViews : IO Unit := do
  let assembly := PrimeCandidates.SharedJudgmentFragment.common
  let observeProducer : ContextViews.State .producer → ContextViews.Readout .producer :=
    assembly.observe .producer
  let observeResumed : ContextViews.State .resumed → ContextViews.Readout .resumed :=
    assembly.observe .resumed
  let compactResume : ContextViews.Readout .producer → ContextViews.Readout .resumed :=
    assembly.compactResume
  let first := ObservationStudy.Native.trueWorlds
  let second := ObservationStudy.Native.falseWorlds
  expect "view.answers-collide"
    (ObservationStudy.answerView first == ObservationStudy.answerView second) true
  expect "view.contextual-producers-collide"
    (observeProducer first == observeProducer second) false
  expect "view.resumed-intents-collide"
    (ContextViews.suffixes (assembly.resume first) ==
      ContextViews.suffixes (assembly.resume second)) false
  expect "view.actual-operation-square"
    (observeResumed (assembly.resume first) == compactResume (observeProducer first)) true
  expect "view.branch-history-hidden"
    (observeProducer first == observeProducer ContextViews.Native.differentBranchWorlds) true
  expect "view.actual-branch-histories-equal"
    (first.map WorldResult.branch ==
      ContextViews.Native.differentBranchWorlds.map WorldResult.branch) false

open PrimeCandidates.SharedJudgmentServices
open Mettapedia.GSLT.LanguageDef

/-- The executable matching case is an instance of the existing service
qualification and arbitrary-program backend crowns. -/
theorem matching_backend_crown (state : Bool) (branch : BranchTrace) :
    ∃ program : Program Bool (Tower.Tm 2) Nat,
      continuationProgram PrimeCandidates.SharedJudgmentFragment.common
        Examples.canonicalMatchingSource
        (invoke PrimeCandidates.SharedJudgmentFragment.common Examples.canonicalMatchingSource.request) =
          some program ∧
      ContextualEffectTreeLanguage.execute
        (ContextualEffectTreeLanguage.depth (ScopedComputationEffectTree.nativeProgram program))
        (ScopedComputationEffectTree.request program state branch) =
          [ScopedComputationEffectTree.completion (runWorldsAt program state branch)] ∧
      ContextualEffectTreeLanguage.theory.Step
        (ScopedComputationEffectTree.request program state branch)
        (ScopedComputationEffectTree.completion (runWorldsAt program state branch)) ∧
      ∀ output ∈ runWorldsAt program state branch,
        FormationSensitive.Judgment PrimeCandidates.SharedJudgmentFragment.common.rules
          NativeExamples.context output.answer
          (Examples.payloadSigma Examples.canonicalTransport.proposition) := by
  rcases Examples.canonical_matching_workload state branch with
    ⟨program, selected, _, admitted⟩
  exact ⟨program, selected,
    ScopedComputationEffectTree.native_executor_exact program _ state branch (Nat.le_refl _),
    (ScopedComputationEffectTree.native_complete_iff program state branch _).mpr rfl, admitted⟩

/-- The represented HOL formula is the native payload; source proof
admission remains at the checked service crossing. -/
theorem hol_backend_crown (state : Bool) (branch : BranchTrace) :
    ∃ program : Program Bool (Tower.Tm 2) Nat,
      continuationProgram PrimeCandidates.SharedJudgmentFragment.common
        Examples.actualHOLSource
        (invoke PrimeCandidates.SharedJudgmentFragment.common Examples.actualHOLSource.request) =
          some program ∧
      ContextualEffectTreeLanguage.execute
        (ContextualEffectTreeLanguage.depth (ScopedComputationEffectTree.nativeProgram program))
        (ScopedComputationEffectTree.request program state branch) =
          [ScopedComputationEffectTree.completion (runWorldsAt program state branch)] ∧
      ContextualEffectTreeLanguage.theory.Step
        (ScopedComputationEffectTree.request program state branch)
        (ScopedComputationEffectTree.completion (runWorldsAt program state branch)) ∧
      ∀ output ∈ runWorldsAt program state branch,
        FormationSensitive.Judgment PrimeCandidates.SharedJudgmentFragment.common.rules
          NativeExamples.context output.answer
          (Examples.payloadSigma (.const `HOLUniformList.prop)) := by
  rcases Examples.actual_hol_workload state branch with
    ⟨program, selected, _, admitted⟩
  exact ⟨program, selected,
    ScopedComputationEffectTree.native_executor_exact program _ state branch (Nat.le_refl _),
    (ScopedComputationEffectTree.native_complete_iff program state branch _).mpr rfl, admitted⟩

private def successfulService (label : String) (source : Source 2)
    (payload : Tower.Tm 2) : IO Unit := do
  let assembly := PrimeCandidates.SharedJudgmentFragment.common
  let response := invoke assembly source.request
  expect s!"service.{label}.invoked-success" (decide (response.status = .success)) true
  expect s!"service.{label}.selected-payload"
    (response.nativePayload?.map Prod.fst == some payload) true
  let selected := continuationProgram assembly source response
  expect s!"service.{label}.continuation-selected" selected.isSome true
  match selected with
  | none => throw (IO.userError s!"The successful {label} service selected no continuation")
  | some program =>
      let state := false
      let branch := [true, false]
      let worlds := Code.worlds (assembly.execution 2).primitive (consSub payload ids)
        source.continuation state branch
      let expected : List (WorldResult Bool (Tower.Tm 2) Nat) :=
        [{ branch := false :: branch, answer := .pair payload (.refl payload),
           state := true, intents := [10, 30] },
         { branch := true :: branch, answer := .pair payload (.refl payload),
           state := false, intents := [20, 40] }]
      expect s!"service.{label}.native-world-count" worlds.length 2
      expect s!"service.{label}.primitive-worlds-exact"
        (ScopedComputationEffectTree.encodeWorlds worlds ==
          ScopedComputationEffectTree.encodeWorlds expected) true
      expect s!"service.{label}.selected-program-worlds-exact"
        (ScopedComputationEffectTree.encodeWorlds (runWorldsAt program state branch) ==
          ScopedComputationEffectTree.encodeWorlds worlds) true
      expect s!"service.{label}.native-world-codec-roundtrip"
        ((ScopedComputationEffectTree.decodeWorlds? 2
            (ScopedComputationEffectTree.encodeWorlds worlds)).map
              ScopedComputationEffectTree.encodeWorlds ==
          some (ScopedComputationEffectTree.encodeWorlds worlds)) true
      let depth := ContextualEffectTreeLanguage.depth
        (ScopedComputationEffectTree.nativeProgram program)
      let request := ScopedComputationEffectTree.request program state branch
      let targets := ContextualEffectTreeLanguage.execute depth request
      IO.println s!"service.{label}.adequate-contextual-depth: {depth}"
      expect s!"service.{label}.backend-exact-completion"
        (targets == [ScopedComputationEffectTree.completion worlds]) true
      expect s!"service.{label}.backend-reversed-completion"
        (targets.contains (ScopedComputationEffectTree.completion worlds.reverse)) false
      expect s!"service.{label}.backend-truncated-completion"
        (targets.contains (ScopedComputationEffectTree.completion (worlds.take 1))) false
      expect s!"service.{label}.backend-deleted-intent-completion"
        (targets.contains (ScopedComputationEffectTree.completion
          (worlds.map fun world => { world with intents := [] }))) false
      let shallow := depth - 1
      expect s!"service.{label}.shallow-budget-inadequate" (decide (shallow < depth)) true
      let pending := ContextualEffectTreeLanguage.execute shallow request
      expect s!"service.{label}.shallow-completion-count" pending.length 0
      -- Empty bounded execution is pending, not a decision of semantic falsity.
      -- The same request has its exact complete worlds at the adequate bound.
      expect s!"service.{label}.shallow-operational-status"
        (if pending.isEmpty then "pending" else "completed") "pending"

private def declinedService (label : String) (source : Source 2) : IO Unit := do
  let assembly := PrimeCandidates.SharedJudgmentFragment.common
  let response := invoke assembly source.request
  expect s!"service.{label}.invoked-declined" (decide (response.status = .declined)) true
  expect s!"service.{label}.native-payload-present" response.nativePayload?.isSome false
  expect s!"service.{label}.continuation-selected"
    (continuationProgram assembly source response).isSome false

def serviceBackend : IO Unit := do
  successfulService "matching" Examples.canonicalMatchingSource
    (liftClosed Examples.canonicalTransport.source)
  successfulService "hol" Examples.actualHOLSource Examples.holPayload
  declinedService "changed-index" Examples.alteredIndexSource
  declinedService "changed-output" Examples.alteredOutputSource
  declinedService "changed-premises" Examples.alteredPremisesHOLSource
  declinedService "changed-claim" Examples.changedClaimHOLSource
  declinedService "changed-certificate" Examples.malformedHOLSource

/-- These checks execute the nested scoped source. The separate repeated-run
backend and OSLF theorems establish qualification; runtime labels alone do not.
Full request indices remain in each run; labels below are only readouts. -/
def repeatedServices : IO Unit := do
  let assembly := PrimeCandidates.SharedJudgmentFragment.common
  let branch := [true, false]
  let successful := PrimeCandidates.SharedJudgmentServicePrograms.Code.run assembly ids
    PrimeCandidates.SharedJudgmentServicePrograms.Examples.matchingThenHOL false branch
  let stopped := PrimeCandidates.SharedJudgmentServicePrograms.Code.run assembly ids
    PrimeCandidates.SharedJudgmentServicePrograms.Examples.matchingThenChangedHOL false branch
  let statusLabel {request : Request 2} (response : Response request) :=
    match response.status with
    | .success => "success"
    | .declined => "declined"
    | .representationFailure => "representation-failure"
  expect "nested.success.world-count" successful.length 1
  for result in successful do
    expect "nested.success.reply-count" result.replies.length 2
    expect "nested.success.reply-order"
      (String.intercalate "," (result.replies.map fun reply =>
        match reply.1 with
        | .matching _ _ => "matching"
        | .hol _ _ _ => "hol")) "matching,hol"
    expect "nested.success.statuses"
      (String.intercalate "," (result.replies.map fun reply => statusLabel reply.2)) "success,success"
    expect "nested.success.branch-preserved" (result.world.branch == branch) true
    expect "nested.success.state-preserved" result.world.state false
    let correct := match result.world.answer with
      | .value value => value == .pair
          (PrimeCandidates.SharedJudgmentServicePrograms.Examples.matchingValue 2)
          (PrimeCandidates.SharedJudgmentServicePrograms.Examples.holValue 2)
      | .stopped _ => false
    expect "nested.success.uses-both-payloads" correct true
  expect "nested.changed-claim.world-count" stopped.length 1
  for result in stopped do
    expect "nested.changed-claim.reply-count" result.replies.length 2
    expect "nested.changed-claim.statuses"
      (String.intercalate "," (result.replies.map fun reply => statusLabel reply.2)) "success,declined"
    let outcome := match result.world.answer with
      | .value _ => "value"
      | .stopped reply => statusLabel reply.2
    expect "nested.changed-claim.outcome" outcome "declined"
    expect "nested.changed-claim.state-preserved" result.world.state false
  let original := PrimeCandidates.SharedJudgmentServicePrograms.Code.run assembly ids
    (PrimeCandidates.SharedJudgmentServicePrograms.ofSource Examples.canonicalMatchingSource) false branch
  expect "nested.original-source.world-count" original.length 2
  expect "nested.original-source.intents"
    (original.map (fun result => result.world.intents) == [[10, 30], [20, 40]]) true
  expect "nested.original-source.private-states"
    (original.map (fun result => result.world.state) == [true, false]) true
  expect "nested.original-source.reply-counts"
    (original.map (fun result => result.replies.length) == [1, 1]) true
  let dependent := PrimeCandidates.SharedJudgmentServicePrograms.Code.run assembly ids
    PrimeCandidates.SharedJudgmentServicePrograms.AdmissionExamples.matchingThenHOLIdentity false branch
  expect "nested.dependent.world-count" dependent.length 1
  for result in dependent do
    let correct := match result.world.answer with
      | .value value => value == PrimeCandidates.SharedJudgmentServicePrograms.AdmissionExamples.nestedValue
      | .stopped _ => false
    expect "nested.dependent.retained-values-and-identity" correct true

namespace RepeatedRunViews

open PrimeCandidates.SharedJudgmentFragment PrimeCandidates.SharedJudgmentServicePrograms
open PrimeCandidates.SharedJudgmentServiceProgramBackend
open PrimeCandidates.SharedJudgmentServiceProgramOSLF
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

local instance : DecidableEq Mettapedia.Logic.HOL.UniformListInduction.BaseSort
  | .element, .element | .sequence, .sequence | .count, .count => .isTrue rfl
  | .element, .sequence | .element, .count | .sequence, .element
  | .sequence, .count | .count, .element | .count, .sequence =>
      .isFalse (by intro same; cases same)

local instance (type : Mettapedia.Logic.HOL.Ty Mettapedia.Logic.HOL.UniformListInduction.BaseSort) :
    DecidableEq (Mettapedia.Logic.HOL.UniformListInduction.Symbol type) := by
  intro first second
  cases first <;> cases second <;> exact .isTrue rfl

/-- The fixtures below evaluate source worlds. This theorem, not an IO test,
connects their complete observations to the same backend's generated native
types under the independently proved common execution qualification. -/
theorem source_world_observation_crown (code : PrimeCandidates.SharedJudgmentServicePrograms.Code 2)
    (observation : List (Output 2) → Prop) (state : Bool) (branch : BranchTrace) :
    (gsltOSLF (runView common 2)).satisfies (S := ())
      (start ids code state branch) (completeNativeType common observation).pred ↔
      observation (PrimeCandidates.SharedJudgmentServicePrograms.Code.worlds common ids code state branch) :=
  completeNativeType_iff_worlds common common_execution observation ids code state branch

/-- Expected constructors are stated independently of either source runner.
The HOL payload is a represented formula, not a native proof of its truth. -/
private def expectedValue : Tower.Tm 2 :=
  .pair (liftClosed PrimeCandidates.SharedJudgmentServices.Examples.canonicalTransport.source)
    (.pair (PrimeCandidates.SharedJudgmentServicePrograms.Examples.holValue 2)
      (.refl (PrimeCandidates.SharedJudgmentServicePrograms.Examples.holValue 2)))

private def value? (output : Output 2) : Option (Tower.Tm 2) :=
  match output.world.answer with
  | .value value => some value
  | .stopped _ => none

private def statusLabel {request : Request 2} (response : Response request) : String :=
  match response.status with
  | .success => "success"
  | .declined => "declined"
  | .representationFailure => "representation-failure"

private def replyLabels (output : Output 2) : List (String × String) :=
  output.replies.map fun reply =>
    (match reply.1 with | .matching _ _ => "matching" | .hol _ _ _ => "hol", statusLabel reply.2)

private def worldFields (output : Output 2) :
    BranchTrace × Option (Tower.Tm 2) × Bool × List Nat :=
  (output.world.branch, value? output, output.world.state, output.world.intents)

/-- These are source computations and lossy executable readouts, not an
executable driver for the proof-indexed backend or a test of OSLF soundness. -/
def check : IO Unit := do
  let branch := [true, false]
  let single := PrimeCandidates.SharedJudgmentServicePrograms.Code.worlds common ids
    AdmissionExamples.matchingThenHOLIdentity false branch
  let forked := PrimeCandidates.SharedJudgmentServicePrograms.Code.worlds common ids
    Controls.forkedNested false branch
  let stopped := PrimeCandidates.SharedJudgmentServicePrograms.Code.worlds common ids
    PrimeCandidates.SharedJudgmentServicePrograms.Examples.matchingThenChangedHOL false branch
  let exposes := fun output => value? output == some expectedValue
  expect "run-view.single.exposed-value" (single.any exposes) true
  expect "run-view.forked.exposed-value" (forked.any exposes) true
  expect "run-view.single.matching-value-count" (single.countP exposes) 1
  expect "run-view.forked.matching-value-count" (forked.countP exposes) 2
  expect "run-view.single.second-position" ((single[1]?).bind value?).isSome false
  expect "run-view.forked.second-position-value"
    ((forked[1]?).bind value? == some expectedValue) true
  let expectedSingle := [(branch, some expectedValue, false, ([] : List Nat))]
  let expectedForked :=
    [(false :: branch, some expectedValue, false, ([] : List Nat)),
     (true :: branch, some expectedValue, false, [])]
  expect "run-view.single.ordered-world-fields" (single.map worldFields == expectedSingle) true
  expect "run-view.forked.ordered-world-fields" (forked.map worldFields == expectedForked) true
  let successReplies := [("matching", "success"), ("hol", "success")]
  expect "run-view.single.chronological-replies" (single.map replyLabels == [successReplies]) true
  expect "run-view.forked.chronological-replies"
    (forked.map replyLabels == [successReplies, successReplies]) true
  expect "run-view.forked.reversed-replies-match"
    ((forked.map replyLabels).map List.reverse == [successReplies, successReplies]) false
  expect "run-view.forked.truncated-worlds-match"
    ((forked.take 1).map worldFields == expectedForked) false
  expect "run-view.stopped.world-count" stopped.length 1
  expect "run-view.stopped.value-count" (stopped.countP fun output => (value? output).isSome) 0
  expect "run-view.stopped.outcome"
    (stopped.map (fun output => match output.world.answer with
      | .value _ => "value"
      | .stopped reply => statusLabel reply.2) == ["declined"]) true
  expect "run-view.stopped.chronological-replies"
    (stopped.map replyLabels == [[("matching", "success"), ("hol", "declined")]]) true
  expect "run-view.stopped.ordered-world-fields"
    (stopped.map worldFields == [(branch, none, false, [])]) true
  let stoppedClaimIs := fun original => stopped.all fun output =>
    match output.world.answer with
    | .value _ => false
    | .stopped reply =>
        match reply.1 with
        | .matching _ _ => false
        | .hol gamma replay _ =>
            if original then decide (replay.claim = UniformListChartNIKService.mapLengthClaim gamma)
            else decide (replay.claim =
              (Mettapedia.Logic.HOL.UniformListInduction.equations (Γ := gamma),
               Mettapedia.Logic.HOL.UniformListInduction.mapLength))
  expect "run-view.stopped.changed-premises-and-conclusion" (stoppedClaimIs false) true
  expect "run-view.stopped.original-claim" (stoppedClaimIs true) false

end RepeatedRunViews

def fourFaceServices : IO Unit := do
  let successful := Mettapedia.GSLT.Dynamics.ServiceResumption.runWorlds
    NIKServiceResumption.invoke (NIKServiceResumption.PositiveNaturalControl.pipeline 2) 90
  expect "four-face.success.world-count" successful.length 1
  for result in successful do
    expect "four-face.success.reply-count" result.replies.length 4
    expect "four-face.success.face-order"
      (decide (result.replies.map (fun reply => reply.1.1.face) =
        [.directDecision, .nativeOperation, .nativeProof, .certificateBoundary])) true
    expect "four-face.success.state-from-first-reply" result.world.state 2
    expect "four-face.success.value-dependent-intents" (result.world.intents == [2, 3]) true
    expect (α := Nat) "four-face.success.final-value"
      (match result.world.answer with | .inl _ => 0 | .inr value => value) 3
  let rejected := Mettapedia.GSLT.Dynamics.ServiceResumption.runWorlds
    NIKServiceResumption.invoke (NIKServiceResumption.PositiveNaturalControl.submittedProof 0) 90
  expect "four-face.rejected-proof.world-count" rejected.length 1
  for result in rejected do
    expect "four-face.rejected-proof.prefix-retained" result.replies.length 2
    expect "four-face.rejected-proof.no-later-intent" result.world.intents.isEmpty true
    expect "four-face.rejected-proof.outcome"
      (match result.world.answer with | .inl _ => "stopped" | .inr _ => "value") "stopped"
  let falseClaim := Mettapedia.GSLT.Dynamics.ServiceResumption.runWorlds
    NIKServiceResumption.invoke (NIKServiceResumption.PositiveNaturalControl.pipeline 0) 90
  expect "four-face.false-decision.world-count" falseClaim.length 1
  for result in falseClaim do
    expect "four-face.false-decision.only-first-call" result.replies.length 1
    expect "four-face.false-decision.no-state-write" result.world.state 90

def noncanonicalData : IO Unit := do
  let payload := NativeWireDataDenotation.Examples.improperTail
  let different := NativeWireDataDenotation.Examples.nonsymbolHead
  let submitted := subst (NativeWireDataDenotation.fillParameter payload)
    NativeWireDataDenotation.parameterTerm
  expect "data.improper-tail.canonical-decoder-present"
    (NativeWireData.decodeList (NativeWireDataDenotation.quote (n := 3) payload)).isSome false
  expect "data.nonsymbol-head.canonical-decoder-present"
    (NativeWireData.decode (NativeWireDataDenotation.quote (n := 3) different)).isSome false
  expect "data.actual-substitution.retains-both-parameter-uses"
    (submitted == NativeWireDataDenotation.quote
      (.application payload (.cons (.symbol "opaque-payload") payload))) true
  expect "data.changed-parameter.same-native-source"
    (submitted == subst (NativeWireDataDenotation.fillParameter different)
      NativeWireDataDenotation.parameterTerm) false
  expect "data.submitted-constructor.is-identity-proof"
    (submitted == .refl (NativeWireDataDenotation.quote payload)) false

def inspectableEvidence : IO Unit := do
  let proposition : Mettapedia.Logic.HOL.UniformListInduction.Sentence [] := .top
  expect "proof.direct.nodes"
    (Mettapedia.Logic.HOL.ProofSyntax.Controls.direct proposition).nodeCount 2
  expect "proof.detour.nodes"
    (Mettapedia.Logic.HOL.ProofSyntax.Controls.detour proposition).nodeCount 5
  expect "proof.first-assumption.occurrence"
    ((Mettapedia.Logic.HOL.ProofSyntax.Controls.firstOccurrence proposition).rootObservation.hypothesisOccurrence.getD 99) 0
  expect "proof.second-assumption.occurrence"
    ((Mettapedia.Logic.HOL.ProofSyntax.Controls.secondOccurrence proposition).rootObservation.hypothesisOccurrence.getD 99) 1
  let value := NativeWireDataDenotation.Value.symbol "payload"
  let direct := PrimeCandidates.SharedJudgmentPublicContext.Controls.direct value
  let detour := PrimeCandidates.SharedJudgmentPublicContext.Controls.detour value
  let expected := NativeWireDataDenotation.quote (n := 3)
    (NativeWireDataDenotation.parameterValue value)
  let outputs := direct.run PrimeCandidates.SharedJudgmentFragment.common
  let later := detour.run PrimeCandidates.SharedJudgmentFragment.common
  expect "context.direct.world-count" outputs.length 1
  expect "context.detour.world-count" later.length 1
  for output in outputs ++ later do
    expect "context.output.retains-substituted-value"
      (match output.world.answer with | .value term => term == expected | .stopped _ => false) true
  let changed := PrimeCandidates.SharedJudgmentPublicContext.Controls.parameterInput
    (.symbol "different-payload")
  for output in changed.run PrimeCandidates.SharedJudgmentFragment.common do
    expect "context.changed-binding.same-value"
      (match output.world.answer with | .value term => term == expected | .stopped _ => false) false

namespace SubmittedProofEvidence

open PrimeCandidates.SharedJudgmentProofEvidence
open Mettapedia.Logic HOL HOL.UniformListInduction

/-- Coarse admission equality and actual HOL theorem application are proved
facts, not executable comparisons of proofs. The retained input strategies
remain distinct despite this common theorem-application view. -/
theorem application_crown :
    (Controls.actual []).applicationView = (Controls.detoured []).applicationView ∧
      HOL.ExtDerivation Symbol (theory (Γ := [element]))
        (preservesLength (.lam (.var .vz)) (cons (.var .vz) nil)) :=
  ⟨Controls.same_application_view [], Controls.actual_application⟩

/-- These computations observe submitted reconstruction and finite structural
selection, not full learning, revision freshness or raw proof-byte checking. -/
def check : IO Unit := do
  let original := Controls.actual []
  let detoured := Controls.detoured []
  let first := produce? original.request
  let second := produce? detoured.request
  expect "retained.original.produced" first.isSome true
  expect "retained.detoured.produced" second.isSome true
  expect "retained.original.produced-nodes" ((first.map fun evidence => evidence.tree.nodeCount).getD 0) 50
  expect "retained.detoured.produced-nodes" ((second.map fun evidence => evidence.tree.nodeCount).getD 0) 52
  expect "retained.original.restored-nodes"
    (((restore? original.request original.applicationView).map ProofSyntax.nodeCount).getD 0) 50
  expect "retained.detoured.restored-nodes"
    (((restore? detoured.request detoured.applicationView).map ProofSyntax.nodeCount).getD 0) 52
  expect "retained.strategy.original-preferred" (preferLeft original detoured) true
  expect "retained.strategy.detoured-preferred" (preferLeft detoured original) false
  expect "retained.strategy.forward-selected-nodes" (prefer original detoured).tree.nodeCount 50
  expect "retained.strategy.reverse-selected-nodes" (prefer detoured original).tree.nodeCount 50
  expect "retained.changed-premises.restored"
    (restore? { original.request with stepPremises :=
      HOL.UniformListInductionChart.alteredStepAssumptions [] } original.applicationView).isSome false
  expect "retained.malformed-certificate.restored"
    (restore? { original.request with stepProof :=
      HOL.UniformListInductionChart.malformedCertificate [] } original.applicationView).isSome false
  expect "retained.missing-induction.restored"
    (restore? { original.request with claim := (equations, mapLength) }
      original.applicationView).isSome false
  expect "retained.actual-theorem-application.nodes" Controls.applied.nodeCount 52

end SubmittedProofEvidence

namespace RequiredServiceRegistry

open PrimeCandidates.SharedJudgmentServiceRegistry

/-- The fixed four-face fixtures have actual admission and native
representation theorems; the IO observations below only execute their calls. -/
theorem invocation_crown (face : NIK.Face) :
    (NIKServiceInvocation.invoke (Controls.request face)).acceptedValue =
        some (Controls.expected face) ∧
      FormationSensitive.Judgment PrimeCandidates.SharedJudgmentFragment.common.rules
        NativeMatchedTransportDenotation.parameterContext
        (PrimeCandidates.SharedJudgmentServiceInterpretation.WireControls.parameterPayload
          (Controls.expected face)) NativeWireData.dataType :=
  ⟨Controls.four_invocations face, Controls.four_native_representations face⟩

/-- Exact wire comparisons use the existing native encoding, whose decoder
roundtrip retains every constructor and payload; no rendering is compared. -/
def check : IO Unit := do
  let original : NativeWireData.Wire :=
    .application "native-input" [.symbol "opaque-payload", .natural 7]
  let wrapped : NativeWireData.Wire := .application "wrapped" [original]
  let faces : List (String × NIK.Face) :=
    [("decision", .directDecision), ("proof", .nativeProof),
     ("operation", .nativeOperation), ("certificate", .certificateBoundary)]
  for (label, face) in faces do
    let expected := if face == .nativeOperation then wrapped else original
    let returned := (NIKServiceInvocation.invoke (Controls.request face)).acceptedValue.map
      (NativeWireData.encode (n := 0))
    expect s!"registry.{label}.native-encoded-result"
      (returned == some (NativeWireData.encode expected)) true
  let badProof : NIKServiceInvocation.Request
      (Controls.registry.serviceAt Controls.registry_qualified .nativeProof) :=
    .nativeProof original ("other-head", [.natural 7])
  let badCertificate : NIKServiceInvocation.Request
      (Controls.registry.serviceAt Controls.registry_qualified .certificateBoundary) :=
    .certificateBoundary original ("other-head", [.natural 7])
  expect "registry.malformed-proof.accepted"
    (NIKServiceInvocation.invoke badProof).acceptedValue.isSome false
  expect "registry.malformed-certificate.accepted"
    (NIKServiceInvocation.invoke badCertificate).acceptedValue.isSome false
  let operationResult :=
    (NIKServiceInvocation.invoke (Controls.request .nativeOperation)).acceptedValue.map
      (NativeWireData.encode (n := 0))
  expect "registry.operation.unchanged-encoded-result"
    (operationResult == some (NativeWireData.encode original)) false

end RequiredServiceRegistry

namespace ActualAssemblyServices

open PrimeCandidates.SharedJudgmentFragment
open PrimeCandidates.SharedJudgmentAssemblyServices
open PolarizedNeedMatchedIndex PolarizedNeedMatchedIndex.Examples

def check : IO Unit := do
  let original := admittedWire canonical
  let changed := admittedWire changedOutput
  let accepted assembly admission coverage wire :=
    (NIKServiceInvocation.invoke
      (receiptRequest assembly admission coverage canonical.request wire)).acceptedValue.isSome
  expect "callbacks.receipt.common" (accepted common common_match_admission common_match_coverage original) true
  expect "callbacks.receipt.alternate"
    (accepted ReceiptControls.reflexivityAssembly ReceiptControls.reflexivity_admission
      ReceiptControls.reflexivity_coverage original) true
  expect "callbacks.receipt.changed"
    (accepted ReceiptControls.reflexivityAssembly ReceiptControls.reflexivity_admission
      ReceiptControls.reflexivity_coverage changed) false
  expect "callbacks.receipt.distinct-proof-syntax"
    (common.reconstructMatch canonical.request original ==
      ReceiptControls.reflexivityAssembly.reconstructMatch canonical.request original) false
  expect "callbacks.receipt.dropped"
    (ReceiptControls.droppedMatching.reconstructMatch canonical.request original).isSome false
  expect "callbacks.receipt.unqualified-replay"
    (ReceiptControls.replayedMatching.reconstructMatch canonical.request changed).isSome true
  expect "callbacks.hol.actual" (holRun? common (UniformListChartNIKService.actualRequest [])).isSome true
  expect "callbacks.hol.detour" (holRun? common (UniformListChartProofSyntax.detouredRequest [])).isSome true
  expect "callbacks.hol.changed-premises" (holRun? common (HOLCallbackControls.changedPremises [])).isSome false
  expect "callbacks.hol.valid-proof-ignores-history"
    (holRun? HOLCallbackControls.replayedHOL (HOLCallbackControls.changedPremises [])).isSome true
  expect "callbacks.hol.changed-claim"
    (holRun? HOLCallbackControls.replayedHOL
      { UniformListChartNIKService.actualRequest [] with
        claim := (Mettapedia.Logic.HOL.UniformListInduction.theory,
          Mettapedia.Logic.HOL.UniformListInduction.lengthNil) }).isSome false
  expect "callbacks.hol.missing-induction"
    (holRun? common
      { UniformListChartNIKService.actualRequest [] with
        claim := (Mettapedia.Logic.HOL.UniformListInduction.equations,
          Mettapedia.Logic.HOL.UniformListInduction.mapLength) }).isSome false

end ActualAssemblyServices

namespace LivePropositions

open Mettapedia.GSLT.LanguageDef

private def selection : Option Bool → String
  | some true => "then"
  | some false => "else"
  | none => "residual"

def check : IO Unit := do
  let outcomes : List (String × Option Bool × String) := [
    ("support", NIKPropositionBranching.Controls.acceptedThen.asBool, "then"),
    ("bad-proof", NIKPropositionBranching.Controls.badSupport.asBool, "residual"),
    ("partial-refutation", NIKPropositionBranching.Controls.partialOpposition.asBool, "residual"),
    ("complete-refutation", NIKPropositionBranching.Controls.acceptedElse.asBool, "else")]
  for (label, outcome, wanted) in outcomes do
    expect s!"branch.{label}" (selection outcome) wanted
  let positive := CompletenessSpectrum.SAT.Canary.positiveFormula
  let negative := CompletenessSpectrum.SAT.Canary.contradictionFormula
  expect "branch.empty-search"
    (selection (NIKPropositionBranching.Controls.sampleAssignments [] positive []).asBool) "residual"
  expect "branch.unsuccessful-search"
    (selection (NIKPropositionBranching.Controls.sampleAssignments [] positive
      [CompletenessSpectrum.SAT.Canary.falseAssignment]).asBool) "residual"
  expect "branch.successful-search"
    (selection (NIKPropositionBranching.Controls.sampleAssignments [] positive
      [CompletenessSpectrum.SAT.Canary.falseAssignment, CompletenessSpectrum.SAT.Canary.trueAssignment]).asBool) "then"
  expect "branch.complete-decision.positive"
    (selection (NIKPropositionBranching.decideOutcome NIKPropositionBranching.Controls.meaning []
      (NIKPropositionBranching.Controls.decision []) positive).asBool) "then"
  expect "branch.complete-decision.negative"
    (selection (NIKPropositionBranching.decideOutcome NIKPropositionBranching.Controls.meaning []
      (NIKPropositionBranching.Controls.decision []) negative).asBool) "else"
  expect "branch.bad-proof.no-effects"
    ((runWorldsAt (NIKPropositionBranching.branchProgram NIKPropositionBranching.Controls.badSupport
      NIKPropositionBranching.Controls.thenEffect NIKPropositionBranching.Controls.elseEffect) 7 [true]).map
        (fun world => (world.branch, world.state, world.intents)) == [([true], 7, [])]) true
  expect "branch.empty-search.no-effects"
    ((runWorldsAt (NIKPropositionBranching.branchProgram
      (NIKPropositionBranching.Controls.sampleAssignments [] positive [])
      NIKPropositionBranching.Controls.thenEffect NIKPropositionBranching.Controls.elseEffect) 7 [true]).map
        (fun world => (world.branch, world.state, world.intents)) == [([true], 7, [])]) true
  expect "branch.support.only-then-effects"
    ((runWorldsAt (NIKPropositionBranching.branchProgram NIKPropositionBranching.Controls.acceptedThen
      NIKPropositionBranching.Controls.thenEffect NIKPropositionBranching.Controls.elseEffect) 7 [true]).map
        (fun world => (world.branch, world.state, world.intents)) == [([true], 8, ["then"])]) true
  expect "branch.refutation.only-else-effects"
    ((runWorldsAt (NIKPropositionBranching.branchProgram NIKPropositionBranching.Controls.acceptedElse
      NIKPropositionBranching.Controls.thenEffect NIKPropositionBranching.Controls.elseEffect) 7 [true]).map
        (fun world => (world.branch, world.state, world.intents)) == [([true], 107, ["else"])]) true
  let result : Option (List Nat) := (NIKServiceInvocation.invoke
    (FiniteSetRepresentationService.unionRequest FiniteSetRepresentationService.Controls.first
      FiniteSetRepresentationService.Controls.second FiniteSetRepresentationService.Controls.input)).acceptedValue
  expect "finite-set.actual-ordered-code" (result == some [2, 1, 2, 3, 1]) true
  expect "finite-set.code-is-not-deduplicated" (result == some [1, 2, 3]) false
  expect "finite-set.present.only-then"
    ((runWorldsAt (FiniteSetRepresentationService.Controls.branchAfterUnion 3) 7 [true]).map
      (fun world => (world.answer.asBool, world.branch, world.state, world.intents)) ==
        [(some true, [true], 8, ["then"])]) true
  expect "finite-set.absent.only-else"
    ((runWorldsAt (FiniteSetRepresentationService.Controls.branchAfterUnion 4) 7 [true]).map
      (fun world => (world.answer.asBool, world.branch, world.state, world.intents)) ==
        [(some false, [true], 107, ["else"])]) true
  expect "finite-set.wrong-union-drops-three"
    ((FiniteSetRepresentationService.Controls.leftOnly FiniteSetRepresentationService.Controls.input).contains 3) false

end LivePropositions

namespace ProgramContexts

open PrimeCandidates.SharedJudgmentProgramContexts

private def observed (output : PrimeCandidates.SharedJudgmentServiceProgramBackend.Output 2) :
    Option (Tower.Tm 2) × Bool × BranchTrace × List Nat × Nat :=
  (match output.world.answer with | .value value => some value | .stopped _ => none,
    output.world.state, output.world.branch, output.world.intents, output.replies.length)

def check : IO Unit := do
  let assembly := PrimeCandidates.SharedJudgmentFragment.common
  let environment : Sub Tower.Head 1 2 := fun _ => .var 0
  let after (code : PrimeCandidates.SharedJudgmentServicePrograms.Code 1) :=
    PrimeCandidates.SharedJudgmentServicePrograms.Code.sequenceSigma code
      (.native (.call .reflexivity (.var 0)))
  for state in [false, true] do
    let direct := (PrimeCandidates.SharedJudgmentServicePrograms.Code.worlds assembly environment
      (after Controls.direct) state [true]).map observed
    let detour := (PrimeCandidates.SharedJudgmentServicePrograms.Code.worlds assembly environment
      (after Controls.detour) state [true]).map observed
    expect s!"program-context.detour.after-state-{state}" (direct == detour) true
    expect s!"program-context.dependent-result.state-{state}"
      (direct == [(some (.pair (.var 0) (.refl (.var 0))), state, [true],
        [if state then 30 else 40], 0)]) true
  expect "program-context.present-answers-collide"
    (((Controls.input false).run assembly).map (fun output => (observed output).1) ==
      ((Controls.input true).run assembly).map (fun output => (observed output).1)) true
  expect "program-context.present-answer-is-native-variable"
    (((Controls.input false).run assembly).map (fun output => (observed output).1) ==
      [some (.var 0)]) true
  expect "program-context.future-false-intent"
    (Controls.futureIntents (Controls.input false) == [[40]]) true
  expect "program-context.future-true-intent"
    (Controls.futureIntents (Controls.input true) == [[30]]) true

end ProgramContexts

namespace PolarizedServiceRuns

open NeedReference Presentation.PolarizedNeedMachine
open PrimeCandidates.SharedJudgmentPolarizedServices
open PrimeCandidates.SharedJudgmentPolarizedServices.Controls

private def initial (source : Closure Tower.Head (Operation 1) Nat 1) :
    NeedMachine Tower.Head (Operation 1) Nat Empty (Residual 1) 1 :=
  ⟨⟨0, [], .empty, .empty, 0, 0⟩, .run (.evaluate source .done) [], {}⟩

private def value? : Outcome Tower.Head (Operation 1) Nat Empty (Residual 1) 1 → Option (Tower.Tm 1)
  | .value (.returned (.native value)) => some value
  | _ => none

private def label : Outcome Tower.Head (Operation 1) Nat Empty (Residual 1) 1 → String
  | .value (.returned (.native _)) => "native-value"
  | .retryableFault (.domain (.native (.unreadable _ _))) => "unreadable-residual"
  | .retryableFault (.domain (.native (.noPayload _ _))) => "no-payload-residual"
  | _ => "other"

private def run (source : Closure Tower.Head (Operation 1) Nat 1) :=
  NeedLocalSteps.answers (extension (primitive PrimeCandidates.SharedJudgmentFragment.common))
    24 (initial source)

def check : IO Unit := do
  let captured := run (applyCaptured matchingOperation receiptArgument alteredArgument)
  expect "polarized-service.captured-matching.only-native-result"
    (captured.map value? == [some (liftClosed PrimeCandidates.SharedJudgmentServices.Examples.canonicalTransport.source)]) true
  expect "polarized-service.changed-capture.is-residual"
    ((run (applyCaptured matchingOperation alteredArgument receiptArgument)).map label ==
      ["no-payload-residual"]) true
  let passed (operation : Operation 1) (argument : Tower.Tm 1) :
      Closure Tower.Head (Operation 1) Nat 1 :=
    ⟨1, 0, 0, passedCall operation (.var 0), (fun _ => argument), Fin.elim0, Fin.elim0⟩
  expect "polarized-service.passed-matching.only-native-result"
    ((run (passed matchingOperation receiptArgument)).map value? ==
      [some (liftClosed PrimeCandidates.SharedJudgmentServices.Examples.canonicalTransport.source)]) true
  expect "polarized-service.higher-order-hol.only-native-result"
    ((run (passed holOperation PrimeCandidates.SharedJudgmentServices.SubstitutionExamples.functionSquare)).map
      value? == [some holPayload]) true
  expect "polarized-service.changed-theory.is-residual"
    ((run (passed alteredHOL PrimeCandidates.SharedJudgmentServices.SubstitutionExamples.functionSquare)).map
      label == ["no-payload-residual"]) true
  expect "polarized-service.unreadable-input.is-distinct-residual"
    ((run (passed matchingOperation (.var 0))).map label == ["unreadable-residual"]) true

end PolarizedServiceRuns

namespace DeclarationInstances

open PrimeCandidates.SharedJudgmentDeclarationInterpretation
open PrimeCandidates.SharedJudgmentDeclarationInterpretation.Controls

def check : IO Unit := do
  let assembly := PrimeCandidates.SharedJudgmentFragment.common
  let natural := naturalInstance 7 LevelExpr.param
  expect "declaration.natural.actual-installed-type"
    ((assembly.declarations.entries natural.name).map (·.type) == some natural.entry.type) true
  expect "declaration.actual-native-seven"
    (NativeWireData.decode (n := 0) (.const natural.name) == some (.natural 7)) true
  expect "declaration.actual-native-seven-is-not-eight"
    (NativeWireData.decode (n := 0) (.const natural.name) == some (.natural 8)) false
  let correct := dataInstance Tower.zero
  let changed := dataInstance (.succ Tower.zero)
  expect "declaration.data.original-level-installed"
    ((assembly.declarations.entries correct.name).map (·.type) == some correct.entry.type) true
  expect "declaration.same-name-changed-level-installed"
    ((assembly.declarations.entries changed.name).map (·.type) == some changed.entry.type) false

end DeclarationInstances

namespace FormedComparisons

open FormationSensitiveContextual FormationSensitiveContextual.ComparisonControls

def check : IO Unit := do
  expect "formed-context.expanded-annotation-visible"
    (newestIsApplication (extend Common.context expandedWireType)) true
  expect "formed-context.original-annotation-visible"
    (newestIsApplication (extend Common.context Common.wireType)) false
  expect "formed-context.dependent-family-retained"
    ((variableIdentity.reindex wireComparison.hom).code ==
      .id NativeWireData.dataType (.var 0) (.var 0)) true
  expect "formed-context.reflexivity-code-retained"
    ((variableReflexivity.reindex wireComparison.hom).code == .refl (.var 0)) true

end FormedComparisons

namespace CrossTargetServices

open NeedReference Presentation.PolarizedNeedMachine
open PrimeCandidates.SharedJudgmentPolarizedServices
open PrimeCandidates.SharedJudgmentPolarizedServices.Controls
open PrimeCandidates.SharedJudgmentServiceNaturality

private def answers {n : Nat} (operation : Operation n) (argument : Tower.Tm n) :=
  let source : Closure Tower.Head (Operation n) Nat n :=
    ⟨1, 0, 0, passedCall operation (.var 0), (fun _ => argument), Fin.elim0, Fin.elim0⟩
  let machine : NeedMachine Tower.Head (Operation n) Nat Empty (Residual n) n :=
    ⟨⟨0, [], .empty, .empty, 0, 0⟩, .run (.evaluate source .done) [], {}⟩
  NeedLocalSteps.answers (extension (primitive PrimeCandidates.SharedJudgmentFragment.common)) 24 machine

private def readValue {n : Nat} : Outcome Tower.Head (Operation n) Nat Empty (Residual n) n →
    Option (Tower.Tm n)
  | .value (.returned (.native value)) => some value
  | _ => none

private def readFault {n : Nat} : Outcome Tower.Head (Operation n) Nat Empty (Residual n) n → String
  | .retryableFault (.domain (.native (.unreadable _ _))) => "unreadable"
  | .retryableFault (.domain (.native (.noPayload _ _))) => "no-payload"
  | _ => "other"

def check : IO Unit := do
  let canonical := PrimeCandidates.SharedJudgmentServices.Examples.canonicalTransport.source
  let fill := WireControls.fillReceipt
  let liftedMatch := reindexOperation fill matchingOperation
  expect "target-scope.open-variable-before" ((answers matchingOperation (.var 0)).map readFault ==
    ["unreadable"]) true
  expect "target-scope.filled-variable-after" ((answers liftedMatch (subst fill (.var 0))).map readValue ==
    [some (liftClosed canonical)]) true
  expect "target-scope.encoded-before" ((answers matchingOperation receiptArgument).map readValue ==
    [some (liftClosed canonical)]) true
  expect "target-scope.encoded-after" ((answers liftedMatch (subst fill receiptArgument)).map readValue ==
    [some (liftClosed canonical)]) true
  expect "target-scope.altered-receipt-after" ((answers liftedMatch (subst fill alteredArgument)).map readFault ==
    ["no-payload"]) true
  expect "target-scope.hol-before"
    ((answers holOperation PrimeCandidates.SharedJudgmentServices.SubstitutionExamples.functionSquare).map readValue ==
      [some holPayload]) true
  expect "target-scope.hol-after"
    ((answers (reindexOperation HOLControls.weakenTarget holOperation) HOLControls.liftedSquare).map readValue ==
      [some (subst HOLControls.weakenTarget holPayload)]) true
  expect "target-scope.changed-hol-after"
    ((answers (reindexOperation HOLControls.weakenTarget alteredHOL) HOLControls.liftedSquare).map readFault ==
      ["no-payload"]) true
  expect "target-scope.no-lambda-capture"
    (HOLControls.liftedSquare == (.lam (.app (.var 1) (.app (.var 1) (.var 0))) : Tower.Tm 2)) false
  let transported := reindexProduced fill
    (primitive PrimeCandidates.SharedJudgmentFragment.common matchingOperation (.var 0))
  expect "target-scope.old-residual-does-not-manufacture-success"
    (match transported with | .value _ => true | _ => false) false

end CrossTargetServices

namespace ConversionViews

open FormationSensitiveContextual

def check : IO Unit := do
  expect "conversion-view.raw-projection-is-inspectably-different"
    ((NativeWireData.decode (Common.projected (.natural 7)).code).isNone) true
  expect "conversion-view.raw-seven" (NativeWireData.decode (Common.result (.natural 7)).code ==
    some (.natural 7)) true
  expect "conversion-view.raw-eight" (NativeWireData.decode (Common.result (.natural 8)).code ==
    some (.natural 8)) true
  expect "conversion-view.original-universe-witnesses-differ"
    (Common.wireType.level == FibreControls.raisedWireType.level) false

end ConversionViews

namespace UniverseCodes

open FormationSensitiveContextual

def check : IO Unit := do
  expect "universe-code.computed-dependent-identity"
    (NativeRelatorConversionChecking.check QuotientUniverses.Controls.mixedIdentityConversion
      (FibreControls.projectedIdentity (.natural 7)).code
      (FibreControls.resultIdentity (.natural 7)).code) true
  expect "universe-code.changed-dependent-endpoint"
    (NativeRelatorConversionChecking.check QuotientUniverses.Controls.mixedIdentityConversion
      (FibreControls.projectedIdentity (.natural 7)).code
      (FibreControls.resultIdentity (.natural 8)).code) false
  let lower : Tower.Head := .sort (.param 0)
  let sameLevel : Tower.Head := .sort (.max (.param 0) (.const 0))
  let higher : Tower.Head := .sort (.succ (.param 0))
  expect "universe-code.level-conversion"
    (NativeRelatorConversionChecking.check (.single (.head lower sameLevel) :
      NativeRelatorConversionChecking.Code 0) (.head lower) (.head sameLevel)) true
  expect "universe-code.successor-is-not-conversion"
    (NativeRelatorConversionChecking.check (.single (.head lower higher) :
      NativeRelatorConversionChecking.Code 0) (.head lower) (.head higher)) false
  expect "universe-code.cumulative-admission" (decide (Tower.Cumulative lower higher)) true
  expect "universe-code.no-lowering" (decide (Tower.Cumulative higher lower)) false

end UniverseCodes

namespace AdmittedDependentJ

open NativeIndexedFamilies.Intrinsic
open FormationSensitiveContextual.QuotientIdentity

private def sample := Controls.mixedInput (.natural 7)

private def certificate : NativeRelatorConversionChecking.StepCode 0 :=
  .root (.indexed (.identity sample.type sample.left sample.motive sample.method))

private def source : Tower.Tm 0 :=
  identityEliminateApp sample.type sample.left sample.motive sample.method
    sample.left (.refl sample.left)

/-- This checks the actual fixed declaration's computation, separately
from the source-admission and dependent-motive theorems in the model. -/
def check : IO Unit := do
  expect "admitted-j.path-dependent-motive.computation"
    (NativeRelatorConversionChecking.checkStep certificate source sample.method) true
  expect "admitted-j.path-dependent-motive.wrong-method"
    (NativeRelatorConversionChecking.checkStep certificate source (.refl sample.left)) false
  expect "admitted-j.path-dependent-motive.changed-endpoint"
    (NativeRelatorConversionChecking.checkStep certificate
      (identityEliminateApp sample.type sample.left sample.motive sample.method
        (NativeWireData.encode (.natural 8)) (.refl sample.left)) sample.method) false

end AdmittedDependentJ

namespace NativeIdentitySection

open FormationSensitiveContextual
open QuotientIdentityGeometry

/-- Inspect the actual typed native section. It substitutes the supplied
endpoint and reflexivity witness separately, preserving older variables. -/
def check : IO Unit := do
  let submitted := Common.projected (.natural 7)
  let native := nativeReflSection Common.wireType submitted
  expect "identity-section.actual-reflexivity-witness"
    (native.substitution 0 == Presentation.Tm.refl submitted.code) true
  expect "identity-section.actual-endpoint"
    (native.substitution 1 == submitted.code) true
  expect "identity-section.changed-endpoint"
    (native.substitution 1 == (Common.projected (.natural 8)).code) false
  let extended := newest Common.context Common.wireType
  let openNative := nativeReflSection
    (Common.wireType.reindex (projectionHom Common.context Common.wireType)) extended
  expect "identity-section.older-variable-retained"
    (openNative.substitution 2 == Presentation.Tm.var 0) true

end NativeIdentitySection

namespace NativeMotiveRetention

open FormationSensitiveContextual.QuotientIdentityInputCoherence
open NativeIndexedFamilies.Intrinsic

/-- Reflexivity computations agree even though the submitted motive and
open J syntax differ. The separate conversion theorem, not these finite
syntax tests, establishes the non-conversion of the open terms. -/
def check : IO Unit := do
  let first := Controls.variableInput
  let second := abstractedInput first
  expect "motive-retention.submitted-functions-differ" (first.motive == second.motive) false
  expect "motive-retention.open-j-syntax-differs"
    (FormationSensitiveBasedIdentity.genericTerm first.type first.left first.motive first.method ==
      FormationSensitiveBasedIdentity.genericTerm second.type second.left second.motive second.method) false
  for input in [first, second] do
    let certificate : NativeRelatorConversionChecking.StepCode 4 :=
      .root (.indexed (.identity input.type input.left input.motive input.method))
    let redex := identityEliminateApp input.type input.left input.motive input.method
      input.left (.refl input.left)
    expect "motive-retention.same-method-at-reflexivity"
      (NativeRelatorConversionChecking.checkStep certificate redex first.method) true
  let wrong : NativeRelatorConversionChecking.StepCode 4 :=
    .root (.indexed (.identity first.type first.left first.motive first.method))
  expect "motive-retention.changed-result-rejected"
    (NativeRelatorConversionChecking.checkStep wrong
      (identityEliminateApp first.type first.left first.motive first.method first.left (.refl first.left))
      first.left) false

end NativeMotiveRetention

namespace RetainedNativeInstantiation

open FormationSensitiveContextual

/-- Actual substitution of the four-variable declaration telescope is
checked before the separately proved quotient reindexing law is applied. -/
def check : IO Unit := do
  let template := QuotientIdentityInputCoherence.Controls.variableInput
  let actual := template.reindex (QuotientIdentityNativeReindexing.Controls.instantiate (.natural 7))
  let expected := QuotientIdentity.Controls.mixedInput (.natural 7)
  expect "retained-input.instantiated-type" (actual.type == expected.type) true
  expect "retained-input.instantiated-left" (actual.left == expected.left) true
  expect "retained-input.instantiated-function" (actual.motive == expected.motive) true
  expect "retained-input.instantiated-method" (actual.method == expected.method) true
  expect "retained-input.changed-left-rejected"
    (actual.left == (QuotientIdentity.Controls.mixedInput (.natural 8)).left) false

end RetainedNativeInstantiation

namespace InconclusiveViews

open Mettapedia.GSLT.LanguageDef
open NIKPropositionBranching.Controls CompletenessSpectrum.SAT.Canary
open Mettapedia.TypeTheory.AuthorityOutcomeViews

def check : IO Unit := do
  let untouched := sampleAssignments [] positiveFormula []
  let attempted := sampleAssignments [] positiveFormula [falseAssignment]
  let established := sampleAssignments [] positiveFormula [falseAssignment, trueAssignment]
  expect "attempt-view.same-empty-answer" (untouched.asBool == attempted.asBool) true
  expect "attempt-view.same-incomplete-status" (untouched.publicStatus == attempted.publicStatus) true
  expect "attempt-view.empty-submission" (NIKOutcomeViewControls.sampledReceiptSize [] positiveFormula []) (some 0)
  expect "attempt-view.rejected-submission" (NIKOutcomeViewControls.sampledReceiptSize [] positiveFormula [falseAssignment]) (some 1)
  expect "attempt-view.retained-submission"
    ((retainedIncompleteReceipt (retainedView attempted)).map List.length) (some 1)
  expect "attempt-view.success" established.asBool (some true)
  expect "attempt-view.success-no-incomplete-receipt" (incompleteReceipt established).isNone true

end InconclusiveViews

namespace InstantiatedDependentJ

open NativeIndexedFamilies.Intrinsic NativeIdentityLevelInstantiation

private def chosen := Controls.higherLevels (.const 3)
private def signature := HOLNativeRelatorCompatibility.signature
private def motive : Tower.Tm 0 := .lam (.lam (Controls.higherBody (.const 3)))
private def method : Tower.Tm 0 := .refl (.refl (.head .legacyGround))
private def certificate : NativeRelatorConversionChecking.StepCode 0 :=
  .root (.indexed (.identity (sortTm (.const 3)) (.head .legacyGround) motive method))

/-- The transformed environment really changes the declared profile; the
same computation checker still rejects a crossed method or endpoint. -/
def check : IO Unit := do
  expect "instantiated-j.new-environment-lookup"
    ((rules chosen signature).constantType identityEliminateName == some (declarationType chosen)) true
  expect "instantiated-j.original-environment-is-different"
    ((OpaqueRelatorExtension.rules signature).constantType identityEliminateName == some (declarationType chosen)) false
  expect "instantiated-j.higher-motive.computation"
    (NativeRelatorConversionChecking.checkStep certificate (Controls.higherSource (.const 3)) method) true
  expect "instantiated-j.higher-motive.wrong-method"
    (NativeRelatorConversionChecking.checkStep certificate (Controls.higherSource (.const 3))
      (.refl (.head .legacyGround))) false
  expect "instantiated-j.higher-motive.changed-endpoint"
    (NativeRelatorConversionChecking.checkStep certificate
      (identityEliminateApp (sortTm (.const 3)) (.head .legacyGround) motive method
        (sortTm (.const 0)) (.refl (.head .legacyGround))) method) false
  expect "instantiated-j.element-level" (LevelExpr.eval (fun _ => 0) (chosen 0)) 4
  expect "instantiated-j.motive-level" (LevelExpr.eval (fun _ => 0) (chosen 1)) 5
  expect "instantiated-j.other-parameter-retained" (chosen 2 == .param 2) true

end InstantiatedDependentJ

namespace FormedContextBoundary

open FormationSensitiveContextSourceObstruction

/-- These are observations of the actual substitution used by the proved
unformed-source obstruction, not a Boolean test for arbitrary formation. -/
def check : IO Unit := do
  expect "formed-context.substituted-abstract-function"
    (substitution 1 == (dataFunction : Tower.Tm 0)) true
  expect "formed-context.substituted-abstract-type"
    (substitution 2 == (dataFunctionType : Tower.Tm 0)) true
  expect "formed-context.newest-annotation-becomes-redex"
    (subst substitution (source.lookup 0) == (.app dataFunction wire : Tower.Tm 0)) true
  expect "formed-context.newest-annotation-is-not-literal-data"
    (subst substitution (source.lookup 0) == (NativeWireData.dataType : Tower.Tm 0)) false

end FormedContextBoundary

namespace NamedContexts

open Mettapedia.TypeTheory.NamedValueContexts Mettapedia.TypeTheory.NamedContextDataflow
open Mettapedia.TypeTheory.NamedContextDataflow.Controls

def check : IO Unit := do
  expect "named-context.captured-before" (runReady arithmetic originalTable originalCurrent fixed) (some (some 10))
  expect "named-context.live-before" (runReady arithmetic originalTable originalCurrent live) (some (some 10))
  expect "named-context.captured-after" (runReady arithmetic revisedTable revisedCurrent fixed) (some (some 10))
  expect "named-context.live-after" (runReady arithmetic revisedTable revisedCurrent live) (some (some 12))
  expect "named-context.no-overwrite" (publishVersion? revisedTable originalVersion revised).isNone true
  expect "named-context.fresh-publication" (publishVersion? originalTable revisedVersion revised).isSome true
  expect "named-context.unrelated-edit"
    (Mettapedia.Languages.Dataflow.readyValue arithmetic ((99, 1000) :: original) addition) (some 10)
  expect "named-context.missing-context" (runReady arithmetic originalTable revisedCurrent live) none
  let incomplete := Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation.writeSource
    originalTable (revisedVersion, [(0, 3)])
  expect "named-context.missing-binding" (runReady arithmetic incomplete revisedCurrent live) (some none)
  expect "named-context.inspected-bindings"
    ((inspect revisedTable revisedCurrent Mettapedia.Languages.Dataflow.lookup fixed [0, 1]).map Prod.snd)
    (some [(0, some 3), (1, some 7)])
  expect "named-context.inspection-no-destination" (Mettapedia.Languages.Dataflow.lookup original 2) none
  let oldInput := PrimeCandidates.SharedJudgmentNamedContext.resolveInput
    PrimeCandidates.SharedJudgmentNamedContext.Controls.oldTable
    PrimeCandidates.SharedJudgmentNamedContext.Controls.before
    PrimeCandidates.SharedJudgmentNamedContext.Controls.live
  let newInput := PrimeCandidates.SharedJudgmentNamedContext.resolveInput
    PrimeCandidates.SharedJudgmentNamedContext.Controls.newTable
    PrimeCandidates.SharedJudgmentNamedContext.Controls.after
    PrimeCandidates.SharedJudgmentNamedContext.Controls.live
  expect "named-context.native-environment-changed"
    (oldInput.map (fun input => input.environment 0) == newInput.map (fun input => input.environment 0)) false

end NamedContexts

namespace UniformFusion

open Mettapedia.Logic.HOL Mettapedia.Logic.HOL.UniformListInduction
open Mettapedia.Logic.HOL.UniformListMapFusion

def check : IO Unit := do
  expect "uniform-fusion.object-proof-nodes" (mapFusionProof (Γ := [])).nodeCount 60
  let f : Expr [mapping, mapping, sequence] mapping := .var .vz
  let g : Expr [mapping, mapping, sequence] mapping := .var (.vs .vz)
  let xs : Expr [mapping, mapping, sequence] sequence := .var (.vs (.vs .vz))
  expect "uniform-fusion.three-universal-instantiations" (applyFusion f g xs).nodeCount 63
  expect "uniform-fusion.quantified-proof-root"
    ((mapFusionProof (Γ := [])).rootObservation.rule == Mettapedia.Logic.HOL.ProofSyntax.RuleTag.allI) true
  expect "uniform-fusion.instantiated-proof-root"
    ((applyFusion f g xs).rootObservation.rule == Mettapedia.Logic.HOL.ProofSyntax.RuleTag.allE) true
  expect "uniform-fusion.noncommuting-boolean-functions"
    (([false].map Bool.not).map (fun _ => true)) [true]
  expect "uniform-fusion.swapped-counterexample"
    (([false].map (fun _ => true)).map Bool.not) [false]

end UniformFusion

namespace IndexedCoherence

open Mettapedia.TypeTheory.MonoidIndexedTransportCoherence
open Mettapedia.TypeTheory.MonoidIndexedTransportCoherence.Controls
open Mettapedia.TypeTheory.MonoidIndexedFamilyConversion
open Mettapedia.TypeTheory.ConversionDecisionComparison

def check : IO Unit := do
  expect "indexed-coherence.direct-route-size" (pathConstructorCount directReceipt.conversion) 1
  expect "indexed-coherence.expanded-route-size" (pathConstructorCount expandedReceipt.conversion) 5
  expect "indexed-coherence.direct-cursor" (transport rightUnitPath cursor).val 1
  expect "indexed-coherence.expanded-cursor" (transport expandedRightUnitPath cursor).val 1
  expect "indexed-coherence.substitution-expands-cursor"
    (substituteValue expandIndex packetX targetCursor).val 2
  expect "indexed-coherence.transported-expanded-cursor"
    (transport (substPath expandIndex rightUnitPath)
      (substituteValue expandIndex packetXUnit cursor)).val 2

end IndexedCoherence

namespace RetainedPresentations

open Mettapedia.TypeTheory.RetainedPresentationViews
open Mettapedia.TypeTheory.RetainedPresentationViews.Controls
open Mettapedia.TypeTheory.NamedValueContexts
open Mettapedia.TypeTheory.MonoidIndexedTransportCoherence
open Mettapedia.TypeTheory.ConversionDecisionComparison

def check : IO Unit := do
  expect "retained-presentation.original" capturedReadout (some (1, some 5))
  expect "retained-presentation.stable-after-publication" retainedAfterPublicationReadout (some 5)
  expect "retained-presentation.explicit-live" liveAfterPublicationReadout (some 1)
  expect "retained-presentation.equivalent-not-original" representativeReadout (1, 1)
  expect "retained-presentation.missing-key"
    (recover (Presentation := PacketPresentation) (fun _ => none) retained).isNone true
  expect "retained-presentation.occupied-key-rejected"
    (publishVersion? originalStore retained.version direct).isNone true
  expect "retained-presentation.coarse-view-retains-reference"
    ((recover originalStore (mapView (fun _ => ()) retained)).map
      (fun presentation => pathConstructorCount presentation.path)) (some 5)
  expect "retained-presentation.nonconstant-value" (observePacket zero).val 0

end RetainedPresentations

namespace NamedIdentityRegions

open PrimeCandidates.SharedJudgmentNamedIdentityRegions
open PrimeCandidates.SharedJudgmentNamedIdentityRegions.Controls
open Mettapedia.TypeTheory.RetainedPresentationViews
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

def check : IO Unit := do
  expect "named-identity.distinct-native-presentations" (direct.term != discharged.term) true
  expect "named-identity.original-after-new-publication"
    ((recover extendedProofStore view).map fun proof => proof.term == discharged.term) (some true)
  expect "named-identity.live-application"
    ((resolveApplication proofStore bindings before view (.live "region-assumptions")).map
      fun proof => proof.term == discharged.term) (some true)
  expect "named-identity.missing-live-binding"
    (resolveApplication proofStore bindings afterWithdrawal view (.live "region-assumptions")).isNone true
  expect "named-identity.original-binding-still-applies"
    ((resolveApplication proofStore bindings afterWithdrawal view (.versioned bindingVersion)).map
      fun proof => proof.term == discharged.term) (some true)
  expect "named-identity.unrelated-revision"
    ((resolveApplication proofStore bindings (before.update "unrelated" 1) view (.live "region-assumptions")).map
      fun proof => proof.term == discharged.term) (some true)
  expect "named-identity.genuine-reindexing"
    ((resolveApplication proofStore extendedBindings before view (.live "region-assumptions")).map
      fun proof => proof.term == subst projection discharged.term) (some true)
  expect "named-identity.old-witness-not-fresh"
    (extendedBinding.substitution (0 : Fin 6) == (.var 0)) false

end NamedIdentityRegions

def run : IO Unit := do
  expect "scoped-identity.derived-assumed-inspection-and-guest-controls"
    PrimeCandidates.SharedJudgmentScopedIdentityQualification.Controls.checks [true, true, true, true]
  expect "native-decidable-identity.constructor-controls"
    PrimeCandidates.SharedJudgmentNativeDecidableIdentity.Controls.syntaxChecks [true, true, true, true]
  expect "native-boolean-region.same-instance-named-controls"
    PrimeCandidates.SharedJudgmentNativeBooleanNamedRegion.checks [true, true, true, true, true, true]
  expect "native-hedberg.constructed-proof-and-distinct-paths"
    PrimeCandidates.SharedJudgmentNativeHedberg.Controls.syntaxChecks [true, true, true, true]
  expect "native-identity-region.syntax-and-scope"
    PrimeCandidates.SharedJudgmentIdentityRegions.Controls.syntaxChecks [true, true, true, true]
  RetainedPresentations.check
  NamedIdentityRegions.check
  NamedContexts.check
  UniformFusion.check
  IndexedCoherence.check
  matching
  cognitive
  contextualViews
  serviceBackend
  repeatedServices
  RepeatedRunViews.check
  fourFaceServices
  noncanonicalData
  inspectableEvidence
  SubmittedProofEvidence.check
  RequiredServiceRegistry.check
  ActualAssemblyServices.check
  LivePropositions.check
  ProgramContexts.check
  PolarizedServiceRuns.check
  DeclarationInstances.check
  FormedComparisons.check
  CrossTargetServices.check
  ConversionViews.check
  UniverseCodes.check
  AdmittedDependentJ.check
  NativeIdentitySection.check
  NativeMotiveRetention.check
  RetainedNativeInstantiation.check
  InconclusiveViews.check
  InstantiatedDependentJ.check
  FormedContextBoundary.check

#eval run

end JointExperiments
