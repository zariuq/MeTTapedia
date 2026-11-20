import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMachine
import Mettapedia.OSLF.MeTTaIL.CollectionContextCoverage
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionFiringCoverage
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceReadout
import Mettapedia.OSLF.MeTTaIL.CollectionRootCoverage

/-!
# Matching-to-publication coverage of retained collection occurrence work

Accepted matching allocations are installed at the same global work allowance
that publishes them. Every installed continuation retains its initialization
history. Depth-qualified source outcomes therefore reach the joint log while
matching continues. Actual receipt firings with increasing capture spines and
checked nullary or mode-parametric canonical provider queries are covered through canonical typed
context variants. Input guards require canonical finite provider rows.
Additional equation theories, outputs, quantified and child-step premises
remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMatcher

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax CollectionOccurrenceHandoff CollectionOccurrenceBatch

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}

theorem collect_contains (job : Job) (licensed : job.Valid plan bound expected source)
    (work depth : Nat) (answers : List RecursiveCollectionMachine.Answer)
    (published : ∀ answer ∈ answers, Published job work answer)
    {answer : RecursiveCollectionMachine.Answer} (member : answer ∈ answers)
    {allocation : Allocation plan bound expected source}
    (made : allocate? job licensed work answer (published answer member) depth = some allocation) :
    allocation ∈ collect job licensed work depth answers published := by
  induction answers with
  | nil => cases member
  | cons first answers ih =>
    rcases List.mem_cons.mp member with rfl | inside
    · simp only [collect, made, Option.toList_some, List.singleton_append]
      exact List.mem_cons_self
    · exact List.mem_append_right _ (ih _ inside made)

theorem lanes_contains (job : Job) (licensed : job.Valid plan bound expected source) :
    Lane.begin job licensed ∈ lanes plan bound expected source :=
  List.mem_map.mpr ⟨⟨job, (jobs_exact ..).mpr licensed⟩, List.mem_attach _ _, rfl⟩

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMatcher

namespace Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMachine

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralPremise CollectionOccurrenceBatch CollectionOccurrenceMatcher

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}

variable {matcher : MatchingExecution}

theorem runWith_matchers (profile : SeedProfile matcher plan bound expected source)
    (depth work : Nat) (state : State plan bound expected source matcher) :
    (runWith profile depth work state).matchers = state.matchers.map (Lane.resume work) := by
  induction work generalizing state with
  | zero =>
    have idle : (Lane.resume 0 : Lane plan bound expected source → _) = id := by
      funext lane
      cases lane
      simp only [Lane.resume, Nat.add_zero, RecursiveCollectionMachine.run]
      rfl
    change state.matchers = state.matchers.map (Lane.resume 0)
    rw [idle, List.map_id]
  | succ work ih =>
    change (runWith profile depth work (roundWith profile depth state)).matchers = _
    simp only [ih, roundWith, List.map_map]
    apply List.map_congr_left
    intro lane _
    exact (Lane.resume_add 1 work lane).symm.trans (by rw [Nat.add_comm 1 work])

theorem run_matchers (depth work : Nat) (state : State plan bound expected source) :
    (run depth work state).matchers = state.matchers.map (Lane.resume work) :=
  runWith_matchers (ordinarySeedProfile plan bound expected source) depth work state

def InitializedWith (profile : SeedProfile matcher plan bound expected source)
    (frame : Frame plan bound expected source matcher) : Prop :=
  ∃ work, frame = Frame.run work (Frame.initialWith profile frame.allocation)

def Initialized (frame : Frame plan bound expected source) : Prop :=
  ∃ work, frame = Frame.run work (Frame.initial frame.allocation)

theorem InitializedWith_ordinary (frame : Frame plan bound expected source) :
    InitializedWith (ordinarySeedProfile plan bound expected source) frame ↔ Initialized frame := Iff.rfl

theorem roundWith_initialized (profile : SeedProfile matcher plan bound expected source)
    (depth : Nat) {state : State plan bound expected source matcher}
    (initialized : ∀ frame ∈ state.batch.frames, InitializedWith profile frame) :
    ∀ frame ∈ (roundWith profile depth state).batch.frames, InitializedWith profile frame := by
  intro frame member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  rcases List.mem_append.mp present with old | fresh
  · obtain ⟨work, same⟩ := initialized original old
    refine ⟨work + 1, ?_⟩
    change Frame.run 1 original = Frame.run (work + 1) (Frame.initialWith profile original.allocation)
    rw [same, Frame.run_add]
    rfl
  · obtain ⟨allocation, _, same⟩ := List.mem_map.mp fresh
    cases same
    exact ⟨1, rfl⟩

theorem round_initialized (depth : Nat) {state : State plan bound expected source}
    (initialized : ∀ frame ∈ state.batch.frames, Initialized frame) :
    ∀ frame ∈ (round depth state).batch.frames, Initialized frame :=
  roundWith_initialized (ordinarySeedProfile plan bound expected source) depth initialized

theorem runWith_initialized (profile : SeedProfile matcher plan bound expected source)
    (depth work : Nat) :
    ∀ frame ∈ (runWith profile depth work (beginWith matcher plan bound expected source)).batch.frames,
      InitializedWith profile frame := by
  have propagate : ∀ work (state : State plan bound expected source matcher),
      (∀ frame ∈ state.batch.frames, InitializedWith profile frame) →
      ∀ frame ∈ (runWith profile depth work state).batch.frames, InitializedWith profile frame := by
    intro work
    induction work with
    | zero => exact fun _ ready => ready
    | succ work ih =>
        exact fun state ready => ih (roundWith profile depth state) (roundWith_initialized profile depth ready)
  exact propagate work _ (by intro frame member; cases member)

theorem run_initialized (depth work : Nat) :
    ∀ frame ∈ (run depth work (begin plan bound expected source)).batch.frames, Initialized frame :=
  runWith_initialized (ordinarySeedProfile plan bound expected source) depth work

/-- Every accepted allocation is present in retained conditional work as
soon as its matching answer appears in the source job's retained matcher. -/
theorem accepted_allocation_installedWith
    (profile : SeedProfile matcher plan bound expected source) (depth work : Nat) (job : CollectionOccurrenceHandoff.Job)
    (licensed : job.Valid plan bound expected source) (answer : RecursiveCollectionMachine.Answer)
    (published : Published job work answer) (allocation : Allocation plan bound expected source)
    (made : allocate? job licensed work answer published depth = some allocation) :
    ∃ spent, Frame.run spent (Frame.initialWith profile allocation) ∈
      (runWith profile depth work (beginWith matcher plan bound expected source)).batch.frames := by
  let lane := (Lane.begin job licensed).resume work
  have retained : lane ∈ (runWith profile depth work (beginWith matcher plan bound expected source)).matchers := by
    rw [runWith_matchers]
    exact List.mem_map_of_mem (lanes_contains job licensed)
  have inside : allocation ∈ lane.account depth := by
    simpa only [lane, Lane.account, Lane.resume, Lane.begin, Nat.zero_add] using
      (collect_contains job licensed work depth _ (fun _ member => member) published made)
  have sourceAccount := List.mem_flatMap.mpr ⟨lane, retained, inside⟩
  have installed := (installed_accountWith profile depth work).symm.subset sourceAccount
  obtain ⟨frame, present, same⟩ := List.mem_map.mp installed
  obtain ⟨spent, initialized⟩ := runWith_initialized profile depth work frame present
  rw [same] at initialized
  exact ⟨spent, initialized ▸ present⟩

theorem accepted_allocation_installed (depth work : Nat) (job : CollectionOccurrenceHandoff.Job)
    (licensed : job.Valid plan bound expected source) (answer : RecursiveCollectionMachine.Answer)
    (published : Published job work answer) (allocation : Allocation plan bound expected source)
    (made : allocate? job licensed work answer published depth = some allocation) :
    ∃ spent, Frame.run spent (Frame.initial allocation) ∈
      (run depth work (begin plan bound expected source)).batch.frames :=
  accepted_allocation_installedWith (ordinarySeedProfile plan bound expected source) depth work job licensed
    answer published allocation made

theorem accepted_allocation_source_coverage (depth work : Nat) (job : CollectionOccurrenceHandoff.Job)
    (licensed : job.Valid plan bound expected source) (answer : RecursiveCollectionMachine.Answer)
    (published : Published job work answer) (allocation : Allocation plan bound expected source)
    (made : allocate? job licensed work answer published depth = some allocation)
    (trace : List GeneralScopedMatchMachine.BagChoice) (completed : ScopedRuleMatching.Assignment)
    (history : List GeneralPremise.Event) (target : Pattern)
    (held : GeneralPremise.RootFiring allocation.request.environment allocation.request.bound
      allocation.request.type allocation.request.prepared.source allocation.request.index trace
      allocation.request.prepared.ordinary.assignment completed history target)
    (bounded : StructuralDescent.eventsDepth history ≤ allocation.request.depth) :
    ∃ total, tag allocation
        ⟨allocation.request.prepared.ordinary.trace, allocation.request.prepared.ordinary.assignment,
          completed, history, target⟩ ∈
      (run depth total (begin plan bound expected source)).batch.log := by
  obtain ⟨spent, installed⟩ := accepted_allocation_installed depth work job licensed answer published allocation made
  obtain ⟨extra, emitted⟩ := retained_source_coverage depth _
    (run_invariant depth work (begin_invariant depth)) allocation spent installed
    trace completed history target held bounded
  exact ⟨work + extra, (run_add depth work extra _).symm ▸ emitted⟩

/-- Independent recursive matching evidence and the local static checks
earn eventual installation. There is no supplied execution result or
completeness certificate in the hypotheses. -/
theorem valid_match_eventually_installedWith
    (profile : SeedProfile matcher plan bound expected source) (depth : Nat) (job : CollectionOccurrenceHandoff.Job)
    (licensed : job.Valid plan bound expected source) (answer : RecursiveCollectionMachine.Answer)
    (matched : EquationalScopedReceipts.Matches ScopedRuleMatching.literalBodyComparison
      job.request.rule job.request.spec job.request.ambient job.request.site job.request.path
      job.request.depth job.request.initial job.request.schema job.request.target answer.trace answer.assignment)
    (admitted : RuleBinding.admittedFor job.origin.declaration.rule job.origin.declaration.binding.spec = true)
    (sorted : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language (GeneralPlanEnvironment.environment plan).free
      job.variant.site.focusBound job.variant.site.focusType job.variant.site.focus) :
    ∃ (work : Nat) (allocation : Allocation plan bound expected source) (spent : Nat),
      allocation.job = job ∧ allocation.answer = answer ∧
        Frame.run spent (Frame.initialWith profile allocation) ∈
          (runWith profile depth work (beginWith matcher plan bound expected source)).batch.frames := by
  obtain ⟨work, finished⟩ := RecursiveCollectionMachine.finiteDrain job.request
    (RecursiveCollectionMachine.start job.request)
  have published : Published job work answer := by
    unfold Published
    rw [RecursiveCollectionMachine.completed_traces job.request work finished]
    exact RecursiveCollectionMachine.referenceAt_complete matched
  obtain ⟨allocation, made, sameJob, sameAnswer⟩ :=
    allocate_published_exists job licensed work depth answer published admitted sorted
  obtain ⟨spent, installed⟩ := accepted_allocation_installedWith profile depth work job licensed answer
    published allocation made
  exact ⟨work, allocation, spent, sameJob, sameAnswer, installed⟩

theorem valid_match_eventually_installed (depth : Nat) (job : CollectionOccurrenceHandoff.Job)
    (licensed : job.Valid plan bound expected source) (answer : RecursiveCollectionMachine.Answer)
    (matched : EquationalScopedReceipts.Matches ScopedRuleMatching.literalBodyComparison
      job.request.rule job.request.spec job.request.ambient job.request.site job.request.path
      job.request.depth job.request.initial job.request.schema job.request.target answer.trace answer.assignment)
    (admitted : RuleBinding.admittedFor job.origin.declaration.rule job.origin.declaration.binding.spec = true)
    (sorted : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language (GeneralPlanEnvironment.environment plan).free
      job.variant.site.focusBound job.variant.site.focusType job.variant.site.focus) :
    ∃ (work : Nat) (allocation : Allocation plan bound expected source) (spent : Nat),
      allocation.job = job ∧ allocation.answer = answer ∧
        Frame.run spent (Frame.initial allocation) ∈
          (run depth work (begin plan bound expected source)).batch.frames :=
  valid_match_eventually_installedWith (ordinarySeedProfile plan bound expected source) depth job licensed
    answer matched admitted sorted

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMachine

namespace Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceHandoff

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax CanonicalBags ScopedRuleMatching
open GeneralPremise GeneralTypedSites CollectionSelection RecursiveCollectionHandoff
open Mettapedia.GSLT.LanguageDef WellSorted GeneralTypedOccurrence

/-- An actual conditional source receipt determines a generated job at the
canonical source, a published recursive allocation, and a valid receipt at
its prepared presentation. Checked nullary or mode-parametric canonical provider queries are transported. The
result class and complete premise history are preserved, including through
set contexts whose original occurrences merge during canonicalization. -/
theorem receipt_has_prepared_replay {plan : GeneralExecutionAdmission.Plan}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    {original : GeneralRuleJobs.Receipt}
    (valid : original.Valid plan bound expected source)
    (binderOk : BinderLawsFor [] (GeneralPlanEnvironment.environment plan).reflection original.job.declaration.rule)
    (increasing : IncreasingSpines original.job.declaration.rule
      original.job.declaration.binding.spec)
    (guards : CollectionGuardFragment plan.snapshot.provider
      ⟨original.job.ordinal, original.job.declaration.rule, original.job.declaration.binding.spec,
        original.job.site.focusBound, 0, 0⟩ original.job.declaration.rule.premises) :
    ∃ (job : Job) (work : Nat) (answer : RecursiveCollectionMachine.Answer)
        (prepared : Prepared) (target : Pattern),
      job.Valid plan bound expected (canon source) ∧
      CollectionOccurrenceMatcher.Published job work answer ∧
      prepare job.request answer = some prepared ∧ prepared.Valid job.request answer ∧
      prepared.ordinary.assignment = canonAssignment original.captured ∧
      Same original.target (job.variant.site.context.fill target) ∧
      GeneralRuleJobs.Receipt.Valid plan bound expected (job.presentedSource prepared)
        ⟨job.preparedJob prepared, prepared.ordinary.trace, prepared.ordinary.assignment,
          canonAssignment original.completed, original.premiseHistory, target,
          job.variant.site.context.fill target⟩ ∧
      job.origin.ordinal = original.job.ordinal ∧
      job.origin.declaration = original.job.declaration := by
  obtain ⟨site, context, licensed, focus, focusBound, focusType, frames,
    member, contextShape, compare⟩ := licensed_canonical_variant valid.1.2
  let job : Job := ⟨{ original.job with site }, ⟨site, recontext site context⟩⟩
  have licensedJob : job.Valid plan bound expected (canon source) := by
    refine ⟨⟨valid.1.1, licensed⟩, ?_⟩
    exact List.mem_map.mpr ⟨context, member, rfl⟩
  have requestEq : job.request = RecursiveCollectionFiringCoverage.request
      original.job.declaration.rule original.job.declaration.binding.spec
      original.job.site.focusBound original.job.site.focus := by
    simp only [Job.request, job, recontext, focus, focusBound,
      RecursiveCollectionFiringCoverage.request]
  obtain ⟨work, answer, prepared, target, published, captures, computed, matching, replayed, sameTarget⟩ :=
    RecursiveCollectionFiringCoverage.firing_has_prepared_match valid.2.1
      (GeneralRuleJobs.Job.selected_rule valid.1)
      (GeneralRuleJobs.Job.selected_specification valid.1) binderOk increasing guards
  have preparedValid : prepared.Valid job.request answer := requestEq.symm ▸ matching
  have sameCapture : prepared.ordinary.assignment = canonAssignment original.captured :=
    preparedValid.assignment.trans captures
  have replayed' : RootFiring (GeneralPlanEnvironment.environment plan)
      (job.preparedJob prepared).site.focusBound (job.preparedJob prepared).site.focusType
      (job.preparedJob prepared).site.focus (job.preparedJob prepared).ordinal
      prepared.ordinary.trace prepared.ordinary.assignment (canonAssignment original.completed)
      original.premiseHistory target := by
    simpa only [Job.preparedJob, job, refocus, recontext, focusBound, focusType, sameCapture,
      GeneralPlanEnvironment.environmentWith_empty]
      using replayed
  have represented : (job.preparedJob prepared).site.acceptsReplacementRepresentation
      (GeneralPlanEnvironment.environment plan).language target = true := by
    have transported := contextShape.replacementRepresentations
      (language := (GeneralPlanEnvironment.environment plan).language)
      original.job.site.typingFrames
      (fun parameter => matchesParameterRepresentation?_same parameter sameTarget)
    change replacementRepresentations? _ context site.typingFrames target = true
    rw [frames, ← transported]
    exact valid.2.2.1
  have globalSame : Same original.target (context.fill target) := by
    rw [valid.2.2.2.1]
    exact compare _ _ sameTarget
  refine ⟨job, work, answer, prepared, target, licensedJob,
    (by simpa only [CollectionOccurrenceMatcher.Published, requestEq] using published),
    requestEq.symm ▸ computed, preparedValid, sameCapture,
    globalSame, ?_⟩
  refine ⟨?_, rfl, rfl⟩
  exact ⟨job.prepared_valid licensedJob preparedValid, replayed', represented, rfl,
    openPatternWellSorted_of_eqvGen ((same_iff _ _).mp globalSame) valid.2.2.2.2⟩

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceHandoff

namespace Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMachine

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax CanonicalBags ScopedRuleMatching
open GeneralPremise CollectionOccurrenceHandoff CollectionOccurrenceMatcher CollectionOccurrenceBatch

/-- A finite check of precisely the rule-side hypotheses used below. It
does not discharge equation, contextual-policy, or emitted-runtime duties. -/
def checkNullaryFragment (plan : GeneralExecutionAdmission.Plan) : Bool :=
  plan.rules.all fun declaration =>
    CollectionRootSearch.checkBindingSpines declaration.binding.spec &&
      checkNullaryGuards declaration.rule.premises &&
      checkBinderLawsFor [] (GeneralPlanEnvironment.environment plan).reflection declaration.rule

theorem checkNullaryFragment_sound {plan : GeneralExecutionAdmission.Plan}
    (checked : checkNullaryFragment plan = true)
    (declaration : GeneralExecutionAdmission.RulePlan) (selected : declaration ∈ plan.rules) :
    IncreasingSpines declaration.rule declaration.binding.spec ∧ NullaryGuards declaration.rule.premises ∧
      BinderLawsFor [] (GeneralPlanEnvironment.environment plan).reflection declaration.rule := by
  have both := List.all_eq_true.mp checked declaration selected
  simp only [Bool.and_eq_true] at both
  exact ⟨CollectionRootSearch.checkBindingSpines_sound both.1.1,
    (checkNullaryGuards_iff _).mp both.1.2, (checkBinderLawsFor_iff _ _ _).mp both.2⟩

/-- The query profile checks actual occurrence spines, input object templates,
all argument modes and canonical provider rows. Nullary guards retain their
original scope. -/
def checkGuardFragment (plan : GeneralExecutionAdmission.Plan) : Bool :=
  plan.rules.all fun declaration =>
    CollectionRootSearch.checkBindingSpines declaration.binding.spec &&
      checkCollectionGuardFragment plan.snapshot.provider
        ⟨0, declaration.rule, declaration.binding.spec, [], 0, 0⟩ declaration.rule.premises &&
      checkBinderLawsFor [] (GeneralPlanEnvironment.environment plan).reflection declaration.rule

theorem checkGuardFragment_sound {plan : GeneralExecutionAdmission.Plan}
    (checked : checkGuardFragment plan = true)
    (declaration : GeneralExecutionAdmission.RulePlan) (selected : declaration ∈ plan.rules)
    (bound : List TypeExpr) (index : Nat) :
    IncreasingSpines declaration.rule declaration.binding.spec ∧
      CollectionGuardFragment plan.snapshot.provider
        ⟨index, declaration.rule, declaration.binding.spec, bound, 0, 0⟩ declaration.rule.premises ∧
      BinderLawsFor [] (GeneralPlanEnvironment.environment plan).reflection declaration.rule := by
  have both := List.all_eq_true.mp checked declaration selected
  simp only [Bool.and_eq_true] at both
  refine ⟨CollectionRootSearch.checkBindingSpines_sound both.1.1, ?_, (checkBinderLawsFor_iff _ _ _).mp both.2⟩
  exact ((checkCollectionGuardFragment_iff _ _ _).mp both.1.2).recontext bound index

theorem checkNullaryFragment_guard {plan : GeneralExecutionAdmission.Plan}
    (checked : checkNullaryFragment plan = true) : checkGuardFragment plan = true := by
  apply List.all_eq_true.mpr
  intro declaration selected
  have both := List.all_eq_true.mp checked declaration selected
  simp only [Bool.and_eq_true] at both
  simp only [Bool.and_eq_true, checkCollectionGuardFragment, Bool.or_eq_true]
  exact ⟨⟨both.1.1, .inl both.1.2⟩, both.2⟩

/-- Every valid source receipt in the increasing-spine, checked-guard
fragment eventually reaches the actual joint matching/continuation log.
The native finisher accepts the reconstructed receipt. The source premise
history is retained exactly and the target retains its collection meaning.
This is coverage of receipt firings, independently of additional equations. -/
theorem receipt_eventually_published_with_bindings {plan : GeneralExecutionAdmission.Plan}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    {original : GeneralRuleJobs.Receipt}
    (valid : original.Valid plan bound expected source)
    (binderOk : BinderLawsFor [] (GeneralPlanEnvironment.environment plan).reflection original.job.declaration.rule)
    (increasing : IncreasingSpines original.job.declaration.rule original.job.declaration.binding.spec)
    (guards : CollectionGuardFragment plan.snapshot.provider
      ⟨original.job.ordinal, original.job.declaration.rule, original.job.declaration.binding.spec,
        original.job.site.focusBound, 0, 0⟩ original.job.declaration.rule.premises)
    (depth : Nat) (bounded : StructuralDescent.eventsDepth original.premiseHistory ≤ depth) :
    ∃ (work : Nat) (packet : Publication) (receipt : GeneralRuleJobs.Receipt),
      packet ∈ (run depth work (begin plan bound expected (canon source))).batch.log ∧
      packet.finish? plan bound expected = some receipt ∧
      packet.job.Valid plan bound expected (canon source) ∧
      receipt.job = packet.job.preparedJob packet.prepared ∧
      receipt.captured = canonAssignment original.captured ∧
      receipt.completed = canonAssignment original.completed ∧
      receipt.premiseHistory = original.premiseHistory ∧
      packet.job.origin.ordinal = original.job.ordinal ∧
      packet.job.origin.declaration = original.job.declaration ∧
      receipt.job.ordinal = original.job.ordinal ∧
      receipt.job.declaration = original.job.declaration ∧
      Same original.target receipt.target := by
  obtain ⟨job, work, answer, prepared, target, licensed, published, computed, matching,
    captures, sameTarget, replayed, ordinal, declaration⟩ := receipt_has_prepared_replay valid binderOk increasing guards
  let receipt : GeneralRuleJobs.Receipt :=
    ⟨job.preparedJob prepared, prepared.ordinary.trace, prepared.ordinary.assignment,
      canonAssignment original.completed, original.premiseHistory, target,
      job.variant.site.context.fill target⟩
  have root := GeneralRuleJobs.receipt_root_readout replayed
  have sorted : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language (GeneralPlanEnvironment.environment plan).free
      job.variant.site.focusBound job.variant.site.focusType job.variant.site.focus := by
    exact openPatternWellSorted_of_eqvGen ((same_iff _ _).mp matching.source.symm) root.2.1
  obtain ⟨allocation, made, sameJob, sameAnswer⟩ := allocate_published_exists job licensed
    work depth answer published root.1 sorted
  obtain ⟨_, _, sameDepth, allocationPrepared⟩ := allocate_readout job licensed work depth
    answer published made
  have samePrepared : allocation.prepared = prepared :=
    Option.some.inj (allocationPrepared.symm.trans computed)
  have ready := allocation.request_fields
  have origin := allocation.request_origin
  have held : RootFiring allocation.request.environment allocation.request.bound allocation.request.type
      allocation.request.prepared.source allocation.request.index prepared.ordinary.trace
      allocation.request.prepared.ordinary.assignment (canonAssignment original.completed)
      original.premiseHistory target := by
    rw [origin.1, origin.2, samePrepared, ready.2.1, ready.2.2.1, ready.2.2.2.2.1, sameJob]
    exact replayed.2.1
  have bounded' : StructuralDescent.eventsDepth original.premiseHistory ≤ allocation.request.depth := by
    rw [ready.1, sameDepth]
    exact bounded
  obtain ⟨total, logged⟩ := accepted_allocation_source_coverage depth work job licensed answer
    published allocation made prepared.ordinary.trace (canonAssignment original.completed)
    original.premiseHistory target held bounded'
  let packet : Publication := ⟨job, answer, prepared,
    ⟨prepared.ordinary.trace, prepared.ordinary.assignment, canonAssignment original.completed,
      original.premiseHistory, target⟩⟩
  have packetLogged : packet ∈
      (run depth total (begin plan bound expected (canon source))).batch.log := by
    simpa only [tag, origin.2, samePrepared, sameJob, sameAnswer, packet] using logged
  refine ⟨total, packet, receipt, packetLogged, ?_, licensed, rfl, captures, rfl,
    rfl, ordinal, declaration, ordinal, declaration, sameTarget⟩
  change GeneralRuleJobs.finish? plan bound expected receipt.job receipt.matcherTrace
    receipt.captured receipt.completed receipt.premiseHistory = some receipt
  exact GeneralRuleJobs.finish_complete (receipt := receipt) replayed

theorem receipt_eventually_published {plan : GeneralExecutionAdmission.Plan}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    {original : GeneralRuleJobs.Receipt}
    (valid : original.Valid plan bound expected source)
    (binderOk : BinderLawsFor [] (GeneralPlanEnvironment.environment plan).reflection original.job.declaration.rule)
    (increasing : IncreasingSpines original.job.declaration.rule original.job.declaration.binding.spec)
    (guards : CollectionGuardFragment plan.snapshot.provider
      ⟨original.job.ordinal, original.job.declaration.rule, original.job.declaration.binding.spec,
        original.job.site.focusBound, 0, 0⟩ original.job.declaration.rule.premises)
    (depth : Nat) (bounded : StructuralDescent.eventsDepth original.premiseHistory ≤ depth) :
    ∃ (work : Nat) (packet : Publication) (receipt : GeneralRuleJobs.Receipt),
      packet ∈ (run depth work (begin plan bound expected (canon source))).batch.log ∧
      packet.finish? plan bound expected = some receipt ∧
      receipt.premiseHistory = original.premiseHistory ∧
      receipt.job.ordinal = original.job.ordinal ∧
      receipt.job.declaration = original.job.declaration ∧
      Same original.target receipt.target := by
  obtain ⟨work, packet, receipt, logged, finished, _, _, _, _, history, _, _,
    ordinal, declaration, target⟩ :=
    receipt_eventually_published_with_bindings valid binderOk increasing guards depth bounded
  exact ⟨work, packet, receipt, logged, finished, history, ordinal, declaration, target⟩

/-- Presented source steps are covered by the retained joint search when
the model equality is exactly the built-in collection equality. Contexts
remain those licensed by the plan; no root-only or set-free restriction is
required. Additional declared equations require their own comparison. -/
theorem presented_covered {plan : GeneralExecutionAdmission.Plan}
    {bound : List TypeExpr} {expected : TypeExpr} {source target : Pattern}
    (checked : checkGuardFragment plan = true)
    (noEquations : plan.equations = [])
    (noLaws : Complete.Normalized.laws plan = [])
    (noExtrusions : Complete.Normalized.extrusions plan = [])
    (depth : Nat)
    (stepped : (Complete.Presented.gslt plan bound expected).Step source target) :
    ∃ (work : Nat) (packet : Publication) (receipt : GeneralRuleJobs.Receipt),
      packet ∈ (run depth work (begin plan bound expected (canon source))).batch.log ∧
      packet.finish? plan bound expected = some receipt ∧ Same target receipt.target := by
  obtain ⟨representative, original, before, valid, after⟩ := stepped
  have sameSource := CollectionRootSearch.modelEquiv_canon expected noEquations noLaws noExtrusions before
  have sameTarget := CollectionRootSearch.modelEquiv_canon expected noEquations noLaws noExtrusions after
  have fragment := checkGuardFragment_sound checked original.job.declaration
    (List.fst_mem_of_mem_zipIdx valid.1.1) original.job.site.focusBound original.job.ordinal
  have bounded : StructuralDescent.eventsDepth original.premiseHistory ≤ depth := by
    rw [valid.2.1.collection_guards_history_depth (GeneralRuleJobs.Job.selected_rule valid.1)
      (GeneralRuleJobs.Job.selected_specification valid.1) fragment.2.1]
    exact Nat.zero_le _
  obtain ⟨work, packet, receipt, logged, finished, _, _, _, observed⟩ :=
    receipt_eventually_published valid fragment.2.2 fragment.1 fragment.2.1 depth bounded
  rw [← sameSource] at logged
  exact ⟨work, packet, receipt, logged, finished, sameTarget.symm.trans observed⟩

/-- Two-sided equality of successor classes for the selected fragment.
Multiplicity and derivation identity remain separate observations of the
retained packets; equality proofs do not create execution occurrences. -/
theorem presented_iff_published {plan : GeneralExecutionAdmission.Plan}
    {bound : List TypeExpr} {expected : TypeExpr} {source target : Pattern}
    (checked : checkGuardFragment plan = true)
    (noEquations : plan.equations = [])
    (noLaws : Complete.Normalized.laws plan = [])
    (noExtrusions : Complete.Normalized.extrusions plan = []) (depth : Nat) :
    (Complete.Presented.gslt plan bound expected).Step source target ↔
      ∃ (work : Nat) (packet : Publication) (receipt : GeneralRuleJobs.Receipt),
        packet ∈ (run depth work (begin plan bound expected (canon source))).batch.log ∧
        packet.finish? plan bound expected = some receipt ∧ Same target receipt.target := by
  constructor
  · exact presented_covered checked noEquations noLaws noExtrusions depth
  · rintro ⟨work, packet, receipt, logged, finished, observed⟩
    obtain ⟨representative, original, before, valid, after⟩ :=
      publication_source_sound depth work logged finished
    exact ⟨representative, original,
      .trans _ _ _ (Complete.Presented.canon_equiv plan bound expected source) before,
      valid, .trans _ _ _ after (same_model_equiv plan bound expected observed.symm)⟩

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMachine

#print axioms Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMachine.receipt_eventually_published_with_bindings

namespace Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMachine
#print axioms InitializedWith_ordinary
#print axioms runWith_matchers
#print axioms roundWith_initialized
#print axioms runWith_initialized
end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMachine


namespace Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceHandoff

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax CanonicalBags ScopedRuleMatching
open GeneralPremise GeneralTypedSites CollectionSelection RecursiveCollectionHandoff
open Mettapedia.GSLT.LanguageDef WellSorted GeneralTypedOccurrence

private theorem canonical_receipt_matching {plan : GeneralExecutionAdmission.Plan}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    {receipt : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event}
    (valid : receipt.ValidInWith canonicalMatchingInterpretation DynamicProvider.empty plan bound expected source) :
    canonicalMatchingInterpretation.Matches
      ⟨receipt.job.declaration.rule, receipt.job.declaration.binding.spec,
        receipt.job.site.focusBound.length, .left, [], 0, [], receipt.job.declaration.rule.left,
        receipt.job.site.focus⟩ receipt.matcherTrace receipt.captured := by
  have selected := GeneralRuleJobs.Job.selected_rule valid.1
  have specified := GeneralRuleJobs.Job.selected_specification valid.1
  cases valid.2.1 with
  | @fire localBound type localSource target index rule spec trace captured completed history declared specification
      admitted sourceTyped matching capturedTyped premises reduced targetTyped =>
    have ruleSame : rule = receipt.job.declaration.rule := Option.some.inj (declared.symm.trans selected)
    have specSame : spec = receipt.job.declaration.binding.spec := Option.some.inj (specification.symm.trans specified)
    cases ruleSame
    cases specSame
    exact matching

/-- A canonical interpreted receipt determines a real published recursive
allocation with the same seed trace and captures. Every premise history and
completed assignment is retained; no original-reference authority is inferred. -/
theorem canonical_receipt_has_prepared_replay {plan : GeneralExecutionAdmission.Plan}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    {original : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event}
    (valid : original.ValidInWith canonicalMatchingInterpretation DynamicProvider.empty plan bound expected source) :
    ∃ (job : Job) (work : Nat) (answer : RecursiveCollectionMachine.Answer) (prepared : Prepared),
      job.Valid plan bound expected (canon source) ∧
      CollectionOccurrenceMatcher.Published job work answer ∧
      prepare job.request answer = some prepared ∧ prepared.Valid job.request answer ∧
      answer.trace = original.matcherTrace ∧ answer.assignment = original.captured ∧
      Same original.target (job.variant.site.context.fill original.localTarget) ∧
      GeneralRuleJobs.Receipt.ValidInWith canonicalMatchingInterpretation DynamicProvider.empty
        plan bound expected (job.presentedSource prepared)
        ⟨job.preparedJob prepared, answer.trace, answer.assignment, original.completed,
          original.premiseHistory, original.localTarget, job.variant.site.context.fill original.localTarget⟩ ∧
      job.origin.ordinal = original.job.ordinal ∧ job.origin.declaration = original.job.declaration := by
  obtain ⟨site, context, licensed, focus, focusBound, focusType, frames,
    member, contextShape, compare⟩ := licensed_canonical_variant valid.1.2
  let job : Job := ⟨{ original.job with site }, ⟨site, recontext site context⟩⟩
  have licensedJob : job.Valid plan bound expected (canon source) := by
    refine ⟨⟨valid.1.1, licensed⟩, ?_⟩
    exact List.mem_map.mpr ⟨context, member, rfl⟩
  have requestEq : job.request = RecursiveCollectionFiringCoverage.request
      original.job.declaration.rule original.job.declaration.binding.spec
      original.job.site.focusBound original.job.site.focus := by
    simp only [Job.request, job, recontext, focus, focusBound,
      RecursiveCollectionFiringCoverage.request]
  let answer : RecursiveCollectionMachine.Answer := ⟨original.captured, original.matcherTrace⟩
  have matched : EquationalScopedReceipts.Matches literalBodyComparison
      job.request.rule job.request.spec job.request.ambient job.request.site job.request.path
      job.request.depth job.request.initial job.request.schema job.request.target answer.trace answer.assignment := by
    rw [requestEq]
    exact canonical_receipt_matching valid
  obtain ⟨work, finished⟩ := RecursiveCollectionMachine.finiteDrain job.request
    (RecursiveCollectionMachine.start job.request)
  have published : CollectionOccurrenceMatcher.Published job work answer := by
    unfold CollectionOccurrenceMatcher.Published
    rw [RecursiveCollectionMachine.completed_traces job.request work finished]
    exact RecursiveCollectionMachine.referenceAt_complete matched
  obtain ⟨prepared, computed, matching⟩ := prepare_complete job.request answer matched
  have sameFocus : Same original.job.site.focus prepared.source := by
    simpa only [requestEq, RecursiveCollectionFiringCoverage.request, Same, canon_idempotent]
      using matching.source
  have replayed := canonical_firing_same_source sameFocus valid.2.1
  have replayed' : Interpreted.RootFiring canonicalMatchingInterpretation (GeneralPlanEnvironment.environment plan)
      (job.preparedJob prepared).site.focusBound (job.preparedJob prepared).site.focusType
      (job.preparedJob prepared).site.focus (job.preparedJob prepared).ordinal
      answer.trace answer.assignment original.completed original.premiseHistory original.localTarget := by
    simpa only [Job.preparedJob, job, refocus, recontext, focusBound, focusType, answer,
      GeneralPlanEnvironment.environmentWith_empty] using replayed
  have represented : (job.preparedJob prepared).site.acceptsReplacementRepresentation
      (GeneralPlanEnvironment.environment plan).language original.localTarget = true := by
    have transported := contextShape.replacementRepresentations
      (language := (GeneralPlanEnvironment.environment plan).language)
      original.job.site.typingFrames
      (fun parameter => matchesParameterRepresentation?_same parameter (rfl : Same original.localTarget original.localTarget))
    change replacementRepresentations? _ context site.typingFrames original.localTarget = true
    rw [frames, ← transported]
    exact valid.2.2.1
  have globalSame : Same original.target (context.fill original.localTarget) := by
    rw [valid.2.2.2.1]
    exact compare _ _ rfl
  refine ⟨job, work, answer, prepared, licensedJob, published, computed, matching, rfl, rfl,
    globalSame, ?_, rfl, rfl⟩
  exact ⟨job.prepared_valid licensedJob matching, replayed', represented, rfl,
    openPatternWellSorted_of_eqvGen ((same_iff _ _).mp globalSame) valid.2.2.2.2⟩

#print axioms canonical_receipt_has_prepared_replay

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceHandoff


namespace Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMachine

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax CanonicalBags ScopedRuleMatching
open GeneralPremise CollectionOccurrenceHandoff CollectionOccurrenceMatcher CollectionOccurrenceBatch

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}

/-- An actual accepted canonical allocation reaches the same retained joint
log through its original initialized frame and bounded premise witness. -/
theorem canonical_accepted_allocation_source_coverage (depth work : Nat) (job : CollectionOccurrenceHandoff.Job)
    (licensed : job.Valid plan bound expected (canon source)) (answer : RecursiveCollectionMachine.Answer)
    (published : Published job work answer) (allocation : Allocation plan bound expected (canon source))
    (made : allocate? job licensed work answer published depth = some allocation)
    (trace : List EquationalScopedReceipts.Event) (completed : ScopedRuleMatching.Assignment)
    (history : List (GeneralPremise.Event EquationalScopedReceipts.Event)) (target : Pattern)
    (held : Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation
      allocation.request.environment allocation.request.bound allocation.request.type
      allocation.request.prepared.source allocation.request.index trace
      allocation.request.answer.assignment completed history target)
    (bounded : StructuralDescent.eventsDepth history ≤ allocation.request.depth) :
    ∃ total, tag allocation
        ⟨allocation.request.answer.trace, allocation.request.answer.assignment, completed, history, target⟩ ∈
      (runCanonical depth total (beginCanonical plan bound expected source)).batch.log := by
  obtain ⟨spent, installed⟩ := accepted_allocation_installedWith
    (canonicalSeedProfile plan bound expected source) depth work job licensed answer published allocation made
  obtain ⟨extra, emitted⟩ := canonical_retained_source_coverage depth _
    (runWith_invariant (canonicalSeedProfile plan bound expected source) depth work
      (beginWith_invariant RecursiveCollectionHandoff.canonicalMatchingExecution depth)) allocation spent installed
    trace completed history target held bounded
  exact ⟨work + extra, (canonical_run_add depth work extra _).symm ▸ emitted⟩

/-- Every finite-depth canonical interpreted receipt reaches the actual joint
log and original finisher. The producer seed and full premise history remain
exact; this does not identify that judgment with ReferenceStep authority. -/
theorem canonical_receipt_eventually_published_with_bindings
    {original : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event}
    (valid : original.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation
      DynamicProvider.empty plan bound expected source)
    (depth : Nat) (bounded : StructuralDescent.eventsDepth original.premiseHistory ≤ depth) :
    ∃ (work : Nat) (packet : Publication EquationalScopedReceipts.Event)
        (receipt : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event),
      packet ∈ (runCanonical depth work (beginCanonical plan bound expected source)).batch.log ∧
      packet.finishCanonical? plan bound expected = some receipt ∧
      packet.job.Valid plan bound expected (canon source) ∧
      receipt.job = packet.job.preparedJob packet.prepared ∧
      receipt.matcherTrace = original.matcherTrace ∧ receipt.captured = original.captured ∧
      receipt.completed = original.completed ∧ receipt.premiseHistory = original.premiseHistory ∧
      packet.answer.trace = original.matcherTrace ∧ packet.answer.assignment = original.captured ∧
      packet.job.origin.ordinal = original.job.ordinal ∧
      packet.job.origin.declaration = original.job.declaration ∧
      receipt.job.ordinal = original.job.ordinal ∧ receipt.job.declaration = original.job.declaration ∧
      Same original.target receipt.target := by
  obtain ⟨job, work, answer, prepared, licensed, published, computed, matching,
    trace, captures, sameTarget, replayed, ordinal, declaration⟩ :=
    CollectionOccurrenceHandoff.canonical_receipt_has_prepared_replay valid
  let receipt : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event :=
    ⟨job.preparedJob prepared, answer.trace, answer.assignment, original.completed,
      original.premiseHistory, original.localTarget, job.variant.site.context.fill original.localTarget⟩
  have root := GeneralRuleJobs.receipt_root_readout_interpreted_with replayed
  have sorted : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language (GeneralPlanEnvironment.environment plan).free
      job.variant.site.focusBound job.variant.site.focusType job.variant.site.focus := by
    exact openPatternWellSorted_of_eqvGen ((same_iff _ _).mp matching.source.symm) root.2.1
  obtain ⟨allocation, made, sameJob, sameAnswer⟩ := allocate_published_exists job licensed
    work depth answer published root.1 sorted
  obtain ⟨_, _, sameDepth, allocationPrepared⟩ := allocate_readout job licensed work depth
    answer published made
  have samePrepared : allocation.prepared = prepared :=
    Option.some.inj (allocationPrepared.symm.trans computed)
  have ready := allocation.request_fields
  have origin := allocation.request_origin
  have held : Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation
      allocation.request.environment allocation.request.bound allocation.request.type
      allocation.request.prepared.source allocation.request.index answer.trace
      allocation.request.answer.assignment original.completed original.premiseHistory original.localTarget := by
    rw [origin.1, origin.2, samePrepared, ready.2.1, ready.2.2.1, ready.2.2.2.2.1, sameJob,
      allocation.request_answer, sameAnswer]
    exact replayed.2.1
  have bounded' : StructuralDescent.eventsDepth original.premiseHistory ≤ allocation.request.depth := by
    rw [ready.1, sameDepth]
    exact bounded
  obtain ⟨total, logged⟩ := canonical_accepted_allocation_source_coverage depth work job licensed answer
    published allocation made answer.trace original.completed original.premiseHistory original.localTarget held bounded'
  let packet : Publication EquationalScopedReceipts.Event := ⟨job, answer, prepared,
    ⟨answer.trace, answer.assignment, original.completed, original.premiseHistory, original.localTarget⟩⟩
  have packetLogged : packet ∈
      (runCanonical depth total (beginCanonical plan bound expected source)).batch.log := by
    simpa only [tag, origin.2, samePrepared, sameJob, sameAnswer, allocation.request_answer, packet] using logged
  refine ⟨total, packet, receipt, packetLogged, ?_, licensed, rfl, trace, captures, rfl,
    rfl, trace, captures, ordinal, declaration, ordinal, declaration, sameTarget⟩
  change GeneralRuleJobs.finishWith? DynamicProvider.empty plan bound expected receipt.job receipt.matcherTrace
    receipt.captured receipt.completed receipt.premiseHistory = some receipt
  exact GeneralRuleJobs.finishWith_interpreted_complete (receipt := receipt) replayed

#print axioms accepted_allocation_installedWith
#print axioms valid_match_eventually_installedWith
#print axioms canonical_accepted_allocation_source_coverage
#print axioms canonical_receipt_eventually_published_with_bindings

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMachine
