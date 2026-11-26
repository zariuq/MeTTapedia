import Mettapedia.Languages.MeTTa.PeTTa.EquationEquality
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPlanExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionBackendSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Candidates
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentExpand
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Positions
import Mettapedia.OSLF.MeTTaIL.CollectionMatcherBackend

/-!
# Native collection matcher backend

The backend turns one checked collection allocation into an ordinary scoped
matcher request.  Its returned answers are therefore suitable for the shared
typed/premise/reduct continuation.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax CollectionSelection
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval BridgeKit WireKit
open CompleteExecution.DescentCodec
open scoped ProgramQuotation

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name


def collectionBaseSource : SpaceSemantics.Program :=
  CollectionSelectionExecution.source.program.append ScopedCollectionExecution.source.program

def collectionBaseLibrary : BridgeKit.Library := RetainedMatchingWire.interpretedLibrary

theorem collectionBase_checked : collectionBaseLibrary.check = true := RetainedMatchingWire.interpreted_checked

def library : BridgeKit.Library := RetainedMatchingWire.interpretedLibrary

theorem checked : library.check = true := RetainedMatchingWire.interpreted_checked

private def backendObservedInheritedHeads : List String :=
  ((source.program.equations.flatMap (fun row => CompleteExecution.sourceLiteralHeads row.body)).filter
    (fun head => head.startsWith "gslt:" && !(source.program.equations.map (·.head)).contains head)).eraseDups

/-- The outward calls of all twenty physical backend bodies. -/
def backendProofInheritedHeads : List String :=
  ["gslt:automata:append", "gslt:complete:matcher-answers", "gslt:descent:continue-root-answer",
    "gslt:complete:take", "gslt:descent:run", "gslt:automata:length", "gslt:complete:drop"]

theorem backendProofInheritedHeads_derived :
    backendObservedInheritedHeads = backendProofInheritedHeads := by decide +kernel

private def backendMetadataBase : SpaceSemantics.Program where
  equations :=
    [RuleExecutionProgram.scopedProgram.equations[0]'(by decide +kernel),
     RuleExecutionProgram.scopedProgram.equations[1]'(by decide +kernel),
     CompleteExecution.descentSource.program.equations[4]'(by decide +kernel),
     CompleteExecution.descentSource.program.equations[11]'(by decide +kernel),
     CompleteExecution.completeSource.program.equations[12]'(by decide +kernel),
     CompleteExecution.completeSource.program.equations[26]'(by decide +kernel),
     CompleteExecution.completeSource.program.equations[32]'(by decide +kernel)]
  declarations :=
    [RuleExecutionProgram.scopedProgram.declarations[0]'(by decide +kernel),
     RuleExecutionProgram.scopedProgram.declarations[1]'(by decide +kernel),
     CompleteExecution.descentSource.program.declarations[4]'(by decide +kernel),
     CompleteExecution.descentSource.program.declarations[11]'(by decide +kernel),
     CompleteExecution.completeSource.program.declarations[12]'(by decide +kernel),
     CompleteExecution.completeSource.program.declarations[26]'(by decide +kernel),
     CompleteExecution.completeSource.program.declarations[32]'(by decide +kernel)]

/-- A source-derived body and metadata view; operation proofs execute in the shared runtime. -/
def backendProofLibrary : Library :=
  ⟨backendMetadataBase, source.program, ["gslt:collection-backend:"]⟩

def backendProofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || (backendProofLibrary.runtime.equations.map (·.head)).contains head

theorem backendProof_source_count : source.program.equations.length = 20 := by decide +kernel

theorem backendProof_row_count : backendProofLibrary.runtime.equations.length = 27 := by decide +kernel

theorem backendProof_checked : backendProofLibrary.check = true := by decide +kernel

private local instance backendEquationEq : DecidableEq SpaceSemantics.Equation :=
  SpaceSemantics.Equation.decideEq

theorem backendProof_agreement :
    ProgramAgreementOn backendProofHeads backendProofLibrary.runtime library.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

@[local simp] private theorem backend_match_variable
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (name : String) (value : Atom) :
    SpaceSemantics.matchValue bindings (.var name) value =
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom bindings (.var name) value := by
  cases value <;> simp [SpaceSemantics.matchValue]

private abbrev patternValue (pattern : Pattern) : Atom :=
  encoded (InferenceCettaWire.encodePattern pattern)

def rawOrdinaryTarget (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) : Pattern :=
  .collection request.kind
    (receipt.allocation.values ++ receipt.allocation.residual) none

theorem rawOrdinaryTarget_eq (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt)
    (fixed : CanonicalBags.arrange request.kind receipt.allocation.residual =
      receipt.allocation.residual) :
    rawOrdinaryTarget request receipt =
      CollectionMatcherCompatibility.ordinaryTarget request receipt := by
  simp [rawOrdinaryTarget, CollectionMatcherCompatibility.ordinaryTarget, fixed]

syntax "collection_backend_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| collection_backend_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic|
      (metta_call_in backendProof_checked using backendProof_agreement
       metta_eval [$facts,*] with backendProof_checked in backendProof_agreement
        unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
          Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
          backend_match_variable, $extra,*]))

theorem backend_append_returns (state : State) : ∀ (left right : List Pattern),
    PureReturns library.runtime [] state
      (apply "gslt:automata:append"
        [encoded (encodeList InferenceCettaWire.encodePattern left),
          encoded (encodeList InferenceCettaWire.encodePattern right)])
      state (encoded (encodeList InferenceCettaWire.encodePattern (left ++ right)))
  | left, right => CompleteExecution.complete_append_returns InferenceCettaWire.encodePattern state left right

private theorem pcollection_template :
    PureData.Template library.runtime
      (a "PCollection" [v "kind", v "presented", .symbol "RNone"]) := by
  apply template_in_program backendProof_agreement ?_ (by decide +kernel)
  apply PureData.Template.constructor "PCollection" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .captured _
  · exact .captured _
  · exact .symbol _

@[metta_head "gslt:collection-backend:ordinary-target"]
theorem ordinary_target_returns (state : State)
    (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:ordinary-target"
        [encoded (InferenceCettaWire.encodeCollectionType request.kind),
          encoded (encodeList InferenceCettaWire.encodePattern receipt.allocation.values),
          encoded (encodeList InferenceCettaWire.encodePattern receipt.allocation.residual)])
      state (patternValue (rawOrdinaryTarget request receipt)) := by
  have joined := backend_append_returns state receipt.allocation.values receipt.allocation.residual
  let caller :=
    ("presented", encoded (encodeList InferenceCettaWire.encodePattern
      (receipt.allocation.values ++ receipt.allocation.residual))) ::
    Library.bind ["kind", "values", "residual"]
      [encoded (InferenceCettaWire.encodeCollectionType request.kind),
        encoded (encodeList InferenceCettaWire.encodePattern receipt.allocation.values),
        encoded (encodeList InferenceCettaWire.encodePattern receipt.allocation.residual)]
  have returned := PureData.template_return library.runtime caller state
    (a "PCollection" [v "kind", v "presented", .symbol "RNone"])
    pcollection_template
  cases kind : request.kind <;> all_goals
    have returned' : PureReturns library.runtime caller state
        (a "PCollection" [v "kind", v "presented", .symbol "RNone"]) state
        (patternValue (rawOrdinaryTarget request receipt)) := by
      simpa [caller, patternValue, rawOrdinaryTarget, kind, Library.bind, encoded,
        CettaWireAtom.encode, CettaWireAtom.encodeMany,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,
        InferenceCettaWire.encodePattern, InferenceCettaWire.encodeCollectionType,
        InferenceCettaWire.encodeRest,
        InferenceCettaWire.encodePatterns_eq_encodeList, encodeList] using returned
    metta_call_in backendProof_checked using backendProof_agreement
    apply pure_let_returns _ _ _ _ _ _ _ _ (by rfl)
    · metta_capture_any joined unfolding [InferenceCettaWire.encodePattern,
        InferenceCettaWire.encodeCollectionType, kind, encodeList]
    · simpa only [caller, kind] using returned'

def rawOrdinaryRequest (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) : GeneralScopedMatchMachine.Request :=
  { request.machine with target := rawOrdinaryTarget request receipt }

@[metta_head "gslt:collection-backend:ordinary-request"]
theorem ordinary_request_returns (state : State)
    (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:ordinary-request"
        [encoded (InferenceCettaWire.AuthoredRule.rewriteTerm request.machine.rule),
          encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm request.machine.spec),
          number request.machine.ambient,
          encoded (InferenceCettaWire.AuthoredRule.siteTerm request.machine.site),
          encoded (encodeList Term.natural request.machine.path),
          number request.machine.depth,
          encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm
            request.machine.initial),
          patternValue request.machine.schema,
          patternValue (rawOrdinaryTarget request receipt)])
      state (encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm
        (rawOrdinaryRequest request receipt))) := by
  cases kind : request.kind <;>
    collection_backend_eval unfolding [patternValue,
      ScopedCollectionMachine.Request.machine, rawOrdinaryRequest, rawOrdinaryTarget,
      RuleInstantiationExecution.GeneralExecution.matcherRequestTerm,
      RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
      InferenceCettaWire.AuthoredRule.rewriteTerm,
      InferenceCettaWire.AuthoredRule.bindingSpecTerm,
      InferenceCettaWire.AuthoredRule.siteTerm,
      MatchAutomataBindingExecution.patternsTerm, InferenceCettaWire.encodePattern,
      InferenceCettaWire.encodePatterns_eq_encodeList, InferenceCettaWire.encodeRest,
      InferenceCettaWire.encodeCollectionType, kind, encodeList, patternValue]

/-- Keep every ordinary matcher answer with the allocation's assignment.  The
trace remains untouched, so multiple origins for the same assignment remain
distinct answer occurrences. -/
def filterAnswers (assignment : ScopedRuleMatching.Assignment) :
    List GeneralScopedMatchMachine.Answer → List GeneralScopedMatchMachine.Answer
  | answers => answers.filter fun answer => answer.assignment == assignment

@[metta_head "gslt:collection-backend:filter-assignment"]
theorem filter_assignment_returns (state : State)
    (assignment : ScopedRuleMatching.Assignment) :
    ∀ answers : List GeneralScopedMatchMachine.Answer,
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:filter-assignment"
        [encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment),
          encoded (encodeList RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm answers)])
      state (encoded (encodeList RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm
        (filterAnswers assignment answers)))
  | [] => by
      collection_backend_eval unfolding [filterAnswers]
  | answer :: rest => by
      have later := filter_assignment_returns state assignment rest
      by_cases same : answer.assignment = assignment
      · metta_call_in backendProof_checked using backendProof_agreement
        all_goals simp [filterAnswers, same,
          RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm,
          RuleInstantiationExecution.GeneralExecution.traceTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, encodeList, Library.bind]
        metta_eval [later] with backendProof_checked in backendProof_agreement unfolding [filterAnswers, same,
          RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm,
          RuleInstantiationExecution.GeneralExecution.traceTerm,
          RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm_injective.eq_iff,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, encodeList]
      · have wire_ne :
            RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm answer.assignment ≠
              RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment :=
          fun equal => same
            (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm_injective equal)
        metta_call_in backendProof_checked using backendProof_agreement
        all_goals simp [filterAnswers, same,
          RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm,
          RuleInstantiationExecution.GeneralExecution.traceTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, encodeList, Library.bind]
        metta_eval [later] with backendProof_checked in backendProof_agreement unfolding [filterAnswers, same, wire_ne,
          RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm,
          RuleInstantiationExecution.GeneralExecution.traceTerm,
          RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm_injective.eq_iff,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, encodeList]

/-- The complete ordinary matcher answers selected by one collection
allocation.  This is the executable counterpart of the proof-relevant
`adaptations` list. -/
def backendAnswers (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) :
    List GeneralScopedMatchMachine.Answer :=
  filterAnswers receipt.matching.assignment
    (CompleteExecution.finishedAnswers (rawOrdinaryRequest request receipt))

theorem rawOrdinaryTarget_eq_of_valid
    {request : ScopedCollectionMachine.Request}
    {receipt : ScopedCollectionMachine.Receipt}
    (fixed : CanonicalBags.arrange request.kind request.targets = request.targets)
    (valid : ScopedCollectionMachine.Valid request receipt) :
    rawOrdinaryTarget request receipt =
      CollectionMatcherCompatibility.ordinaryTarget request receipt := by
  apply rawOrdinaryTarget_eq
  apply ScopedCollectionMachine.allocation_residual_fixed request fixed
  have recovered := CollectionSelection.replay_complete valid.2.1
  simpa only [ScopedCollectionMachine.Request.allocations, valid.1,
    CollectionSelection.Allocation.erase] using recovered

/-- On an admitted canonical carrier, the emitted complete matcher returns
exactly the proof-erased semantic adapter frontier, in the same order and with
the same traces. -/
theorem backendAnswers_eq_ordinary
    {request : ScopedCollectionMachine.Request}
    {receipt : ScopedCollectionMachine.Receipt}
    (fixed : CanonicalBags.arrange request.kind request.targets = request.targets)
    (valid : ScopedCollectionMachine.Valid request receipt) :
    backendAnswers request receipt =
      CollectionMatcherCompatibility.ordinaryAnswerValues request receipt := by
  have targetEq := rawOrdinaryTarget_eq_of_valid fixed valid
  have requestEq : rawOrdinaryRequest request receipt =
      CollectionMatcherCompatibility.ordinaryRequest request receipt := by
    simp only [rawOrdinaryRequest, CollectionMatcherCompatibility.ordinaryRequest,
      ScopedCollectionMachine.Request.machine, targetEq]
  rw [CollectionMatcherCompatibility.ordinaryAnswerValues_eq]
  simp only [backendAnswers, filterAnswers, CompleteExecution.finishedAnswers, requestEq]

theorem backendAnswers_eq_rawRootAnswerValues
    {query : ScopedCollectionMachine.Request} {receipt : ScopedCollectionMachine.Receipt}
    (ready : CollectionMatcherBackend.RootReady query)
    (fixed : CanonicalBags.arrange query.kind query.targets = query.targets)
    (valid : ScopedCollectionMachine.Valid query receipt) :
    backendAnswers query receipt =
      (CollectionMatcherBackend.rawRootAnswers query receipt ready).map Subtype.val := by
  rw [backendAnswers_eq_ordinary fixed valid,
    CollectionMatcherBackend.rawRootAnswerValues_eq_ordinary]

theorem backendAnswers_eq_rootAnswerValues
    {firing : CollectionPlanMachine.Firing}
    (ready : CollectionMatcherBackend.RootReady firing.request)
    (fixed : CanonicalBags.arrange firing.request.kind firing.request.targets =
      firing.request.targets)
    (valid : firing.Valid) :
    backendAnswers firing.request firing.receipt.source =
      (CollectionMatcherBackend.rootAnswers firing ready).map Subtype.val :=
  backendAnswers_eq_rawRootAnswerValues ready fixed valid.1

@[metta_head "gslt:collection-backend:answers"]
theorem answers_returns (state : State)
    (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:answers"
        [encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm
            (rawOrdinaryRequest request receipt)),
          encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm
            receipt.matching.assignment)])
      state (encoded (encodeList RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm
        (backendAnswers request receipt))) := by
  have answered := CompleteExecution.matcher_answers_returns state (rawOrdinaryRequest request receipt)
  have filtered := filter_assignment_returns state receipt.matching.assignment
    (CompleteExecution.finishedAnswers (rawOrdinaryRequest request receipt))
  metta_call_in backendProof_checked using backendProof_agreement
  metta_eval [answered, filtered] with backendProof_checked in backendProof_agreement unfolding [backendAnswers]

private def certifiedValues {request : GeneralScopedMatchMachine.Request}
    (answers : List {answer : GeneralScopedMatchMachine.Answer // answer.Valid request}) :
    List GeneralScopedMatchMachine.Answer :=
  answers.map Subtype.val

/-- A finite frontier from any certified matcher backend enters the generic
scheduled post-match continuation. -/
@[metta_head "gslt:collection-backend:continue-answers"]
theorem continue_answers_returns (state : State)
    (environment : GeneralPremise.Environment) (footprint : List String)
    {outer : StructuralDescent.Scheduled.Goal}
    (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (index : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index = some spec)
    (admitted : RuleBinding.admittedFor rule spec = true)
    (sorted : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      environment.language environment.free bound type source)
    (tail : StructuralDescent.Scheduled.Continuation environment
      (.root (depth + 1) bound type source index) outer)
    (next : List (StructuralDescent.Scheduled.Task environment outer)) :
    ∀ answers : List {answer : GeneralScopedMatchMachine.Answer //
        answer.Valid ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩},
      (∀ answer ∈ answers,
        ScopedRuleMatching.assignmentFreeWithin footprint answer.val.assignment) →
      PureReturns library.runtime [] state
        (apply "gslt:collection-backend:continue-answers"
          [CompleteExecution.environmentValue environment (environment.free.entriesOn footprint),
            number depth,
            encoded (PremiseOperationsExecution.GeneralExecution.Base.typesTerm bound),
            encoded (InferenceCettaWire.AuthoredRule.typeTerm type),
            encoded (InferenceCettaWire.encodePattern source), number index,
            encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule),
            encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec),
            encoded (encodeList RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm
              (certifiedValues answers)),
            encoded (continuationTerm tail), encoded (encodeList taskTerm next)])
        state (encoded (encodeOption expansionTerm (some
          (StructuralDescent.Scheduled.continueRootAnswers environment outer depth bound
            type source index rule spec declared specified admitted sorted answers tail next))))
  | [], _ => by
      collection_backend_eval unfolding [certifiedValues,
        StructuralDescent.Scheduled.continueRootAnswers]
  | answer :: rest, covered => by
      have later := continue_answers_returns state environment footprint depth bound type source
        index rule spec declared specified admitted sorted tail next rest
        (fun item member => covered item (List.mem_cons_of_mem answer member))
      have continued := CompleteExecution.descent_continue_root_answer_returns state
        environment footprint depth bound type source index rule spec declared specified admitted
        sorted answer.val answer.property (covered answer List.mem_cons_self) tail
        (StructuralDescent.Scheduled.continueRootAnswers environment outer depth bound type source
          index rule spec declared specified admitted sorted rest tail next).tasks
      have laterAnswers :
          (StructuralDescent.Scheduled.continueRootAnswers environment outer depth bound
            type source index rule spec declared specified admitted sorted rest tail next).answers = [] :=
        StructuralDescent.Scheduled.continueRootAnswers_answers ..
      have laterUnresolved :
          (StructuralDescent.Scheduled.continueRootAnswers environment outer depth bound
            type source index rule spec declared specified admitted sorted rest tail next).unresolved = [] :=
        StructuralDescent.Scheduled.continueRootAnswers_unresolved ..
      collection_backend_eval [later, continued] unfolding [certifiedValues,
        StructuralDescent.Scheduled.continueRootAnswers,
        laterAnswers, laterUnresolved, expansionTerm,
        PremiseSchedulerExecution.schedulerExpansionTerm, encodeOption,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, encodeList,
        RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm,
        RuleInstantiationExecution.GeneralExecution.traceTerm]

def expansionState {environment : GeneralPremise.Environment}
    {goal : StructuralDescent.Scheduled.Goal}
    (expansion : GeneralPremise.Scheduler.Expansion
      (StructuralDescent.Scheduled.Task environment goal)
      (StructuralDescent.Scheduled.Result environment goal)
      StructuralDescent.Scheduled.Obligation) :
    StructuralDescent.Scheduled.State environment goal :=
  { agenda := expansion.tasks, answers := expansion.answers,
    unresolved := expansion.unresolved, work := 0 }

@[metta_head "gslt:collection-backend:expansion-state"]
theorem expansion_state_returns (state : State)
    {environment : GeneralPremise.Environment}
    {goal : StructuralDescent.Scheduled.Goal}
    (expansion : GeneralPremise.Scheduler.Expansion
      (StructuralDescent.Scheduled.Task environment goal)
      (StructuralDescent.Scheduled.Result environment goal)
      StructuralDescent.Scheduled.Obligation) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:expansion-state"
        [encoded (encodeOption expansionTerm (some expansion))])
      state (encoded (stateTerm (expansionState expansion))) := by
  collection_backend_eval unfolding [expansionState, expansionTerm, stateTerm,
    PremiseSchedulerExecution.schedulerExpansionTerm,
    PremiseSchedulerExecution.schedulerStateTerm, encodeOption]

/-- A raw match starts the existing typed/premise continuation through one
ordinary validating witness. No provisional right-hand side is required. -/
@[metta_head "gslt:collection-backend:begin-match"]
theorem begin_match_returns (state : State)
    (environment : GeneralPremise.Environment) (footprint : List String)
    (depth : Nat) (type : TypeExpr) (ordinal : Nat)
    (query : ScopedCollectionMachine.Request) (receipt : ScopedCollectionMachine.Receipt)
    (ready : CollectionMatcherBackend.RootReady query)
    (fixed : CanonicalBags.arrange query.kind query.targets =
      query.targets)
    (valid : ScopedCollectionMachine.Valid query receipt)
    (declared : environment.language.rewrites[ordinal]? = some query.rule)
    (specified : GeneralPremise.specification? environment ordinal =
      some query.spec)
    (admitted : RuleBinding.admittedFor query.rule query.spec = true)
    (sorted : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      environment.language environment.free [] type
      (CollectionMatcherCompatibility.ordinaryTarget query receipt))
    (covered : ∀ answer ∈ CollectionMatcherBackend.rawRootAnswers query receipt ready,
      ScopedRuleMatching.assignmentFreeWithin footprint answer.val.assignment) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:begin-match"
        [CompleteExecution.environmentValue environment (environment.free.entriesOn footprint),
          number depth, encoded (InferenceCettaWire.AuthoredRule.typeTerm type),
          number ordinal, encoded (ScopedCollectionExecution.requestTerm query),
          encoded (ScopedCollectionExecution.receiptTerm receipt)])
      state (encoded (stateTerm (CollectionMatcherBackend.startRequest environment depth type
        ordinal query receipt ready declared specified admitted sorted))) := by
  let presented := CollectionMatcherCompatibility.ordinaryTarget query receipt
  let goal : StructuralDescent.Scheduled.Goal := .root (depth + 1) [] type presented ordinal
  have targetEq := rawOrdinaryTarget_eq_of_valid fixed valid
  have ordinary := ordinary_target_returns state query receipt
  rw [targetEq] at ordinary
  have requested := ordinary_request_returns state query receipt
  have answers := answers_returns state query receipt
  have answersEq := backendAnswers_eq_rawRootAnswerValues ready fixed valid
  rw [answersEq] at answers
  have takenAtComplete := CompleteExecution.take_list_returns
    RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm state 1
    ((CollectionMatcherBackend.rawRootAnswers query receipt ready).map Subtype.val)
  rw [← List.map_take] at takenAtComplete
  have taken := takenAtComplete
  have continued := continue_answers_returns state environment footprint depth [] type presented
    ordinal query.rule query.spec declared specified admitted sorted
    (.done goal) [] (((CollectionMatcherBackend.rawRootAnswers query receipt ready).take 1))
    (fun answer present => covered answer (List.mem_of_mem_take present))
  have expanded := expansion_state_returns state
    (StructuralDescent.Scheduled.continueRootAnswers environment goal depth [] type presented
      ordinal query.rule query.spec declared specified admitted sorted
      (((CollectionMatcherBackend.rawRootAnswers query receipt ready).take 1)) (.done goal) [])
  have initialization : expansionState
      (StructuralDescent.Scheduled.continueRootAnswers environment goal depth [] type presented
        ordinal query.rule query.spec declared specified admitted sorted
        ((CollectionMatcherBackend.rawRootAnswers query receipt ready).take 1) (.done goal) []) =
      CollectionMatcherBackend.startRequest environment depth type ordinal query receipt ready
        declared specified admitted sorted := rfl
  rw [initialization] at expanded
  collection_backend_eval [ordinary, requested, answers, taken, continued, expanded]
    unfolding [CollectionPlanExecution.planFiringTerm, ScopedCollectionExecution.requestTerm,
      ScopedCollectionExecution.firingTerm, ScopedCollectionExecution.receiptTerm,
      CollectionSelectionExecution.allocationTerm, CollectionMatcherBackend.startRequest,
      CollectionMatcherBackend.rawRootAnswers, expansionState, presented, goal,
      ready.schema, ready.ambient, ready.site, ready.path, ready.depth, ready.index,
      ready.initial, rawOrdinaryRequest, ScopedCollectionMachine.Request.machine,
      targetEq, certifiedValues, goalTerm, continuationTerm,
      RuleInstantiationExecution.GeneralExecution.matcherRequestTerm,
      RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm,
      RuleInstantiationExecution.GeneralExecution.traceTerm,
      RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
      InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns_eq_encodeList,
      InferenceCettaWire.encodeCollectionType, InferenceCettaWire.encodeRest,
      InferenceCettaWire.AuthoredRule.siteTerm, encodeList]
  all_goals
    refine PureData.raw_capture_returns library.runtime [] _ state state
      "gslt:collection-backend:expansion-state" _ _ _ ?_ ?_ ?_ ?_ expanded
    · rw [← backendProof_agreement.dispatch _ (by decide +kernel)]
      decide +kernel
    · intro index bounded
      have zero : index = 0 := by simpa using bounded
      subst index
      rw [← backendProof_agreement.demand _ 0 (by decide +kernel)]
      decide +kernel
    · decide
    · simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,
        List.map_cons, List.map_nil, CettaWireAtom.applySubst_encode, encoded]; rfl



/-- A retained root firing starts the existing scheduled continuation through
one ordinary validating witness. The initial scheduled state is reconstructed
from the firing, not supplied as input. -/
@[metta_head "gslt:collection-backend:begin"]
theorem begin_returns (state : State)
    (environment : GeneralPremise.Environment) (footprint : List String)
    (depth : Nat) (type : TypeExpr) (firing : CollectionPlanMachine.Firing)
    (ready : CollectionMatcherBackend.RootReady firing.request)
    (fixed : CanonicalBags.arrange firing.request.kind firing.request.targets =
      firing.request.targets)
    (valid : firing.Valid)
    (declared : environment.language.rewrites[firing.ordinal]? = some firing.request.rule)
    (specified : GeneralPremise.specification? environment firing.ordinal =
      some firing.request.spec)
    (admitted : RuleBinding.admittedFor firing.request.rule firing.request.spec = true)
    (sorted : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      environment.language environment.free [] type
      (CollectionMatcherCompatibility.ordinaryTarget firing.request firing.receipt.source))
    (covered : ∀ answer ∈ CollectionMatcherBackend.rootAnswers firing ready,
      ScopedRuleMatching.assignmentFreeWithin footprint answer.val.assignment) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:begin"
        [CompleteExecution.environmentValue environment (environment.free.entriesOn footprint),
          number depth, encoded (InferenceCettaWire.AuthoredRule.typeTerm type),
          encoded (CollectionPlanExecution.planFiringTerm firing)])
      state (encoded (stateTerm (CollectionMatcherBackend.startFiring environment depth type
        firing ready declared specified admitted sorted))) := by
  have started := begin_match_returns state environment footprint depth type firing.ordinal
    firing.request firing.receipt.source ready fixed valid.1 declared specified admitted sorted covered
  collection_backend_eval [started]
    unfolding [CollectionPlanExecution.planFiringTerm, ScopedCollectionExecution.firingTerm,
      CollectionMatcherBackend.startFiring]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution.backendProofInheritedHeads_derived
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution.backendProof_source_count
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution.backendProof_row_count
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution.backendProof_checked
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution.backendProof_agreement
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution.backend_append_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution.ordinary_target_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution.ordinary_request_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution.filter_assignment_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution.answers_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution.continue_answers_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution.expansion_state_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution.begin_match_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution.begin_returns
