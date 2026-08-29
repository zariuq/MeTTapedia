import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardWire
import Mettapedia.GSLT.Core.GSLT

/-!
# Ordered operational control for mainline PeTTa call guards

This module gives the cold compiler and hot executor explicit transition
systems.  The compiler traverses resolved declarations in authored order.  The
executor traverses compiled plans and their argument modes in order, recording
evaluation, exact-type, metatype, body-evaluation, and branch-installation
events.  Primitive judgments remain narrow; no primitive returns a precomputed
plan or family verdict.

The executable observations are defined independently from the G2 result
functions.  Exact correspondence theorems then recover `compileGuards` and
`executeCompilation`, including fallback distinctions and ordered declaration
occurrences.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardWire

set_option autoImplicit false

/-! ## Cold ordered compilation control -/

inductive CompileControl where
  | running
      (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
      (remaining : List ArrowDeclaration) (accepted : List GuardPlan)
  | halted (result : CompilationResult)
deriving DecidableEq, Repr

def compileStart (owned : OwnedSnapshot) (head : String) (arity : Nat) :
    CompileControl :=
  .running owned.owner owned.snapshot.revision head arity
    owned.snapshot.declarations []

/- One declaration-inspection transition. -/
def compileStep? : CompileControl → Option CompileControl
  | .halted _ => none
  | .running owner revision head arity [] accepted =>
      some (.halted (.compiled
        ⟨owner, revision, head, arity, accepted⟩))
  | .running owner revision head arity
      (declaration :: remaining) accepted =>
      if Relevant declaration head arity then
        match compileGuard declaration with
        | none => some (.halted .outsideFragment)
        | some plan =>
            some (.running owner revision head arity remaining
              (accepted ++ [plan]))
      else
        some (.running owner revision head arity remaining accepted)

def runCompile : Nat → CompileControl → CompileControl
  | 0, control => control
  | fuel + 1, control =>
      match compileStep? control with
      | none => control
      | some next => runCompile fuel next

/- Direct denotation of the transition machine from an arbitrary cursor. -/
def compileOrdered (owner : SpaceOwner) (revision : Nat)
    (head : String) (arity : Nat) (accepted : List GuardPlan) :
    List ArrowDeclaration → CompilationResult
  | [] => .compiled ⟨owner, revision, head, arity, accepted⟩
  | declaration :: remaining =>
      if Relevant declaration head arity then
        match compileGuard declaration with
        | none => .outsideFragment
        | some plan =>
            compileOrdered owner revision head arity
              (accepted ++ [plan]) remaining
      else
        compileOrdered owner revision head arity accepted remaining

theorem runCompile_running_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan) :
    runCompile (remaining.length + 1)
        (.running owner revision head arity remaining accepted) =
      .halted (compileOrdered owner revision head arity accepted remaining) := by
  induction remaining generalizing accepted with
  | nil => simp [runCompile, compileStep?, compileOrdered]
  | cons declaration remaining inductionHypothesis =>
      by_cases relevant : Relevant declaration head arity
      · cases compiled : compileGuard declaration with
        | none =>
            simp [runCompile, compileStep?, compileOrdered, relevant, compiled]
        | some plan =>
            simp [runCompile, compileStep?, compileOrdered, relevant, compiled,
              inductionHypothesis]
      · simp [runCompile, compileStep?, compileOrdered, relevant,
          inductionHypothesis]

theorem compileOrdered_eq_reference
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) (declarations : List ArrowDeclaration) :
    compileOrdered owner revision head arity accepted declarations =
      match compileRelevantGuards owner revision head arity declarations with
      | .outsideFragment => .outsideFragment
      | .compiled family =>
          .compiled { family with plans := accepted ++ family.plans } := by
  induction declarations generalizing accepted with
  | nil => simp [compileOrdered, compileRelevantGuards]
  | cons declaration declarations inductionHypothesis =>
      by_cases relevant : Relevant declaration head arity
      · cases compiled : compileGuard declaration with
        | none =>
            simp [compileOrdered, compileRelevantGuards, relevant, compiled]
        | some plan =>
            simp only [compileOrdered, relevant, if_pos, compiled,
              compileRelevantGuards]
            rw [inductionHypothesis]
            cases tailResult :
                compileRelevantGuards owner revision head arity declarations with
            | outsideFragment => simp
            | compiled family =>
                cases family
                simp [List.append_assoc]
      · simp [compileOrdered, compileRelevantGuards, relevant,
          inductionHypothesis]

theorem compileControl_normalizes_exactly
    (owned : OwnedSnapshot) (head : String) (arity : Nat) :
    runCompile (owned.snapshot.declarations.length + 1)
        (compileStart owned head arity) =
      .halted (compileGuards owned head arity) := by
  unfold compileStart
  rw [runCompile_running_exact]
  unfold compileGuards
  rw [compileOrdered_eq_reference]
  cases result : compileRelevantGuards owned.owner owned.snapshot.revision
      head arity owned.snapshot.declarations with
  | outsideFragment => rfl
  | compiled family =>
      cases family
      simp

theorem compile_running_has_next
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan) :
    ∃ next, compileStep?
      (.running owner revision head arity remaining accepted) = some next := by
  cases remaining with
  | nil => simp [compileStep?]
  | cons declaration remaining =>
      by_cases relevant : Relevant declaration head arity
      · cases compiled : compileGuard declaration <;>
          simp [compileStep?, relevant, compiled]
      · simp [compileStep?, relevant]

@[simp] theorem compile_halted_has_no_step (result : CompilationResult) :
    compileStep? (.halted result) = none := rfl

/-! ## Hot ordered execution control and receipts -/

inductive ControlEvent where
  | beginPlan (occurrence : Nat)
  | useRawArgument (index : Nat)
  | evaluateArgument (index : Nat)
  | queryExactType (index : Nat) (expected : Term) (succeeded : Bool)
  | queryMetatype (index : Nat) (expected : Term) (succeeded : Bool)
  | argumentShapeMismatch (index : Nat)
  | evaluateCall (occurrence : Nat)
  | queryResultType (expected : Term) (succeeded : Bool)
  | queryResultMetatype (expected : Term) (succeeded : Bool)
  | installOccurrence (occurrence : Nat)
  | rejectOccurrence (occurrence : Nat)
  | fallback (reason : GuardFallbackReason)
deriving DecidableEq, Repr

structure DecisionTrace where
  accepted : Bool
  events : List ControlEvent
deriving DecidableEq, Repr

def getTypeDecision (snapshot : Snapshot) (value expected : Term) : Bool :=
  decide (GetType snapshot value expected)

def getMetatypeDecision (snapshot : Snapshot) (value expected : Term) : Bool :=
  decide (GetMetatype snapshot value expected)

def runArgMode (snapshot : Snapshot) (index : Nat)
    (mode : ArgMode) (source value : Term) : DecisionTrace :=
  match mode with
  | .rawAtom =>
      ⟨decide (value = source), [.useRawArgument index]⟩
  | .evalUnchecked =>
      ⟨true, [.evaluateArgument index]⟩
  | .evalSoftcutType expected =>
      let exact := getTypeDecision snapshot value expected
      if exact then
        ⟨true, [.evaluateArgument index,
          .queryExactType index expected true]⟩
      else
        let metatypeSucceeded := getMetatypeDecision snapshot value expected
        DecisionTrace.mk metatypeSucceeded [.evaluateArgument index,
          .queryExactType index expected false,
          .queryMetatype index expected metatypeSucceeded]

def runArguments (snapshot : Snapshot) :
    Nat → List ArgMode → List Term → List Term → DecisionTrace
  | _, [], [], [] => ⟨true, []⟩
  | index, mode :: modes, source :: sources, value :: values =>
      let current := runArgMode snapshot index mode source value
      if current.accepted then
        let remaining := runArguments snapshot (index + 1) modes sources values
        DecisionTrace.mk remaining.accepted
          (current.events ++ remaining.events)
      else
        current
  | index, _, _, _ => ⟨false, [.argumentShapeMismatch index]⟩

def runResultMode (snapshot : Snapshot) (mode : ResultMode)
    (value : Term) : DecisionTrace :=
  match mode with
  | .resultUnchecked => ⟨true, []⟩
  | .resultSoftcutType expected =>
      let exact := getTypeDecision snapshot value expected
      if exact then
        ⟨true, [.queryResultType expected true]⟩
      else
        let metatypeSucceeded := getMetatypeDecision snapshot value expected
        DecisionTrace.mk metatypeSucceeded [.queryResultType expected false,
          .queryResultMetatype expected metatypeSucceeded]

def runPlan (snapshot : Snapshot) (call : Call)
    (plan : GuardPlan) : DecisionTrace :=
  let eventsPrefix := [.beginPlan plan.declarationOccurrence]
  if plan.declaration.function = call.function then
    let arguments := runArguments snapshot 0 plan.argumentModes
      call.sourceArguments call.evaluatedArguments
    if arguments.accepted then
      let result := runResultMode snapshot plan.resultMode call.result
      let body := [.evaluateCall plan.declarationOccurrence]
      if result.accepted then
        ⟨true, eventsPrefix ++ arguments.events ++ body ++ result.events ++
          [.installOccurrence plan.declarationOccurrence]⟩
      else
        ⟨false, eventsPrefix ++ arguments.events ++ body ++ result.events ++
          [.rejectOccurrence plan.declarationOccurrence]⟩
    else
      ⟨false, eventsPrefix ++ arguments.events ++
        [.rejectOccurrence plan.declarationOccurrence]⟩
  else
    ⟨false, eventsPrefix ++ [.rejectOccurrence plan.declarationOccurrence]⟩

structure PlanListTrace where
  declarations : List ArrowDeclaration
  events : List ControlEvent
deriving DecidableEq, Repr

def runPlanList (snapshot : Snapshot) (call : Call) :
    List GuardPlan → PlanListTrace
  | [] => ⟨[], []⟩
  | plan :: plans =>
      let current := runPlan snapshot call plan
      let remaining := runPlanList snapshot call plans
      if current.accepted then
        ⟨plan.declaration :: remaining.declarations,
          current.events ++ remaining.events⟩
      else
        ⟨remaining.declarations, current.events ++ remaining.events⟩

structure ControlObservation where
  outcome : GuardExecution
  events : List ControlEvent
deriving DecidableEq, Repr

def executeFamilyControl (current : OwnedSnapshot) (call : Call)
    (family : CompiledGuardFamily) : ControlObservation :=
  if family.owner = current.owner then
    if family.revision = current.snapshot.revision then
      if family.head = call.function then
        if family.arity = call.sourceArguments.length then
          let trace := runPlanList current.snapshot call family.plans
          { outcome := .executed trace.declarations
            events := trace.events }
        else
          ⟨.fallback .wrongArity, [.fallback .wrongArity]⟩
      else
        ⟨.fallback .wrongHead, [.fallback .wrongHead]⟩
    else
      ⟨.fallback .staleRevision, [.fallback .staleRevision]⟩
  else
    ⟨.fallback .foreignOwner, [.fallback .foreignOwner]⟩

def executeControl (current : OwnedSnapshot) (call : Call) :
    CompilationResult → ControlObservation
  | .outsideFragment =>
      ⟨.fallback .outsideFragment, [.fallback .outsideFragment]⟩
  | .compiled family => executeFamilyControl current call family

theorem runArgMode_accepted_iff
    (snapshot : Snapshot) (index : Nat) (mode : ArgMode)
    (source value : Term) :
    (runArgMode snapshot index mode source value).accepted = true ↔
      mode.Accepts snapshot source value := by
  cases mode with
  | rawAtom => simp [runArgMode, ArgMode.Accepts]
  | evalUnchecked => simp [runArgMode, ArgMode.Accepts]
  | evalSoftcutType expected =>
      by_cases exact : GetType snapshot value expected
      · simp [runArgMode, getTypeDecision, exact, ArgMode.Accepts]
      · by_cases metatype : GetMetatype snapshot value expected
        · simp [runArgMode, getTypeDecision, getMetatypeDecision,
            exact, metatype, ArgMode.Accepts]
        · simp [runArgMode, getTypeDecision, getMetatypeDecision,
            exact, metatype, ArgMode.Accepts]

theorem runArguments_accepted_iff
    (snapshot : Snapshot) (index : Nat) (modes : List ArgMode)
    (sources values : List Term) :
    (runArguments snapshot index modes sources values).accepted = true ↔
      ArgumentsAccept snapshot modes sources values := by
  induction modes generalizing index sources values with
  | nil =>
      cases sources <;> cases values <;>
        simp [runArguments, ArgumentsAccept]
  | cons mode modes inductionHypothesis =>
      cases sources with
      | nil => cases values <;> simp [runArguments, ArgumentsAccept]
      | cons source sources =>
          cases values with
          | nil => simp [runArguments, ArgumentsAccept]
          | cons value values =>
              by_cases accepted :
                  (runArgMode snapshot index mode source value).accepted = true
              · have modeAccept :=
                  (runArgMode_accepted_iff snapshot index mode source value).1
                    accepted
                simp [runArguments, accepted, modeAccept,
                  inductionHypothesis, ArgumentsAccept]
              · have modeReject :
                  ¬ mode.Accepts snapshot source value := by
                    intro accepts
                    exact accepted
                      ((runArgMode_accepted_iff snapshot index mode source value).2
                        accepts)
                cases current : runArgMode snapshot index mode source value
                simp_all [runArguments, ArgumentsAccept]

theorem runResultMode_accepted_iff
    (snapshot : Snapshot) (mode : ResultMode) (value : Term) :
    (runResultMode snapshot mode value).accepted = true ↔
      mode.Accepts snapshot value := by
  cases mode with
  | resultUnchecked => simp [runResultMode, ResultMode.Accepts]
  | resultSoftcutType expected =>
      by_cases exact : GetType snapshot value expected
      · simp [runResultMode, getTypeDecision, exact, ResultMode.Accepts]
      · by_cases metatype : GetMetatype snapshot value expected
        · simp [runResultMode, getTypeDecision, getMetatypeDecision,
            exact, metatype, ResultMode.Accepts]
        · simp [runResultMode, getTypeDecision, getMetatypeDecision,
            exact, metatype, ResultMode.Accepts]

theorem runPlan_accepted_iff
    (snapshot : Snapshot) (call : Call) (plan : GuardPlan) :
    (runPlan snapshot call plan).accepted = true ↔
      plan.Accepts snapshot call := by
  by_cases head : plan.declaration.function = call.function
  · by_cases arguments :
      (runArguments snapshot 0 plan.argumentModes call.sourceArguments
        call.evaluatedArguments).accepted = true
    · by_cases result :
        (runResultMode snapshot plan.resultMode call.result).accepted = true
      · simp [runPlan, head, arguments, result, GuardPlan.Accepts,
          (runArguments_accepted_iff snapshot 0 plan.argumentModes
            call.sourceArguments call.evaluatedArguments).1 arguments,
          (runResultMode_accepted_iff snapshot plan.resultMode call.result).1
            result]
      · have resultReject :
          ¬ plan.resultMode.Accepts snapshot call.result := by
            intro accepts
            exact result
              ((runResultMode_accepted_iff snapshot plan.resultMode call.result).2
                accepts)
        cases trace : runResultMode snapshot plan.resultMode call.result
        simp_all [runPlan, GuardPlan.Accepts]
    · have argumentsReject :
        ¬ ArgumentsAccept snapshot plan.argumentModes call.sourceArguments
          call.evaluatedArguments := by
          intro accepts
          exact arguments
            ((runArguments_accepted_iff snapshot 0 plan.argumentModes
              call.sourceArguments call.evaluatedArguments).2 accepts)
      cases trace : runArguments snapshot 0 plan.argumentModes
        call.sourceArguments call.evaluatedArguments
      simp_all [runPlan, GuardPlan.Accepts]
  · simp [runPlan, head, GuardPlan.Accepts]

theorem runPlanList_declarations_exact
    (snapshot : Snapshot) (call : Call) (plans : List GuardPlan) :
    (runPlanList snapshot call plans).declarations =
      executePlanList snapshot call plans := by
  induction plans with
  | nil => rfl
  | cons plan plans inductionHypothesis =>
      by_cases accepted : (runPlan snapshot call plan).accepted = true
      · have planAccept := (runPlan_accepted_iff snapshot call plan).1 accepted
        simp [runPlanList, executePlanList, accepted, planAccept,
          inductionHypothesis]
      · have planReject : ¬ plan.Accepts snapshot call := by
          intro accepts
          exact accepted ((runPlan_accepted_iff snapshot call plan).2 accepts)
        cases trace : runPlan snapshot call plan
        simp_all [runPlanList, executePlanList]

theorem executeFamilyControl_outcome_exact
    (current : OwnedSnapshot) (call : Call)
    (family : CompiledGuardFamily) :
    (executeFamilyControl current call family).outcome =
      executeGuardFamily current call family := by
  by_cases ownerCurrent : family.owner = current.owner
  · by_cases revisionCurrent : family.revision = current.snapshot.revision
    · by_cases headMatches : family.head = call.function
      · by_cases arityMatches : family.arity = call.sourceArguments.length
        · simp [executeFamilyControl, executeGuardFamily, ownerCurrent,
            revisionCurrent, headMatches, arityMatches,
            runPlanList_declarations_exact]
        · simp [executeFamilyControl, executeGuardFamily, ownerCurrent,
            revisionCurrent, headMatches, arityMatches]
      · simp [executeFamilyControl, executeGuardFamily, ownerCurrent,
          revisionCurrent, headMatches]
    · simp [executeFamilyControl, executeGuardFamily, ownerCurrent,
        revisionCurrent]
  · simp [executeFamilyControl, executeGuardFamily, ownerCurrent]

theorem executeControl_outcome_exact
    (current : OwnedSnapshot) (call : Call) (result : CompilationResult) :
    (executeControl current call result).outcome =
      executeCompilation current call result := by
  cases result with
  | outsideFragment => rfl
  | compiled family => exact executeFamilyControl_outcome_exact current call family

theorem valid_execution_successfulDeclarations_exact
    {owned : OwnedSnapshot} {call : Call}
    {family : CompiledGuardFamily}
    (valid : family.ValidFor owned)
    (requestMatches : family.MatchesCall call) :
    (executeControl owned call (.compiled family)).outcome =
      .executed (successfulDeclarations ⟨owned.snapshot, call⟩) := by
  rw [executeControl_outcome_exact]
  exact executeCompilation_eq_successfulDeclarations
    owned call family valid requestMatches

theorem runPlanList_occurrences_no_invention
    (snapshot : Snapshot) (call : Call) (plans : List GuardPlan)
    {declaration : ArrowDeclaration}
    (member : declaration ∈ (runPlanList snapshot call plans).declarations) :
    ∃ plan ∈ plans, plan.declaration = declaration := by
  induction plans with
  | nil => simp [runPlanList] at member
  | cons plan plans inductionHypothesis =>
      by_cases accepted : (runPlan snapshot call plan).accepted = true
      · simp [runPlanList, accepted] at member
        rcases member with rfl | member
        · exact ⟨plan, by simp, rfl⟩
        · obtain ⟨candidate, candidateMember, exact⟩ :=
            inductionHypothesis member
          exact ⟨candidate, by simp [candidateMember], exact⟩
      · cases trace : runPlan snapshot call plan
        simp_all [runPlanList]

/-! ## Operational canaries -/

namespace Canary

open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan.Canary

theorem exact_type_success_has_no_metatype_event :
    (runArgMode exactTypeSnapshot 0 (.evalSoftcutType numberType)
      (.number "1") (.number "1")).events =
        [.evaluateArgument 0, .queryExactType 0 numberType true] := by
  decide

theorem metatype_only_after_exact_failure :
    (runArgMode CallGuardNativeKernel.Canary.fallbackClaim.snapshot 0
      (.evalSoftcutType groundedMetaType)
      (.number "3") (.number "3")).events =
        [.evaluateArgument 0,
          .queryExactType 0 groundedMetaType false,
          .queryMetatype 0 groundedMetaType true] := by
  decide

theorem unchecked_has_no_type_query :
    (runArgMode exactTypeSnapshot 0 .evalUnchecked
      (.number "1") (.string "changed")).events = [.evaluateArgument 0] := by
  decide

theorem raw_has_no_evaluation_event :
    (runArgMode exactTypeSnapshot 0 .rawAtom
      (.atom "x") (.atom "x")).events = [.useRawArgument 0] := by
  decide

theorem failed_type_and_metatype_rejects :
    (runArgMode exactTypeSnapshot 0 (.evalSoftcutType numberType)
      (.string "bad") (.string "bad")).accepted = false := by
  decide

theorem overloads_install_in_authored_order :
    ∃ family,
      compileGuards
          (owned CallGuardNativeKernel.Canary.overloadedClaim.snapshot) "f" 1 =
        .compiled family ∧
      (executeControl
          (owned CallGuardNativeKernel.Canary.overloadedClaim.snapshot)
          CallGuardNativeKernel.Canary.overloadedClaim.call
          (.compiled family)).events.filterMap
            (fun event => match event with
              | .installOccurrence occurrence => some occurrence
              | _ => none) = [10, 13] := by
  refine ⟨_, rfl, ?_⟩
  decide

theorem execution_distinctions_remain_disjoint :
    (executeControl (owned exactTypeSnapshot) wrongOrdinaryInputCall
        (compileGuards (owned exactTypeSnapshot) "n" 1)).outcome = .executed [] ∧
      (executeControl foreignCurrent CallGuardNativeKernel.Canary.claim.call
        (.compiled rawFamily)).outcome = .fallback .foreignOwner ∧
      (executeControl staleCurrent CallGuardNativeKernel.Canary.claim.call
        (.compiled rawFamily)).outcome = .fallback .staleRevision ∧
      (executeControl (owned mixedSupportedAndOpenSnapshot)
        CallGuardNativeKernel.Canary.claim.call .outsideFragment).outcome =
          .fallback .outsideFragment := by
  decide

end Canary

/-! ## Typed operational GSLTs

The source operational theories below use the actual typed compiler and guard
predicates.  They do not consume a preclassified answer protocol.  The hot
machine is deliberately a completed-call machine: its `Call` already names the
evaluated argument occurrences and body result.  A later operational
realization may expand those semantic operations into resumable evaluator and
choicepoint paths without changing the guard judgment.
-/

/-- The cold compiler as an authored deterministic GSLT.  One source step
inspects exactly one declaration, or closes the cursor. -/
def compileGSLT : Mettapedia.GSLT.GSLT where
  Term := CompileControl
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => compileStep? source = some target
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

@[simp] theorem compileGSLT_step_iff
    (source target : CompileControl) :
    compileGSLT.Step source target ↔ compileStep? source = some target :=
  Iff.rfl

theorem compileGSLT_step_deterministic
    {source first second : CompileControl}
    (firstStep : compileGSLT.Step source first)
    (secondStep : compileGSLT.Step source second) :
    first = second := by
  exact Option.some.inj (firstStep.symm.trans secondStep)

theorem compileGSLT_halted_normal (result : CompilationResult) :
    compileGSLT.IsNormalForm (.halted result) := by
  rintro ⟨target, step⟩
  change compileStep? (.halted result) = some target at step
  simp at step

/-- Execution phases retain the exact cursor that remains after selecting one
compiled declaration occurrence. -/
inductive ExecuteControl where
  | request
      (current : OwnedSnapshot) (call : Call) (compilation : CompilationResult)
  | plans
      (snapshot : Snapshot) (call : Call) (remaining : List GuardPlan)
      (accepted : List ArrowDeclaration) (events : List ControlEvent)
  | arguments
      (snapshot : Snapshot) (call : Call) (plan : GuardPlan)
      (remainingPlans : List GuardPlan) (index : Nat)
      (modes : List ArgMode) (sources values : List Term)
      (accepted : List ArrowDeclaration) (events : List ControlEvent)
  | result
      (snapshot : Snapshot) (call : Call) (plan : GuardPlan)
      (remainingPlans : List GuardPlan)
      (accepted : List ArrowDeclaration) (events : List ControlEvent)
  | halted (observation : ControlObservation)
deriving DecidableEq, Repr

/-- One authentic completed-call guard transition.  Authority checks, plan
selection, argument traversal, exact-before-metatype soft cut, body ordering,
result checking, and occurrence installation are all determined here from the
PeTTa snapshot and compiled plan. -/
def executeStep? : ExecuteControl → Option ExecuteControl
  | .halted _ => none
  | .request _ _ .outsideFragment =>
      some (.halted ⟨.fallback .outsideFragment, [.fallback .outsideFragment]⟩)
  | .request current call (.compiled family) =>
      if family.owner = current.owner then
        if family.revision = current.snapshot.revision then
          if family.head = call.function then
            if family.arity = call.sourceArguments.length then
              some (.plans current.snapshot call family.plans [] [])
            else
              some (.halted ⟨.fallback .wrongArity, [.fallback .wrongArity]⟩)
          else
            some (.halted ⟨.fallback .wrongHead, [.fallback .wrongHead]⟩)
        else
          some (.halted ⟨.fallback .staleRevision, [.fallback .staleRevision]⟩)
      else
        some (.halted ⟨.fallback .foreignOwner, [.fallback .foreignOwner]⟩)
  | .plans _ _ [] accepted events =>
      some (.halted ⟨.executed accepted, events⟩)
  | .plans snapshot call (plan :: remaining) accepted events =>
      let begun := events ++ [.beginPlan plan.declarationOccurrence]
      if plan.declaration.function = call.function then
        some (.arguments snapshot call plan remaining 0 plan.argumentModes
          call.sourceArguments call.evaluatedArguments accepted begun)
      else
        some (.plans snapshot call remaining accepted
          (begun ++ [.rejectOccurrence plan.declarationOccurrence]))
  | .arguments snapshot call plan remaining _index [] [] [] accepted events =>
      some (.result snapshot call plan remaining accepted
        (events ++ [.evaluateCall plan.declarationOccurrence]))
  | .arguments snapshot call plan remaining index
      (mode :: modes) (source :: sources) (value :: values) accepted events =>
      let current := runArgMode snapshot index mode source value
      if current.accepted then
        some (.arguments snapshot call plan remaining (index + 1)
          modes sources values accepted (events ++ current.events))
      else
        some (.plans snapshot call remaining accepted
          (events ++ current.events ++
            [.rejectOccurrence plan.declarationOccurrence]))
  | .arguments snapshot call plan remaining index _ _ _ accepted events =>
      some (.plans snapshot call remaining accepted
        (events ++ [.argumentShapeMismatch index,
          .rejectOccurrence plan.declarationOccurrence]))
  | .result snapshot call plan remaining accepted events =>
      let checked := runResultMode snapshot plan.resultMode call.result
      if checked.accepted then
        some (.plans snapshot call remaining
          (accepted ++ [plan.declaration])
          (events ++ checked.events ++
            [.installOccurrence plan.declarationOccurrence]))
      else
        some (.plans snapshot call remaining accepted
          (events ++ checked.events ++
            [.rejectOccurrence plan.declarationOccurrence]))

def runExecute : Nat → ExecuteControl → ExecuteControl
  | 0, control => control
  | fuel + 1, control =>
      match executeStep? control with
      | none => control
      | some next => runExecute fuel next

/-- The hot completed-call executor as an authored deterministic GSLT. -/
def executeGSLT : Mettapedia.GSLT.GSLT where
  Term := ExecuteControl
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => executeStep? source = some target
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

@[simp] theorem executeGSLT_step_iff
    (source target : ExecuteControl) :
    executeGSLT.Step source target ↔ executeStep? source = some target :=
  Iff.rfl

theorem executeGSLT_step_deterministic
    {source first second : ExecuteControl}
    (firstStep : executeGSLT.Step source first)
    (secondStep : executeGSLT.Step source second) :
    first = second := by
  exact Option.some.inj (firstStep.symm.trans secondStep)

theorem executeGSLT_halted_normal (observation : ControlObservation) :
    executeGSLT.IsNormalForm (.halted observation) := by
  rintro ⟨target, step⟩
  change (none : Option ExecuteControl) = some target at step
  exact Option.some_ne_none target step.symm

/-! ### Independent terminal observation -/

/-- Complete the untouched suffix of the plan cursor with the independently
defined G2/G3 executor. -/
def plansObservation (snapshot : Snapshot) (call : Call)
    (remaining : List GuardPlan) (accepted : List ArrowDeclaration)
    (events : List ControlEvent) : ControlObservation :=
  let suffix := runPlanList snapshot call remaining;
  ⟨.executed (accepted ++ suffix.declarations), events ++ suffix.events⟩

/-- Independent meaning of a result-check cursor. -/
def resultObservation (snapshot : Snapshot) (call : Call) (plan : GuardPlan)
    (remaining : List GuardPlan) (accepted : List ArrowDeclaration)
    (events : List ControlEvent) : ControlObservation :=
  let checked := runResultMode snapshot plan.resultMode call.result;
  if checked.accepted then
    plansObservation snapshot call remaining
      (accepted ++ [plan.declaration])
      (events ++ checked.events ++
        [.installOccurrence plan.declarationOccurrence])
  else
    plansObservation snapshot call remaining accepted
      (events ++ checked.events ++
        [.rejectOccurrence plan.declarationOccurrence])

/-- Independent meaning of a partially traversed argument cursor. -/
def argumentsObservation (snapshot : Snapshot) (call : Call)
    (plan : GuardPlan) (remaining : List GuardPlan) (index : Nat)
    (modes : List ArgMode) (sources values : List Term)
    (accepted : List ArrowDeclaration) (events : List ControlEvent) :
    ControlObservation :=
  let checked := runArguments snapshot index modes sources values;
  if checked.accepted then
    resultObservation snapshot call plan remaining accepted
      (events ++ checked.events ++ [.evaluateCall plan.declarationOccurrence])
  else
    plansObservation snapshot call remaining accepted
      (events ++ checked.events ++
        [.rejectOccurrence plan.declarationOccurrence])

/-- Denotation of every operational cursor.  This function is independent of
`executeStep?`: it completes a partial cursor through the already proved
ordered GuardPlan semantics. -/
def ExecuteControl.denote : ExecuteControl → ControlObservation
  | .request current call compilation => executeControl current call compilation
  | .plans snapshot call remaining accepted events =>
      plansObservation snapshot call remaining accepted events
  | .arguments snapshot call plan remaining index modes sources values
      accepted events =>
      argumentsObservation snapshot call plan remaining index modes sources
        values accepted events
  | .result snapshot call plan remaining accepted events =>
      resultObservation snapshot call plan remaining accepted events
  | .halted observation => observation

theorem executeStep_denote_preserved
    {source target : ExecuteControl}
    (step : executeStep? source = some target) :
    source.denote = target.denote := by
  cases source with
  | halted observation =>
      change (none : Option ExecuteControl) = some target at step
      exact (Option.some_ne_none target step.symm).elim
  | request current call compilation =>
      cases compilation with
      | outsideFragment =>
          simp only [executeStep?] at step
          cases Option.some.inj step
          rfl
      | compiled family =>
          by_cases ownerCurrent : family.owner = current.owner
          · by_cases revisionCurrent :
                family.revision = current.snapshot.revision
            · by_cases headMatches : family.head = call.function
              · by_cases arityMatches :
                    family.arity = call.sourceArguments.length
                · simp only [executeStep?, ownerCurrent, revisionCurrent,
                    headMatches, arityMatches, if_pos] at step
                  cases Option.some.inj step
                  simp [ExecuteControl.denote, executeControl,
                    executeFamilyControl, plansObservation, ownerCurrent,
                    revisionCurrent, headMatches, arityMatches]
                · simp only [executeStep?, ownerCurrent, revisionCurrent,
                    headMatches, arityMatches, if_pos] at step
                  cases Option.some.inj step
                  simp [ExecuteControl.denote, executeControl,
                    executeFamilyControl, ownerCurrent, revisionCurrent,
                    headMatches, arityMatches]
              · simp only [executeStep?, ownerCurrent, revisionCurrent,
                  headMatches, if_pos] at step
                cases Option.some.inj step
                simp [ExecuteControl.denote, executeControl,
                  executeFamilyControl, ownerCurrent, revisionCurrent,
                  headMatches]
            · simp only [executeStep?, ownerCurrent, revisionCurrent,
                if_pos] at step
              cases Option.some.inj step
              simp [ExecuteControl.denote, executeControl,
                executeFamilyControl, ownerCurrent, revisionCurrent]
          · simp only [executeStep?, ownerCurrent] at step
            cases Option.some.inj step
            simp [ExecuteControl.denote, executeControl,
              executeFamilyControl, ownerCurrent]
  | plans snapshot call remaining accepted events =>
      cases remaining with
      | nil =>
          simp only [executeStep?] at step
          cases Option.some.inj step
          simp [ExecuteControl.denote, plansObservation, runPlanList]
      | cons plan remaining =>
          by_cases headMatches : plan.declaration.function = call.function
          · simp only [executeStep?, headMatches, if_pos] at step
            cases Option.some.inj step
            by_cases argumentsAccepted :
                (runArguments snapshot 0 plan.argumentModes
                  call.sourceArguments call.evaluatedArguments).accepted = true
            · by_cases resultAccepted :
                  (runResultMode snapshot plan.resultMode call.result).accepted = true
              · simp [ExecuteControl.denote, plansObservation,
                  argumentsObservation, resultObservation, runPlanList, runPlan,
                  headMatches, argumentsAccepted, resultAccepted,
                  List.append_assoc]
              · simp [ExecuteControl.denote, plansObservation,
                  argumentsObservation, resultObservation, runPlanList, runPlan,
                  headMatches, argumentsAccepted, resultAccepted,
                  List.append_assoc]
            · simp [ExecuteControl.denote, plansObservation,
                argumentsObservation, runPlanList, runPlan,
                headMatches, argumentsAccepted, List.append_assoc]
          · simp only [executeStep?, headMatches] at step
            cases Option.some.inj step
            simp [ExecuteControl.denote, plansObservation,
              runPlanList, runPlan, headMatches, List.append_assoc]
  | arguments snapshot call plan remaining index modes sources values
      accepted events =>
      cases modes with
      | nil =>
          cases sources <;> cases values <;>
            simp only [executeStep?] at step <;>
            cases Option.some.inj step <;>
            simp [ExecuteControl.denote, argumentsObservation,
              resultObservation, plansObservation, runArguments,
              List.append_assoc]
      | cons mode modes =>
          cases sources with
          | nil =>
              cases values <;>
                simp only [executeStep?] at step <;>
                cases Option.some.inj step <;>
                simp [ExecuteControl.denote, argumentsObservation,
                  plansObservation, runArguments, List.append_assoc]
          | cons source sources =>
              cases values with
              | nil =>
                  simp only [executeStep?] at step
                  cases Option.some.inj step
                  simp [ExecuteControl.denote, argumentsObservation,
                    plansObservation, runArguments, List.append_assoc]
              | cons value values =>
                  by_cases currentAccepted :
                      (runArgMode snapshot index mode source value).accepted = true
                  · simp only [executeStep?, currentAccepted, if_pos] at step
                    cases Option.some.inj step
                    simp [ExecuteControl.denote, argumentsObservation,
                      plansObservation, runArguments, currentAccepted,
                      List.append_assoc]
                  · simp only [executeStep?, currentAccepted] at step
                    cases Option.some.inj step
                    simp [ExecuteControl.denote, argumentsObservation,
                      plansObservation, runArguments, currentAccepted,
                      List.append_assoc]
  | result snapshot call plan remaining accepted events =>
      by_cases checked :
          (runResultMode snapshot plan.resultMode call.result).accepted = true
      · simp only [executeStep?, checked, if_pos] at step
        cases Option.some.inj step
        simp [ExecuteControl.denote, resultObservation, checked]
      · simp only [executeStep?, checked] at step
        cases Option.some.inj step
        simp [ExecuteControl.denote, resultObservation, checked]

theorem executeGSLT_step_denote_preserved
    {source target : ExecuteControl}
    (step : executeGSLT.Step source target) :
    source.denote = target.denote :=
  executeStep_denote_preserved step

theorem executeGSLT_multiStep_denote_preserved :
    ∀ {source target : ExecuteControl},
      executeGSLT.MultiStep source target → source.denote = target.denote
  | _, _, .refl _ => rfl
  | _, _, .step one rest =>
      (executeGSLT_step_denote_preserved one).trans
        (executeGSLT_multiStep_denote_preserved rest)

/-- Any terminal result reachable from the authentic hot GSLT is exactly the
independent GuardPlan execution result, including ordered occurrences and all
fallback distinctions. -/
theorem executeGSLT_terminal_exact
    (current : OwnedSnapshot) (call : Call) (compilation : CompilationResult)
    (observation : ControlObservation)
    (steps : executeGSLT.MultiStep
      (.request current call compilation) (.halted observation)) :
    observation = executeControl current call compilation := by
  exact (executeGSLT_multiStep_denote_preserved steps).symm

/-! ### Total normalization -/

/-- A conservative bound for traversing one remaining plan, including entry,
body/result processing, and return to the plan cursor. -/
def GuardPlan.stepBound (plan : GuardPlan) : Nat :=
  plan.argumentModes.length + 3

/-- A conservative bound for an authored-order plan suffix, including its
terminal observation step. -/
def planListStepBound (plans : List GuardPlan) : Nat :=
  (plans.map GuardPlan.stepBound).sum + 1

/-- Structural work remaining in the completed-call executor. -/
def ExecuteControl.stepBound : ExecuteControl → Nat
  | .request _ _ .outsideFragment => 1
  | .request _ _ (.compiled family) => 1 + planListStepBound family.plans
  | .plans _ _ remaining _ _ => planListStepBound remaining
  | .arguments _ _ _ remaining _ modes _ _ _ _ =>
      modes.length + 2 + planListStepBound remaining
  | .result _ _ _ remaining _ _ => 1 + planListStepBound remaining
  | .halted _ => 0

theorem executeStep?_none_iff_halted (source : ExecuteControl) :
    executeStep? source = none ↔
      ∃ observation, source = .halted observation := by
  cases source with
  | halted observation => simp [executeStep?]
  | request current call compilation =>
      cases compilation with
      | outsideFragment => simp [executeStep?]
      | compiled family =>
          by_cases ownerCurrent : family.owner = current.owner
          · by_cases revisionCurrent :
                family.revision = current.snapshot.revision
            · by_cases headMatches : family.head = call.function
              · by_cases arityMatches :
                    family.arity = call.sourceArguments.length
                · simp [executeStep?, ownerCurrent, revisionCurrent,
                    headMatches, arityMatches]
                · simp [executeStep?, ownerCurrent, revisionCurrent,
                    headMatches, arityMatches]
              · simp [executeStep?, ownerCurrent, revisionCurrent,
                  headMatches]
            · simp [executeStep?, ownerCurrent, revisionCurrent]
          · simp [executeStep?, ownerCurrent]
  | plans snapshot call remaining accepted events =>
      cases remaining with
      | nil => simp [executeStep?]
      | cons plan remaining =>
          by_cases headMatches :
              plan.declaration.function = call.function <;>
            simp [executeStep?, headMatches]
  | arguments snapshot call plan remaining index modes sources values
      accepted events =>
      cases modes with
      | nil => cases sources <;> cases values <;> simp [executeStep?]
      | cons mode modes =>
          cases sources with
          | nil => cases values <;> simp [executeStep?]
          | cons source sources =>
              cases values with
              | nil => simp [executeStep?]
              | cons value values =>
                  by_cases acceptedNow :
                      (runArgMode snapshot index mode source value).accepted =
                        true <;>
                    simp [executeStep?, acceptedNow]
  | result snapshot call plan remaining accepted events =>
      by_cases resultAccepted :
          (runResultMode snapshot plan.resultMode call.result).accepted = true <;>
        simp [executeStep?, resultAccepted]

/-- Every executor transition consumes structural work.  This is the
termination fact used by the source GSLT, not a runtime fuel check. -/
theorem executeStep_stepBound_decreases
    {source target : ExecuteControl}
    (step : executeStep? source = some target) :
    target.stepBound < source.stepBound := by
  cases source with
  | halted observation =>
      simp [executeStep?] at step
  | request current call compilation =>
      cases compilation with
      | outsideFragment =>
          simp [executeStep?] at step
          subst target
          simp [ExecuteControl.stepBound]
      | compiled family =>
          by_cases ownerCurrent : family.owner = current.owner
          · by_cases revisionCurrent :
                family.revision = current.snapshot.revision
            · by_cases headMatches : family.head = call.function
              · by_cases arityMatches :
                    family.arity = call.sourceArguments.length
                · simp [executeStep?, ownerCurrent, revisionCurrent,
                    headMatches, arityMatches] at step
                  subst target
                  simp [ExecuteControl.stepBound]
                · simp [executeStep?, ownerCurrent, revisionCurrent,
                    headMatches, arityMatches] at step
                  subst target
                  simp [ExecuteControl.stepBound]
              · simp [executeStep?, ownerCurrent, revisionCurrent,
                  headMatches] at step
                subst target
                simp [ExecuteControl.stepBound]
            · simp [executeStep?, ownerCurrent, revisionCurrent] at step
              subst target
              simp [ExecuteControl.stepBound]
          · simp [executeStep?, ownerCurrent] at step
            subst target
            simp [ExecuteControl.stepBound]
  | plans snapshot call remaining accepted events =>
      cases remaining with
      | nil =>
          simp [executeStep?] at step
          subst target
          simp [ExecuteControl.stepBound, planListStepBound]
      | cons plan remaining =>
          by_cases headMatches : plan.declaration.function = call.function
          · simp [executeStep?, headMatches] at step
            subst target
            simp [ExecuteControl.stepBound, planListStepBound,
              GuardPlan.stepBound]
          · simp [executeStep?, headMatches] at step
            subst target
            simp [ExecuteControl.stepBound, planListStepBound,
              GuardPlan.stepBound]
  | arguments snapshot call plan remaining index modes sources values
      accepted events =>
      cases modes with
      | nil =>
          cases sources <;> cases values <;>
            simp [executeStep?] at step <;>
            subst target <;>
            simp [ExecuteControl.stepBound, planListStepBound]
      | cons mode modes =>
          cases sources with
          | nil =>
              cases values <;>
                simp [executeStep?] at step <;>
                subst target <;>
                simp [ExecuteControl.stepBound, planListStepBound]
          | cons source sources =>
              cases values with
              | nil =>
                  simp [executeStep?] at step
                  subst target
                  simp [ExecuteControl.stepBound, planListStepBound]
              | cons value values =>
                  by_cases acceptedNow :
                      (runArgMode snapshot index mode source value).accepted =
                        true
                  · simp [executeStep?, acceptedNow] at step
                    subst target
                    simp [ExecuteControl.stepBound, planListStepBound]
                  · simp [executeStep?, acceptedNow] at step
                    subst target
                    simp [ExecuteControl.stepBound, planListStepBound]
  | result snapshot call plan remaining accepted events =>
      by_cases resultAccepted :
          (runResultMode snapshot plan.resultMode call.result).accepted = true
      · simp [executeStep?, resultAccepted] at step
        subst target
        simp [ExecuteControl.stepBound, planListStepBound]
      · simp [executeStep?, resultAccepted] at step
        subst target
        simp [ExecuteControl.stepBound, planListStepBound]

/-- Every hot source state reaches its unique independent terminal
observation. -/
theorem executeGSLT_normalizes (source : ExecuteControl) :
    ∃ observation,
      executeGSLT.MultiStep source (.halted observation) ∧
        observation = source.denote := by
  induction source using (measure ExecuteControl.stepBound).wf.induction with
  | h source inductionHypothesis =>
      cases next : executeStep? source with
      | none =>
          obtain ⟨observation, rfl⟩ :=
            (executeStep?_none_iff_halted source).1 next
          exact ⟨observation, .refl _, rfl⟩
      | some target =>
          obtain ⟨observation, steps, observationExact⟩ :=
            inductionHypothesis target
              (executeStep_stepBound_decreases next)
          exact ⟨observation, .step next steps,
            observationExact.trans (executeStep_denote_preserved next).symm⟩

theorem executeStep_argument_accepts
    (snapshot : Snapshot) (call : Call) (plan : GuardPlan)
    (remaining : List GuardPlan) (index : Nat) (mode : ArgMode)
    (modes : List ArgMode) (source : Term) (sources : List Term)
    (value : Term) (values : List Term)
    (accepted : List ArrowDeclaration) (events : List ControlEvent)
    (accepts : mode.Accepts snapshot source value) :
    executeStep? (.arguments snapshot call plan remaining index
      (mode :: modes) (source :: sources) (value :: values) accepted events) =
      some (.arguments snapshot call plan remaining (index + 1)
        modes sources values accepted
        (events ++ (runArgMode snapshot index mode source value).events)) := by
  simp only [executeStep?]
  rw [if_pos ((runArgMode_accepted_iff snapshot index mode source value).2 accepts)]

theorem executeStep_argument_rejects
    (snapshot : Snapshot) (call : Call) (plan : GuardPlan)
    (remaining : List GuardPlan) (index : Nat) (mode : ArgMode)
    (modes : List ArgMode) (source : Term) (sources : List Term)
    (value : Term) (values : List Term)
    (accepted : List ArrowDeclaration) (events : List ControlEvent)
    (rejects : ¬ mode.Accepts snapshot source value) :
    executeStep? (.arguments snapshot call plan remaining index
      (mode :: modes) (source :: sources) (value :: values) accepted events) =
      some (.plans snapshot call remaining accepted
        (events ++ (runArgMode snapshot index mode source value).events ++
          [.rejectOccurrence plan.declarationOccurrence])) := by
  simp only [executeStep?]
  rw [if_neg]
  intro acceptedByMachine
  exact rejects
    ((runArgMode_accepted_iff snapshot index mode source value).1
      acceptedByMachine)

/-! ## Lawful cold/hot composition -/

/-- Remaining compilation meaning from any cold cursor. -/
def CompileControl.denote : CompileControl → CompilationResult
  | .running owner revision head arity remaining accepted =>
      compileOrdered owner revision head arity accepted remaining
  | .halted result => result

theorem compileStep_denote_preserved
    {source target : CompileControl}
    (step : compileStep? source = some target) :
    source.denote = target.denote := by
  cases source with
  | halted result =>
      change (none : Option CompileControl) = some target at step
      exact (Option.some_ne_none target step.symm).elim
  | running owner revision head arity remaining accepted =>
      cases remaining with
      | nil =>
          simp only [compileStep?] at step
          cases Option.some.inj step
          rfl
      | cons declaration remaining =>
          by_cases relevant : Relevant declaration head arity
          · cases compiled : compileGuard declaration with
            | none =>
                simp only [compileStep?, relevant, compiled, if_pos] at step
                cases Option.some.inj step
                simp [CompileControl.denote, compileOrdered, relevant, compiled]
            | some plan =>
                simp only [compileStep?, relevant, compiled, if_pos] at step
                cases Option.some.inj step
                simp [CompileControl.denote, compileOrdered, relevant, compiled]
          · simp only [compileStep?, relevant] at step
            cases Option.some.inj step
            simp [CompileControl.denote, compileOrdered, relevant]

theorem compileStart_denote_exact
    (owned : OwnedSnapshot) (head : String) (arity : Nat) :
    (compileStart owned head arity).denote = compileGuards owned head arity := by
  change compileOrdered owned.owner owned.snapshot.revision head arity []
      owned.snapshot.declarations =
    compileRelevantGuards owned.owner owned.snapshot.revision head arity
      owned.snapshot.declarations
  rw [compileOrdered_eq_reference]
  cases result : compileRelevantGuards owned.owner owned.snapshot.revision
      head arity owned.snapshot.declarations with
  | outsideFragment => rfl
  | compiled family =>
      cases family
      simp

/-- Structural work remaining in the cold declaration cursor. -/
def CompileControl.stepBound : CompileControl → Nat
  | .running _ _ _ _ remaining _ => remaining.length + 1
  | .halted _ => 0

theorem compileStep?_none_iff_halted (source : CompileControl) :
    compileStep? source = none ↔ ∃ result, source = .halted result := by
  cases source with
  | halted result => simp [compileStep?]
  | running owner revision head arity remaining accepted =>
      obtain ⟨next, hasNext⟩ := compile_running_has_next
        owner revision head arity remaining accepted
      constructor
      · intro noStep
        rw [noStep] at hasNext
        contradiction
      · rintro ⟨result, impossible⟩
        cases impossible

theorem compileStep_stepBound_decreases
    {source target : CompileControl}
    (step : compileStep? source = some target) :
    target.stepBound < source.stepBound := by
  cases source with
  | halted result => simp [compileStep?] at step
  | running owner revision head arity remaining accepted =>
      cases remaining with
      | nil =>
          simp [compileStep?] at step
          subst target
          simp [CompileControl.stepBound]
      | cons declaration remaining =>
          by_cases relevant : Relevant declaration head arity
          · cases compiled : compileGuard declaration with
            | none =>
                simp [compileStep?, relevant, compiled] at step
                subst target
                simp [CompileControl.stepBound]
            | some plan =>
                simp [compileStep?, relevant, compiled] at step
                subst target
                simp [CompileControl.stepBound]
          · simp [compileStep?, relevant] at step
            subst target
            simp [CompileControl.stepBound]

theorem compileGSLT_step_denote_preserved
    {source target : CompileControl}
    (step : compileGSLT.Step source target) :
    source.denote = target.denote :=
  compileStep_denote_preserved step

theorem compileGSLT_multiStep_denote_preserved :
    ∀ {source target : CompileControl},
      compileGSLT.MultiStep source target → source.denote = target.denote
  | _, _, .refl _ => rfl
  | _, _, .step one rest =>
      (compileGSLT_step_denote_preserved one).trans
        (compileGSLT_multiStep_denote_preserved rest)

/-- Every cold cursor reaches its exact compiler result. -/
theorem compileGSLT_normalizes (source : CompileControl) :
    ∃ result,
      compileGSLT.MultiStep source (.halted result) ∧
        result = source.denote := by
  induction source using (measure CompileControl.stepBound).wf.induction with
  | h source inductionHypothesis =>
      cases next : compileStep? source with
      | none =>
          obtain ⟨result, rfl⟩ :=
            (compileStep?_none_iff_halted source).1 next
          exact ⟨result, .refl _, rfl⟩
      | some target =>
          obtain ⟨result, steps, resultExact⟩ :=
            inductionHypothesis target
              (compileStep_stepBound_decreases next)
          exact ⟨result, .step next steps,
            resultExact.trans (compileStep_denote_preserved next).symm⟩

/-- The composed source makes the compiler/executor boundary explicit without
turning it into a runtime service protocol. -/
inductive CallGuardControl where
  | compiling (owned : OwnedSnapshot) (call : Call) (compiler : CompileControl)
  | executing (executor : ExecuteControl)
deriving DecidableEq, Repr

def callGuardStart (owned : OwnedSnapshot) (call : Call) : CallGuardControl :=
  .compiling owned call
    (compileStart owned call.function call.sourceArguments.length)

def callGuardStep? : CallGuardControl → Option CallGuardControl
  | .compiling owned call compiler =>
      match compileStep? compiler with
      | some next => some (.compiling owned call next)
      | none =>
          match compiler with
          | .halted result => some (.executing (.request owned call result))
          | .running _ _ _ _ _ _ => none
  | .executing executor =>
      (executeStep? executor).map .executing

def callGuardGSLT : Mettapedia.GSLT.GSLT where
  Term := CallGuardControl
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => callGuardStep? source = some target
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

theorem callGuardGSLT_step_deterministic
    {source first second : CallGuardControl}
    (firstStep : callGuardGSLT.Step source first)
    (secondStep : callGuardGSLT.Step source second) :
    first = second := by
  exact Option.some.inj (firstStep.symm.trans secondStep)

theorem callGuardGSLT_halted_normal (observation : ControlObservation) :
    callGuardGSLT.IsNormalForm (.executing (.halted observation)) := by
  rintro ⟨target, step⟩
  change callGuardStep? (.executing (.halted observation)) = some target at step
  simp [callGuardStep?, executeStep?] at step

def CallGuardControl.denote : CallGuardControl → ControlObservation
  | .compiling owned call compiler =>
      executeControl owned call compiler.denote
  | .executing executor => executor.denote

/-- Work remaining in the composed cold/hot source.  The denotation term in
the cold case fixes the size of the future hot phase while declarations are
being inspected. -/
def CallGuardControl.stepBound : CallGuardControl → Nat
  | .compiling owned call compiler =>
      compiler.stepBound + 1 +
        (ExecuteControl.request owned call compiler.denote).stepBound
  | .executing executor => executor.stepBound

theorem callGuardStep_denote_preserved
    {source target : CallGuardControl}
    (step : callGuardStep? source = some target) :
    source.denote = target.denote := by
  cases source with
  | compiling owned call compiler =>
      cases moved : compileStep? compiler with
      | some next =>
          simp only [callGuardStep?, moved] at step
          cases Option.some.inj step
          simp only [CallGuardControl.denote]
          rw [compileStep_denote_preserved moved]
      | none =>
          cases compiler with
          | halted result =>
              simp only [callGuardStep?, compileStep?] at step
              cases Option.some.inj step
              rfl
          | running owner revision head arity remaining accepted =>
              obtain ⟨next, hasNext⟩ := compile_running_has_next
                owner revision head arity remaining accepted
              rw [moved] at hasNext
              contradiction
  | executing executor =>
      cases moved : executeStep? executor with
      | none =>
          simp [callGuardStep?, moved] at step
      | some next =>
          simp only [callGuardStep?, moved, Option.map] at step
          cases Option.some.inj step
          exact executeStep_denote_preserved moved

theorem callGuardStep?_none_iff_halted (source : CallGuardControl) :
    callGuardStep? source = none ↔
      ∃ observation, source = .executing (.halted observation) := by
  cases source with
  | compiling owned call compiler =>
      cases compiler with
      | halted result => simp [callGuardStep?, compileStep?]
      | running owner revision head arity remaining accepted =>
          obtain ⟨next, hasNext⟩ := compile_running_has_next
            owner revision head arity remaining accepted
          simp [callGuardStep?, hasNext]
  | executing executor =>
      simpa [callGuardStep?, Option.map_eq_none_iff] using
        executeStep?_none_iff_halted executor

theorem callGuardStep_stepBound_decreases
    {source target : CallGuardControl}
    (step : callGuardStep? source = some target) :
    target.stepBound < source.stepBound := by
  cases source with
  | compiling owned call compiler =>
      cases compiler with
      | halted result =>
          simp only [callGuardStep?, compileStep?] at step
          cases Option.some.inj step
          simp [CallGuardControl.stepBound, CompileControl.stepBound,
            CompileControl.denote]
      | running owner revision head arity remaining accepted =>
          obtain ⟨next, moved⟩ := compile_running_has_next
            owner revision head arity remaining accepted
          simp only [callGuardStep?, moved] at step
          cases Option.some.inj step
          have coldDecrease := compileStep_stepBound_decreases moved
          have denotationExact := compileStep_denote_preserved moved
          simp only [CallGuardControl.stepBound]
          rw [← denotationExact]
          omega
  | executing executor =>
      cases moved : executeStep? executor with
      | none => simp [callGuardStep?, moved] at step
      | some next =>
          simp only [callGuardStep?, moved, Option.map] at step
          cases Option.some.inj step
          exact executeStep_stepBound_decreases moved

theorem callGuardGSLT_step_denote_preserved
    {source target : CallGuardControl}
    (step : callGuardGSLT.Step source target) :
    source.denote = target.denote :=
  callGuardStep_denote_preserved step

theorem callGuardGSLT_multiStep_denote_preserved :
    ∀ {source target : CallGuardControl},
      callGuardGSLT.MultiStep source target → source.denote = target.denote
  | _, _, .refl _ => rfl
  | _, _, .step one rest =>
      (callGuardGSLT_step_denote_preserved one).trans
        (callGuardGSLT_multiStep_denote_preserved rest)

theorem callGuardStart_denote_exact
    (owned : OwnedSnapshot) (call : Call) :
    (callGuardStart owned call).denote =
      executeControl owned call
        (compileGuards owned call.function call.sourceArguments.length) := by
  simp [callGuardStart, CallGuardControl.denote, compileStart_denote_exact]

/-- Terminal adequacy of the composed source GSLT against the independent
compiler/executor meaning. -/
theorem callGuardGSLT_terminal_exact
    (owned : OwnedSnapshot) (call : Call) (observation : ControlObservation)
    (steps : callGuardGSLT.MultiStep (callGuardStart owned call)
      (.executing (.halted observation))) :
    observation = executeControl owned call
      (compileGuards owned call.function call.sourceArguments.length) := by
  calc
    observation = (callGuardStart owned call).denote :=
      (callGuardGSLT_multiStep_denote_preserved steps).symm
    _ = executeControl owned call
        (compileGuards owned call.function call.sourceArguments.length) :=
      callGuardStart_denote_exact owned call

/-- The complete cold/hot source always reaches a terminal observation, and
that observation is its independently defined meaning. -/
theorem callGuardGSLT_normalizes (source : CallGuardControl) :
    ∃ observation,
      callGuardGSLT.MultiStep source (.executing (.halted observation)) ∧
        observation = source.denote := by
  induction source using (measure CallGuardControl.stepBound).wf.induction with
  | h source inductionHypothesis =>
      cases next : callGuardStep? source with
      | none =>
          obtain ⟨observation, rfl⟩ :=
            (callGuardStep?_none_iff_halted source).1 next
          exact ⟨observation, .refl _, rfl⟩
      | some target =>
          obtain ⟨observation, steps, observationExact⟩ :=
            inductionHypothesis target
              (callGuardStep_stepBound_decreases next)
          exact ⟨observation, .step next steps,
            observationExact.trans
              (callGuardStep_denote_preserved next).symm⟩

/-- Unconditional total correctness of the authentic source GSLT. -/
theorem callGuardGSLT_total_exact (owned : OwnedSnapshot) (call : Call) :
    ∃ observation,
      callGuardGSLT.MultiStep (callGuardStart owned call)
          (.executing (.halted observation)) ∧
        observation = executeControl owned call
          (compileGuards owned call.function
            call.sourceArguments.length) := by
  obtain ⟨observation, steps, observationExact⟩ :=
    callGuardGSLT_normalizes (callGuardStart owned call)
  exact ⟨observation, steps,
    observationExact.trans (callGuardStart_denote_exact owned call)⟩

/-- Covered reflection: a terminal observation is reachable exactly when it
is the independent compiler/executor observation. -/
theorem callGuardGSLT_terminal_iff
    (owned : OwnedSnapshot) (call : Call) (observation : ControlObservation) :
    callGuardGSLT.MultiStep (callGuardStart owned call)
        (.executing (.halted observation)) ↔
      observation = executeControl owned call
        (compileGuards owned call.function
          call.sourceArguments.length) := by
  constructor
  · exact callGuardGSLT_terminal_exact owned call observation
  · intro observationExact
    obtain ⟨actual, steps, actualExact⟩ :=
      callGuardGSLT_total_exact owned call
    have equal : actual = observation :=
      actualExact.trans observationExact.symm
    simpa [equal] using steps

/-- On the admitted closed fragment, the composed GSLT terminates only at the
exact SWI-PeTTa ordered successful-declaration fibre. -/
theorem callGuardGSLT_terminal_successfulDeclarations_exact
    (owned : OwnedSnapshot) (call : Call) (family : CompiledGuardFamily)
    (observation : ControlObservation)
    (wellFormed : owned.snapshot.WellFormed)
    (compiled : compileGuards owned call.function
      call.sourceArguments.length = .compiled family)
    (steps : callGuardGSLT.MultiStep (callGuardStart owned call)
      (.executing (.halted observation))) :
    observation.outcome =
      .executed (successfulDeclarations ⟨owned.snapshot, call⟩) := by
  have terminal := callGuardGSLT_terminal_exact owned call observation steps
  have valid := compileGuards_family_valid owned call.function
    call.sourceArguments.length family wellFormed compiled
  have coordinates :
      family.owner = owned.owner ∧
        family.revision = owned.snapshot.revision ∧
          family.head = call.function ∧
            family.arity = call.sourceArguments.length :=
    compileGuards_coordinates compiled
  have requestMatches : family.MatchesCall call :=
    ⟨coordinates.2.2.1, coordinates.2.2.2⟩
  rw [terminal, compiled]
  exact valid_execution_successfulDeclarations_exact valid requestMatches

/-- Total closed-fragment adequacy: the exact ordered SWI-PeTTa declaration
fibre is not only the unique possible terminal result; it is reached. -/
theorem callGuardGSLT_total_successfulDeclarations_exact
    (owned : OwnedSnapshot) (call : Call) (family : CompiledGuardFamily)
    (wellFormed : owned.snapshot.WellFormed)
    (compiled : compileGuards owned call.function
      call.sourceArguments.length = .compiled family) :
    ∃ observation,
      callGuardGSLT.MultiStep (callGuardStart owned call)
          (.executing (.halted observation)) ∧
        observation.outcome =
          .executed (successfulDeclarations ⟨owned.snapshot, call⟩) := by
  obtain ⟨observation, steps, _observationExact⟩ :=
    callGuardGSLT_total_exact owned call
  exact ⟨observation, steps,
    callGuardGSLT_terminal_successfulDeclarations_exact owned call family
      observation wellFormed compiled steps⟩

/-- Declining the admitted fragment is a reachable fallback observation, not
a negative typing judgment. -/
theorem callGuardGSLT_total_outsideFragment
    (owned : OwnedSnapshot) (call : Call)
    (outside : compileGuards owned call.function
      call.sourceArguments.length = .outsideFragment) :
    ∃ observation,
      callGuardGSLT.MultiStep (callGuardStart owned call)
          (.executing (.halted observation)) ∧
        observation.outcome = .fallback .outsideFragment := by
  obtain ⟨observation, steps, observationExact⟩ :=
    callGuardGSLT_total_exact owned call
  refine ⟨observation, steps, ?_⟩
  rw [observationExact, outside]
  rfl

namespace OperationalCanary

open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan.Canary

theorem outside_fragment_is_explicit_fallback_step :
    executeStep? (.request (owned exactTypeSnapshot)
      wrongOrdinaryInputCall .outsideFragment) =
      some (.halted ⟨.fallback .outsideFragment,
        [.fallback .outsideFragment]⟩) := by
  rfl

theorem exact_argument_step_has_no_metatype_event :
    executeStep? (.arguments exactTypeSnapshot exactTypeCall rawPlan [] 0
      [.evalSoftcutType numberType] [(.number "1")] [(.number "1")]
      [] []) =
      some (.arguments exactTypeSnapshot exactTypeCall rawPlan [] 1
        [] [] [] []
        [.evaluateArgument 0, .queryExactType 0 numberType true]) := by
  decide

theorem failed_argument_step_rejects_occurrence :
    executeStep? (.arguments exactTypeSnapshot wrongOrdinaryInputCall rawPlan [] 0
      [.evalSoftcutType numberType] [(.string "bad")] [(.string "bad")]
      [] []) =
      some (.plans exactTypeSnapshot wrongOrdinaryInputCall [] []
        [.evaluateArgument 0,
          .queryExactType 0 numberType false,
          .queryMetatype 0 numberType false,
          .rejectOccurrence rawPlan.declarationOccurrence]) := by
  decide

theorem overload_execution_reaches_reference_observation :
    ∃ family,
      compileGuards
          (owned CallGuardNativeKernel.Canary.overloadedClaim.snapshot) "f" 1 =
        .compiled family ∧
      runExecute 32
        (.request
          (owned CallGuardNativeKernel.Canary.overloadedClaim.snapshot)
          CallGuardNativeKernel.Canary.overloadedClaim.call
          (.compiled family)) =
        .halted
          (executeControl
            (owned CallGuardNativeKernel.Canary.overloadedClaim.snapshot)
            CallGuardNativeKernel.Canary.overloadedClaim.call
            (.compiled family)) := by
  refine ⟨_, rfl, ?_⟩
  decide

theorem rejection_and_authority_fallback_remain_distinct :
    runExecute 16
        (.request (owned exactTypeSnapshot) wrongOrdinaryInputCall
          (compileGuards (owned exactTypeSnapshot) "n" 1)) =
      .halted (executeControl (owned exactTypeSnapshot) wrongOrdinaryInputCall
        (compileGuards (owned exactTypeSnapshot) "n" 1)) ∧
    runExecute 4
        (.request foreignCurrent CallGuardNativeKernel.Canary.claim.call
          (.compiled rawFamily)) =
      .halted (executeControl foreignCurrent
        CallGuardNativeKernel.Canary.claim.call (.compiled rawFamily)) := by
  decide

theorem composed_overloads_install_in_authored_order :
    ∃ observation,
      callGuardGSLT.MultiStep
          (callGuardStart
            (owned CallGuardNativeKernel.Canary.overloadedClaim.snapshot)
            CallGuardNativeKernel.Canary.overloadedClaim.call)
          (.executing (.halted observation)) ∧
        observation.events.filterMap
          (fun event => match event with
            | .installOccurrence occurrence => some occurrence
            | _ => none) = [10, 13] := by
  obtain ⟨observation, steps, observationExact⟩ :=
    callGuardGSLT_total_exact
      (owned CallGuardNativeKernel.Canary.overloadedClaim.snapshot)
      CallGuardNativeKernel.Canary.overloadedClaim.call
  refine ⟨observation, steps, ?_⟩
  rw [observationExact]
  decide

theorem composed_bad_type_rejects_without_fallback :
    ∃ observation,
      callGuardGSLT.MultiStep
          (callGuardStart (owned exactTypeSnapshot) wrongOrdinaryInputCall)
          (.executing (.halted observation)) ∧
        observation.outcome = .executed [] := by
  obtain ⟨observation, steps, observationExact⟩ :=
    callGuardGSLT_total_exact (owned exactTypeSnapshot)
      wrongOrdinaryInputCall
  refine ⟨observation, steps, ?_⟩
  rw [observationExact]
  decide

theorem composed_open_overload_declines_to_fallback :
    ∃ observation,
      callGuardGSLT.MultiStep
          (callGuardStart (owned mixedSupportedAndOpenSnapshot)
            CallGuardNativeKernel.Canary.claim.call)
          (.executing (.halted observation)) ∧
        observation.outcome = .fallback .outsideFragment := by
  exact callGuardGSLT_total_outsideFragment
    (owned mixedSupportedAndOpenSnapshot)
    CallGuardNativeKernel.Canary.claim.call rfl

end OperationalCanary

#print axioms runCompile_running_exact
#print axioms compileOrdered_eq_reference
#print axioms compileControl_normalizes_exactly
#print axioms compile_running_has_next
#print axioms runArgMode_accepted_iff
#print axioms runArguments_accepted_iff
#print axioms runResultMode_accepted_iff
#print axioms runPlan_accepted_iff
#print axioms runPlanList_declarations_exact
#print axioms executeFamilyControl_outcome_exact
#print axioms executeControl_outcome_exact
#print axioms valid_execution_successfulDeclarations_exact
#print axioms runPlanList_occurrences_no_invention
#print axioms Canary.exact_type_success_has_no_metatype_event
#print axioms Canary.metatype_only_after_exact_failure
#print axioms Canary.unchecked_has_no_type_query
#print axioms Canary.raw_has_no_evaluation_event
#print axioms Canary.overloads_install_in_authored_order
#print axioms Canary.execution_distinctions_remain_disjoint
#print axioms compileGSLT_step_deterministic
#print axioms compileGSLT_halted_normal
#print axioms compileStep_denote_preserved
#print axioms compileStart_denote_exact
#print axioms compileStep?_none_iff_halted
#print axioms compileStep_stepBound_decreases
#print axioms compileGSLT_multiStep_denote_preserved
#print axioms compileGSLT_normalizes
#print axioms executeGSLT_step_deterministic
#print axioms executeGSLT_halted_normal
#print axioms executeStep_denote_preserved
#print axioms executeGSLT_multiStep_denote_preserved
#print axioms executeGSLT_terminal_exact
#print axioms executeStep?_none_iff_halted
#print axioms executeStep_stepBound_decreases
#print axioms executeGSLT_normalizes
#print axioms executeStep_argument_accepts
#print axioms executeStep_argument_rejects
#print axioms callGuardGSLT_step_deterministic
#print axioms callGuardGSLT_halted_normal
#print axioms callGuardStep_denote_preserved
#print axioms callGuardStep?_none_iff_halted
#print axioms callGuardStep_stepBound_decreases
#print axioms callGuardGSLT_multiStep_denote_preserved
#print axioms callGuardStart_denote_exact
#print axioms callGuardGSLT_terminal_exact
#print axioms callGuardGSLT_normalizes
#print axioms callGuardGSLT_total_exact
#print axioms callGuardGSLT_terminal_iff
#print axioms callGuardGSLT_terminal_successfulDeclarations_exact
#print axioms callGuardGSLT_total_successfulDeclarations_exact
#print axioms callGuardGSLT_total_outsideFragment
#print axioms OperationalCanary.outside_fragment_is_explicit_fallback_step
#print axioms OperationalCanary.exact_argument_step_has_no_metatype_event
#print axioms OperationalCanary.failed_argument_step_rejects_occurrence
#print axioms OperationalCanary.overload_execution_reaches_reference_observation
#print axioms OperationalCanary.rejection_and_authority_fallback_remain_distinct
#print axioms OperationalCanary.composed_overloads_install_in_authored_order
#print axioms OperationalCanary.composed_bad_type_rejects_without_fallback
#print axioms OperationalCanary.composed_open_overload_declines_to_fallback
end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
