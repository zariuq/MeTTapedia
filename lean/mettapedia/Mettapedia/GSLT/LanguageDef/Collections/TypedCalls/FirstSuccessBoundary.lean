import Mettapedia.Machines.BoundaryCore
import Mettapedia.Languages.MeTTa.HE.FirstSuccessScopedRecursiveAdequacy
import Mettapedia.Languages.MeTTa.HE.CompletedDelivery

/-!
# Shared boundaries for the scoped first-success HE worker

The entry adapter uses the actual first-success selector with invocation
types freshened against the complete configuration. Its continuation receives
the existing retained worker state, including caller stack and emitted prefix.
The selected signature controls both argument demand and the return type;
successful typing alternatives do not multiply body execution.

The source-region theorem consumes the existing earned recursive admission
derivation. It derives the worker execution and the independent contextual
source judgment, rather than taking either whole execution as a premise.
It applies to that admitted, selected source realization; it does not claim
that every other source choice is made by a native callback or runtime.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.FirstSuccessBoundary

open Mettapedia.Machines.BoundaryCore
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks
open Mettapedia.Languages.MeTTa.HE.Spec.Eval (SelectedTypePolicy)
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery (arrowType)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- The actual functions-scan checkpoint, not just a current head/value. -/
structure Site where
  space : Space
  expression : Atom
  expected : Atom
  incoming : Bindings
  depth : Nat
  candidates : List Atom
  live : List Atom
  stack : List Frame
  emitted : ResultSet

def Site.state (site : Site) : Configuration :=
  ⟨site.space, .work (.functions site.expression site.expected site.incoming
    site.depth site.candidates site.live), site.stack, site.emitted⟩

def Site.lookup (site : Site) : TypeLookup :=
  FirstSuccessRecursiveExecution.invocationTypes site.state

def Site.selection (site : Site) : FirstSuccessRecursiveStrategy.Selection :=
  FirstSuccessRecursiveStrategy.select site.space site.expression site.expected site.incoming
    site.depth site.candidates site.lookup

def Site.ready (site : Site) : Prop :=
  FirstSuccessRecursiveStrategy.selectionReady site.space site.expression site.expected site.incoming
    site.depth site.candidates site.lookup = true

structure SelectedFrame where
  site : Site
  signature : SelectedTypePolicy
  alternatives : List Bindings

def SelectedFrame.returnType (frame : SelectedFrame) : Atom :=
  if frame.signature.returnType = Atom.expressionType then Atom.undefinedType
  else frame.signature.returnType

def SelectedFrame.state (frame : SelectedFrame) : Configuration :=
  {frame.site.state with control := .work (.bindingAlternatives frame.site.expression
    frame.signature.functionType frame.returnType frame.site.depth frame.alternatives frame.site.live)}

def exhaustedState (site : Site) (errors : List Atom) (tupleEligible : Bool) : Configuration :=
  if tupleEligible then
    {site.state with control := .work (.tupleCalls site.expression site.expected site.incoming
      site.depth site.live), stack := .prepend (errors.map fun error => (error, site.incoming)) :: site.stack}
  else {site.state with control := .returning (errors.map fun error => (error, site.incoming))}

/-- A refusal/exhausted scan enters the existing fallback continuation. A
selected scan gives one retained signature frame to the continuation. -/
def entryProtocol {O : Type} (resumeRegion : Configuration → List O) :
    Protocol List Site SelectedFrame O O (· ++ ·) where
  early := fun site => match site.selection with
    | .selected _ _ => []
    | .exhausted errors eligible => resumeRegion (exhaustedState site errors eligible)
  enter := fun site => match site.selection with
    | .selected signature alternatives => [⟨site, signature, alternatives⟩]
    | .exhausted _ _ => []
  leave := fun _ answer => [answer]
  select := id

def expanded (dispatch : GroundedDispatch) (site : Site) : Configuration :=
  let entered := FirstSuccessRecursiveStrategy.enter site.space dispatch
    (.functions site.expression site.expected site.incoming site.depth site.candidates site.live) site.lookup
  {site.state with control := entered.1, stack := entered.2 ++ site.stack}

/-- The shared boundary factors the actual strategy transition. It does not
replace first-success selection by an all-candidate answer union. -/
theorem entryProtocol_run {O : Type} (resumeRegion : Configuration → List O)
    (dispatch : GroundedDispatch) (site : Site) :
    (entryProtocol resumeRegion).run (fun frame => resumeRegion frame.state) site =
      resumeRegion (expanded dispatch site) := by
  cases chosen : site.selection with
  | selected signature alternatives =>
      have chosen' := chosen
      simp only [Site.selection] at chosen'
      simp [Protocol.run, entryProtocol, chosen, expanded, FirstSuccessRecursiveStrategy.enter,
        chosen', SelectedFrame.state, SelectedFrame.returnType, Site.state]
  | exhausted errors eligible =>
      have chosen' := chosen
      simp only [Site.selection] at chosen'
      cases eligible <;>
        simp [Protocol.run, entryProtocol, chosen, expanded, FirstSuccessRecursiveStrategy.enter,
          chosen', exhaustedState, Site.state]

/-- Every actual selected entry contains exactly the one first binding,
even if the applicability service found more alternatives. -/
theorem selected_frame_singleton (site : Site) (signature : SelectedTypePolicy)
    (alternatives : List Bindings)
    (selected : site.selection = .selected signature alternatives) :
    ∃ binding, alternatives = [binding] :=
  FirstSuccessRecursiveStrategy.selected_is_singleton selected

theorem selected_frame_context (frame : SelectedFrame) :
    frame.state.space = frame.site.space ∧ frame.state.stack = frame.site.stack ∧
      frame.state.emitted = frame.site.emitted := ⟨rfl, rfl, rfl⟩

/-- Readiness covers the actual scoped applicability calls before the checked
worker takes its strategy step. -/
theorem checked_entry_step (dispatch : GroundedDispatch) (site : Site) (ready : site.ready) :
    (FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).step
      site.state = some (.silent (expanded dispatch site)) := by
  simp [FirstSuccessRecursiveExecution.Checked.machine, RecursiveMachine.Checked.guardMachine,
    FirstSuccessRecursiveExecution.Checked.blocked, FirstSuccessRecursiveStrategy.taskReady,
    FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
    FirstSuccessRecursiveExecution.scopedTypes, Site.state, Site.ready, Site.lookup,
    expanded, Transition.relabel] at ready ⊢
  rw [ready]
  rfl

abbrev WorkerOutcome := Outcome Configuration Configuration FirstSuccessRecursiveExecution.Checked.ResourceRequest
abbrev WorkerResult := ResultSet × WorkerOutcome

/-- The continuation is the existing checked scoped worker, at an explicit
finite region budget. Its result retains the full residual configuration. -/
def continueWorker (dispatch : GroundedDispatch) (budget : Nat) (state : Configuration) : List WorkerResult :=
  [(FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).run
    budget state]

theorem entryProtocol_worker_run (dispatch : GroundedDispatch) (site : Site)
    (ready : site.ready) (budget : Nat) :
    (entryProtocol (continueWorker dispatch budget)).run
      (fun frame => continueWorker dispatch budget frame.state) site =
      [(FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).run
        (budget + 1) site.state] := by
  rw [entryProtocol_run, continueWorker,
    (FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).run_succ_silent
      (checked_entry_step dispatch site ready)]

def expressionState (space : Space) (operator : Atom) (arguments : List Atom)
    (expected : Atom) (incoming : Bindings) (depth : Nat) (live : List Atom)
    (stack : List Frame) (emitted : ResultSet) : Configuration :=
  ⟨space, .work (.expression (.expression (operator :: arguments)) expected incoming
    (depth + 1) live), stack, emitted⟩

/-- Candidates are obtained from the actual expression checkpoint's scoped
query. They are not caller-supplied raw annotations or separately freshened
at a synthetic empty stack. -/
def Site.fromExpression (space : Space) (operator : Atom) (arguments : List Atom)
    (expected : Atom) (incoming : Bindings) (depth : Nat) (live : List Atom)
    (stack : List Frame) (emitted : ResultSet) : Site :=
  ⟨space, .expression (operator :: arguments), expected, incoming, depth,
    FirstSuccessRecursiveExecution.invocationTypes
      (expressionState space operator arguments expected incoming depth live stack emitted)
      incoming operator expected, live, stack, emitted⟩

theorem scoped_expression_step (dispatch : GroundedDispatch) (space : Space)
    (operator : Atom) (arguments : List Atom) (expected : Atom) (incoming : Bindings)
    (depth : Nat) (live : List Atom) (stack : List Frame) (emitted : ResultSet) :
    (FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).step
      (expressionState space operator arguments expected incoming depth live stack emitted) =
        some (.silent (Site.fromExpression space operator arguments expected incoming depth live stack emitted).state) := by
  simp [FirstSuccessRecursiveExecution.Checked.machine, RecursiveMachine.Checked.guardMachine,
    FirstSuccessRecursiveExecution.Checked.blocked, FirstSuccessRecursiveStrategy.taskReady,
    RecursiveMachine.Checked.taskReady, FirstSuccessRecursiveExecution.machine,
    FirstSuccessRecursiveExecution.next, FirstSuccessRecursiveExecution.scopedTypes,
    FirstSuccessRecursiveStrategy.enter, expressionState, Site.fromExpression, Site.state,
    Transition.relabel]

/-- The shared boundary includes the genuine call-site freshening prefix,
then first-success selection, then the existing retained continuation. -/
theorem expressionProtocol_worker_run (dispatch : GroundedDispatch) (space : Space)
    (operator : Atom) (arguments : List Atom) (expected : Atom) (incoming : Bindings)
    (depth : Nat) (live : List Atom) (stack : List Frame) (emitted : ResultSet)
    (ready : (Site.fromExpression space operator arguments expected incoming depth live stack emitted).ready)
    (budget : Nat) :
    (entryProtocol (continueWorker dispatch budget)).run
      (fun frame => continueWorker dispatch budget frame.state)
      (Site.fromExpression space operator arguments expected incoming depth live stack emitted) =
      [(FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).run
        (budget + 2) (expressionState space operator arguments expected incoming depth live stack emitted)] := by
  rw [entryProtocol_worker_run dispatch _ ready budget,
    (FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).run_succ_silent
      (scoped_expression_step dispatch space operator arguments expected incoming depth live stack emitted)]

/-- Ordinary return is a separate boundary phase. The expected type here is
the selected callee's normalized return type, not the caller's former type. -/
structure ReturnSite where
  space : Space
  original : Atom
  value : Atom
  expected : Atom
  bindings : Bindings
  depth : Nat
  live : List Atom
  stack : List Frame
  emitted : ResultSet

def ReturnSite.state (site : ReturnSite) : Configuration :=
  ⟨site.space, .work (.returned site.original site.value site.expected site.bindings
    site.depth site.live), site.stack, site.emitted⟩

def ReturnSite.deliver (site : ReturnSite) (value : Atom) : Configuration :=
  {site.state with control := .returning [(value, site.bindings)]}

def ReturnSite.evaluate (site : ReturnSite) : Configuration :=
  {site.state with control := .work (.atom site.value site.expected site.bindings site.depth site.live)}

def returnProtocol {O : Type} (resumeRegion : Configuration → List O) :
    Protocol List ReturnSite ReturnSite O O (· ++ ·) where
  early := fun site =>
    if site.value == Atom.notReducible then resumeRegion (site.deliver site.original)
    else if isEmptyOrError site.value then resumeRegion (site.deliver site.value)
    else []
  enter := fun site =>
    if site.value == Atom.notReducible then []
    else if isEmptyOrError site.value then [] else [site]
  leave := fun _ answer => [answer]
  select := id

def returnExpanded (site : ReturnSite) : Configuration :=
  if site.value == Atom.notReducible then site.deliver site.original
  else if isEmptyOrError site.value then site.deliver site.value else site.evaluate

theorem returnProtocol_run {O : Type} (resumeRegion : Configuration → List O) (site : ReturnSite) :
    (returnProtocol resumeRegion).run (fun frame => resumeRegion frame.evaluate) site =
      resumeRegion (returnExpanded site) := by
  by_cases refused : site.value = Atom.notReducible <;>
    cases stopped : isEmptyOrError site.value <;>
    simp [Protocol.run, returnProtocol, returnExpanded, refused, stopped]

theorem checked_return_step (dispatch : GroundedDispatch) (site : ReturnSite) :
    (FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).step
      site.state = some (.silent (returnExpanded site)) := by
  by_cases refused : site.value = Atom.notReducible <;>
    cases stopped : isEmptyOrError site.value <;>
    simp [FirstSuccessRecursiveExecution.Checked.machine, RecursiveMachine.Checked.guardMachine,
      FirstSuccessRecursiveExecution.Checked.blocked, FirstSuccessRecursiveStrategy.taskReady,
      RecursiveMachine.Checked.taskReady, FirstSuccessRecursiveExecution.machine,
      FirstSuccessRecursiveExecution.next, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      ReturnSite.state, ReturnSite.deliver, ReturnSite.evaluate, returnExpanded,
      refused, stopped, Transition.relabel]

/-- Return resumption uses the same shared algebra and the same actual
scoped worker, at every continuation budget, including resource suspension. -/
theorem returnProtocol_worker_run (dispatch : GroundedDispatch) (site : ReturnSite) (budget : Nat) :
    (returnProtocol (continueWorker dispatch budget)).run
      (fun frame => continueWorker dispatch budget frame.evaluate) site =
      [(FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).run
        (budget + 1) site.state] := by
  rw [returnProtocol_run, continueWorker,
    (FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).run_succ_silent
      (checked_return_step dispatch site)]

/-- Exhausted evaluation depth retains the typed return receiver. It is a
resource suspension, not a completed empty answer batch. -/
theorem returned_zero_depth_suspends (dispatch : GroundedDispatch) (site : ReturnSite)
    (ordinary : site.value ≠ Atom.notReducible) (active : isEmptyOrError site.value = false)
    (empty : site.depth = 0) :
    (FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).run
      2 site.state = ([], .suspended .evaluationDepth site.evaluate) := by
  rw [(FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).run_succ_silent
    (checked_return_step dispatch site)]
  have target : returnExpanded site = site.evaluate := by simp [returnExpanded, ordinary, active]
  rw [target]
  apply FirstSuccessRecursiveExecution.Checked.blocked_run
  simp [FirstSuccessRecursiveExecution.Checked.blocked, ReturnSite.evaluate, ReturnSite.state,
    FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady, empty, Task.depth]

theorem returned_zero_depth_not_finished (dispatch : GroundedDispatch) (site : ReturnSite)
    (ordinary : site.value ≠ Atom.notReducible) (active : isEmptyOrError site.value = false)
    (empty : site.depth = 0) :
    ¬ ∃ final, (FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).run
      2 site.state = ([], .finished final) := by
  rw [returned_zero_depth_suspends dispatch site ordinary active empty]
  simp

open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.FirstSuccessScopedAdequacy.ScopedRetainedRelation
open Mettapedia.Languages.MeTTa.HE.FirstSuccessScopedAdequacy.UniversalScopedPolymorphicApplication

section Earned

variable {space : Space} {dispatch : Mettapedia.Languages.MeTTa.HE.GroundedDispatch}
  {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Completed.Policy}
  {wEmitted : ResultSet} {cEmitted : List Completed.Result}
  {fuel steps : Nat} {wLive cLive : List Atom} {scope : List String}
  {value : Atom} {ctxVal : Entry.Value} {expected : Atom}
  {wB : Bindings} {cFrame : Completed.Frame}
  {wStack : List RecursiveTasks.Frame}
  {cStack : List RecursiveTasks.Contextual.Continuation}
  {wResults : ResultSet} {cResults : List Completed.Result}

/-- Existing structural/source admission earns both executions and the
ordered occurrence relation at the exact retained caller boundary. The
default admission profile has no external atom-branch realization premise. -/
theorem earned_region
    (derivation : ScopedAtomDerivation space dispatch hostDispatch policy
      wEmitted cEmitted fuel wLive cLive scope value ctxVal expected wB cFrame
      wStack cStack steps wResults cResults) :
    (∀ budget,
      (FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).run
        (steps + budget) ⟨space, .work (.atom value expected wB fuel wLive), wStack, wEmitted⟩ =
      (FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).run
        budget ⟨space, .returning wResults, wStack, wEmitted⟩) ∧
    Completed.AtomRel space hostDispatch Completed.scopedLookup cLive scope
      ctxVal expected cFrame cResults (policy := policy) ∧
    RecursiveMachine.Contextual.LocalSteps space hostDispatch Completed.scopedLookup policy
      (.work (.atom cLive scope ctxVal expected cFrame), cStack)
      (.returning cResults, cStack) ∧
    List.Forall₂ ScopedResultRel wResults cResults := by
  have runs := derivation.task_run
  exact ⟨runs.worker_run, derivation.to_completed_atomRel, runs.contextual_steps, runs.results_rel⟩

/-- The region cannot invent or lose an endpoint result, caller frame, or
published prefix. This iff is about the admitted selected realization, not
about arbitrary alternative source derivations. -/
theorem earned_endpoint_iff
    (derivation : ScopedAtomDerivation space dispatch hostDispatch policy
      wEmitted cEmitted fuel wLive cLive scope value ctxVal expected wB cFrame
      wStack cStack steps wResults cResults)
    (results : ResultSet) (stack : List RecursiveTasks.Frame) (emitted : ResultSet) :
    (FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).run
      steps ⟨space, .work (.atom value expected wB fuel wLive), wStack, wEmitted⟩ =
        ([], .exhausted ⟨space, .returning results, stack, emitted⟩) ↔
      results = wResults ∧ stack = wStack ∧ emitted = wEmitted := by
  have completed := derivation.task_run.worker_run 0
  simp only [Nat.add_zero] at completed
  rw [completed]
  simp only [Machine.run, Prod.mk.injEq, true_and,
    Outcome.exhausted.injEq, Configuration.mk.injEq, Control.returning.injEq]
  constructor <;> intro h <;> exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

/-- Same-position correspondence is two-sided and preserves physical
duplicates. Binding frames remain related rather than being erased. -/
theorem earned_occurrence_alignment
    (derivation : ScopedAtomDerivation space dispatch hostDispatch policy
      wEmitted cEmitted fuel wLive cLive scope value ctxVal expected wB cFrame
      wStack cStack steps wResults cResults) :
    wResults.length = cResults.length ∧
      ∀ (i : Nat) (hw : i < wResults.length) (hc : i < cResults.length),
        ScopedResultRel (wResults.get ⟨i, hw⟩) (cResults.get ⟨i, hc⟩) := by
  have paired := derivation.task_run.results_rel
  exact ⟨paired.length_eq, fun _ hw hc => paired.get hw hc⟩

end Earned

namespace Controls

def numberArrow : Atom := arrowType [.symbol "Number"] (.symbol "Number")
def stringArrow : Atom := arrowType [.symbol "String"] (.symbol "String")
def numericSignature : SelectedTypePolicy :=
  ⟨numberArrow, [.symbol "Number"], .symbol "Number", rfl⟩

def source : Space := Space.ofList [
  .expression [.symbol ":", .symbol "f", stringArrow],
  .expression [.symbol ":", .symbol "f", numberArrow]]

def retainedSite : Site :=
  ⟨source, .expression [.symbol "f", .grounded (.int 7)], .symbol "Number",
    Bindings.empty, 12, [stringArrow, numberArrow], [.var "live"],
    [.calls Atom.undefinedType 4 [.var "caller"]], [(.var "published", Bindings.empty)]⟩

/-- This selected-call fixture comes from the actual scoped invocation
lookup at its expression checkpoint, not an invented candidate list. -/
theorem retainedSite_from_expression :
    Site.fromExpression source (.symbol "f") [.grounded (.int 7)] (.symbol "Number")
      Bindings.empty 12 [.var "live"] [.calls Atom.undefinedType 4 [.var "caller"]]
      [(.var "published", Bindings.empty)] = retainedSite := by
  cbv

/-- A failed earlier candidate does not prevent the first successful one;
the retained caller and publication context participates in scoped lookup. -/
theorem selected_after_rejection :
    retainedSite.selection = .selected numericSignature [Bindings.empty] := by
  cbv

theorem selected_ready : retainedSite.ready := by
  unfold Site.ready
  decide +kernel

theorem selected_step_keeps_context :
    (entryProtocol (fun state => [state])).run (fun frame => [frame.state]) retainedSite =
      [({retainedSite.state with control := .work (.bindingAlternatives
        retainedSite.expression numberArrow (.symbol "Number")
          retainedSite.depth [Bindings.empty] retainedSite.live)} : Configuration)] := by
  simp [Protocol.run, entryProtocol, selected_after_rejection, SelectedFrame.state,
    SelectedFrame.returnType, numericSignature, Atom.expressionType]

/-- Repeated applicability candidates do not create two body activations. -/
def repeatedSite : Site := {retainedSite with candidates := [numberArrow, numberArrow]}

theorem repeated_selection_is_one :
    repeatedSite.selection = .selected numericSignature [Bindings.empty] := by cbv

theorem repeated_candidates_do_not_duplicate_entry :
    ((entryProtocol (fun state => [state])).enter repeatedSite).length = 1 ∧
      ((entryProtocol (fun state => [state])).enter repeatedSite).length ≠ 2 := by
  simp [entryProtocol, repeated_selection_is_one]

/-- The selected return type is not replaced by the caller's expected type.
Expression retains the existing special return normalization. -/
def expressionSignature : SelectedTypePolicy :=
  ⟨arrowType [] Atom.expressionType, [], Atom.expressionType, rfl⟩

theorem expression_return_is_undefined :
    (SelectedFrame.mk retainedSite expressionSignature [Bindings.empty]).returnType = Atom.undefinedType ∧
      (SelectedFrame.mk retainedSite expressionSignature [Bindings.empty]).returnType ≠ retainedSite.expected := by
  constructor <;> decide

def retainedReturn : ReturnSite :=
  ⟨source, retainedSite.expression, .grounded (.int 7), .symbol "String", Bindings.empty,
    0, retainedSite.live, retainedSite.stack, retainedSite.emitted⟩

theorem pending_cast_keeps_range_and_context :
    (FirstSuccessRecursiveExecution.Checked.machine Mettapedia.Languages.MeTTa.HE.GroundedDispatch.none
      FirstSuccessRecursiveExecution.scopedTypes).run 2 retainedReturn.state =
      ([], .suspended .evaluationDepth retainedReturn.evaluate) ∧
    retainedReturn.evaluate.control =
      .work (.atom (.grounded (.int 7)) (.symbol "String") Bindings.empty 0 retainedSite.live) ∧
    retainedReturn.evaluate.stack = retainedSite.stack ∧
    retainedReturn.evaluate.emitted = retainedSite.emitted := by
  exact ⟨returned_zero_depth_suspends _ retainedReturn (by decide) rfl rfl, rfl, rfl, rfl⟩

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.FirstSuccessBoundary
