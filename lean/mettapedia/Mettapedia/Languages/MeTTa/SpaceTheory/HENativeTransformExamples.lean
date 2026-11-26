import Mettapedia.Languages.MeTTa.SpaceTheory.HEArgumentPaths
import Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls

/-! Native-effect and denied-operation controls on the actual Transform step. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HENativeTransformExamples

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Frame Policy Result)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (WorldConfiguration Continuation Task)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (WorldStepWith)
open Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls
  (World services environment execute)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (ReadsBag exists_reads)
open HEFocused (Focus NativeRequest Parent)
open HENativeOnTransform
open HEControlOnTransform (Shows source source_of_focus return_and_publish_path)

/-- The two stores remain named even when their atom lists agree. -/
def code : Presentation Bool World where
  context b := .grounded (.bool b)
  world w := .expression [.expression (w false), .expression (w true)]
  context_injective := by intro a b e; simpa using e
  world_injective := by
    intro a b e
    have same : a false = b false ∧ a true = b true := by simpa using e
    funext label
    cases label
    · exact same.1
    · exact same.2

private def world : World := fun child => if child then [] else [.symbol "outside"]
private def updated : World := Function.update world true [.symbol "token"]
private def parents : List (Parent Bool) := [⟨false, [.singleton]⟩]
private def published : List Result := [(.symbol "already-published", Frame.empty)]
private def request : NativeRequest :=
  ⟨[], [], none, .active, .symbol "model-store", .symbol "silent-put", .symbol "token", Frame.empty⟩

private theorem authorized :
    services.nativeCall true world request.name.erase request.operation.erase request.argument.erase
      request.frame [] updated := by
  simp [services, execute, Entry.Value.erase, world, updated, request]

private def pending : Focus Bool World := ⟨world, true, .work request.task, [], parents, published⟩
private def returned : Focus Bool World := ⟨updated, true, .returning [], [], parents, published⟩

theorem child_effect_in_the_source :
    WorldStepWith environment.arguments environment.view services environment.dispatch environment.lookup .unmarked
      (HEFocused.restore pending) (HEFocused.restore returned) := by
  apply HEFocused.restore_step
  exact (HEFocused.native_step_iff request world true [] parents published returned).mpr
    ⟨[], updated, authorized, rfl⟩

/-- An answerless edit is still a firing. It changes the child's space,
retains the inactive parent, and does not publish an answer occurrence. -/
theorem answerless_child_effect_fires :
    ∃ start after,
      ReadsBag start {requestAtom code request world true [] parents published} ∧
      (HEControlOnTransform.theory Nat code environment .unmarked).Step start after ∧
      ReadsBag after {returnAtom code updated true [] [] parents published} ∧
      updated true = [.symbol "token"] ∧ updated false = world false := by
  obtain ⟨start, shown⟩ := exists_reads {requestAtom code request world true [] parents published}
  have initial : Shows code (HEFocused.restore pending) start := by
    simpa only [Shows, HEFocused.focus_restore, pending, HEControlOnTransform.encode_native] using shown
  have step : (source environment .unmarked).Step (HEFocused.restore pending) (HEFocused.restore returned) :=
    ⟨by rw [HEFocused.focus_restore]; exact Or.inl ⟨request, NativeRequest.recognize_task request⟩,
      child_effect_in_the_source⟩
  obtain ⟨final, fired, last⟩ := HEControlOnTransform.realize_step environment .unmarked code initial step
  have endpoint : ReadsBag final {returnAtom code updated true [] [] parents published} := by
    simpa only [Shows, HEFocused.focus_restore, returned, HEControlOnTransform.encode_return] using last
  exact ⟨start, final, shown, fired, endpoint, by simp [updated], by simp [updated]⟩

private def denied : NativeRequest := { request with name := .symbol "other-service" }

/-- The same request shape, with an unprovided service, cannot fire. -/
theorem wrong_service_cannot_fire {start final}
    (shown : ReadsBag start {requestAtom code denied world true [] parents published}) :
    ¬ (HEControlOnTransform.theory Nat code environment .unmarked).Step start final := by
  intro fired
  let rejected : Focus Bool World := ⟨world, true, .work denied.task, [], parents, published⟩
  have initial : Shows code (HEFocused.restore rejected) start := by
    simpa only [Shows, HEFocused.focus_restore, rejected, HEControlOnTransform.encode_native] using shown
  obtain ⟨after, ⟨_, moved⟩, _⟩ := HEControlOnTransform.reflect_step environment .unmarked code initial fired
  have focused := HEFocused.focus_step moved
  rw [HEFocused.focus_restore] at focused
  obtain ⟨_, _, allowed, _⟩ :=
    (HEFocused.native_step_iff denied world true [] parents published _).mp focused
  simp [environment, services, denied, Entry.Value.erase] at allowed

section Mixed

open Mettapedia.GSLT.IndexedOperational (ExecutionPath)
open Mettapedia.GSLT.Ultrainfinite (Route)

private def caller : List (Parent Bool) := [⟨false, []⟩]

private def callFrom (before : World) (action : NativeRequest) : Focus Bool World :=
  ⟨before, true, .work action.task, [], caller, published⟩

private def finishAt (after : World) (answers : List Result) : Focus Bool World :=
  ⟨after, false, .returning [], [], [], published ++ answers⟩

private theorem one_call_through_return (before after : World) (action : NativeRequest) (answers : List Result)
    (effect : services.nativeCall true before action.name.erase action.operation.erase action.argument.erase
      action.frame answers after) :
    ∃ start final, Shows code (HEFocused.restore (callFrom before action)) start ∧
      ∃ path : ExecutionPath (HEControlOnTransform.theory Nat code environment .unmarked) start final,
        Shows code (HEFocused.restore (finishAt after answers)) final ∧ path.length = answers.length + 2 := by
  obtain ⟨start, read⟩ := exists_reads {HEControlOnTransform.encodeFocus code (callFrom before action)}
  have shown : Shows code (HEFocused.restore (callFrom before action)) start := by
    simpa only [Shows, HEFocused.focus_restore] using read
  have captured :
      HEFocused.Move environment.arguments environment.view services environment.dispatch environment.lookup .unmarked
        (callFrom before action) ⟨after, true, .returning answers, [], caller, published⟩ :=
    (HEFocused.native_step_iff action before true [] caller published _).mpr ⟨answers, after, effect, rfl⟩
  have called := source_of_focus environment .unmarked
    (show HEControlOnTransform.Covered (callFrom before action) from Or.inl ⟨action, NativeRequest.recognize_task action⟩)
    captured
  have empty : ∀ store ∈ caller, store.stack = [] := by
    simp [caller]
  obtain ⟨returning, controlCost⟩ := return_and_publish_path environment .unmarked after true answers published caller empty
  let run : ExecutionPath (source environment .unmarked)
      (HEFocused.restore (callFrom before action)) (HEFocused.restore (finishAt after answers)) :=
    .cons ⟨called⟩ returning
  obtain ⟨final, firings, done, cost⟩ := HEControlOnTransform.realize_path environment .unmarked code shown run
  refine ⟨start, final, shown, firings, done, cost.trans ?_⟩
  change returning.length + 1 = answers.length + 2
  rw [controlCost]
  rfl

private def write : NativeRequest := { request with operation := .symbol "put" }
private def reply : Result := (.expression .active [], Frame.empty)

/-- The child writes, returns to its distinct parent, and publishes one
reply, with three actual firings in the same program. -/
theorem mixed_effect_run :
    ∃ start final, Shows code (HEFocused.restore (callFrom world write)) start ∧
      ∃ path : ExecutionPath (HEControlOnTransform.theory Nat code environment .unmarked) start final,
        Shows code (HEFocused.restore (finishAt updated [reply])) final ∧ path.length = 3 := by
  exact one_call_through_return world updated write [reply] (by
    simp [services, execute, Entry.Value.erase, Entry.Value.ofAtom, world, updated, write, request, reply])

private def twoTokens : World := Function.update world true [.symbol "token", .symbol "token"]
private def inspect : NativeRequest := { request with operation := .symbol "read" }
private def token : Result := (.symbol "token", Frame.empty)

theorem mixed_duplicate_run :
    ∃ start final, Shows code (HEFocused.restore (callFrom twoTokens inspect)) start ∧
      ∃ path : ExecutionPath (HEControlOnTransform.theory Nat code environment .unmarked) start final,
        Shows code (HEFocused.restore (finishAt twoTokens [token, token])) final ∧ path.length = 4 := by
  exact one_call_through_return twoTokens twoTokens inspect [token, token] (by
    simp [services, execute, Entry.Value.erase, Entry.Value.ofAtom, twoTokens, inspect, request, token])

/-- Even given a real input and a real firing, a child cannot bypass return
and make a pending occurrence visible as an outer publication. -/
theorem child_cannot_publish {start final}
    (initial : Shows code (HEFocused.restore ⟨updated, true, .returning [reply], [], caller, published⟩) start)
    (claimed : Shows code (HEFocused.restore (finishAt updated [reply])) final) :
    ¬ (HEControlOnTransform.theory Nat code environment .unmarked).Step start final := by
  intro fired
  obtain ⟨after, ⟨_, moved⟩, observed⟩ :=
    HEControlOnTransform.reflect_step environment .unmarked code initial fired
  have actual := HEControlOnTransform.shows_unique code observed claimed
  subst after
  have focused := HEFocused.focus_step moved
  rw [HEFocused.focus_restore, HEFocused.focus_restore] at focused
  have retained := HEFocused.no_inner_publication focused (by simp [caller])
  have count := congrArg List.length retained
  simp [finishAt, published] at count

end Mixed

section ContextInstructions

open Mettapedia.GSLT.IndexedOperational (ExecutionPath)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Task)
open HEContextEntry (Request)

private def collisionHost : Completed.WorldEnvironment Bool World :=
  { environment with services := { services with contextPayload := fun _ => .int 0 } }

private def enterEval : Request :=
  ⟨[], [], none, .active, .evalc (.symbol "held-by-parent") (.int 0), Frame.empty⟩

private def entering (action : Request) : Focus Bool World :=
  ⟨world, false, .work action.task, [.singleton], [], published⟩

private def inside (child : Bool) (work : Task) : Focus Bool World :=
  ⟨world, child, .work work, [], [⟨false, [.singleton]⟩], published⟩

private def invocation : Task :=
  .invocation [] [] none (Frame.empty.read .unmarked (.symbol "held-by-parent")) Frame.empty

private theorem choose_context (child : Bool) :
    (source collisionHost .unmarked).Step
      (HEFocused.restore (entering enterEval)) (HEFocused.restore (inside child invocation)) := by
  apply source_of_focus collisionHost .unmarked
  · exact Or.inr (Or.inl ⟨enterEval, Request.recognize_task enterEval⟩)
  · exact (HEContextEntry.step_iff enterEval world false [.singleton] [] published _).mpr ⟨child, rfl, rfl⟩

/-- A handle shared by two different spaces cannot authorize an arbitrary
choice of just one of them. Both source choices survive and their target
endpoints are different. -/
theorem colliding_handle_preserves_both_children :
    ∃ start first second,
      Shows code (HEFocused.restore (entering enterEval)) start ∧
      (HEControlOnTransform.theory Nat code collisionHost .unmarked).Step start first ∧
      (HEControlOnTransform.theory Nat code collisionHost .unmarked).Step start second ∧
      Shows code (HEFocused.restore (inside false invocation)) first ∧
      Shows code (HEFocused.restore (inside true invocation)) second ∧
      first ≠ second ∧ world false ≠ world true := by
  obtain ⟨start, read⟩ := exists_reads {HEControlOnTransform.encodeFocus code (entering enterEval)}
  have shown : Shows code (HEFocused.restore (entering enterEval)) start := by
    simpa only [Shows, HEFocused.focus_restore] using read
  obtain ⟨first, quiet, firstChild⟩ :=
    HEControlOnTransform.realize_step collisionHost .unmarked code shown (choose_context false)
  obtain ⟨second, other, secondChild⟩ :=
    HEControlOnTransform.realize_step collisionHost .unmarked code shown (choose_context true)
  refine ⟨start, first, second, shown, quiet, other, firstChild, secondChild, ?_, by simp [world]⟩
  intro same
  subst second
  have worlds := HEControlOnTransform.shows_unique code firstChild secondChild
  have scopes := congrArg (fun state : WorldConfiguration Bool World => (HEFocused.focus state).scope) worlds
  simp only [HEFocused.focus_restore, inside] at scopes
  cases scopes

private def missingHandle : Request :=
  { enterEval with instruction := .evalc (.symbol "held-by-parent") (.int 1) }

theorem unknown_handle_has_no_firing {start final}
    (shown : Shows code (HEFocused.restore (entering missingHandle)) start) :
    ¬ (HEControlOnTransform.theory Nat code collisionHost .unmarked).Step start final := by
  intro fired
  obtain ⟨after, ⟨_, step⟩, _⟩ :=
    HEControlOnTransform.reflect_step collisionHost .unmarked code shown fired
  have moved := HEFocused.focus_step step
  rw [HEFocused.focus_restore] at moved
  have result := (HEContextEntry.step_iff missingHandle world false [.singleton] [] published (HEFocused.focus after)).mp moved
  obtain ⟨child, names, _⟩ := result
  cases names

private def requestMetta : Request :=
  ⟨[], [], none, .active, .metta (.expression .held [.symbol "f"]) (.symbol "Atom") (.int 1), Frame.empty⟩

private def explicitDemand : Task :=
  .atom [] [] (.expression .held [.symbol "f"]) (.symbol "Atom") Frame.empty

theorem metta_passes_the_explicit_type_to_the_child :
    ∃ start final, Shows code (HEFocused.restore (entering requestMetta)) start ∧
      (HEControlOnTransform.theory Nat code environment .unmarked).Step start final ∧
      Shows code (HEFocused.restore (inside true explicitDemand)) final := by
  obtain ⟨start, read⟩ := exists_reads {HEControlOnTransform.encodeFocus code (entering requestMetta)}
  have shown : Shows code (HEFocused.restore (entering requestMetta)) start := by
    simpa only [Shows, HEFocused.focus_restore] using read
  have sourceStep : (source environment .unmarked).Step (HEFocused.restore (entering requestMetta))
      (HEFocused.restore (inside true explicitDemand)) := by
    apply source_of_focus environment .unmarked
    · exact Or.inr (Or.inl ⟨requestMetta, Request.recognize_task requestMetta⟩)
    · apply (HEContextEntry.step_iff requestMetta world false [.singleton] [] published _).mpr
      exact ⟨true, rfl, by simp [inside, explicitDemand, requestMetta, Entry.Value.erase]⟩
  obtain ⟨final, fired, result⟩ := HEControlOnTransform.realize_step environment .unmarked code shown sourceStep
  exact ⟨start, final, shown, fired, result⟩

private def currentRequest : Request := ⟨[], [], none, .active, .contextSpace, Frame.empty⟩
private def currentInput : Focus Bool World := ⟨updated, true, .work currentRequest.task, [], caller, published⟩
private def currentReply : Result := (.grounded (.int 1), Frame.empty)

/-- A child returns its own handle even after the space changes. The
combined program then returns to the parent and publishes that handle. -/
theorem current_handle_round_trip :
    ∃ start final, Shows code (HEFocused.restore currentInput) start ∧
      ∃ path : ExecutionPath (HEControlOnTransform.theory Nat code environment .unmarked) start final,
        Shows code (HEFocused.restore (finishAt updated [currentReply])) final ∧ path.length = 3 := by
  obtain ⟨start, read⟩ := exists_reads {HEControlOnTransform.encodeFocus code currentInput}
  have initial : Shows code (HEFocused.restore currentInput) start := by
    simpa only [Shows, HEFocused.focus_restore] using read
  have moved :
      HEFocused.Move environment.arguments environment.view services environment.dispatch environment.lookup .unmarked
        currentInput ⟨updated, true, .returning [currentReply], [], caller, published⟩ :=
    (HEContextEntry.step_iff currentRequest updated true [] caller published _).mpr rfl
  have looked := source_of_focus environment .unmarked
    (show HEControlOnTransform.Covered currentInput from
      Or.inr (Or.inl ⟨currentRequest, Request.recognize_task currentRequest⟩)) moved
  have empty : ∀ saved ∈ caller, saved.stack = [] := by simp [caller]
  obtain ⟨returning, count⟩ :=
    return_and_publish_path environment .unmarked updated true [currentReply] published caller empty
  let path : ExecutionPath (source environment .unmarked) (HEFocused.restore currentInput)
      (HEFocused.restore (finishAt updated [currentReply])) := .cons ⟨looked⟩ returning
  obtain ⟨final, fired, done, length⟩ := HEControlOnTransform.realize_path environment .unmarked code initial path
  refine ⟨start, final, initial, fired, done, length.trans ?_⟩
  change returning.length + 1 = 3
  rw [count]
  rfl

end ContextInstructions

section TypedEntry

open Mettapedia.GSLT.IndexedOperational (ExecutionPath)
open Mettapedia.Languages.MeTTa.HE (Space Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Type
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Task)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions (RelationStep)

private def actionAsData : Entry.Value :=
  .expression .active [.symbol "call-native", .symbol "model-store", .symbol "put", .symbol "token"]

private def rawMetta : HEContextEntry.Request :=
  ⟨[], [], none, .active, .metta actionAsData (.symbol "Atom") (.int 1), Frame.empty⟩

private def rawDemand : HEAtomEntry.Request := ⟨[], [], actionAsData, Atom.atomType, Frame.empty⟩

private def rootRequest : Focus Bool World := ⟨world, false, .work rawMetta.task, [], [], published⟩
private def rawChild : Focus Bool World := ⟨world, true, .work rawDemand.task, [], caller, published⟩
private def rawReply : Result := (rawDemand.read .unmarked, Frame.empty)
private def rawReturned : Focus Bool World := ⟨world, true, .returning [rawReply], [], caller, published⟩

private theorem demand_step :
    (source environment .unmarked).Step (HEFocused.restore rootRequest) (HEFocused.restore rawChild) := by
  apply source_of_focus environment .unmarked
  · exact Or.inr (Or.inl ⟨rawMetta, HEContextEntry.Request.recognize_task rawMetta⟩)
  · apply (HEContextEntry.step_iff rawMetta world false [] [] published _).mpr
    exact ⟨true, rfl, by
      simp [rawChild, rawDemand, rawMetta, caller, Atom.atomType, Entry.Value.erase, HEAtomEntry.Request.task]⟩

/-- A complete run through context entry and typed delivery. A write-shaped
operand is returned as data and the encoded world remains unchanged. -/
theorem atom_demand_round_trip :
    ∃ start final, Shows code (HEFocused.restore rootRequest) start ∧
      ∃ path : ExecutionPath (HEControlOnTransform.theory Nat code environment .unmarked) start final,
        Shows code (HEFocused.restore (finishAt world [rawReply])) final ∧ path.length = 4 := by
  obtain ⟨start, read⟩ := exists_reads {HEControlOnTransform.encodeFocus code rootRequest}
  have initial : Shows code (HEFocused.restore rootRequest) start := by
    simpa only [Shows, HEFocused.focus_restore] using read
  have delivery : (source environment .unmarked).Step (HEFocused.restore rawChild) (HEFocused.restore rawReturned) := by
    apply source_of_focus environment .unmarked
    · exact HEControlOnTransform.covered_atom rawDemand _ _ _ _ _
    · exact (HEAtomEntry.atom_demand_iff environment .unmarked rawDemand rfl world true [] caller published _).mpr rfl
  have empty : ∀ saved ∈ caller, saved.stack = [] := by simp [caller]
  obtain ⟨tail, count⟩ := return_and_publish_path environment .unmarked world true [rawReply] published caller empty
  let path : ExecutionPath (source environment .unmarked) (HEFocused.restore rootRequest)
      (HEFocused.restore (finishAt world [rawReply])) := .cons ⟨demand_step⟩ (.cons ⟨delivery⟩ tail)
  obtain ⟨final, fired, done, length⟩ := HEControlOnTransform.realize_path environment .unmarked code initial path
  refine ⟨start, final, initial, fired, done, length.trans ?_⟩
  change tail.length + 1 + 1 = 4
  rw [count]
  rfl

theorem atom_demand_rejects_spurious_write {start final}
    (initial : Shows code (HEFocused.restore rawChild) start)
    (claimed : Shows code (HEFocused.restore { rawReturned with world := updated }) final) :
    ¬ (HEControlOnTransform.theory Nat code environment .unmarked).Step start final := by
  intro fired
  obtain ⟨next, ⟨_, moved⟩, real⟩ := HEControlOnTransform.reflect_step environment .unmarked code initial fired
  have endpoint := HEControlOnTransform.shows_unique code real claimed
  subst next
  have focused := HEFocused.focus_step moved
  rw [HEFocused.focus_restore, HEFocused.focus_restore] at focused
  have follows := (HEAtomEntry.atom_demand_iff environment .unmarked rawDemand rfl world true [] caller published _).mp focused
  have same := congrArg (fun state : Focus Bool World => state.world true) follows
  simp [updated, world] at same

private def tupleDemand : HEAtomEntry.Request :=
  ⟨[], [], .expression .active [.symbol "operator", .symbol "operand"], Atom.undefinedType, Frame.empty⟩

private def annotated : World :=
  Function.update world true [.expression [.symbol ":", .symbol "operator", .symbol "SomeType"]]

private theorem operator_annotation :
    AnnotationTypesRel (.symbol "operator") (environment.view annotated true).atoms [Atom.symbol "SomeType"] := by
  simpa [environment, annotated] using
    (show AnnotationTypesRel (.symbol "operator") [.expression [.symbol ":", .symbol "operator", .symbol "SomeType"]]
      [Atom.symbol "SomeType"] from .hit .nil)

private theorem tuple_license :
    HEAtomEntry.Licensed environment.arguments (environment.view world true) environment.lookup .unmarked tupleDemand
      (.tuple (.symbol "operator") [.symbol "operand"]) := by
  refine ⟨?_, ⟨.active, ?_⟩, ?_⟩
  · have classified : Entry.Rel .reinterpret .active
        (.expression [.symbol "operator", .symbol "operand"]) Atom.undefinedType .interpret := by
      apply Entry.Rel.expression
      · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
      · simp [Atom.undefinedType, Atom.atomType, Atom.expressionType, Atom.variableType]
      · exact Or.inl rfl
    simpa [HEAtomEntry.Request.action, HEAtomEntry.Request.read, tupleDemand, HEAtomEntry.Reply.action,
      Entry.Value.status, Entry.Value.erase, Policy.unmarked] using classified
  · simp [HEAtomEntry.Request.read, tupleDemand]
  · simpa [environment, world, Entry.Value.erase, withUndefined, annotationOccurrences] using
      (TypeOccurrencesRel.symbol (atoms := 0) "operator")

theorem untyped_tuple_enters_on_transform :
    ∃ start final,
      Shows code (HEFocused.restore ⟨world, true, .work tupleDemand.task, [], [], published⟩) start ∧
      (HEControlOnTransform.theory Nat code environment .unmarked).Step start final ∧
      let next := HEAtomEntry.continuation .unmarked tupleDemand (.tuple (.symbol "operator") [.symbol "operand"])
      Shows code (HEFocused.restore ⟨world, true, next.1, next.2, [], published⟩) final := by
  let before : Focus Bool World := ⟨world, true, .work tupleDemand.task, [], [], published⟩
  obtain ⟨start, read⟩ := exists_reads {HEControlOnTransform.encodeFocus code before}
  have initial : Shows code (HEFocused.restore before) start := by
    simpa only [Shows, HEFocused.focus_restore] using read
  let reply : HEAtomEntry.Reply := .tuple (.symbol "operator") [.symbol "operand"]
  let next := HEAtomEntry.continuation .unmarked tupleDemand reply
  have step : (source environment .unmarked).Step (HEFocused.restore before)
      (HEFocused.restore ⟨world, true, next.1, next.2, [], published⟩) := by
    apply source_of_focus environment .unmarked
    · exact HEControlOnTransform.covered_atom tupleDemand _ _ _ _ _
    · apply (HEAtomEntry.step_iff environment .unmarked tupleDemand world true [] [] published _).mpr
      exact ⟨reply, tuple_license, by simp only [List.append_nil, next]⟩
  obtain ⟨final, fired, done⟩ := HEControlOnTransform.realize_step environment .unmarked code initial step
  exact ⟨start, final, initial, fired, done⟩

/-- Updating the active declarations blocks the untyped-tuple rule,
without forcing other interpretation branches to have no answer. -/
theorem assignment_blocks_the_untyped_tuple_rule (after) :
    ¬ RelationStep (HEAtomOnTransform.operations code environment .unmarked) (HEAtomOnTransform.rule .tuple)
      {HEAtomOnTransform.requestAtom code tupleDemand annotated true [] [] published} after := by
  intro fired
  obtain ⟨reply, branch, licensed, _⟩ :=
    (HEAtomOnTransform.rule_exact code environment .unmarked .tuple tupleDemand annotated true [] [] published after).mp fired
  cases reply <;> cases branch
  case tuple head arguments =>
    obtain ⟨⟨readiness, expression⟩, types⟩ := licensed.2
    simp [HEAtomEntry.Request.read, tupleDemand] at expression
    obtain ⟨_, rfl, rfl⟩ := expression
    have declared : TypeOccurrencesRel ((environment.view annotated true).atoms : Multiset Atom)
        (.symbol "operator") {Atom.symbol "SomeType"} := by
      simpa [withUndefined, operator_annotation.occurrences] using
        (TypeOccurrencesRel.symbol (atoms := ((environment.view annotated true).atoms : Multiset Atom)) "operator")
    have exactType : TypeOccurrencesRel ((environment.view annotated true).atoms : Multiset Atom)
        (.symbol "operator") {Atom.undefinedType} := by simpa [Entry.Value.erase] using types
    have same := Multiset.singleton_inj.mp (declared.unique exactType)
    simp [Atom.undefinedType] at same

private def castDemand : HEAtomEntry.Request :=
  ⟨[], [], .symbol "operator", Atom.undefinedType, Frame.empty⟩

private def castAnswer : Result := (.symbol "operator", Frame.empty)

private theorem cast_license :
    HEAtomEntry.Licensed environment.arguments (environment.view annotated true) environment.lookup .unmarked castDemand
      (.cast [castAnswer]) := by
  have action : Entry.Rel .reinterpret .active (.symbol "operator") Atom.undefinedType .cast := by
    apply Entry.Rel.cast
    · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · exact .symbol _
    · simp [Atom.undefinedType, Atom.atomType, Atom.symbolType, Atom.variableType]
    · exact Or.inl ⟨"operator", rfl⟩
    · intro _
      exact Or.inl rfl
  refine ⟨?_, [(.symbol "operator", Bindings.empty)], ?_, ?_⟩
  · simpa [HEAtomEntry.Request.action, HEAtomEntry.Request.read, castDemand, HEAtomEntry.Reply.action,
      Entry.Value.status, Entry.Value.erase, Policy.unmarked] using action
  · have query : rawTypeLookupRel (environment.view annotated true) Bindings.empty
        (.symbol "operator") Atom.undefinedType [.symbol "SomeType"] :=
      StorageTypesRel.symbolKnown operator_annotation (by simp)
    have typed : TypeCastBatchRel (environment.view annotated true) (.symbol "operator") Atom.undefinedType
        Bindings.empty [(.symbol "operator", Bindings.empty)] :=
      .success (earlierTypes := []) (laterTypes := []) query rfl (by simp) (.undefinedLeft _ _)
    simp only [HEAtomEntry.Request.read, castDemand, Frame.read_empty, Entry.Value.erase]
    exact typed
  · apply List.Forall₂.cons _ .nil
    refine ⟨?_, .same _, ?_⟩
    · simp [castAnswer, Completed.rawResult, Entry.Value.erase, Frame.empty]
    · simp [castAnswer, castDemand, HEAtomEntry.Request.read, Entry.Value.erase]

theorem symbolic_cast_at_the_annotated_snapshot :
    ∃ start final,
      Shows code (HEFocused.restore ⟨annotated, true, .work castDemand.task, [], [], published⟩) start ∧
      (HEControlOnTransform.theory Nat code environment .unmarked).Step start final ∧
      Shows code (HEFocused.restore ⟨annotated, true, .returning [castAnswer], [], [], published⟩) final := by
  let before : Focus Bool World := ⟨annotated, true, .work castDemand.task, [], [], published⟩
  obtain ⟨start, read⟩ := exists_reads {HEControlOnTransform.encodeFocus code before}
  have initial : Shows code (HEFocused.restore before) start := by
    simpa only [Shows, HEFocused.focus_restore] using read
  have step : (source environment .unmarked).Step (HEFocused.restore before)
      (HEFocused.restore ⟨annotated, true, .returning [castAnswer], [], [], published⟩) := by
    apply source_of_focus environment .unmarked
    · exact HEControlOnTransform.covered_atom castDemand _ _ _ _ _
    · exact (HEAtomEntry.step_iff environment .unmarked castDemand annotated true [] [] published _).mpr
        ⟨.cast [castAnswer], cast_license, rfl⟩
  obtain ⟨final, fired, done⟩ := HEControlOnTransform.realize_step environment .unmarked code initial step
  exact ⟨start, final, initial, fired, done⟩

end TypedEntry

section Invocation

open Mettapedia.GSLT.IndexedOperational (ExecutionPath)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationFrontierRel EquationWork)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.FrontierControls (work complete context)
open Mettapedia.Machines.OrderedProtocol.Completion (SuccessPriorityRel)
open HEControlOnTransform (covered_invocation)

private def evalEffect : HEContextEntry.Request :=
  ⟨[], [], none, .active, .evalc actionAsData (.int 1), Frame.empty⟩

private def effectCall : HEInvocationEntry.Request := .invoke ⟨[], [], actionAsData, Frame.empty⟩ (.raw none)
private def evalSource : Focus Bool World := ⟨world, false, .work evalEffect.task, [], [], published⟩

/-- The write-shaped operand that `metta` returned as data under Atom
demand is executed by `evalc`, through the raw invocation guard. -/
theorem evalc_write_round_trip :
    ∃ start final, Shows code (HEFocused.restore evalSource) start ∧
      ∃ path : ExecutionPath (HEControlOnTransform.theory Nat code environment .unmarked) start final,
        Shows code (HEFocused.restore (finishAt updated [reply])) final ∧ path.length = 5 := by
  obtain ⟨start, read⟩ := exists_reads {HEControlOnTransform.encodeFocus code evalSource}
  have initial : Shows code (HEFocused.restore evalSource) start := by
    simpa only [Shows, HEFocused.focus_restore] using read
  let routed : Focus Bool World := ⟨world, true, .work effectCall.task, [], caller, published⟩
  let native : Focus Bool World := callFrom world write
  let returnedWrite : Focus Bool World := ⟨updated, true, .returning [reply], [], caller, published⟩
  have enter : (source environment .unmarked).Step (HEFocused.restore evalSource) (HEFocused.restore routed) := by
    apply source_of_focus environment .unmarked
    · exact Or.inr (Or.inl ⟨evalEffect, HEContextEntry.Request.recognize_task evalEffect⟩)
    · apply (HEContextEntry.step_iff evalEffect world false [] [] published _).mpr
      exact ⟨true, rfl, by simp [routed, evalEffect, caller, effectCall, HEInvocationEntry.Request.task]⟩
  have schedule : (source environment .unmarked).Step (HEFocused.restore routed) (HEFocused.restore native) := by
    apply source_of_focus environment .unmarked
    · exact covered_invocation effectCall _ _ _ _ _
    · apply (HEInvocationEntry.step_iff environment .unmarked effectCall world true [] caller published _).mpr
      refine ⟨.embedded, world, .work write.task, [], ?_, rfl, rfl⟩
      simp [HEInvocationEntry.Licensed, effectCall, HEInvocationEntry.Mode.mayInvoke, HEInvocationEntry.Mode.expected,
        environment, Minimal.HostCall, Minimal.embeddedInstruction, actionAsData, Entry.Value.erase]
  have writeStep : (source environment .unmarked).Step (HEFocused.restore native) (HEFocused.restore returnedWrite) := by
    apply source_of_focus environment .unmarked
    · exact Or.inl ⟨write, NativeRequest.recognize_task write⟩
    · apply (HEFocused.native_step_iff write world true [] caller published _).mpr
      exact ⟨[reply], updated, by
        simp [environment, services, execute, world, updated, write, request, reply, Entry.Value.erase, Entry.Value.ofAtom], rfl⟩
  have empty : ∀ saved ∈ caller, saved.stack = [] := by simp [caller]
  obtain ⟨tail, count⟩ := return_and_publish_path environment .unmarked updated true [reply] published caller empty
  let path : ExecutionPath (source environment .unmarked) (HEFocused.restore evalSource)
      (HEFocused.restore (finishAt updated [reply])) := .cons ⟨enter⟩ (.cons ⟨schedule⟩ (.cons ⟨writeStep⟩ tail))
  obtain ⟨final, fired, done, length⟩ := HEControlOnTransform.realize_path environment .unmarked code initial path
  refine ⟨start, final, initial, fired, done, length.trans ?_⟩
  change tail.length + 1 + 1 + 1 = 5
  rw [count]
  rfl

private def equationWorld : World := Function.update world true context.atoms
private def eqInput : HEInvocationEntry.Input := ⟨[], [], .symbol "a", Frame.empty⟩
private def newQuery : HEInvocationEntry.Request := .invoke eqInput (.raw none)
private def oldWork : List EquationWork := [work 0, work 3]
private def selectedOld : HEInvocationEntry.Request := .retained eqInput none oldWork

private theorem fresh_query_guard :
    NonGroundedCallRel environment.dispatch eqInput.value.erase := by
  simp [NonGroundedCallRel, Minimal.HostCall, Minimal.embeddedInstruction, eqInput, environment, Entry.Value.erase]

private theorem oldQueryLicensed :
    HEInvocationEntry.Licensed environment .unmarked equationWorld true newQuery (.query oldWork) equationWorld := by
  refine ⟨rfl, ?_, fresh_query_guard, ?_⟩
  · intro _ impossible
    cases impossible
  · simpa [environment, equationWorld, eqInput, oldWork, Frame.empty, Entry.Value.erase,
      HEInvocationEntry.Mode.protect, HEInvocationEntry.Mode.expected] using complete

theorem old_query_captures_both_occurrences :
    ∃ start final,
      Shows code (HEFocused.restore ⟨equationWorld, true, .work newQuery.task, [], [], published⟩) start ∧
      (HEControlOnTransform.theory Nat code environment .unmarked).Step start final ∧
      Shows code (HEFocused.restore ⟨equationWorld, true, .work selectedOld.task, [], [], published⟩) final := by
  let before : Focus Bool World := ⟨equationWorld, true, .work newQuery.task, [], [], published⟩
  obtain ⟨start, read⟩ := exists_reads {HEControlOnTransform.encodeFocus code before}
  have initial : Shows code (HEFocused.restore before) start := by
    simpa only [Shows, HEFocused.focus_restore] using read
  have step : (source environment .unmarked).Step (HEFocused.restore before)
      (HEFocused.restore ⟨equationWorld, true, .work selectedOld.task, [], [], published⟩) := by
    apply source_of_focus environment .unmarked
    · exact covered_invocation newQuery _ _ _ _ _
    · exact (HEInvocationEntry.step_iff environment .unmarked newQuery equationWorld true [] [] published _).mpr
        ⟨.query oldWork, equationWorld, .work selectedOld.task, [], oldQueryLicensed, rfl, rfl⟩
  obtain ⟨final, fired, next⟩ := HEControlOnTransform.realize_step environment .unmarked code initial step
  exact ⟨start, final, initial, fired, next⟩

theorem fresh_query_cannot_select_removed_definitions :
    ¬ HEInvocationEntry.Licensed environment .unmarked world true newQuery (.query oldWork) world := by
  intro stale
  have frontier : EquationFrontierRel (environment.view world true) [] (.symbol "a") Bindings.empty oldWork := by
    simpa [eqInput, newQuery, Entry.Value.erase, Frame.empty, HEInvocationEntry.Mode.protect,
      HEInvocationEntry.Mode.expected] using stale.2.2.2
  obtain ⟨_, witness⟩ := frontier.occurrence (show work 0 ∈ oldWork by simp [oldWork])
  have absent := witness.stored
  simp [environment, world] at absent

theorem fresh_query_reads_the_removal_on_transform :
    ∃ start final,
      Shows code (HEFocused.restore ⟨world, true, .work newQuery.task, [], [], published⟩) start ∧
      (HEControlOnTransform.theory Nat code environment .unmarked).Step start final ∧
      Shows code (HEFocused.restore
        ⟨world, true, .returning [(.symbol "NotReducible", Frame.empty)], [], [], published⟩) final := by
  let before : Focus Bool World := ⟨world, true, .work newQuery.task, [], [], published⟩
  let refused : Focus Bool World := ⟨world, true, .returning [(.symbol "NotReducible", Frame.empty)], [], [], published⟩
  obtain ⟨start, read⟩ := exists_reads {HEControlOnTransform.encodeFocus code before}
  have initial : Shows code (HEFocused.restore before) start := by
    simpa only [Shows, HEFocused.focus_restore] using read
  have licensed : HEInvocationEntry.Licensed environment .unmarked world true newQuery (.query []) world := by
    refine ⟨rfl, ?_, fresh_query_guard, ?_⟩
    · intro _ impossible
      cases impossible
    · exact EquationFrontierRel.completed (blocks := []) .nil
  have step : (source environment .unmarked).Step (HEFocused.restore before) (HEFocused.restore refused) := by
    apply source_of_focus environment .unmarked
    · exact covered_invocation newQuery _ _ _ _ _
    · exact (HEInvocationEntry.step_iff environment .unmarked newQuery world true [] [] published _).mpr
        ⟨.query [], world, refused.leaf, [], licensed, rfl, rfl⟩
  obtain ⟨final, fired, endpoint⟩ := HEControlOnTransform.realize_step environment .unmarked code initial step
  exact ⟨start, final, initial, fired, endpoint⟩

/-- After editing the live world, the captured first body and the second
pending occurrence are still reached by one actual firing. This is a
check at the edited snapshot, not an assertion that the edit is an HE
firing in this run. -/
theorem retained_work_can_run_after_removal :
    ∃ start final,
      Shows code (HEFocused.restore ⟨world, true, .work selectedOld.task, [], [], published⟩) start ∧
      (HEControlOnTransform.theory Nat code environment .unmarked).Step start final ∧
      Shows code (HEFocused.restore ⟨world, true, .work
        (.boundary [] [] (some (.symbol "a")) .producer (Frame.empty.read .unmarked (.symbol "result")) Frame.empty),
        [.append (HEInvocationEntry.Request.task (.retained eqInput none [work 3]))], [], published⟩) final := by
  let before : Focus Bool World := ⟨world, true, .work selectedOld.task, [], [], published⟩
  obtain ⟨start, read⟩ := exists_reads {HEControlOnTransform.encodeFocus code before}
  have initial : Shows code (HEFocused.restore before) start := by
    simpa only [Shows, HEFocused.focus_restore] using read
  have licensed : HEInvocationEntry.Licensed environment .unmarked world true selectedOld
      (.use (work 0) [work 3] Frame.empty) world := by
    refine ⟨rfl, rfl, rfl, .ordinary (.identical ?_)⟩
    simp [eqInput, work, Entry.Value.ofAtom, Entry.Value.substitute]
  have step : (source environment .unmarked).Step (HEFocused.restore before)
      (HEFocused.restore ⟨world, true, .work
        (.boundary [] [] (some (.symbol "a")) .producer (Frame.empty.read .unmarked (.symbol "result")) Frame.empty),
        [.append (HEInvocationEntry.Request.task (.retained eqInput none [work 3]))], [], published⟩) := by
    apply source_of_focus environment .unmarked
    · exact covered_invocation selectedOld _ _ _ _ _
    · exact (HEInvocationEntry.step_iff environment .unmarked selectedOld world true [] [] published _).mpr
        ⟨.use (work 0) [work 3] Frame.empty, world, _, _, licensed, rfl, by
          simp [eqInput, work, Entry.Value.erase, Entry.Value.ofAtom]⟩
  obtain ⟨final, fired, endpoint⟩ := HEControlOnTransform.realize_step environment .unmarked code initial step
  exact ⟨start, final, initial, fired, endpoint⟩

private def atWork (w : World) (task : Task)
    (stack : List Continuation) : Focus Bool World := ⟨w, true, .work task, stack, [], published⟩

private def atReturn (w : World) (batch : List Result)
    (stack : List Continuation) : Focus Bool World := ⟨w, true, .returning batch, stack, [], published⟩

private def answer : Result := (.symbol "result", Frame.empty)

private def retry (pending : List EquationWork) : HEInvocationEntry.Request :=
  .retained eqInput none pending

private def producer : Task :=
  .boundary [] [] (some (.symbol "a")) .producer answer.1 answer.2

private abbrev FromTo (first last : Focus Bool World) :=
  (source environment .unmarked).Step (HEFocused.restore first) (HEFocused.restore last)

private theorem enterOccurrence (w : World) (position : Nat) (pending : List EquationWork)
    (stack : List Continuation) :
    FromTo (atWork w (retry (work position :: pending)).task stack)
      (atWork w producer (.append (retry pending).task :: stack)) := by
  apply source_of_focus environment .unmarked (before := atWork w (retry (work position :: pending)).task stack)
  · exact covered_invocation _ _ _ _ _ _
  · apply (HEInvocationEntry.step_iff environment .unmarked (retry (work position :: pending)) w true
      stack [] published _).mpr
    refine ⟨.use (work position) pending Frame.empty, w, _, _, ?_, rfl, ?_⟩
    · refine ⟨rfl, rfl, rfl, .ordinary (.identical ?_)⟩
      simp [eqInput, work, Entry.Value.ofAtom, Entry.Value.substitute]
    · simp [atWork, producer, answer, retry, eqInput, work, Entry.Value.erase, Entry.Value.ofAtom]

private theorem produceOccurrence (w : World) (stack : List Continuation) :
    FromTo (atWork w producer stack) (atReturn w [answer] stack) := by
  apply source_of_focus environment .unmarked (before := atWork w producer stack)
  · exact HEControlOnTransform.covered_body _ _ _ _ _ _ rfl
  · apply (HEBodyEntry.step_iff environment .unmarked producer rfl w true stack [] published _).mpr
    exact ⟨.returning [answer], [], .producerRaw (by
      simp [answer, Completed.FunctionPending, Minimal.IsFunction, Entry.Value.erase]), rfl⟩

private theorem continueOccurrence (w : World) (pending : List EquationWork) (stack : List Continuation) :
    FromTo (atReturn w [answer] (.append (retry pending).task :: stack))
      (atWork w (retry pending).task (.prepend [answer] :: stack)) := by
  apply source_of_focus environment .unmarked
    (before := atReturn w [answer] (.append (retry pending).task :: stack))
  · exact HEControlOnTransform.covered_return _ _ _ _ _ _ _
  · exact (HEReturnEntry.step_iff environment .unmarked (.append (retry pending).task) rfl
      [answer] w true stack [] published _).mpr ⟨_, _, .append, rfl⟩

private theorem exhaustedOccurrences (w : World) (stack : List Continuation) :
    FromTo (atWork w (retry []).task stack) (atReturn w [] stack) := by
  apply source_of_focus environment .unmarked (before := atWork w (retry []).task stack)
  · exact covered_invocation _ _ _ _ _ _
  · exact (HEInvocationEntry.step_iff environment .unmarked (retry []) w true stack [] published _).mpr
      ⟨.exhausted, w, _, _, ⟨rfl, rfl⟩, rfl, rfl⟩

private theorem restoreOccurrence (w : World) (batch : List Result) (stack : List Continuation) :
    FromTo (atReturn w batch (.prepend [answer] :: stack)) (atReturn w (answer :: batch) stack) := by
  apply source_of_focus environment .unmarked (before := atReturn w batch (.prepend [answer] :: stack))
  · exact HEControlOnTransform.covered_return _ _ _ _ _ _ _
  · exact (HEReturnEntry.step_iff environment .unmarked (.prepend [answer]) rfl batch w true
      stack [] published _).mpr ⟨_, _, .prepend, rfl⟩

private def finalOccurrences (w : World) : Focus Bool World :=
  ⟨w, true, .returning [], [], [], published ++ [answer, answer]⟩

/-- Only the entered equation frontier is captured. Running it needs
neither a second read of those definitions nor a new source-level call. -/
private theorem finishCaptured (w : World) :
    Nonempty (ExecutionPath (source environment .unmarked)
      (HEFocused.restore (atWork w selectedOld.task [])) (HEFocused.restore (finalOccurrences w))) := by
  obtain ⟨finish, _⟩ := HEControlOnTransform.publish_path environment .unmarked w true [answer, answer] published
  let saved := Continuation.prepend [answer]
  refine ⟨.cons ⟨enterOccurrence w 0 [work 3] []⟩
    (.cons ⟨produceOccurrence w [.append (retry [work 3]).task]⟩
    (.cons ⟨continueOccurrence w [work 3] []⟩
    (.cons ⟨enterOccurrence w 3 [] [saved]⟩
    (.cons ⟨produceOccurrence w [.append (retry []).task, saved]⟩
    (.cons ⟨continueOccurrence w [] [saved]⟩
    (.cons ⟨exhaustedOccurrences w [saved, saved]⟩
    (.cons ⟨restoreOccurrence w [] [saved]⟩
    (.cons ⟨restoreOccurrence w [answer] []⟩ finish))))))))⟩

/-- Two equal equations generate two published occurrences in a single
Transform execution, including the initial selection from the space. -/
theorem both_equal_equations_reach_publication :
    ∃ start final,
      Shows code (HEFocused.restore (atWork equationWorld newQuery.task [])) start ∧
      Nonempty (ExecutionPath (HEControlOnTransform.theory Nat code environment .unmarked) start final) ∧
      Shows code (HEFocused.restore (finalOccurrences equationWorld)) final := by
  obtain ⟨start, _, initial, fired, reading⟩ := old_query_captures_both_occurrences
  obtain ⟨tail⟩ := finishCaptured equationWorld
  obtain ⟨final, remaining, seen, _⟩ := HEControlOnTransform.realize_path environment .unmarked code reading tail
  exact ⟨start, final, initial, ⟨.cons ⟨fired⟩ remaining⟩, seen⟩

/-- The same captured definitions finish after the space has changed,
whereas the fresh query above cannot select those definitions. -/
theorem both_captured_equations_finish_after_removal :
    ∃ start final,
      Shows code (HEFocused.restore (atWork world selectedOld.task [])) start ∧
      Nonempty (ExecutionPath (HEControlOnTransform.theory Nat code environment .unmarked) start final) ∧
      Shows code (HEFocused.restore (finalOccurrences world)) final := by
  obtain ⟨start, read⟩ := exists_reads {HEControlOnTransform.encodeFocus code (atWork world selectedOld.task [])}
  have initial : Shows code (HEFocused.restore (atWork world selectedOld.task [])) start := by
    simpa only [Shows, HEFocused.focus_restore] using read
  obtain ⟨tail⟩ := finishCaptured world
  obtain ⟨final, fired, seen, _⟩ := HEControlOnTransform.realize_path environment .unmarked code initial tail
  exact ⟨start, final, initial, ⟨fired⟩, seen⟩

private def diagnostic : Result :=
  (.expression .active [.symbol "Error", .symbol "a", .symbol "failed"], Frame.empty)

private def priorityInput : Focus Bool World :=
  atReturn equationWorld [answer, diagnostic, answer] [.publish (.symbol "a")]

private def priorityOutput : Focus Bool World := atReturn equationWorld [answer, answer] []

private theorem priorityMove :
    HEFocused.Move environment.arguments environment.view environment.services environment.dispatch
      environment.lookup .unmarked priorityInput priorityOutput := by
  apply (HEReturnEntry.step_iff environment .unmarked (.publish (.symbol "a")) rfl
    [answer, diagnostic, answer] equationWorld true [] [] published _).mpr
  refine ⟨.returning [answer, answer], [], ?_, rfl⟩
  have chosen : SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
      ([answer, diagnostic, answer].map (Completed.readResult .unmarked)) [answer, answer] := by
    have accepted : ∃ item ∈ [answer, diagnostic, answer].map (Completed.readResult .unmarked),
        isErrorAtom item.1.erase = false := by
      refine ⟨Completed.readResult .unmarked answer, List.mem_map.mpr ⟨answer, List.mem_cons_self, rfl⟩, ?_⟩
      simp [answer, Completed.readResult, Frame.read, isErrorAtom, Entry.Value.erase, Entry.Value.substitute]
    simpa [answer, diagnostic, Completed.readResult, Frame.read, Policy.unmarked,
      isErrorAtom, Entry.Value.erase, Entry.Value.substitute, Entry.Value.rebuildStatus] using
      SuccessPriorityRel.successes accepted
  exact .publish (original := .symbol "a") chosen

/-- Completing priority at the nearest frame drops the diagnostic, but
cannot drop either success or publish one before the other is known. -/
theorem success_priority_keeps_both_copies :
    ∃ start final, Shows code (HEFocused.restore priorityInput) start ∧
      (HEControlOnTransform.theory Nat code environment .unmarked).Step start final ∧
      ∀ next, (HEControlOnTransform.theory Nat code environment .unmarked).Step start next →
        Shows code (HEFocused.restore priorityOutput) next := by
  obtain ⟨start, read⟩ := exists_reads {HEControlOnTransform.encodeFocus code priorityInput}
  have initial : Shows code (HEFocused.restore priorityInput) start := by
    simpa only [Shows, HEFocused.focus_restore] using read
  have step : FromTo priorityInput priorityOutput := source_of_focus environment .unmarked trivial priorityMove
  obtain ⟨final, fired, _⟩ := HEControlOnTransform.realize_step environment .unmarked code initial step
  refine ⟨start, final, initial, fired, ?_⟩
  intro next advanced
  obtain ⟨reached, ⟨_, moved⟩, readBack⟩ := HEControlOnTransform.reflect_step environment .unmarked code initial advanced
  have focused := HEFocused.focus_step moved
  rw [HEFocused.focus_restore] at focused
  have same := HEReturnEntry.result_unique environment .unmarked (.publish (.symbol "a")) rfl
    [answer, diagnostic, answer] equationWorld true [] [] published focused priorityMove
  have exactState : reached = HEFocused.restore priorityOutput :=
    HEFocused.focusing.injective (same.trans (HEFocused.focus_restore _).symm)
  exact exactState ▸ readBack

private def tick : Atom := .grounded (.custom "operation" "tick")
private def tickValue : Entry.Value := .expression .active [Entry.Value.ofAtom tick]
private def tickCall : HEInvocationEntry.Request := .invoke ⟨[], [], tickValue, Frame.empty⟩ (.raw none)

private def tickHost : Completed.WorldEnvironment Bool World :=
  { environment with
    dispatch := { environment.dispatch with executable := fun value => value = tick }
    services := { services with groundedCall := fun label old call outcome next =>
      label = true ∧ old = world ∧ call = tickValue ∧ outcome = .ok [] ∧ next = updated } }

private def emptyReply : List Result := [(Entry.Value.ofAtom Atom.empty, Frame.empty)]

/-- A grounded operation is not the embedded call-native instruction.
Its authorization has the actual world update and can return Empty. -/
theorem grounded_call_keeps_its_authorized_effect :
    ∃ start final, Shows code (HEFocused.restore ⟨world, true, .work tickCall.task, [], [], published⟩) start ∧
      (HEControlOnTransform.theory Nat code tickHost .unmarked).Step start final ∧
      Shows code (HEFocused.restore ⟨updated, true, .returning emptyReply, [], [], published⟩) final := by
  let before : Focus Bool World := ⟨world, true, .work tickCall.task, [], [], published⟩
  obtain ⟨start, read⟩ := exists_reads {HEControlOnTransform.encodeFocus code before}
  have initial : Shows code (HEFocused.restore before) start := by
    simpa only [Shows, HEFocused.focus_restore] using read
  have stepped : (source tickHost .unmarked).Step (HEFocused.restore before)
      (HEFocused.restore ⟨updated, true, .returning emptyReply, [], [], published⟩) := by
    apply source_of_focus tickHost .unmarked
    · exact covered_invocation tickCall _ _ _ _ _
    · apply (HEInvocationEntry.step_iff tickHost .unmarked tickCall world true [] [] published _).mpr
      refine ⟨.native tick [] (.done emptyReply), updated, .returning emptyReply, [], ?_, rfl, rfl⟩
      refine ⟨?_, ?_, rfl, .ok [], ?_, .empty⟩
      · intro _ impossible
        cases impossible
      · simp [tickValue, Entry.Value.erase]
      · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨final, fired, done⟩ := HEControlOnTransform.realize_step tickHost .unmarked code initial stepped
  exact ⟨start, final, initial, fired, done⟩

end Invocation

section OrderedArguments

open Mettapedia.GSLT.IndexedOperational (ExecutionPath)
open HEArgumentPaths (atomRequests focusAt)

private def literalArguments : List Entry.Value := [diagnostic.1, actionAsData, diagnostic.1]

private def argumentSource : Focus Bool World :=
  focusAt world true parents published (.work (.arguments [] [] (atomRequests literalArguments) Frame.empty)) []

private def argumentResult : Focus Bool World :=
  focusAt world true parents published (.returning [(Entry.Value.argumentPacket literalArguments, Frame.empty)]) []

/-- Literal errors remain data under Atom demand, including both copies.
The intervening write-shaped operand has its original position and does
not change the space. -/
theorem literal_arguments_remain_ordered_data :
    ∃ start final, Shows code (HEFocused.restore argumentSource) start ∧
      ∃ path : ExecutionPath (HEControlOnTransform.theory Nat code environment .unmarked) start final,
        Shows code (HEFocused.restore argumentResult) final ∧ path.length = 25 := by
  obtain ⟨start, read⟩ := exists_reads {HEControlOnTransform.encodeFocus code argumentSource}
  have initial : Shows code (HEFocused.restore argumentSource) start := by
    simpa only [Shows, HEFocused.focus_restore] using read
  obtain ⟨final, path, done, size⟩ := HEArgumentPaths.atom_arguments_on_transform environment .unmarked
    world true parents published code literalArguments Frame.empty (fun value _ => Frame.read_empty _ value)
    [] [] [] initial
  exact ⟨start, final, initial, path, done, size.trans rfl⟩

private def pendingArguments : List Completed.ArgumentRequest := [(actionAsData, Atom.undefinedType)]

private def stoppedSource : Focus Bool World :=
  focusAt world true parents published (.work (.argumentBranches [] [] answer.1 pendingArguments
    [diagnostic, answer, reply])) []

private def wrongContinuation : Focus Bool World :=
  focusAt world true parents published (.work (.arguments [diagnostic.1.erase] [] pendingArguments diagnostic.2))
    [.argumentTail diagnostic.1, .append (.argumentBranches [] [] answer.1 pendingArguments [answer, reply])]

/-- A produced error cannot begin the rest of its branch. In particular,
it does not cancel either of the other alternatives by doing so. -/
theorem produced_error_does_not_enter_its_tail {start final}
    (initial : Shows code (HEFocused.restore stoppedSource) start)
    (wrong : Shows code (HEFocused.restore wrongContinuation) final) :
    ¬ (HEControlOnTransform.theory Nat code environment .unmarked).Step start final := by
  intro fired
  have stopped : Completed.ArgumentStopped answer.1 diagnostic := by
    refine ⟨Or.inr ⟨[.symbol "a", .symbol "failed"], by simp [diagnostic, Entry.Value.erase]⟩, ?_⟩
    simp [diagnostic, answer, Entry.Value.erase]
  obtain ⟨_, _, exactStep⟩ := HEArgumentPaths.stopped_branch_on_transform environment .unmarked
    world true parents published code [] [] answer.1 pendingArguments diagnostic [answer, reply] [] stopped initial
  have same := HEControlOnTransform.shows_unique code (exactStep final fired) wrong
  have bad := congrArg (fun state : WorldConfiguration Bool World => (HEFocused.focus state).leaf) same
  simp only [HEFocused.focus_restore] at bad
  cases bad

end OrderedArguments

end Mettapedia.Languages.MeTTa.SpaceTheory.HENativeTransformExamples
