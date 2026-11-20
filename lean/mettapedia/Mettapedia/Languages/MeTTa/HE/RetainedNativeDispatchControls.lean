import Mettapedia.Languages.MeTTa.HE.RetainedNativeDispatch

/-!
# Native effects, duplicate answers and two retained caller levels

The local host contract advances one selected context's counter. Its two
successful producer rows are equal values, not one collapsed answer. The
control starts at the reached call after argument production; it does not
claim the entire argument-producing source program has run.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RetainedNativeDispatchControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open RecursiveTasks.Contextual RecursiveMachine.Contextual
open RetainedNativeDispatch

abbrev Store := Bool → Nat
def number (n : Nat) : Entry.Value := .grounded (.int n)
def call : Entry.Value := .expression .active [.symbol "touch", .grounded (.int 7)]
def activation : Completed.Frame := Completed.Controls.argumentAliasFrame
def advance (world : Store) (label : Bool) : Store := Function.update world label (world label + 1)
def rows (world : Store) (label : Bool) : List Result :=
  [(number (world label), activation), (number (world label), activation)]
def errorRows : List Result := [(Entry.Value.ofAtom (Atom.error call.erase (.symbol "boom")), activation)]
def outcome (fails : Bool) (world : Store) (label : Bool) : GroundedResult Entry.Value :=
  if fails then .runtimeError "boom" else .ok
    [(number (world label), Bindings.empty), (number (world label), Bindings.empty)]
def plan (fails : Bool) (world : Store) (label : Bool) : NativeReplyPlan :=
  if fails then .done errorRows else .resume (rows world label)

def dispatch : Spec.Eval.GroundedDispatch where
  executable operator := operator = .symbol "touch"
  outcome := fun _ _ _ => False
  valueProvenance := fun _ _ => .completed
  bindingMode := fun _ _ => .raw

def services (fails : Bool) : WorldServices Bool Store where
  contextPayload label := .bool label
  nativeCall := fun _ _ _ _ _ _ _ _ => False
  groundedCall label world value result after :=
    value = call ∧ result = outcome fails world label ∧ after = advance world label

def environment (fails : Bool) : WorldEnvironment Bool Store where
  view world label := Space.ofList [.expression [.symbol "counter", .grounded (.int (world label))]]
  services := services fails
  dispatch := dispatch
  lookup := Completed.scopedLookup

theorem produced (fails : Bool) (world : Store) (label : Bool) :
    (environment fails).services.groundedAt label world [] [] activation call (outcome fails world label) (advance world label) := by
  exact ⟨rfl, rfl, rfl⟩

theorem prepared (fails : Bool) (world : Store) (label : Bool) :
    NativeOutcomeRel Policy.unmarked dispatch (.symbol "touch") [.grounded (.int 7)] call
      (some Atom.atomType) activation (outcome fails world label) (plan fails world label) := by
  cases fails with
  | true => exact .runtimeError "boom"
  | false =>
    have paired : NativeRowsRel Policy.unmarked dispatch (.symbol "touch") [.grounded (.int 7)] activation
        [(number (world label), Bindings.empty), (number (world label), Bindings.empty)] (rows world label) := by
      simpa [nativeValue, dispatch, rows] using
        (NativeRowsRel.cons (head := (number (world label), Bindings.empty))
          (Frame.NativeRenewRel.empty Policy.unmarked activation)
          (NativeRowsRel.cons (head := (number (world label), Bindings.empty))
            (Frame.NativeRenewRel.empty Policy.unmarked activation) .nil))
    exact .success paired

theorem completed_rows (world : Store) (label : Bool) :
    Stateful.BoundaryBatchRel (environment false) label (advance world label) [] [] none
      (.native call (some Atom.atomType) .completed) (rows world label) (rows world label) (advance world label)
      (policy := Policy.unmarked) := by
  have child : Stateful.BoundaryRel (environment false) label (advance world label) [] [] none
      (.native call (some Atom.atomType) .completed) (number (world label)) activation
      [(number (world label), activation)] (advance world label) (policy := Policy.unmarked) :=
    .nativeCompletedReturn (.keep (Or.inr (Or.inr (Or.inl rfl))))
  simpa only [rows, List.cons_append, List.nil_append] using
    Stateful.BoundaryBatchRel.cons (head := (number (world label), activation)) child
      (.cons (head := (number (world label), activation)) child .nil)

/-- A nonidentity permutation at the real return boundary keeps both
copies of the duplicated reply and the already reached host world. -/
theorem completed_reorder_keeps_duplicates (world : Store) (label : Bool) :
    let a : Result := (number 7, activation)
    let b : Result := (number 8, activation)
    ∃ output, Stateful.BoundaryBatchRel (environment false) label (advance world label) [] [] none
      (.native call (some Atom.atomType) .completed) [b,a,a] output (advance world label)
      (policy := Policy.unmarked) ∧ output.Perm [a,b,a] ∧ output.length = 3 := by
  let a : Result := (number 7, activation)
  let b : Result := (number 8, activation)
  have child (n : Nat) : Stateful.BoundaryRel (environment false) label (advance world label)
      [] [] none (.native call (some Atom.atomType) .completed) (number n) activation
      [(number n, activation)] (advance world label) (policy := Policy.unmarked) :=
    .nativeCompletedReturn (.keep (Or.inr (Or.inr (Or.inl rfl))))
  have batch : Stateful.BoundaryBatchRel (environment false) label (advance world label) [] [] none
      (.native call (some Atom.atomType) .completed) [a,b,a] [a,b,a] (advance world label)
      (policy := Policy.unmarked) :=
    .cons (head := a) (child 7) (.cons (head := b) (child 8) (.cons (head := a) (child 7) .nil))
  obtain ⟨output, swapped, bag⟩ := completed_boundary_permute (List.Perm.swap b a [a]) batch
  exact ⟨output,swapped,bag,bag.length_eq⟩

def world : Store := fun label => if label then 40 else 5
def inner : List Continuation := [.tupleTail (.symbol "inside")]
def outerRows : List Result := [(.symbol "outer", Completed.Frame.empty)]
def stack : List Continuation := [.prepend outerRows]
def emitted : List Result := [(.symbol "already", Completed.Frame.empty)]
def before : WorldConfiguration Bool Store :=
  ⟨world, true, .context false (.work (.call [] [] call Atom.atomType activation)) inner, stack, emitted⟩
def after (fails : Bool) : WorldConfiguration Bool Store :=
  resumeNested dispatch before false inner [] [] call Atom.atomType (.symbol "touch") [.grounded (.int 7)]
    (advance world false) (plan fails world false)
def nativeRows (fails : Bool) : List Result := if fails then errorRows else rows world false
def insideRows (fails : Bool) : List Result := (nativeRows fails).map (tuplePrepend (.symbol "inside"))
def answers (fails : Bool) : List Result := emitted ++ (outerRows ++ insideRows fails)

theorem actual_nested_native_step (fails : Bool) :
    WorldStep (environment fails).view (environment fails).services dispatch Completed.scopedLookup Policy.unmarked
      before (after fails) := by
  exact nested_native_step (environment fails) Policy.unmarked before false inner [] [] call Atom.atomType activation
    (.symbol "touch") [.grounded (.int 7)] (outcome fails world false) (advance world false) (plan fails world false)
    rfl (by simp [call, Entry.Value.erase]) rfl (by simp [call, Entry.Value.erase, IsErrorRel])
    (produced fails world false) (prepared fails world false)

theorem actual_reached_caller_source (fails : Bool) :
    (after fails).SourceRel (environment fails) Policy.unmarked (answers fails) (advance world false) := by
  have innerSource : WorldStackRel (environment fails) Policy.unmarked false (advance world false)
      inner (nativeRows fails) (insideRows fails) (advance world false) :=
    .cons (.tupleTail _ _) (.nil _)
  have outerSource : WorldStackRel (environment fails) Policy.unmarked true (advance world false)
      stack (insideRows fails) (outerRows ++ insideRows fails) (advance world false) :=
    .cons (.prepend _ _) (.nil _)
  refine ⟨insideRows fails, outerRows ++ insideRows fails, advance world false, ?_, outerSource, rfl⟩
  cases fails with
  | true => exact .context (.returning errorRows) innerSource
  | false => exact .context (.work (completed_rows world false)) innerSource

theorem retained_native_source_has_no_whole_run_premise (fails : Bool) :
    before.SourceRel (environment fails) Policy.unmarked (answers fails) (advance world false) := by
  apply (nested_source_iff (environment fails) Policy.unmarked before false inner [] [] call Atom.atomType activation
    (.symbol "touch") [.grounded (.int 7)] (answers fails) (advance world false) rfl
    (by simp [call, Entry.Value.erase]) rfl (by simp [call, Entry.Value.erase, IsErrorRel])).mpr
  exact ⟨outcome fails world false, advance world false, plan fails world false, produced fails world false,
    prepared fails world false, actual_reached_caller_source fails⟩

theorem actual_world_completion (fails : Bool) :
    WorldSteps (environment fails).view (environment fails).services dispatch Completed.scopedLookup Policy.unmarked
      before ⟨advance world false, true, .returning [], [], answers fails⟩ :=
  RecursiveExecution.Contextual.Stateful.source_to_finished (retained_native_source_has_no_whole_run_premise fails)

theorem one_host_operation_changes_only_the_child_context (fails : Bool) :
    (after fails).world false = 6 ∧ (after fails).world true = 40 ∧
      (after fails).context = true ∧ (after fails).stack = stack ∧ (after fails).emitted = emitted := by
  cases fails <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem duplicate_native_values_remain_duplicate :
    (insideRows false).length = 2 ∧ (insideRows false).map (fun item => item.1.erase) =
      [.expression [.symbol "inside", .grounded (.int 5)], .expression [.symbol "inside", .grounded (.int 5)]] := by cbv

theorem caller_binding_theory_survives_the_native_boundary :
    (insideRows false).map (fun item => item.2.bindings) = [activation.bindings, activation.bindings] := by cbv

theorem resetting_the_old_world_cannot_equal_the_reached_cursor (fails : Bool) :
    {after fails with world := world} ≠ after fails := by
  intro same
  have counters := congrArg (fun state : WorldConfiguration Bool Store => state.world false) same
  have changed := (one_host_operation_changes_only_the_child_context fails).1
  change 5 = (after fails).world false at counters
  rw [changed] at counters
  cases counters

theorem replaying_the_host_operation_changes_its_observable_world :
    (advance (advance world false) false) false = 7 ∧ (advance world false) false = 6 := by decide

end Mettapedia.Languages.MeTTa.HE.RetainedNativeDispatchControls

namespace Mettapedia.Languages.MeTTa.HE.RetainedNativeDispatchControls.CapturedMatch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.BindingTheory Spec.Bindings.ScopeObservation
open RecursiveTasks.Contextual RecursiveMachine.Contextual RetainedNativeDispatch
open Mettapedia.Machines.OrderedProtocol.Completion (OrderedStateFlatMapRel)

abbrev StoreWorld := Bool → List Atom
abbrev World := StoreWorld × List Frame

private def row (name : String) : Atom := .expression [.symbol "row", .symbol name]
private def leg : Atom := .expression [.symbol "row", .var "choice"]
private def pattern : Atom := .expression [.symbol ",", leg, leg]
private def selection (name : String) : Bindings := Bindings.empty.assign "choice" (.symbol name)

def initialWorld : World :=
  (fun label => if label then [row "a", row "b"] else [.symbol "outside"], [])

private def body (argument : Entry.Value) : Entry.Value :=
  .expression .active [.symbol "call-native", .symbol "match-test", .symbol "remove-other", argument]

private def template (argument : Entry.Value) : Entry.Value :=
  .expression .active [.symbol "function", body argument]

/-- The fixture's rows are closed, so they have no private locals to open or
project. An exhaustive scan uses the existing HE matcher, not a supplied
table of answers. Each row attempt, including negative ones, is covered. -/
private def leaf (world : World) (label : Bool) (depth : Nat) : Space.MatchQuery.AtomicRead :=
  fun _ query =>
    let work := (world.1 label).map (MatchRequest.atoms query)
    if work.all (matchCovered depth) then some (work.flatMap (evalMatch depth)) else none

private def capture (world : World) (label : Bool) (depth : Nat := 12) : Option (List Bindings) :=
  Space.MatchQuery.capture (leaf world label depth) depth pattern

private def raw (selected : List Bindings) : List (Entry.Value × Bindings) :=
  selected.map fun binding => (template (.var "choice"), binding)

private def answer (world : World) (label : Bool) (selected : Atom) : Entry.Value :=
  number ((if selected = .symbol "a" then 10 else 20) + if row "b" ∈ world.1 label then 1 else 0)

private def removeOther (world : World) (label : Bool) (selected : Atom) : World :=
  (Function.update world.1 label ((world.1 label).erase (if selected = .symbol "a" then row "b" else row "a")),
    world.2)

private def returned (w : World) (label : Bool) (selected : Atom) : Entry.Value :=
  .expression .active [.symbol "return", answer w label selected]

private def arguments (label : Bool) : List Entry.Value :=
  [.grounded (.bool label), Entry.Value.ofAtom pattern, template (.var "choice")]

def call (label : Bool) : Entry.Value :=
  .expression .active (.symbol "match" :: arguments label)

private def dispatch : Spec.Eval.GroundedDispatch where
  executable operator := operator = .symbol "match"
  outcome := fun _ _ _ => False
  valueProvenance := fun _ _ => .emitted
  bindingMode := fun _ _ => .materialized

private def baseServices : WorldServices Bool World where
  contextPayload label := .bool label
  snapshots := some (SnapshotServices.appendModel Bool StoreWorld)
  nativeCall label before name function selected frame results after :=
    name = .symbol "match-test" ∧ function = .symbol "remove-other" ∧
      results = [(returned before label selected, frame)] ∧ after = removeOther before label selected

private def decode (_ : Bool) : Entry.Value → Option (Bool × Atom × Entry.Value)
  | .expression _ [.symbol "match", .grounded (.bool address), pat, body] =>
      some (address, pat.erase, body)
  | _ => none

private def select (_ : Bool) (world : World) (_ : List Atom) (_ : List String) (_ : Frame)
    (address : Bool) : Space.MatchQuery.AtomicRead :=
  leaf world address 12

private def services : WorldServices Bool World := withSnapshotMatch baseServices decode select 12

def environment : WorldEnvironment Bool World where
  view world label := .ofList (world.1 label)
  services := services
  dispatch := dispatch
  lookup := rawLookup

def initial : WorldConfiguration Bool World :=
  ⟨initialWorld, true, .work (.call [] [] (call true) Atom.undefinedType Frame.empty), [], []⟩

private def firstWorld := removeOther initialWorld true (.symbol "a")
def finalWorld := removeOther firstWorld true (.symbol "b")

private theorem deletion_view : firstWorld.1 true = [row "a"] := by decide +kernel

private theorem initial_capture : capture initialWorld true = some [selection "a", selection "b"] := by
  decide +kernel

private theorem host_capture (world : World) (label : Bool) (live : List Atom) (scope : List String)
    (caller : Frame) (selected : List Bindings) (complete : capture world label = some selected) :
    environment.services.groundedAt label world live scope caller (call label) (.ok (raw selected)) world := by
  have decoded : decode label (call label) = some (label, pattern, template (.var "choice")) := by
    simp [decode, call, arguments, Entry.Value.erase_ofAtom]
  apply (snapshot_match_at_iff (base := baseServices) (decode := decode) (select := select)
    (depth := 12) (label := label) (call := call label)
    (address := label) (pattern := pattern) (template := template (.var "choice")) decoded).mpr
  refine ⟨?_,rfl⟩
  change (capture world label).map (GroundedResult.ok ∘ raw) = some (.ok (raw selected))
  rw [complete]
  rfl

private theorem leaf_grows (world : World) (label : Bool) (depth extra : Nat)
    (incoming : Bindings) (query : Atom) (answers : List Bindings)
    (complete : leaf world label depth incoming query = some answers) :
    leaf world label (depth + extra) incoming query = some answers := by
  let work := (world.1 label).map (MatchRequest.atoms query)
  change (if work.all (matchCovered depth) then some (work.flatMap (evalMatch depth))
    else none) = some answers at complete
  have covered : work.all (matchCovered depth) = true := by
    by_contra outside
    simp only [if_neg outside] at complete
    cases complete
  have grows : work.all (matchCovered (depth + extra)) = true :=
    List.all_eq_true.mpr fun request member =>
      matchCovered_mono depth extra request (List.all_eq_true.mp covered request member)
  have answer : work.flatMap (evalMatch (depth + extra)) = work.flatMap (evalMatch depth) :=
    List.flatMap_congr fun request member =>
      matchCovered_stable depth extra request (List.all_eq_true.mp covered request member)
  change (if work.all (matchCovered (depth + extra)) then
    some (work.flatMap (evalMatch (depth + extra))) else none) = some answers
  rw [if_pos grows,answer]
  simpa only [if_pos covered] using complete

/-- The concrete capture does not depend on exhausting the matcher's fuel. -/
theorem capture_depth_stable (extra : Nat) :
    capture initialWorld true (12 + extra) = capture initialWorld true := by
  rw [initial_capture]
  exact Space.MatchQuery.capture_stable 12 extra pattern
    (leaf_grows initialWorld true 12 extra) initial_capture

theorem requery_after_first_loses_the_later_selection :
    capture firstWorld true = some [selection "a"] ∧ finalWorld.1 true = [] ∧
      finalWorld.1 false = [.symbol "outside"] := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Both reads use the same shared variable but can each select either
physical copy. Four witnesses survive; neither leg is a set lookup. -/
theorem conjunction_keeps_occurrence_products :
    capture ((fun _ => [row "a", row "a"]), []) true =
      some (List.replicate 4 (selection "a")) := by decide +kernel

/-- A selector that has not finished is not a completed no-match, and
the empty conjunction has one empty binding without calling the selector. -/
theorem missing_query_certificate_is_not_no_match :
    capture initialWorld true 0 = none ∧ capture finalWorld true 0 = some [] ∧
      Space.MatchQuery.capture (fun _ _ => none) 0 (.expression [.symbol ","]) =
        some [Bindings.empty] := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

private theorem compatible (name : String) :
    LogicalMergeRel (selection name) Frame.empty.bindings (selection name) := by
  refine ⟨?_, (ReadoutCertificate.of_fold
    (single_assignment_presentation "choice" (.symbol name) (by simp [TypeSubst.typeVars]))).satisfiable⟩
  simpa only [Frame.empty, Bindings.empty, List.append_nil] using BindingSourceAgreement.refl (selection name)

private theorem template_read (frame : Frame) (name : String) (binding : frame.bindings = selection name) :
    frame.read .unmarked (template (.var "choice")) = template (.symbol name) := by
  have bare : (Entry.Value.resolve frame.environment "choice").erase = .symbol name := by
    have forced := frame.certified.forced_read (.var "choice") (.symbol name)
      (fun valuation solved => by
        have selected := solved.1 "choice" (.symbol name) (by
          simp [binding, selection, Bindings.assign, Bindings.isBound, Bindings.empty, Bindings.lookup])
        simpa only [applyTypeValuation] using selected)
    have erased := Entry.Value.erase_substitute_environment Policy.unmarked.rebuilding
      frame.environment (.var "choice")
    simpa [Entry.Value.substitute, Entry.Value.erase, forced] using erased
  have exact := show Entry.Value.resolve frame.environment "choice" = .symbol name by
    cases resolved : Entry.Value.resolve frame.environment "choice" <;>
      simp_all [Entry.Value.erase]
  simp [Frame.read, template, body, Entry.Value.substitute, Entry.Value.rebuildStatus, Policy.unmarked, exact]

/-- A raw reply incompatible with itself can't be mistaken for a successful
empty continuation. This exercises the repaired producer decision. -/
theorem rejected_bindings_return_internal_empty :
    let bad : Bindings := ⟨[("choice", .symbol "a"), ("choice", .symbol "b")], []⟩
    let raw : List (Entry.Value × Bindings) := [(template (.var "choice"), bad)]
    NativeOutcomeRel Policy.unmarked dispatch (.symbol "match") ((arguments true).map Entry.Value.erase)
      (call true) (some Atom.undefinedType) Frame.empty (.ok raw)
      (.done [(Entry.Value.ofAtom Atom.empty, Frame.empty)]) ∧
    ¬NativeOutcomeRel Policy.unmarked dispatch (.symbol "match") ((arguments true).map Entry.Value.erase)
      (call true) (some Atom.undefinedType) Frame.empty (.ok raw) (.resume []) := by
  intro bad raw
  have incompatible : ∀ member ∈ raw, ¬∃ after, LogicalMergeRel member.2 Frame.empty.bindings after := by
    rintro member hit ⟨after, merged⟩
    simp only [raw, List.mem_singleton] at hit
    subst member
    obtain ⟨valuation, conflict, _⟩ := merged.common_model
    have first := conflict.1 "choice" (.symbol "a") (by simp [bad])
    have second := conflict.1 "choice" (.symbol "b") (by simp [bad])
    have impossible : (.symbol "a" : Atom) = .symbol "b" := by
      simpa only [applyTypeValuation] using first.symm.trans second
    exact (show "a" ≠ "b" by decide) (Atom.symbol.inj impossible)
  obtain ⟨plan, planned⟩ := NativeOutcomeRel.total .unmarked dispatch (.symbol "match")
    ((arguments true).map Entry.Value.erase) (call true) (some Atom.undefinedType) Frame.empty (.ok raw)
  have forced := planned.all_rejected incompatible
  constructor
  · exact forced ▸ planned
  · intro resumed
    cases resumed.all_rejected incompatible

private theorem evaluate_number (world : World) (label : Bool) (frame : Frame) (value : Nat) :
    Stateful.AtomRel environment label world [] [] (number value) Atom.undefinedType frame
      [(number value, frame)] world := by
  have ready : frame.read .unmarked (number value) = number value := by
    simp [Frame.read, number, Entry.Value.substitute]
  have entry : Entry.Rel Policy.unmarked.reentry .active (.grounded (.int value)) Atom.undefinedType .cast :=
    .cast (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (.grounded _) (by decide)
      (Or.inr (Or.inl ⟨_, rfl⟩)) (by intro impossible; cases impossible)
  apply Stateful.AtomRel.cast (raw := [((number value).erase, frame.bindings)])
  · rw [ready]
    simpa [number, Entry.Value.erase, Entry.Value.status] using entry
  · simp only [ready]
    have stored : StorageTypesRel (environment.view world label) (number value).erase [.symbol "Number"] := by
      simpa [number, Entry.Value.erase] using
        (StorageTypesRel.groundedKnown (space := environment.view world label) (.int value) (by decide))
    exact TypeCastBatchRel.success (earlierTypes := []) (laterTypes := []) stored rfl (by simp)
      (frame.preserved_type_match .unmarked (.undefinedLeft _ _))
  · exact .cons ⟨rfl, .same frame, by simp [ready]⟩ .nil

private theorem run_template (world : World) (label : Bool) (name : String) (frame : Frame)
    (live : List Atom) (scope : List String) (caller : Option Atom) :
    Stateful.MinimalRel environment label world live scope caller (template (.symbol name)) frame
      [(answer world label (.symbol name), frame)] (removeOther world label (.symbol name)) := by
  apply Stateful.MinimalRel.function
    (world1 := removeOther world label (.symbol name))
    (bodyReadiness := .active) (raw := [(returned world label (.symbol name), frame)]) rfl
  · apply Stateful.BodyRel.run (world1 := removeOther world label (.symbol name))
      (raw := [(returned world label (.symbol name), frame)])
    · exact .native (by simp [environment, services, withSnapshotMatch, baseServices, Entry.Value.erase])
    · apply Stateful.BoundaryBatchRel.single_iff.mpr
      have read : frame.read .unmarked (returned world label (.symbol name)) = returned world label (.symbol name) := by
        simp [returned, answer, number, Frame.read, Entry.Value.substitute, Entry.Value.rebuildStatus, Policy.unmarked]
      have terminal : Minimal.embeddedInstruction (frame.read .unmarked (returned world label (.symbol name))).erase =
          false := by
        rw [read]
        simp [returned, Entry.Value.erase, Minimal.embeddedInstruction]
      simpa only [read] using Stateful.BoundaryRel.bodyTerminal terminal
  · exact Stateful.BoundaryBatchRel.single_iff.mpr .functionReturn

private theorem template_pending (name : String) :
    FunctionPending .unmarked (template (.symbol name)) := by
  simp [FunctionPending, Minimal.IsFunction, template, Entry.Value.erase, Policy.unmarked]

private theorem continue_template (world : World) (label : Bool) (name : String) (frame : Frame) :
    Stateful.BoundaryRel environment label world [] [] none (.native (call label) (some Atom.undefinedType) .emitted)
      (template (.symbol name)) frame [(answer world label (.symbol name), frame)]
      (removeOther world label (.symbol name)) := by
  apply Stateful.BoundaryRel.nativeEmittedReturn
    (produced := [(answer world label (.symbol name), frame)])
  · apply Stateful.BoundaryRel.producerFunction
    · exact template_pending name
    · exact run_template world label name frame _ _ _
  · apply Stateful.BoundaryBatchRel.single_iff.mpr
    let count := (if (.symbol name : Atom) = .symbol "a" then 10 else 20) + if row "b" ∈ world.1 label then 1 else 0
    have evaluated := evaluate_number (removeOther world label (.symbol name)) label frame count
    exact .returned (.evaluate (by simp [answer, number, Entry.Value.erase, Atom.notReducible])
      (by simp [answer, number, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
      (by simpa [answer, count] using evaluated))

def resumeAtMatch (rows : List Result) : WorldConfiguration Bool World :=
  resumeNative dispatch initial [] [] (call true) Atom.undefinedType (.symbol "match")
    ((arguments true).map Entry.Value.erase) initialWorld (.resume rows)

private theorem prepared_match :
    ∃ a b : Frame,
      NativeRowsRel .unmarked dispatch (.symbol "match") ((arguments true).map Entry.Value.erase)
        Frame.empty (raw [selection "a", selection "b"]) [(template (.symbol "a"), a), (template (.symbol "b"), b)] := by
  obtain ⟨a, bindingA, mergeA⟩ := Frame.NativeRenewRel.of_logical_merge
    (policy := .unmarked) Frame.empty (compatible "a")
  obtain ⟨b, bindingB, mergeB⟩ := Frame.NativeRenewRel.of_logical_merge
    (policy := .unmarked) Frame.empty (compatible "b")
  refine ⟨a, b, ?_⟩
  simpa [raw, nativeValue, dispatch, template_read a "a" bindingA, template_read b "b" bindingB] using
    (NativeRowsRel.cons (head := (template (.var "choice"), selection "a")) mergeA
      (NativeRowsRel.cons (head := (template (.var "choice"), selection "b")) mergeB .nil)
      (dispatch := dispatch) (operator := .symbol "match") (arguments := (arguments true).map Entry.Value.erase))

private theorem seenA : answer initialWorld true (.symbol "a") = number 11 := by
  simp [answer, initialWorld, row]

private theorem seenB : answer firstWorld true (.symbol "b") = number 20 := by
  simp [answer, deletion_view, row]

/-- Real dispatch earns a retained batch, and the independent continuation
runs in the reached world. The B template runs after its own row was deleted. -/
theorem actual_capture_and_continue :
    ∃ a b : Frame,
      let paused := resumeAtMatch [(template (.symbol "a"), a), (template (.symbol "b"), b)]
      WorldStep (admission := environment.arguments) environment.view environment.services environment.dispatch
        environment.lookup .unmarked initial paused ∧
      paused.SourceRel environment .unmarked [(number 11, a), (number 20, b)] finalWorld := by
  obtain ⟨a, b, prepared⟩ := prepared_match
  let ready := [(template (.symbol "a"), a), (template (.symbol "b"), b)]
  have planned : NativeOutcomeRel .unmarked dispatch (.symbol "match") ((arguments true).map Entry.Value.erase)
      (call true) (some Atom.undefinedType) Frame.empty (.ok (raw [selection "a", selection "b"])) (.resume ready) :=
    NativeOutcomeRel.ok_iff_rows.mpr ⟨ready, prepared, rfl⟩
  refine ⟨a, b, ?_, ?_⟩
  · exact native_step environment .unmarked initial [] [] (call true) Atom.undefinedType Frame.empty
      (.symbol "match") ((arguments true).map Entry.Value.erase) (.ok (raw [selection "a", selection "b"])) initialWorld
      (.resume ready) rfl (by simp [call, Entry.Value.erase]) rfl
      (by simp [call, Entry.Value.erase, IsErrorRel]) (host_capture initialWorld true [] [] _ _ initial_capture) planned
  · have outputs : Stateful.BoundaryBatchRel environment true initialWorld [] [] none
        (.native (call true) (some Atom.undefinedType) .emitted) ready
        [(number 11, a), (number 20, b)] finalWorld := by
      simpa only [ready, seenA, seenB, List.append_nil, List.singleton_append, finalWorld] using
        (Stateful.BoundaryBatchRel.cons (head := (template (.symbol "a"), a)) (world1 := firstWorld)
          (continue_template initialWorld true "a" a)
          (.cons (head := (template (.symbol "b"), b)) (continue_template firstWorld true "b" b) .nil))
    exact ⟨_, _, _, .work outputs, .nil _, rfl⟩

theorem source_runs_captured_templates :
    ∃ a b : Frame, initial.SourceRel environment .unmarked [(number 11, a), (number 20, b)] finalWorld := by
  obtain ⟨a, b, handoff, continuation⟩ := actual_capture_and_continue
  exact ⟨a, b, RecursiveExecution.Contextual.Stateful.retained_prefix (.single handoff) continuation⟩

/-- The same captured multiset, run in two orders, can change even the
unframed answer bag while reaching the same store. This is an exchange
of retained templates, not a second execution of matching. -/
theorem captured_order_can_change_bag :
    ∃ selected : List Result, ∃ a b : Frame,
      let left := [(number 11, a), (number 20, b)]
      let right := [(number 21, b), (number 11, a)]
      selected.length = 2 ∧
      (resumeAtMatch selected).SourceRel environment .unmarked left finalWorld ∧
      (resumeAtMatch selected.reverse).SourceRel environment .unmarked right finalWorld ∧
      ¬ (left.map (fun result => result.1.erase)).Perm
        (right.map (fun result => result.1.erase)) := by
  obtain ⟨a, b, _, forwards⟩ := actual_capture_and_continue
  let next := removeOther initialWorld true (.symbol "b")
  have seenBFirst : answer initialWorld true (.symbol "b") = number 21 := by
    simp [answer, initialWorld, row]
  have view : next.1 true = [row "b"] := by decide +kernel
  have seenALater : answer next true (.symbol "a") = number 11 := by
    simp [answer, view]
  have endWorld : removeOther next true (.symbol "a") = finalWorld := by
    apply Prod.ext
    · funext label
      cases label <;> decide +kernel
    · rfl
  have backwards : Stateful.BoundaryBatchRel environment true initialWorld [] [] none
      (.native (call true) (some Atom.undefinedType) .emitted)
      [(template (.symbol "b"), b), (template (.symbol "a"), a)]
      [(number 21, b), (number 11, a)] finalWorld := by
    simpa only [seenBFirst, seenALater, endWorld, List.append_nil, List.singleton_append] using
      (Stateful.BoundaryBatchRel.cons (head := (template (.symbol "b"), b)) (world1 := next)
        (continue_template initialWorld true "b" b)
        (.cons (head := (template (.symbol "a"), a)) (continue_template next true "a" a) .nil))
  refine ⟨[(template (.symbol "a"), a), (template (.symbol "b"), b)],a,b,rfl,forwards,
    ⟨_,_,_,.work backwards,.nil _,rfl⟩,?_⟩
  intro same
  have appears : (number 20).erase ∈ [(number 11).erase, (number 20).erase] := by simp
  have missing : (number 20).erase ∉ [(number 21).erase, (number 11).erase] := by
    simp [number, Entry.Value.erase]
  exact missing (same.mem_iff.mp appears)

private def evaluator : Entry.Value := .expression .active [.symbol "eval", call true]

private theorem native_invoked_template (world : World) (name : String) (frame : Frame)
    (live : List Atom) (scope : List String) (caller : Option Atom) :
    Stateful.BoundaryRel environment true world live scope caller (.native (call true) none .emitted)
      (template (.symbol name)) frame [(answer world true (.symbol name), frame)]
      (removeOther world true (.symbol name)) :=
  .nativeEmittedRaw (.producerFunction (template_pending name) (run_template world true name frame _ _ _))

private theorem evaluator_runs (live : List Atom) (scope : List String) (caller : Option Atom) :
    ∃ a b : Frame, Stateful.MinimalRel environment true initialWorld live scope caller evaluator Frame.empty
      [(number 11, a), (number 20, b)] finalWorld := by
  obtain ⟨a, b, prepared⟩ := prepared_match
  let ready := [(template (.symbol "a"), a), (template (.symbol "b"), b)]
  have plan : NativeOutcomeRel .unmarked dispatch (.symbol "match") ((arguments true).map Entry.Value.erase)
      (call true) none Frame.empty (.ok (raw [selection "a", selection "b"])) (.resume ready) :=
    NativeOutcomeRel.ok_iff_rows.mpr ⟨ready, prepared, rfl⟩
  have replies : Stateful.BoundaryBatchRel environment true initialWorld live scope caller
      (.native (call true) none .emitted) ready [(number 11, a), (number 20, b)] finalWorld := by
    simpa only [ready, seenA, seenB, List.append_nil, List.singleton_append, finalWorld] using
      (Stateful.BoundaryBatchRel.cons (head := (template (.symbol "a"), a)) (world1 := firstWorld)
        (native_invoked_template initialWorld "a" a live scope caller)
        (.cons (head := (template (.symbol "b"), b))
          (native_invoked_template firstWorld "b" b live scope caller) .nil))
  have called : Stateful.InvocationRel environment true initialWorld live scope caller (call true) Frame.empty
      [(number 11, a), (number 20, b)] finalWorld :=
    .groundedResume (by simp [call, Entry.Value.erase]) rfl
      (host_capture initialWorld true live scope _ _ initial_capture) plan replies
  exact ⟨a, b, .eval (by simpa only [Frame.read_empty] using called)⟩

/-- An actual completed evaluator batch, not a copied earlier world, is
collected by the existing primitive and snapshot service. -/
def collectMatch : Entry.Value := .expression .active [.symbol "collapse-bind", evaluator]

def pairs (first second : Entry.Value) : Entry.Value :=
  .expression .active
    [.expression .active [first, .grounded (.int 0)], .expression .active [second, .grounded (.int 1)]]

def collectionStart : WorldConfiguration Bool World :=
  ⟨initialWorld, true, .work (.minimal [] [] none collectMatch Frame.empty), [], []⟩

def collectionPaused (a b : Frame) : WorldConfiguration Bool World :=
  ⟨finalWorld, true, .returning [(number 11, a), (number 20, b)], [.collect Frame.empty], []⟩

private theorem collection_capture (a b : Frame) :
    CaptureRowsRel (SnapshotServices.appendModel Bool StoreWorld) true finalWorld
      [(number 11, a), (number 20, b)] [] (pairs (number 11) (number 20)) (finalWorld.1, [a, b]) := by
  exact .cons (by simp [number, Atom.empty, Entry.Value.erase])
    (show (SnapshotServices.appendModel Bool StoreWorld).capture true finalWorld a (.int 0) (finalWorld.1, [a])
      from ⟨rfl, rfl⟩)
    (.cons (by simp [number, Atom.empty, Entry.Value.erase])
      (show (SnapshotServices.appendModel Bool StoreWorld).capture true (finalWorld.1, [a]) b (.int 1)
        (finalWorld.1, [a, b]) from ⟨rfl, rfl⟩) .nil)

/-- The actual authored operand and its two successive source effects,
followed by the snapshot plan for the caller's completed collection. -/
theorem collection_plan :
    ∃ (operand : Entry.Value) (a b : Frame),
      collectMatch = .expression .active [.symbol "collapse-bind", operand] ∧
      Stateful.MinimalRel environment true initialWorld [] [] none operand Frame.empty
        [(number 11, a), (number 20, b)] finalWorld ∧
      CaptureRowsRel (SnapshotServices.appendModel Bool StoreWorld) true finalWorld
        [(number 11, a), (number 20, b)] [] (pairs (number 11) (number 20)) (finalWorld.1, [a, b]) := by
  obtain ⟨a, b, child⟩ := evaluator_runs [] [] none
  exact ⟨evaluator, a, b, rfl, child, collection_capture a b⟩

/-- Both writes can already have happened while the collector is still
pending. Its saved continuation packs the actual child results and frames
without undoing those writes or entering the child again. -/
theorem collection_pauses_and_resumes :
    ∃ a b : Frame,
      WorldSteps (admission := environment.arguments) environment.view environment.services
        environment.dispatch environment.lookup .unmarked collectionStart (collectionPaused a b) ∧
      worldObserve (collectionPaused a b) = none ∧
      (collectionPaused a b).SourceRel environment .unmarked
        [(pairs (number 11) (number 20), Frame.empty)] (finalWorld.1, [a, b]) := by
  obtain ⟨a, b, child⟩ := evaluator_runs [] [] none
  let entered : WorldConfiguration Bool World :=
    ⟨initialWorld, true, .work (.minimal [] [] none evaluator Frame.empty), [.collect Frame.empty], []⟩
  have enter : WorldStep (admission := environment.arguments) environment.view environment.services
      environment.dispatch environment.lookup .unmarked collectionStart entered :=
    .internal (.collapseEnter rfl)
  have cut : WorldSteps (admission := environment.arguments) environment.view environment.services
      environment.dispatch environment.lookup .unmarked entered (collectionPaused a b) :=
    RecursiveExecution.Contextual.Stateful.local_steps_lift
      (RecursiveExecution.Contextual.Stateful.task_complete
        (environment := environment) (policy := .unmarked)
        (task := .minimal [] [] none evaluator Frame.empty) child [.collect Frame.empty]) []
  exact ⟨a, b, (Relation.ReflTransGen.single enter).trans cut, rfl,
    _, _, _, .returning _, .cons (.collect rfl (collection_capture a b)) (.nil _), rfl⟩

/-- A completed no-match child gets its internal Empty marker, and collapse
returns one empty collection. Neither fact identifies a waiting iterator
with a finished answer. -/
theorem no_match_collects_one_empty_expression :
    Stateful.MinimalRel environment true finalWorld [] [] none collectMatch Frame.empty
      [(.expression .active [], Frame.empty)] finalWorld := by
  have missing : capture finalWorld true = some [] := by decide +kernel
  have atHost : environment.services.groundedAt true finalWorld [] [] Frame.empty (call true)
      (.ok []) finalWorld := by
    exact host_capture finalWorld true [] [] _ [] missing
  have child : Stateful.InvocationRel environment true finalWorld [] [] none (call true) Frame.empty
        [(Entry.Value.ofAtom Atom.empty, Frame.empty)] finalWorld :=
    .groundedDone (operator := .symbol "match") (arguments := (arguments true).map Entry.Value.erase)
      (by simp [call, Entry.Value.erase]) rfl atHost .empty
  apply Stateful.MinimalRel.collapseBind rfl (.eval (by simpa only [Frame.read_empty] using child))
  exact .empty (Entry.Value.erase_ofAtom _) .nil

end Mettapedia.Languages.MeTTa.HE.RetainedNativeDispatchControls.CapturedMatch
