import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldSourceLoop
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStatefulSelectedComposition
import Mettapedia.Languages.MeTTa.HE.ArgumentAdmission

/-! The collection append source leaf is earned from its closed declaration,
the operand kind cut, and one saved-pair primitive operation. No expression
type inference is demanded for its two held operands. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionAppendSource

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type Spec.Type.Presentation
open Mettapedia.Machines.OrderedProtocol.Completion

def signature : SelectedTypePolicy :=
  ⟨CompletedDelivery.arrowType [Atom.expressionType, Atom.expressionType] Atom.atomType,
    [Atom.expressionType, Atom.expressionType], Atom.atomType, rfl⟩

def call (mark listMark : Entry.Status) (values : List Entry.Value) (pair : Entry.Value) : Entry.Value :=
  .expression mark [.symbol CollectionStdlibSource.appendName, .expression listMark values, pair]

theorem selection (space : Space) (lookup : CastLookup) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (mark listMark pairMark : Entry.Status)
    (values paired : List Entry.Value)
    (queried : lookup (invocationTypeScope scope live (call mark listMark values (.expression pairMark paired)).erase
      Atom.undefinedType before.bindings) space before.bindings (.symbol CollectionStdlibSource.appendName)
      Atom.undefinedType [signature.functionType]) :
    kindArgumentService.selection space lookup policy live scope (call mark listMark values (.expression pairMark paired)).erase
      (.symbol CollectionStdlibSource.appendName) Atom.undefinedType before (.selected signature [before]) := by
  let names := invocationTypeScope scope live (call mark listMark values (.expression pairMark paired)).erase
    Atom.undefinedType before.bindings
  refine ⟨[signature.functionType], queried, .selected (errors := []) ?_ (by simp)⟩
  have first : KindArgumentAdmissionRel space (lookup names space) policy
      (call mark listMark values (.expression pairMark paired)).erase (.expression (values.map Entry.Value.erase))
      Atom.expressionType 1 before [before] [] := .kind (.expression _) .expression
  have second : KindArgumentAdmissionRel space (lookup names space) policy
      (call mark listMark values (.expression pairMark paired)).erase (.expression (paired.map Entry.Value.erase))
      Atom.expressionType 2 before [before] [] := .kind (.expression _) .expression
  simpa [signature, checkedFrames, checkedFailures, names] using
    AdmissionApplicationRel.checked (admit := KindArgumentAdmissionRel)
      (expression := (call mark listMark values (.expression pairMark paired)).erase) (expected := Atom.undefinedType)
      (selected := signature) (before := before) (operator := .symbol CollectionStdlibSource.appendName)
      (arguments := [.expression (values.map Entry.Value.erase), .expression (paired.map Entry.Value.erase)])
      (by simp [call, Entry.Value.erase])
      (.cons (AdmissionFramesRel.single first) (.cons (AdmissionFramesRel.single second) .nil))
      (List.Forall₂.cons (TypeCheckRel.accepted (.unchanged
        (before.preserved_type_match policy (.undefinedLeft _ _)))) List.Forall₂.nil)

theorem operator_source {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (world : World) (live : List Atom) (scope : List String) (frame : Frame)
    (queried : environment.lookup (invocationTypeScope scope live (.symbol CollectionStdlibSource.appendName)
      signature.functionType frame.bindings) (environment.view world label) frame.bindings
      (.symbol CollectionStdlibSource.appendName) signature.functionType [signature.functionType]) :
    Stateful.AtomRel environment label world live scope (.symbol CollectionStdlibSource.appendName)
      signature.functionType frame [(.symbol CollectionStdlibSource.appendName, frame)] world (policy := policy) := by
  have read : frame.read policy (.symbol CollectionStdlibSource.appendName) = .symbol CollectionStdlibSource.appendName := by
    simp [Frame.read, Entry.Value.substitute]
  have closed : TypeSubst.typeVars signature.functionType = [] := by
    simp [signature, CompletedDelivery.arrowType, TypeSubst.typeVars, TypeSubst.typeVarsList,
      Atom.expressionType, Atom.atomType]
  have matched := frame.preserved_type_match policy
    (FirstSuccessSourceApplicability.closed_type_match signature.functionType frame.bindings
      (sizeOf signature.functionType + sizeOf signature.functionType + 2) closed (Nat.le_refl _)).2
  apply Stateful.AtomRel.cast (raw := [(.symbol CollectionStdlibSource.appendName, frame.bindings)])
  · rw [read]
    apply Entry.Rel.cast (metaType := Atom.symbolType)
    · simp [CollectionStdlibSource.appendName, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · simpa only [Entry.Value.erase] using MetaTypeRel.symbol CollectionStdlibSource.appendName
    · simp [signature, CompletedDelivery.arrowType, Atom.atomType, Atom.symbolType, Atom.variableType]
    · exact Or.inl ⟨CollectionStdlibSource.appendName, by simp only [Entry.Value.erase]⟩
    · simp [Entry.Value.erase, Atom.unit]
  · rw [read]
    simp only [Entry.Value.erase]
    exact TypeCastBatchRel.success (earlierTypes := []) (laterTypes := []) queried rfl (by simp) matched
  · rw [read]
    exact .cons ⟨by simp [rawResult, Entry.Value.erase], .same frame, by simp [Entry.Value.erase]⟩ .nil

theorem expression_delivery {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (world : World) (live : List Atom) (scope : List String) (frame : Frame)
    (mark : Entry.Status) (values : List Entry.Value)
    (closed : TypeSubst.typeVarsList (values.map Entry.Value.erase) = []) :
    Stateful.AtomRel environment label world live scope (.expression mark values) Atom.expressionType frame
      [(.expression mark values, frame)] world (policy := policy) := by
  have read := HECollectionClosedAppend.closed_read policy frame (.expression mark values)
    (by simpa only [Entry.Value.erase, TypeSubst.typeVars] using closed)
  have entered : Entry.Rel policy.reentry (.expression mark values : Entry.Value).status
      (.expression mark values : Entry.Value).erase Atom.expressionType .deliver := by
    by_cases stopped : IsEmptyOrErrorRel (.expression mark values : Entry.Value).erase
    · exact .stopped stopped
    · apply Entry.Rel.pass stopped
      · simpa only [Entry.Value.erase] using MetaTypeRel.expression (values.map Entry.Value.erase)
      · exact Or.inr (Or.inl rfl)
  simpa only [read] using Stateful.AtomRel.delivered (environment := environment)
    (label := label) (world0 := world) (live := live) (scope := scope)
    (value := Entry.Value.expression mark values) (expected := Atom.expressionType) (frame := frame) (policy := policy)
    (by simpa only [read] using entered)

theorem arguments_source {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (world : World) (live : List Atom) (scope : List String) (frame : Frame)
    (firstMark secondMark : Entry.Status) (first second : List Entry.Value)
    (firstClosed : TypeSubst.typeVarsList (first.map Entry.Value.erase) = [])
    (secondClosed : TypeSubst.typeVarsList (second.map Entry.Value.erase) = []) :
    Stateful.ArgumentsRel environment label world live scope
      [(.expression firstMark first, Atom.expressionType), (.expression secondMark second, Atom.expressionType)] frame
      [(Entry.Value.argumentPacket [.expression firstMark first, .expression secondMark second], frame)] world
      (policy := policy) := by
  apply Stateful.ArgumentsRel.cons (expression_delivery environment policy label world _ scope frame firstMark first firstClosed)
  have last : ∀ live, Stateful.ArgumentsRel environment label world live scope
      [(.expression secondMark second, Atom.expressionType)] frame
      [(Entry.Value.argumentPacket [.expression secondMark second], frame)] world (policy := policy) := by
    intro nestedLive
    apply Stateful.ArgumentsRel.cons (expression_delivery environment policy label world _ scope frame secondMark second secondClosed)
    simpa only [List.map_cons, List.map_nil, List.append_nil, argumentPrepend_packet] using
      Stateful.ArgumentBranchesRel.continuing (head := (Entry.Value.expression secondMark second, frame))
        (by simp [ArgumentStopped]) (Stateful.ArgumentsRel.nil (frame := frame)) Stateful.ArgumentBranchesRel.nil
  simpa only [List.map_cons, List.map_nil, List.append_nil, argumentPrepend_packet] using
    Stateful.ArgumentBranchesRel.continuing (head := (Entry.Value.expression firstMark first, frame))
      (by simp [ArgumentStopped]) (last _) Stateful.ArgumentBranchesRel.nil

theorem singleton_priority (row : Result) :
    SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase) [row] [row] := by
  cases clean : isErrorAtom row.1.erase with
  | true => exact .allErrors (by simpa only [List.mem_singleton] using fun item (same : item = row) => same ▸ clean)
  | false =>
      simpa only [List.filter_cons, clean, Bool.not_false, List.filter_nil, if_true] using
        (SuccessPriorityRel.successes (isError := fun result : Result => isErrorAtom result.1.erase)
          (raw := [row]) ⟨row, by simp, clean⟩)

theorem completed_call {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (world : World) (live : List Atom) (scope : List String) (frame : Frame)
    (listMark : Entry.Status) (values : List Entry.Value) (pair output : Entry.Value)
    (executable : environment.dispatch.executable (.symbol CollectionStdlibSource.appendName))
    (raw : environment.dispatch.bindingMode (.symbol CollectionStdlibSource.appendName)
      [(.expression listMark values : Entry.Value).erase, pair.erase] = .raw)
    (completed : environment.dispatch.valueProvenance (.symbol CollectionStdlibSource.appendName)
      [(.expression listMark values : Entry.Value).erase, pair.erase] = .completed)
    (executed : environment.services.groundedAt label world live scope frame (call .active listMark values pair)
      (.ok [(output, Bindings.empty)]) world) :
    Stateful.CallRel environment label world live scope (call .active listMark values pair) Atom.atomType frame
      [(output, frame)] world (policy := policy) := by
  let args := [(.expression listMark values : Entry.Value).erase, pair.erase]
  have prepared : NativeRowsRel policy environment.dispatch (.symbol CollectionStdlibSource.appendName) args frame
      [(output, Bindings.empty)] [(output, frame)] := by
    simpa only [nativeValue, raw, args] using
      (NativeRowsRel.cons (dispatch := environment.dispatch) (operator := .symbol CollectionStdlibSource.appendName)
        (arguments := args) (head := (output, Bindings.empty)) (Frame.NativeRenewRel.empty policy frame) .nil)
  refine .groundedResume (operator := .symbol CollectionStdlibSource.appendName) (arguments := args)
    (outcome := .ok [(output, Bindings.empty)]) (rows := [(output, frame)]) (world1 := world)
    ?_ executable ?_ executed (.success prepared) ?_
  · simp only [call, Entry.Value.erase, List.map_cons, List.map_nil, args]
  · simp [call, Entry.Value.erase, IsErrorRel, CollectionStdlibSource.appendName]
  · rw [completed]
    apply Stateful.BoundaryBatchRel.single_iff.mpr
    exact .nativeCompletedReturn (.keep (Or.inr (Or.inr (Or.inl rfl))))

theorem source {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (world : World) (live : List Atom) (scope : List String) (frame : Frame)
    (mark listMark pairMark : Entry.Status) (values paired : List Entry.Value) (newValue : Entry.Value)
    (active : policy.reentry = .reinterpret ∨ mark = .active)
    (kind : environment.arguments = kindArgumentService)
    (queries : ∀ names expected, environment.lookup names (environment.view world label) frame.bindings
      (.symbol CollectionStdlibSource.appendName) expected [signature.functionType])
    (valuesClosed : TypeSubst.typeVarsList (values.map Entry.Value.erase) = [])
    (pairClosed : TypeSubst.typeVarsList (paired.map Entry.Value.erase) = [])
    (newClosed : TypeSubst.typeVars newValue.erase = [])
    (executable : environment.dispatch.executable (.symbol CollectionStdlibSource.appendName))
    (raw : environment.dispatch.bindingMode (.symbol CollectionStdlibSource.appendName)
      [(.expression listMark values : Entry.Value).erase, (.expression pairMark paired : Entry.Value).erase] = .raw)
    (completed : environment.dispatch.valueProvenance (.symbol CollectionStdlibSource.appendName)
      [(.expression listMark values : Entry.Value).erase, (.expression pairMark paired : Entry.Value).erase] = .completed)
    (executed : environment.services.groundedAt label world live scope frame
      (call .active listMark values (.expression pairMark paired))
      (.ok [(.expression listMark (values ++ [newValue]), Bindings.empty)]) world) :
    ∃ nextMark, Stateful.AtomRel environment label world live scope
      (call mark listMark values (.expression pairMark paired)) Atom.undefinedType frame
      [(.expression nextMark (values ++ [newValue]), frame)] world (policy := policy) := by
  let original := call mark listMark values (.expression pairMark paired)
  let output := Entry.Value.expression listMark (values ++ [newValue])
  have originalClosed : TypeSubst.typeVars original.erase = [] := by
    simp [original, call, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList, valuesClosed, pairClosed]
  have originalRead := HECollectionClosedAppend.closed_read policy frame original originalClosed
  have outputClosed : TypeSubst.typeVars output.erase = [] := by
    simp [output, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList_append,
      TypeSubst.typeVarsList, valuesClosed, newClosed]
  have outputRead := HECollectionClosedAppend.closed_read policy frame output outputClosed
  have called := completed_call environment policy label world live scope frame listMark values
    (.expression pairMark paired) output executable raw completed executed
  have calls : Stateful.CallsRel environment label world live scope (invocationReturnType signature)
      ([(Entry.Value.argumentPacket [.expression listMark values, .expression pairMark paired], frame)].map
        (functionAssemble (.symbol CollectionStdlibSource.appendName))) [(output, frame)] world (policy := policy) := by
    simpa [signature, invocationReturnType, Atom.atomType, Atom.expressionType, functionAssemble, call] using
      (Stateful.CallsRel.cons called Stateful.CallsRel.nil)
  have priority : SuccessPriorityRel (fun row : Result => isErrorAtom row.1.erase)
      ([(output, frame)].map (readResult policy)) [(output, frame)] := by
    simpa only [List.map_cons, List.map_nil, readResult, outputRead] using singleton_priority (output, frame)
  have derived := HEStatefulSelectedComposition.selected_of_parts environment policy label world world world world
    live scope original Atom.undefinedType frame frame frame mark
    (.symbol CollectionStdlibSource.appendName) (.symbol CollectionStdlibSource.appendName)
    [.expression listMark values, .expression pairMark paired] signature
    [(Entry.Value.argumentPacket [.expression listMark values, .expression pairMark paired], frame)]
    [(output, frame)] [(output, frame)]
    (by
      rw [originalRead]
      simp only [original, call, Entry.Value.status, Entry.Value.erase, List.map_cons, List.map_nil]
      exact Entry.Rel.expression
        (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, CollectionStdlibSource.appendName])
        (by decide) active)
    (by rw [originalRead]; rfl)
    (by
      rw [originalRead, kind]
      simpa only [original, Entry.Value.erase] using
        selection _ _ policy frame live scope mark listMark pairMark values paired (queries _ _))
    rfl (operator_source environment policy label world _ _ frame (queries _ _))
    (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty, CollectionStdlibSource.appendName])
    (arguments_source environment policy label world _ scope frame listMark pairMark values paired valuesClosed pairClosed)
    calls priority
  refine ⟨(Entry.Value.publish policy.marking original.erase frame.source output).status, ?_⟩
  simpa only [originalRead, List.map_cons, List.map_nil, publishResult, Entry.Value.publish,
    Entry.Value.withStatus, Entry.Value.status, output] using derived

/-- These are local reader and primitive service laws. The operation law
is the saved-pair step, not an evaluation or a finished-array premise. -/
structure Interface {Context World : Type} (environment : WorldEnvironment Context World)
    (snapshots : SnapshotServices Context World) (policy : Policy) (label : Context) (world : World) : Prop where
  kind : environment.arguments = kindArgumentService
  query : ∀ names (frame : Frame) expected, environment.lookup names (environment.view world label) frame.bindings
    (.symbol CollectionStdlibSource.appendName) expected [signature.functionType]
  executable : environment.dispatch.executable (.symbol CollectionStdlibSource.appendName)
  raw : ∀ arguments, environment.dispatch.bindingMode (.symbol CollectionStdlibSource.appendName) arguments = .raw
  completed : ∀ arguments, environment.dispatch.valueProvenance (.symbol CollectionStdlibSource.appendName) arguments = .completed
  primitive : ∀ live scope frame input outcome,
    HECollectionClosedAppend.Step snapshots policy label world input outcome →
    environment.services.groundedAt label world live scope frame input outcome world

theorem append_calls {Context World : Type} {environment : WorldEnvironment Context World}
    {snapshots : SnapshotServices Context World} {policy label world}
    (interface : Interface environment snapshots policy label world) (frame : Frame) :
    HECollectionFoldSourceLoop.AppendCalls environment snapshots policy label world frame := by
  constructor
  intro live scope callMark listMark values row pair active stored closed valuesClosed
  have primitive := HECollectionClosedAppend.append_of_stored snapshots policy label world row pair stored closed .active listMark values
  obtain ⟨payload, same, _⟩ := stored
  subst pair
  have sourceRun := source environment policy label world live scope frame callMark listMark .active values
    [row.1, .grounded payload] row.1 active interface.kind (fun names expected => interface.query names frame expected)
    valuesClosed (by simp [TypeSubst.typeVarsList, Entry.Value.erase, TypeSubst.typeVars, closed]) closed
    interface.executable (interface.raw _) (interface.completed _)
    (interface.primitive live scope frame _ _ primitive)
  exact sourceRun

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionAppendSource
