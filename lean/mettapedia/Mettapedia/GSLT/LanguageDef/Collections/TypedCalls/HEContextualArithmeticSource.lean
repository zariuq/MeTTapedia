import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFiniteSuperposeSource
import Mettapedia.Languages.MeTTa.HE.ScalarValueCasts

/-!
# Arithmetic source returns under retained contextual frames

The finite source example initially starts from an empty record. Authored
range recursion and the collapse macro retain additional records, so their
arithmetic service boundaries must work under the reached frame itself.
These statements use the existing stateful source judgments. The read-only
completed source profile deliberately has no grounded-call constructor.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEContextualArithmeticSource

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Eval Spec.Eval.Completed
open Spec.Type Spec.Type.Presentation Spec.Type.Presentation.BindingTheory
open Spec.Match.Merge

theorem same_symbol_match (name : String) (bindings : Bindings)
    (notUndefined : name ≠ "%Undefined%") (notAtom : name ≠ "Atom") :
    TypeMatchRel (.symbol name) (.symbol name) bindings bindings :=

  same_symbol_type_match name bindings notUndefined notAtom

/-- Closed intrinsic types require no fresh variables, regardless of the
caller's protected names or previously selected type/term bindings. -/
theorem scalar_lookup (space : Space) (protectedNames : List String) (frame : Frame)
    (value : GroundedValue) (name : String) (expected : Atom)
    (typed : getGroundedType value = .symbol name) (notUndefined : name ≠ "%Undefined%") :
    scopedLookup protectedNames space frame.bindings (.grounded value) expected [.symbol name] := by
  refine ⟨[.symbol name], ?_, .cons ?_ (.nil _)⟩
  · have intrinsic : IntrinsicGroundedTypeRel value (getGroundedType value) := by
      cases value <;> constructor
    simpa only [typed] using (StorageTypesRel.groundedKnown (space := space) intrinsic
      (by simpa [typed, Atom.undefinedType] using notUndefined))
  · exact ⟨id, Function.injective_id, by simp, by simp [TypeSubst.typeVars]⟩

/-- A literal arithmetic result is cast under the reached frame and keeps
that exact frame, including bindings absent from the literal's own syntax. -/
theorem scalar_atom {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String)
    (frame : Frame) (value : GroundedValue) (name : String)
    (typed : getGroundedType value = .symbol name)
    (notUndefined : name ≠ "%Undefined%") (notAtom : name ≠ "Atom")
    (notGrounded : name ≠ "Grounded") :
    Stateful.AtomRel environment label world live scope (.grounded value) (.symbol name) frame
      [(.grounded value, frame)] world (policy := policy) := by
  apply Stateful.scalar_from_query environment policy label world live scope frame value name
    notUndefined notAtom notGrounded
  rw [lookup]
  exact scalar_lookup (environment.view world label)
    (invocationTypeScope scope live (.grounded value) (.symbol name) frame.bindings)
    frame value name (.symbol name) typed notUndefined

theorem number_atom {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String)
    (frame : Frame) (value : Int) :
    Stateful.AtomRel environment label world live scope (.grounded (.int value)) (.symbol "Number") frame
      [(.grounded (.int value), frame)] world (policy := policy) :=
  scalar_atom environment lookup policy label world live scope frame (.int value) "Number"
    rfl (by decide) (by decide) (by decide)

theorem boolean_atom {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String)
    (frame : Frame) (value : Bool) :
    Stateful.AtomRel environment label world live scope (.grounded (.bool value)) (.symbol "Bool") frame
      [(.grounded (.bool value), frame)] world (policy := policy) :=
  scalar_atom environment lookup policy label world live scope frame (.bool value) "Bool"
    rfl (by decide) (by decide) (by decide)

/-- A primitive's empty binding contribution preserves the entire reached
caller frame. The scalar still runs its ordinary typed return gate. The
primitive-outcome premise concerns one host operation, not a language run. -/
theorem emitted_scalar_return_of_source {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String)
    (frame : Frame) (original : Entry.Value) (operator : Atom) (arguments : List Atom)
    (value : GroundedValue) (name : String)
    (shape : original.erase = .expression (operator :: arguments))
    (executable : environment.dispatch.executable operator)
    (notError : ¬IsErrorRel original.erase)
    (raw : environment.dispatch.bindingMode operator arguments = .raw)
    (emitted : environment.dispatch.valueProvenance operator arguments = .emitted)
    (executed : environment.services.groundedAt label world live scope frame original
      (.ok [(.grounded value, Bindings.empty)]) world)
    (returned : Stateful.AtomRel environment label world live scope (.grounded value) (.symbol name) frame
      [(.grounded value, frame)] world (policy := policy)) :
    Stateful.CallRel environment label world live scope original (.symbol name) frame
      [(.grounded value, frame)] world (policy := policy) := by
  have renewed : NativeRowsRel policy environment.dispatch operator arguments frame
      [(.grounded value, Bindings.empty)]
      [(nativeValue policy environment.dispatch operator arguments frame (.grounded value), frame)] :=
    .cons (Frame.NativeRenewRel.empty policy frame) .nil
  have replies : NativeRowsRel policy environment.dispatch operator arguments frame
      [(.grounded value, Bindings.empty)] [(.grounded value, frame)] := by
    simpa only [nativeValue, raw] using renewed
  refine Stateful.CallRel.groundedResume (operator := operator) (arguments := arguments)
    (outcome := .ok [(.grounded value, Bindings.empty)]) (rows := [(.grounded value, frame)])
    (world1 := world) shape executable notError executed (.success replies) ?_
  rw [emitted]
  apply Stateful.BoundaryBatchRel.single_iff.mpr
  refine Stateful.BoundaryRel.nativeEmittedReturn (world1 := world)
    (produced := [(.grounded value, frame)]) ?_ ?_
  · apply Stateful.BoundaryRel.producerRaw
    simp [FunctionPending, Minimal.IsFunction, Entry.Value.erase]
  · apply Stateful.BoundaryBatchRel.single_iff.mpr
    apply Stateful.BoundaryRel.returned
    apply Stateful.ReturnRel.evaluate
    · simp [Entry.Value.erase, Atom.notReducible]
    · simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · exact returned

theorem emitted_scalar_return {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String)
    (frame : Frame) (original : Entry.Value) (operator : Atom) (arguments : List Atom)
    (value : GroundedValue) (name : String)
    (shape : original.erase = .expression (operator :: arguments))
    (executable : environment.dispatch.executable operator)
    (notError : ¬IsErrorRel original.erase)
    (raw : environment.dispatch.bindingMode operator arguments = .raw)
    (emitted : environment.dispatch.valueProvenance operator arguments = .emitted)
    (executed : environment.services.groundedAt label world live scope frame original
      (.ok [(.grounded value, Bindings.empty)]) world)
    (typed : getGroundedType value = .symbol name)
    (notUndefined : name ≠ "%Undefined%") (notAtom : name ≠ "Atom")
    (notGrounded : name ≠ "Grounded") :
    Stateful.CallRel environment label world live scope original (.symbol name) frame
      [(.grounded value, frame)] world (policy := policy) :=
  emitted_scalar_return_of_source environment policy label world live scope frame original operator arguments
    value name shape executable notError raw emitted executed
    (scalar_atom environment lookup policy label world live scope frame value name typed notUndefined notAtom notGrounded)

/-- The relation of the existing primitive multiplication operation. This
does not define or execute any surrounding MeTTa program. -/
def arithmeticDispatch : Spec.Eval.GroundedDispatch where
  executable operator := operator = .symbol "*"
  outcome operator arguments outcome := operator = .symbol "*" ∧
    TypedSquareCollection.multiplication.execute operator arguments = outcome

def arithmeticEnvironment (services : Minimal.Services) : WorldEnvironment Space Unit where
  view := fun _ => id
  services := WorldServices.readOnlyGrounded services arithmeticDispatch
  dispatch := arithmeticDispatch
  lookup := scopedLookup

def multiplicationCall (left right : Int) : Entry.Value :=
  .expression .active [.symbol "*", .grounded (.int left), .grounded (.int right)]

/-- Actual multiplication under an arbitrary certified caller record.
The caller need not be empty or disjoint from a fixed test variable list. -/
theorem multiplication_source (services : Minimal.Services) (policy : Policy)
    (space : Space) (live : List Atom) (scope : List String) (frame : Frame) (left right : Int) :
    Stateful.CallRel (arithmeticEnvironment services) space () live scope
      (multiplicationCall left right) (.symbol "Number") frame
      [(.grounded (.int (left * right)), frame)] () (policy := policy) := by
  apply emitted_scalar_return (arithmeticEnvironment services) rfl policy space () live scope frame
    (multiplicationCall left right) (.symbol "*") [.grounded (.int left), .grounded (.int right)]
    (.int (left * right)) "Number" (by simp [multiplicationCall, Entry.Value.erase]) rfl
    (by simp [multiplicationCall, Entry.Value.erase, IsErrorRel]) rfl rfl
  · exact ⟨.symbol "*", [.grounded (.int left), .grounded (.int right)],
      .ok [(.grounded (.int (left * right)), Bindings.empty)],
      by simp [multiplicationCall, Entry.Value.erase], ⟨rfl, rfl⟩,
      by simp [GroundedResult.map, Entry.Value.ofAtom]⟩
  · rfl
  · decide
  · decide
  · decide

def multiplicationSignature : SelectedTypePolicy :=
  ⟨CompletedDelivery.arrowType [.symbol "Number", .symbol "Number"] (.symbol "Number"),
    [.symbol "Number", .symbol "Number"], .symbol "Number", rfl⟩

theorem signature_match (bindings : Bindings) :
    TypeMatchRel multiplicationSignature.functionType multiplicationSignature.functionType bindings bindings := by
  have emptyMerge : MergeRel equalityGroundedSemantic Bindings.empty Bindings.empty Bindings.empty :=
    .mk (by simp [constraints, Bindings.empty]) .nil
  exact .structural (by decide) (by decide) (by decide) (by decide)
    (.expression
      (.cons (.symSym "->" semanticLoopFree_empty) emptyMerge
        (.cons (.symSym "Number" semanticLoopFree_empty) emptyMerge
          (.cons (.symSym "Number" semanticLoopFree_empty) emptyMerge
            (.cons (.symSym "Number" semanticLoopFree_empty) emptyMerge .nil)))) semanticLoopFree_empty)
    (.mk (by simp [constraints, Bindings.empty]) .nil)

theorem signature_lookup (space : Space) (protectedNames : List String) (frame : Frame) (expected : Atom)
    (declared : getAtomTypes space (.symbol "*") = [multiplicationSignature.functionType]) :
    scopedLookup protectedNames space frame.bindings (.symbol "*") expected [multiplicationSignature.functionType] := by
  refine ⟨[multiplicationSignature.functionType], ?_, .cons ?_ (.nil _)⟩
  · simpa only [declared] using FirstSuccessSourceReplies.source_types space (.symbol "*")
  · exact ⟨id, Function.injective_id, by simp,
      by simp [multiplicationSignature, CompletedDelivery.arrowType, TypeSubst.typeVars, TypeSubst.typeVarsList]⟩

theorem numeric_argument_checks (space : Space) (names : List String) (policy : Policy)
    (frame : Frame) (expression : Atom) (position : Nat) (value : Int) :
    ArgumentChecksRel space (scopedLookup names space) policy expression (.grounded (.int value))
      (.symbol "Number") position [frame] [frame] [] := by
  have checked : TypeCheckRel policy (.symbol "Number") frame (.symbol "Number") (.inr frame) :=
    .accepted (.unchanged (frame.preserved_type_match policy
      (same_symbol_match "Number" frame.bindings (by decide) (by decide))))
  simpa [checkedFrames, checkedFailures] using
    (ArgumentChecksRel.cons (expression := expression) (position := position)
      (scalar_lookup space names frame (.int value) "Number" (.symbol "Number") rfl (by decide))
      (.cons checked .nil) .nil)

theorem multiplication_selection (space : Space) (policy : Policy) (frame : Frame)
    (live : List Atom) (scope : List String) (left right : Int)
    (declared : getAtomTypes space (.symbol "*") = [multiplicationSignature.functionType]) :
    InvocationSelectionRel space scopedLookup policy live scope (multiplicationCall left right).erase
      (.symbol "*") (.symbol "Number") frame (.selected multiplicationSignature [frame]) := by
  let names := invocationTypeScope scope live (multiplicationCall left right).erase (.symbol "Number") frame.bindings
  have first := numeric_argument_checks space names policy frame (multiplicationCall left right).erase 1 left
  have second := numeric_argument_checks space names policy frame (multiplicationCall left right).erase 2 right
  have returned : TypeCheckRel policy (.symbol "Number") frame (.symbol "Number") (.inr frame) :=
    .accepted (.unchanged (frame.preserved_type_match policy
      (same_symbol_match "Number" frame.bindings (by decide) (by decide))))
  have checked : ApplicationChecksRel space (scopedLookup names space) policy
      (multiplicationCall left right).erase (.symbol "Number") multiplicationSignature frame [frame] [] := by
    simpa [multiplicationSignature, multiplicationCall, Entry.Value.erase, checkedFrames, checkedFailures] using
      (ApplicationChecksRel.checked (expression := (multiplicationCall left right).erase)
        (expected := .symbol "Number") (selected := multiplicationSignature) (before := frame)
        (operator := .symbol "*") (arguments := [.grounded (.int left), .grounded (.int right)])
        (by simp [multiplicationCall, Entry.Value.erase])
        (.cons first (.cons second .nil)) (.cons returned .nil))
  exact ⟨[multiplicationSignature.functionType], signature_lookup space names frame _ declared,
    .selected checked (by simp)⟩

theorem operator_atom {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String) (frame : Frame)
    (declared : getAtomTypes (environment.view world label) (.symbol "*") = [multiplicationSignature.functionType]) :
    Stateful.AtomRel environment label world live scope (.symbol "*") multiplicationSignature.functionType frame
      [(.symbol "*", frame)] world (policy := policy) := by
  have readSymbol : frame.read policy (.symbol "*") = .symbol "*" := by
    simp [Frame.read, Entry.Value.substitute]
  apply Stateful.AtomRel.cast (raw := [(.symbol "*", frame.bindings)])
  · rw [readSymbol]
    apply Entry.Rel.cast (metaType := Atom.symbolType)
    · simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · simpa only [Entry.Value.erase] using MetaTypeRel.symbol "*"
    · decide
    · exact Or.inl ⟨"*", by simp [Entry.Value.erase]⟩
    · simp [Entry.Value.erase, Atom.unit]
  · rw [lookup, readSymbol]
    simp only [Entry.Value.erase]
    apply TypeCastBatchRel.success (earlierTypes := []) (laterTypes := [])
    · exact signature_lookup _ _ frame _ declared
    · rfl
    · simp
    · exact frame.preserved_type_match policy (signature_match frame.bindings)
  · rw [readSymbol]
    exact .cons ⟨by simp [Completed.rawResult, Entry.Value.erase], .same frame,
      by simp [Entry.Value.erase]⟩ .nil

/-- Typed operand delivery preserves any reached caller frame, even when
the caller contains unrelated range or equation variables. -/
theorem numbers_arguments_of_literals {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy)
    (label : Context) (world : World) (scope : List String) (frame : Frame)
    (values : List Int) (live : List Atom)
    (literals : ∀ (reachedLive : List Atom) (value : Int),
      Stateful.AtomRel environment label world reachedLive scope (.grounded (.int value)) (.symbol "Number") frame
        [(.grounded (.int value), frame)] world (policy := policy)) :
    Stateful.ArgumentsRel environment label world live scope
      (values.map fun value => (Entry.Value.grounded (.int value), Atom.symbol "Number")) frame
      [(Entry.Value.argumentPacket (values.map fun value => Entry.Value.grounded (.int value)), frame)] world
      (policy := policy) := by
  induction values generalizing live with
  | nil => exact .nil
  | cons value values ih =>
      have child := literals
        (argumentScope (values.map fun value => (Entry.Value.grounded (.int value), Atom.symbol "Number")) ++ live)
        value
      have rest : Stateful.ArgumentBranchesRel environment label world live scope
          (.grounded (.int value)) (values.map fun value => (Entry.Value.grounded (.int value), Atom.symbol "Number"))
          [] [] world (policy := policy) := .nil
      have branches := Stateful.ArgumentBranchesRel.continuing
        (head := (Entry.Value.grounded (.int value), frame)) (by simp [ArgumentStopped])
        (ih ((Entry.Value.grounded (.int value)).erase :: live)) rest
      apply Stateful.ArgumentsRel.cons child
      simpa only [List.map_cons, List.map_nil, List.append_nil, argumentPrepend_packet] using branches

theorem numbers_arguments {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (policy : Policy)
    (label : Context) (world : World) (scope : List String) (frame : Frame)
    (values : List Int) (live : List Atom) :
    Stateful.ArgumentsRel environment label world live scope
      (values.map fun value => (Entry.Value.grounded (.int value), Atom.symbol "Number")) frame
      [(Entry.Value.argumentPacket (values.map fun value => Entry.Value.grounded (.int value)), frame)] world
      (policy := policy) :=
  numbers_arguments_of_literals environment policy label world scope frame values live
    (fun reachedLive value => number_atom environment lookup policy label world reachedLive scope frame value)

theorem multiplication_read (policy : Policy) (frame : Frame) (left right : Int) :
    frame.read policy (multiplicationCall left right) = multiplicationCall left right := by
  cases rebuilding : policy.rebuilding <;>
    simp [Frame.read, multiplicationCall, Entry.Value.substitute, Entry.Value.rebuildStatus, rebuilding]

theorem multiplication_function {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String)
    (frame : Frame) (left right : Int)
    (declared : getAtomTypes (environment.view world label) (.symbol "*") = [multiplicationSignature.functionType]) :
    Stateful.FunctionRel environment label world live scope (.symbol "Number") multiplicationSignature
      (.symbol "*") [.grounded (.int left), .grounded (.int right)] frame
      [(multiplicationCall left right, frame)] world (policy := policy) := by
  apply Stateful.FunctionRel.evaluated rfl (operator_atom environment lookup policy label world _ _ frame declared)
  have arguments := numbers_arguments environment lookup policy label world scope frame [left, right]
    ((Entry.Value.symbol "*").erase :: live)
  simpa [multiplicationSignature, multiplicationCall, functionAssemble] using
    (Stateful.FunctionBranchesRel.continuing (environment := environment)
      (label := label) (world0 := world) (world1 := world) (world2 := world)
      (live := live) (scope := scope) (policy := policy)
      (head := (Entry.Value.symbol "*", frame))
      (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) arguments .nil)

/-- Full typed-expression composition from a separately earned ordinary
call. Operator and source operands are checked and delivered here; the
premise is not a whole-expression evaluation equality. -/
theorem multiplication_atom_of_call {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (historical : environment.arguments = .historical) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String)
    (frame : Frame) (left right : Int)
    (declared : getAtomTypes (environment.view world label) (.symbol "*") = [multiplicationSignature.functionType])
    (called : Stateful.CallRel environment label world live scope (multiplicationCall left right)
      (.symbol "Number") frame [(.grounded (.int (left * right)), frame)] world (policy := policy)) :
    Stateful.AtomRel environment label world live scope (multiplicationCall left right)
      (.symbol "Number") frame [(.grounded (.int (left * right)), frame)] world (policy := policy) := by
  have entered : Entry.Rel policy.reentry (multiplicationCall left right).status
      (multiplicationCall left right).erase (.symbol "Number") .interpret := by
    simpa [multiplicationCall, Entry.Value.erase, Entry.Value.status] using
      (Entry.Rel.expression (policy := policy.reentry) (status := .active)
        (head := Atom.symbol "*") (tail := [Atom.grounded (.int left), Atom.grounded (.int right)])
        (expected := Atom.symbol "Number")
        (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (by decide) (Or.inr rfl))
  have selected := multiplication_selection (environment.view world label) policy frame live scope left right declared
  have invoked : Stateful.InvocationsRel environment label world live scope (.symbol "Number") multiplicationSignature
      (.symbol "*") [.grounded (.int left), .grounded (.int right)] [frame]
      [(.grounded (.int (left * right)), frame)] world (policy := policy) := by
    have interpreted := multiplication_function environment lookup policy label world
      (invocationReturnType multiplicationSignature :: live) scope frame left right declared
    have calls : Stateful.CallsRel environment label world live scope (invocationReturnType multiplicationSignature)
        [(multiplicationCall left right, frame)] [(.grounded (.int (left * right)), frame)] world
        (policy := policy) := by
      simpa [invocationReturnType, multiplicationSignature, Atom.expressionType] using
        (Stateful.CallsRel.cons (head := (multiplicationCall left right, frame)) called .nil)
    simpa only [List.append_nil] using Stateful.InvocationsRel.cons interpreted calls .nil
  have priority : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase)
      [(.grounded (.int (left * right)), frame)] [(.grounded (.int (left * right)), frame)] := by
    simpa [Entry.Value.erase, isErrorAtom] using
      (Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.successes
        (isError := fun result : Result => isErrorAtom result.1.erase)
        (raw := [(Entry.Value.grounded (.int (left * right)), frame)])
        ⟨(Entry.Value.grounded (.int (left * right)), frame), by simp,
          by simp [Entry.Value.erase, isErrorAtom]⟩)
  have prioritized : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase)
      ([(Entry.Value.grounded (.int (left * right)), frame)].map (readResult policy))
      [(.grounded (.int (left * right)), frame)] := by
    simpa [readResult, Frame.read, Entry.Value.substitute] using priority
  have result := Stateful.AtomRel.function (environment := environment) (label := label) (world0 := world)
    (value := multiplicationCall left right) (frame := frame) (live := live) (scope := scope)
    (policy := policy) (signature := multiplicationSignature) (readiness := .active)
    (by simpa only [multiplication_read] using entered)
    (by rw [multiplication_read]; rfl)
    (by simpa only [historical, multiplication_read, lookup, Entry.Value.erase] using selected) invoked prioritized
  simpa [publishResult, Entry.Value.publish, Entry.Value.withStatus] using result

/-- An independent contextual source theorem for the complete multiplication
expression, under the actual incoming frame rather than an empty surrogate. -/
theorem multiplication_atom_source (services : Minimal.Services) (policy : Policy)
    (space : Space) (live : List Atom) (scope : List String) (frame : Frame) (left right : Int)
    (declared : getAtomTypes space (.symbol "*") = [multiplicationSignature.functionType]) :
    Stateful.AtomRel (arithmeticEnvironment services) space () live scope
      (multiplicationCall left right) (.symbol "Number") frame
      [(.grounded (.int (left * right)), frame)] () (policy := policy) :=
  multiplication_atom_of_call (arithmeticEnvironment services) rfl rfl policy space () live scope frame
    left right declared (multiplication_source services policy space live scope frame left right)

/-- The existing contextual world machine realizes this earned source tree
under arbitrary saved continuations and previously published occurrences. -/
theorem multiplication_retained_run (services : Minimal.Services) (policy : Policy)
    (space : Space) (live : List Atom) (scope : List String) (frame : Frame) (left right : Int)
    (declared : getAtomTypes space (.symbol "*") = [multiplicationSignature.functionType])
    (stack : List RecursiveTasks.Contextual.Continuation) (emitted : List Result) :
    let environment := arithmeticEnvironment services
    RecursiveMachine.Contextual.WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
      ⟨(), space, .work (.atom live scope (multiplicationCall left right) (.symbol "Number") frame), stack, emitted⟩
      ⟨(), space, .returning [(.grounded (.int (left * right)), frame)], stack, emitted⟩ := by
  dsimp only
  exact RecursiveExecution.Contextual.Stateful.local_steps_lift
    (RecursiveExecution.Contextual.Stateful.task_complete
      (task := .atom live scope (multiplicationCall left right) (.symbol "Number") frame)
      (multiplication_atom_source services policy space live scope frame left right declared) stack) emitted

namespace Controls

def sourceSpace : Space := Space.ofList
  [.expression [.symbol ":", .symbol "*", multiplicationSignature.functionType]]

theorem nonempty_alias_frame_source (services : Minimal.Services) (policy : Policy) :
    Stateful.AtomRel (arithmeticEnvironment services) sourceSpace () [.var "x", .var "y"] ["x", "y"]
      (multiplicationCall 6 7) (.symbol "Number") Completed.Controls.argumentAliasFrame
      [(.grounded (.int 42), Completed.Controls.argumentAliasFrame)] () (policy := policy) :=
  multiplication_atom_source services policy sourceSpace _ _ Completed.Controls.argumentAliasFrame 6 7 (by decide +kernel)

/-- The private alias is still readable after arithmetic; erasing the
caller record would change a later observation even though 42 is ground. -/
theorem erasing_caller_changes_future_read (policy : Policy) :
    Completed.Controls.argumentAliasFrame.read policy (.var "x") = .var "y" ∧
      Frame.empty.read policy (.var "x") = .var "x" ∧
      Completed.Controls.argumentAliasFrame.read policy (.var "x") ≠ Frame.empty.read policy (.var "x") := by
  simp [Completed.Controls.argumentAliasFrame, Entry.Value.Controls.aliasEnvironment,
    Frame.read, Frame.empty, Entry.Value.substitute, Entry.Value.resolve, List.lookup]

theorem alias_frame_machine (services : Minimal.Services) (policy : Policy)
    (stack : List RecursiveTasks.Contextual.Continuation) (emitted : List Result) :
    let environment := arithmeticEnvironment services
    RecursiveMachine.Contextual.WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
      ⟨(), sourceSpace,
        .work (.atom [.var "x", .var "y"] ["x", "y"] (multiplicationCall 6 7) (.symbol "Number")
          Completed.Controls.argumentAliasFrame), stack, emitted⟩
      ⟨(), sourceSpace, .returning [(.grounded (.int 42), Completed.Controls.argumentAliasFrame)], stack, emitted⟩ :=
  multiplication_retained_run services policy sourceSpace _ _ Completed.Controls.argumentAliasFrame 6 7
    (by decide +kernel) stack emitted

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEContextualArithmeticSource
