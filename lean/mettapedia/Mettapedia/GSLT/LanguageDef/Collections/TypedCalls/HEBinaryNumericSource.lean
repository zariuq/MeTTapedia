import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStatefulSelectedComposition

/-!
# Closed binary arithmetic source contracts

Addition and comparison used by the authored range program share the same
source selection and operand-delivery structure. Only the local primitive
result and its intrinsic class vary. Contextual frames remain arbitrary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEBinaryNumericSource

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue executeGroundedOp)
open Spec.Eval Spec.Eval.Completed
open Spec.Type Spec.Type.Presentation Spec.Type.Presentation.BindingTheory
open Spec.Match.Merge HEContextualArithmeticSource

structure Operation where
  name : String
  range : String
  result : Int → Int → GroundedValue
  notEmpty : name ≠ "Empty"
  notError : name ≠ "Error"
  rangeNotUndefined : range ≠ "%Undefined%"
  rangeNotAtom : range ≠ "Atom"
  rangeNotGrounded : range ≠ "Grounded"
  rangeNotExpression : range ≠ "Expression"
  resultType : ∀ left right, getGroundedType (result left right) = .symbol range

def Operation.signature (operation : Operation) : SelectedTypePolicy :=
  ⟨CompletedDelivery.arrowType [.symbol "Number", .symbol "Number"] (.symbol operation.range),
    [.symbol "Number", .symbol "Number"], .symbol operation.range, rfl⟩

def Operation.call (operation : Operation) (left right : Int) : Entry.Value :=
  .expression .active [.symbol operation.name, .grounded (.int left), .grounded (.int right)]

theorem return_demand (operation : Operation) :
    invocationReturnType operation.signature = .symbol operation.range := by
  simp [invocationReturnType, Operation.signature, Atom.expressionType, operation.rangeNotExpression]

theorem signature_match (operation : Operation) (bindings : Bindings) :
    TypeMatchRel operation.signature.functionType operation.signature.functionType bindings bindings := by
  have emptyMerge : MergeRel equalityGroundedSemantic Bindings.empty Bindings.empty Bindings.empty :=
    .mk (by simp [constraints, Bindings.empty]) .nil
  exact .structural (by simp [Operation.signature, CompletedDelivery.arrowType, Atom.undefinedType])
    (by simp [Operation.signature, CompletedDelivery.arrowType, Atom.atomType])
    (by simp [Operation.signature, CompletedDelivery.arrowType, Atom.undefinedType])
    (by simp [Operation.signature, CompletedDelivery.arrowType, Atom.atomType])
    (.expression
      (.cons (.symSym "->" semanticLoopFree_empty) emptyMerge
        (.cons (.symSym "Number" semanticLoopFree_empty) emptyMerge
          (.cons (.symSym "Number" semanticLoopFree_empty) emptyMerge
            (.cons (.symSym operation.range semanticLoopFree_empty) emptyMerge .nil)))) semanticLoopFree_empty)
    (.mk (by simp [constraints, Bindings.empty]) .nil)

theorem signature_lookup (operation : Operation) (space : Space) (names : List String)
    (frame : Frame) (expected : Atom)
    (declared : getAtomTypes space (.symbol operation.name) = [operation.signature.functionType]) :
    scopedLookup names space frame.bindings (.symbol operation.name) expected [operation.signature.functionType] := by
  refine ⟨[operation.signature.functionType], ?_, .cons ?_ (.nil _)⟩
  · simpa only [declared] using FirstSuccessSourceReplies.source_types space (.symbol operation.name)
  · exact ⟨id, Function.injective_id, by simp,
      by simp [Operation.signature, CompletedDelivery.arrowType, TypeSubst.typeVars, TypeSubst.typeVarsList]⟩

theorem selection (operation : Operation) (space : Space) (policy : Policy) (frame : Frame)
    (live : List Atom) (scope : List String) (left right : Int) (expected : Atom)
    (matched : TypeMatchRel expected (.symbol operation.range) frame.bindings frame.bindings)
    (declared : getAtomTypes space (.symbol operation.name) = [operation.signature.functionType]) :
    InvocationSelectionRel space scopedLookup policy live scope (operation.call left right).erase
      (.symbol operation.name) expected frame (.selected operation.signature [frame]) := by
  let names := invocationTypeScope scope live (operation.call left right).erase expected frame.bindings
  have first := numeric_argument_checks space names policy frame (operation.call left right).erase 1 left
  have second := numeric_argument_checks space names policy frame (operation.call left right).erase 2 right
  have returned : TypeCheckRel policy expected frame (.symbol operation.range) (.inr frame) :=
    .accepted (.unchanged (frame.preserved_type_match policy matched))
  have checked : ApplicationChecksRel space (scopedLookup names space) policy
      (operation.call left right).erase expected operation.signature frame [frame] [] := by
    simpa [Operation.signature, Operation.call, Entry.Value.erase, checkedFrames, checkedFailures] using
      (ApplicationChecksRel.checked (expression := (operation.call left right).erase)
        (expected := expected) (selected := operation.signature) (before := frame)
        (operator := .symbol operation.name) (arguments := [.grounded (.int left), .grounded (.int right)])
        (by simp [Operation.call, Entry.Value.erase])
        (.cons first (.cons second .nil)) (.cons returned .nil))
  exact ⟨[operation.signature.functionType], signature_lookup operation space names frame _ declared,
    .selected checked (by simp)⟩

theorem operator_atom_of_query {Context World : Type} (environment : WorldEnvironment Context World)
    (operation : Operation) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String) (frame : Frame)
    (queried : environment.lookup
      (invocationTypeScope scope live (.symbol operation.name) operation.signature.functionType frame.bindings)
      (environment.view world label) frame.bindings (.symbol operation.name) operation.signature.functionType
      [operation.signature.functionType]) :
    Stateful.AtomRel environment label world live scope (.symbol operation.name) operation.signature.functionType frame
      [(.symbol operation.name, frame)] world (policy := policy) := by
  have readSymbol : frame.read policy (.symbol operation.name) = .symbol operation.name := by
    simp [Frame.read, Entry.Value.substitute]
  apply Stateful.AtomRel.cast (raw := [(.symbol operation.name, frame.bindings)])
  · rw [readSymbol]
    apply Entry.Rel.cast (metaType := Atom.symbolType)
    · simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty, operation.notEmpty]
    · simpa only [Entry.Value.erase] using MetaTypeRel.symbol operation.name
    · simp [Operation.signature, CompletedDelivery.arrowType, Atom.atomType, Atom.symbolType, Atom.variableType]
    · exact Or.inl ⟨operation.name, by simp [Entry.Value.erase]⟩
    · simp [Entry.Value.erase, Atom.unit]
  · rw [readSymbol]
    simp only [Entry.Value.erase]
    apply TypeCastBatchRel.success (earlierTypes := []) (laterTypes := [])
    · exact queried
    · rfl
    · simp
    · exact frame.preserved_type_match policy (signature_match operation frame.bindings)
  · rw [readSymbol]
    exact .cons ⟨by simp [Completed.rawResult, Entry.Value.erase], .same frame,
      by simp [Entry.Value.erase]⟩ .nil

theorem operator_atom {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (operation : Operation) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String) (frame : Frame)
    (declared : getAtomTypes (environment.view world label) (.symbol operation.name) = [operation.signature.functionType]) :
    Stateful.AtomRel environment label world live scope (.symbol operation.name) operation.signature.functionType frame
      [(.symbol operation.name, frame)] world (policy := policy) := by
  apply operator_atom_of_query environment operation policy label world live scope frame
  rw [lookup]
  exact signature_lookup operation _ _ frame _ declared

theorem call_read (operation : Operation) (policy : Policy) (frame : Frame) (left right : Int) :
    frame.read policy (operation.call left right) = operation.call left right := by
  cases rebuilding : policy.rebuilding <;>
    simp [Frame.read, Operation.call, Entry.Value.substitute, Entry.Value.rebuildStatus, rebuilding]

/-- The complete typed source call is derived from its local primitive
operation, with source selection and the ordinary result gate both retained. -/
theorem source_call {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (historical : environment.arguments = .historical)
    (operation : Operation) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String)
    (frame : Frame) (left right : Int) (expected : Atom)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (matched : TypeMatchRel expected (.symbol operation.range) frame.bindings frame.bindings)
    (declared : getAtomTypes (environment.view world label) (.symbol operation.name) = [operation.signature.functionType])
    (executable : environment.dispatch.executable (.symbol operation.name))
    (raw : environment.dispatch.bindingMode (.symbol operation.name) [.grounded (.int left), .grounded (.int right)] = .raw)
    (emitted : environment.dispatch.valueProvenance (.symbol operation.name) [.grounded (.int left), .grounded (.int right)] = .emitted)
    (executed : environment.services.groundedAt label world live scope frame (operation.call left right)
      (.ok [(.grounded (operation.result left right), Bindings.empty)]) world) :
    Stateful.AtomRel environment label world live scope (operation.call left right) expected frame
      [(.grounded (operation.result left right), frame)] world (policy := policy) := by
  let output : Entry.Value := .grounded (operation.result left right)
  have called := emitted_scalar_return environment lookup policy label world live scope frame
    (operation.call left right) (.symbol operation.name) [.grounded (.int left), .grounded (.int right)]
    (operation.result left right) operation.range (by simp [Operation.call, Entry.Value.erase]) executable
    (by simp [Operation.call, Entry.Value.erase, IsErrorRel, operation.notError]) raw emitted executed
    (operation.resultType left right) operation.rangeNotUndefined operation.rangeNotAtom operation.rangeNotGrounded
  have arguments := numbers_arguments environment lookup policy label world scope frame [left, right]
    ((Entry.Value.symbol operation.name).erase :: invocationReturnType operation.signature :: live)
  have calls : Stateful.CallsRel environment label world live scope (invocationReturnType operation.signature)
      ([(Entry.Value.argumentPacket [.grounded (.int left), .grounded (.int right)], frame)].map
        (functionAssemble (.symbol operation.name))) [(output, frame)] world (policy := policy) := by
    simpa [Operation.signature, invocationReturnType, Atom.expressionType, operation.rangeNotExpression,
      functionAssemble, Operation.call, output] using
      (Stateful.CallsRel.cons (head := (operation.call left right, frame)) called .nil)
  have priority : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase)
      ([(output, frame)].map (readResult policy)) [(output, frame)] := by
    simpa [output, readResult, Frame.read, Entry.Value.substitute, Entry.Value.erase, isErrorAtom] using
      (Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.successes
        (isError := fun result : Result => isErrorAtom result.1.erase) (raw := [(output, frame)])
        ⟨(output, frame), by simp, by simp [output, Entry.Value.erase, isErrorAtom]⟩)
  have source := HEStatefulSelectedComposition.selected_of_parts environment policy label world world world world
    live scope (operation.call left right) expected frame frame frame .active
    (.symbol operation.name) (.symbol operation.name) [.grounded (.int left), .grounded (.int right)] operation.signature
    [(Entry.Value.argumentPacket [.grounded (.int left), .grounded (.int right)], frame)] [(output, frame)] [(output, frame)]
    (by
      rw [call_read]
      simpa [Operation.call, Entry.Value.erase, Entry.Value.status] using
        (Entry.Rel.expression (policy := policy.reentry) (status := .active)
          (head := Atom.symbol operation.name) (tail := [Atom.grounded (.int left), Atom.grounded (.int right)])
          (expected := expected)
          (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, operation.notError])
          (by
            rintro (asAtom | asExpression | impossible)
            · exact notAtom asAtom
            · exact notExpression asExpression
            · exact (by decide : Atom.expressionType ≠ Atom.variableType) impossible) (Or.inr rfl)))
    (by rw [call_read]; rfl)
    (by simpa only [historical, call_read, lookup, Entry.Value.erase] using
      selection operation (environment.view world label) policy frame live scope left right expected matched declared)
    rfl (operator_atom environment lookup operation policy label world _ _ frame declared)
    (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty, operation.notEmpty])
    arguments calls priority
  simpa [output, publishResult, Entry.Value.publish, Entry.Value.withStatus] using source

def addition : Operation where
  name := "+"
  range := "Number"
  result := fun left right => .int (left + right)
  notEmpty := by decide
  notError := by decide
  rangeNotUndefined := by decide
  rangeNotAtom := by decide
  rangeNotGrounded := by decide
  rangeNotExpression := by decide
  resultType := fun _ _ => rfl

def greaterEqual : Operation where
  name := ">="
  range := "Bool"
  result := fun left right => .bool (decide (left ≥ right))
  notEmpty := by decide
  notError := by decide
  rangeNotUndefined := by decide
  rangeNotAtom := by decide
  rangeNotGrounded := by decide
  rangeNotExpression := by decide
  resultType := fun _ _ => rfl

/-- This service is precisely the existing primitive table on the two
operators used by range. It does not implement conditionals or recursion. -/
def primitiveDispatch : Spec.Eval.GroundedDispatch where
  executable operator := operator = .symbol "+" ∨ operator = .symbol ">="
  outcome operator arguments outcome := ∃ result,
    executeGroundedOp operator arguments = some result ∧
      outcome = .ok [(result, Bindings.empty)]

def primitiveEnvironment (services : Minimal.Services) : WorldEnvironment Space Unit where
  view := fun _ => id
  services := WorldServices.readOnlyGrounded services primitiveDispatch
  dispatch := primitiveDispatch
  lookup := scopedLookup

theorem addition_executes (left right : Int) :
    executeGroundedOp (.symbol addition.name) [.grounded (.int left), .grounded (.int right)] =
      some (.grounded (addition.result left right)) := rfl

theorem greaterEqual_executes (left right : Int) :
    executeGroundedOp (.symbol greaterEqual.name) [.grounded (.int left), .grounded (.int right)] =
      some (.grounded (greaterEqual.result left right)) := rfl

theorem primitive_source (services : Minimal.Services) (policy : Policy) (space : Space)
    (operation : Operation) (live : List Atom) (scope : List String) (frame : Frame)
    (left right : Int) (expected : Atom)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (matched : TypeMatchRel expected (.symbol operation.range) frame.bindings frame.bindings)
    (declared : getAtomTypes space (.symbol operation.name) = [operation.signature.functionType])
    (member : operation.name = "+" ∨ operation.name = ">=")
    (executed : executeGroundedOp (.symbol operation.name)
      [.grounded (.int left), .grounded (.int right)] = some (.grounded (operation.result left right))) :
    Stateful.AtomRel (primitiveEnvironment services) space () live scope
      (operation.call left right) expected frame [(.grounded (operation.result left right), frame)] ()
      (policy := policy) := by
  apply source_call (primitiveEnvironment services) rfl rfl operation policy space () live scope frame
    left right expected notAtom notExpression matched declared
  · rcases member with first | second
    · exact Or.inl (congrArg Atom.symbol first)
    · exact Or.inr (congrArg Atom.symbol second)
  · rfl
  · rfl
  · exact ⟨.symbol operation.name, [.grounded (.int left), .grounded (.int right)],
      .ok [(.grounded (operation.result left right), Bindings.empty)],
      by simp [Operation.call, Entry.Value.erase],
      ⟨.grounded (operation.result left right), executed, rfl⟩,
      by simp [GroundedResult.map, Entry.Value.ofAtom]⟩

theorem addition_source (services : Minimal.Services) (policy : Policy) (space : Space)
    (live : List Atom) (scope : List String) (frame : Frame) (left right : Int)
    (declared : getAtomTypes space (.symbol "+") = [addition.signature.functionType]) :
    Stateful.AtomRel (primitiveEnvironment services) space () live scope
      (addition.call left right) Atom.undefinedType frame [(.grounded (.int (left + right)), frame)] ()
      (policy := policy) :=
  primitive_source services policy space addition live scope frame left right Atom.undefinedType
    (by decide) (by decide) (.undefinedLeft _ _) declared (Or.inl rfl) (addition_executes left right)

theorem comparison_source (services : Minimal.Services) (policy : Policy) (space : Space)
    (live : List Atom) (scope : List String) (frame : Frame) (left right : Int)
    (declared : getAtomTypes space (.symbol ">=") = [greaterEqual.signature.functionType]) :
    Stateful.AtomRel (primitiveEnvironment services) space () live scope
      (greaterEqual.call left right) (.symbol "Bool") frame
      [(.grounded (.bool (decide (left ≥ right))), frame)] () (policy := policy) :=
  primitive_source services policy space greaterEqual live scope frame left right (.symbol "Bool")
    (by decide) (by decide) (same_symbol_match "Bool" frame.bindings (by decide) (by decide))
    declared (Or.inr rfl) (greaterEqual_executes left right)

namespace Controls

def expressionSignature : SelectedTypePolicy :=
  ⟨CompletedDelivery.arrowType [.symbol "Number", .symbol "Number"] Atom.expressionType,
    [.symbol "Number", .symbol "Number"], Atom.expressionType, rfl⟩

/-- Expression ranges have a different ordinary invocation demand; treating
them as the arithmetic class case would silently change source evaluation. -/
theorem expression_range_projection :
    invocationReturnType expressionSignature = Atom.undefinedType ∧
      invocationReturnType expressionSignature ≠ expressionSignature.returnType := by
  constructor <;> decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEBinaryNumericSource
