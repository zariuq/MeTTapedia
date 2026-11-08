import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionWorld
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStatefulSelectedComposition
import Mettapedia.Languages.MeTTa.HE.ScalarValueCasts

/-! Typed arithmetic source leaves in the collection world. Admission,
operator casts, argument delivery and the ordinary native return are earned
from their local queries; no arithmetic evaluator replaces source control. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionArithmetic

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type Spec.Type.Presentation
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment)
open HEBinaryNumericSource (Operation)

open private atomVariables_eq_typeVars from Mettapedia.Languages.MeTTa.HE.EquationFreshening

variable (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
  (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)

local notation "current" => environment minimal nativePolicy external active primitive subtypes
local notation "ops" => HECollectionInferredQueries.currentOps external active primitive subtypes
local notation "label" => HECollectionSpaceExtension.space

theorem closed_operator (world : World) (policy : Policy) (live : List Atom) (scope : List String) (before : Frame)
    (name : String) (type : Atom) (notEmpty : name ≠ "Empty")
    (notAtom : type ≠ Atom.atomType) (notSymbol : type ≠ Atom.symbolType)
    (declared : getAnnotatedTypes label (.symbol name) = [type]) (closed : atomVariables type = []) :
    Stateful.AtomRel current label world live scope (.symbol name) type before [(.symbol name, before)] world (policy := policy) := by
  have queried := HECollectionInferredQueries.closed_head ops external
    (invocationTypeScope scope live (.symbol name) type before.bindings) before name type type declared closed
  have typeClosed : TypeSubst.typeVars type = [] := by
    simpa only [atomVariables_eq_typeVars] using closed
  have matched := before.preserved_type_match policy
    (FirstSuccessSourceApplicability.closed_type_match type before.bindings (sizeOf type + sizeOf type + 2)
      typeClosed (Nat.le_refl _)).2
  have read : before.read policy (.symbol name) = .symbol name := by simp [Frame.read, Entry.Value.substitute]
  apply Stateful.AtomRel.cast (raw := [(.symbol name, before.bindings)])
  · rw [read]
    apply Entry.Rel.cast (metaType := Atom.symbolType)
    · simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty, notEmpty]
    · simpa only [Entry.Value.erase] using MetaTypeRel.symbol name
    · rintro (asAtom | asSymbol | impossible)
      · exact notAtom asAtom
      · exact notSymbol asSymbol
      · exact (by decide : Atom.symbolType ≠ Atom.variableType) impossible
    · exact Or.inl ⟨name, by simp only [Entry.Value.erase]⟩
    · simp [Entry.Value.erase, Atom.unit]
  · rw [read]
    simp only [Entry.Value.erase]
    exact TypeCastBatchRel.success (earlierTypes := []) (laterTypes := []) queried rfl (by simp) matched
  · rw [read]
    exact .cons ⟨by simp [rawResult, Entry.Value.erase], .same before, by simp [Entry.Value.erase]⟩ .nil

theorem number_source (world : World) (policy : Policy) (live : List Atom) (scope : List String) (before : Frame) (value : Int) :
    Stateful.AtomRel current label world live scope (.grounded (.int value)) (.symbol "Number") before
      [(.grounded (.int value), before)] world (policy := policy) :=
  Stateful.scalar_from_query current policy label world live scope before (.int value) "Number"
    (by decide) (by decide) (by decide) (HECollectionInferredQueries.number_query ops external _ before value _)

theorem boolean_source (world : World) (policy : Policy) (live : List Atom) (scope : List String) (before : Frame) (value : Bool) :
    Stateful.AtomRel current label world live scope (.grounded (.bool value)) (.symbol "Bool") before
      [(.grounded (.bool value), before)] world (policy := policy) :=
  Stateful.scalar_from_query current policy label world live scope before (.bool value) "Bool"
    (by decide) (by decide) (by decide) (HECollectionInferredQueries.boolean_query ops external _ before value _)

theorem number_undefined (world : World) (policy : Policy) (live : List Atom) (scope : List String) (before : Frame) (value : Int) :
    Stateful.AtomRel current label world live scope (.grounded (.int value)) Atom.undefinedType before
      [(.grounded (.int value), before)] world (policy := policy) := by
  have read : before.read policy (.grounded (.int value)) = .grounded (.int value) := by simp [Frame.read, Entry.Value.substitute]
  apply Stateful.AtomRel.cast (raw := [(.grounded (.int value), before.bindings)])
  · rw [read]
    apply Entry.Rel.cast (metaType := Atom.groundedType)
    · simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · simpa only [Entry.Value.erase] using MetaTypeRel.grounded (.int value)
    · decide
    · exact Or.inr (Or.inl ⟨.int value, by simp [Entry.Value.erase]⟩)
    · simp [Entry.Value.erase, Atom.unit]
  · rw [read]
    simp only [Entry.Value.erase]
    exact TypeCastBatchRel.success (earlierTypes := []) (laterTypes := [])
      (HECollectionInferredQueries.number_query ops external _ before value _) rfl (by simp)
      (before.preserved_type_match policy (.undefinedLeft _ _))
  · rw [read]
    exact .cons ⟨by simp [rawResult, Entry.Value.erase], .same before, by simp [Entry.Value.erase]⟩ .nil

theorem number_admission (scope : List String) (policy : Policy) (before : Frame)
    (expression : Atom) (position : Nat) (value : Int) :
    KindArgumentAdmissionRel label ((current).lookup scope label) policy expression
      (.grounded (.int value)) (.symbol "Number") position before [before] [] := by
  apply HEArgumentMetatypeRole.singleton_inferred
  · intro kind _ cut
    have possible := HEArgumentMetatypeRole.native_cut cut
    have absent : TypeScopeMatcher.metaCheckAtom (.symbol "Number") kind = none := rfl
    rw [absent] at possible
    cases possible
  · exact HECollectionInferredQueries.number_query ops external scope before value _
  · exact .unchanged (before.preserved_type_match policy
      (same_symbol_type_match "Number" before.bindings (by decide) (by decide)))

theorem selection (operation : Operation) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (left right : Int) (expected : Atom)
    (declared : getAnnotatedTypes label (.symbol operation.name) = [operation.signature.functionType])
    (matched : TypeMatchRel expected (.symbol operation.range) before.bindings before.bindings) :
    (current).arguments.selection label (current).lookup policy live scope
      (operation.call left right).erase (.symbol operation.name) expected before (.selected operation.signature [before]) := by
  let names := invocationTypeScope scope live (operation.call left right).erase expected before.bindings
  refine ⟨[operation.signature.functionType], HECollectionInferredQueries.closed_head ops external names before operation.name _ _ declared rfl, ?_⟩
  apply AdmissionScanRel.selected (errors := []) ?_ (by simp)
  have args : AdmissionArgumentsRel KindArgumentAdmissionRel label ((current).lookup names label) policy
      (operation.call left right).erase 1 [.grounded (.int left), .grounded (.int right)]
      [.symbol "Number", .symbol "Number"] [before] [before] [] :=
    .cons (AdmissionFramesRel.single (number_admission minimal nativePolicy external active primitive subtypes names policy before _ 1 left))
      (.cons (AdmissionFramesRel.single (number_admission minimal nativePolicy external active primitive subtypes names policy before _ 2 right)) .nil)
  simpa [Operation.signature, checkedFrames, checkedFailures, names] using
    AdmissionApplicationRel.checked (admit := KindArgumentAdmissionRel)
      (expression := (operation.call left right).erase) (expected := expected) (selected := operation.signature)
      (before := before) (operator := .symbol operation.name)
      (arguments := [.grounded (.int left), .grounded (.int right)])
      (by simp [Operation.call, Entry.Value.erase]) args
      (List.Forall₂.cons (TypeCheckRel.accepted (.unchanged (before.preserved_type_match policy matched))) List.Forall₂.nil)

theorem source_call (world : World) (operation : Operation) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (left right : Int) (expected : Atom)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (declared : getAnnotatedTypes label (.symbol operation.name) = [operation.signature.functionType])
    (matched : TypeMatchRel expected (.symbol operation.range) before.bindings before.bindings)
    (executable : (current).dispatch.executable (.symbol operation.name))
    (emitted : (current).dispatch.valueProvenance (.symbol operation.name) [.grounded (.int left), .grounded (.int right)] = .emitted)
    (executed : (current).services.groundedAt label world live scope before (operation.call left right)
      (.ok [(.grounded (operation.result left right), Bindings.empty)]) world)
    (returned : Stateful.AtomRel current label world live scope (.grounded (operation.result left right)) (.symbol operation.range) before
      [(.grounded (operation.result left right), before)] world (policy := policy)) :
    Stateful.AtomRel current label world live scope (operation.call left right) expected before
      [(.grounded (operation.result left right), before)] world (policy := policy) := by
  let output := Entry.Value.grounded (operation.result left right)
  have called := HEContextualArithmeticSource.emitted_scalar_return_of_source current policy label world live scope before
    (operation.call left right) (.symbol operation.name) [.grounded (.int left), .grounded (.int right)]
    (operation.result left right) operation.range (by simp [Operation.call, Entry.Value.erase]) executable
    (by simp [Operation.call, Entry.Value.erase, IsErrorRel, operation.notError]) rfl emitted executed returned
  have arguments := HEContextualArithmeticSource.numbers_arguments_of_literals current policy label world scope before
    [left, right] ((Entry.Value.symbol operation.name).erase :: invocationReturnType operation.signature :: live)
    (fun reachedLive value => number_source minimal nativePolicy external active primitive subtypes world policy reachedLive scope before value)
  have calls : Stateful.CallsRel current label world live scope (invocationReturnType operation.signature)
      ([(Entry.Value.argumentPacket [.grounded (.int left), .grounded (.int right)], before)].map
        (functionAssemble (.symbol operation.name))) [(output, before)] world (policy := policy) := by
    simpa [HEBinaryNumericSource.return_demand, functionAssemble, Operation.call, output] using
      (Stateful.CallsRel.cons (head := (operation.call left right, before)) called .nil)
  have priority : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase)
      ([(output, before)].map (readResult policy)) [(output, before)] := by
    simpa [output, readResult, Frame.read, Entry.Value.substitute, Entry.Value.erase, isErrorAtom] using
      (Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.successes
        (isError := fun result : Result => isErrorAtom result.1.erase) (raw := [(output, before)])
        ⟨(output, before), by simp, by simp [output, Entry.Value.erase, isErrorAtom]⟩)
  have complete := HEStatefulSelectedComposition.selected_of_parts current policy label world world world world
    live scope (operation.call left right) expected before before before .active
    (.symbol operation.name) (.symbol operation.name) [.grounded (.int left), .grounded (.int right)] operation.signature
    [(Entry.Value.argumentPacket [.grounded (.int left), .grounded (.int right)], before)] [(output, before)] [(output, before)]
    (by
      rw [HEBinaryNumericSource.call_read]
      simp only [Operation.call, Entry.Value.status, Entry.Value.erase, List.map_cons, List.map_nil]
      apply Entry.Rel.expression
      · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, operation.notError]
      · rintro (asAtom | asExpression | impossible)
        · exact notAtom asAtom
        · exact notExpression asExpression
        · exact (by decide : Atom.expressionType ≠ Atom.variableType) impossible
      · exact Or.inr rfl)
    (by rw [HEBinaryNumericSource.call_read]; rfl)
    (by simpa only [HEBinaryNumericSource.call_read, environment, id_eq, Entry.Value.erase] using
      selection minimal nativePolicy external active primitive subtypes operation policy before live scope left right expected declared matched)
    rfl (HEBinaryNumericSource.operator_atom_of_query current operation policy label world _ _ before
      (HECollectionInferredQueries.closed_head ops external _ before operation.name _ _ declared rfl))
    (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty, operation.notEmpty]) arguments calls priority
  simpa [output, publishResult, Entry.Value.publish, Entry.Value.withStatus] using complete

theorem primitive_call (world : World) (before : Frame) (live : List Atom) (scope : List String)
    (operation : Operation) (left right : Int) (allowed : operation.name ∈ ["+", ">=", "*"])
    (calculated : Mettapedia.Languages.MeTTa.OSLFCore.executeGroundedOp (.symbol operation.name)
      [.grounded (.int left), .grounded (.int right)] = some (.grounded (operation.result left right))) :
    (current).services.groundedAt label world live scope before (operation.call left right)
      (.ok [(.grounded (operation.result left right), Bindings.empty)]) world := by
  refine ⟨rfl, ?_⟩
  have raw : HECollectionWorld.Primitive nativePolicy label world live scope before
      (.expression .active [.symbol operation.name, .grounded (.int left), .grounded (.int right)])
      (.ok [(Entry.Value.ofAtom (.grounded (operation.result left right)), Bindings.empty)]) :=
    .numeric allowed (by simpa only [List.map_cons, List.map_nil, Entry.Value.erase] using calculated)
  simpa only [Operation.call, Entry.Value.ofAtom] using raw

theorem addition_source (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (left right : Int) :
    Stateful.AtomRel current label world live scope (HEBinaryNumericSource.addition.call left right) Atom.undefinedType before
      [(.grounded (.int (left + right)), before)] world (policy := policy) := by
  apply source_call minimal nativePolicy external active primitive subtypes world HEBinaryNumericSource.addition policy before
    live scope left right Atom.undefinedType (by decide) (by decide)
  · rfl
  · exact .undefinedLeft _ _
  · simp [environment, HECollectionWorld.dispatch, HEBinaryNumericSource.addition]
  · simp [environment, HECollectionWorld.dispatch, HEBinaryNumericSource.addition, CollectionStdlibSource.appendName]
  · exact primitive_call minimal nativePolicy external active primitive subtypes world before live scope HEBinaryNumericSource.addition
      left right (by simp [HEBinaryNumericSource.addition]) (HEBinaryNumericSource.addition_executes left right)
  · exact number_source minimal nativePolicy external active primitive subtypes world policy live scope before (left + right)

theorem comparison_source (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (left right : Int) :
    Stateful.AtomRel current label world live scope (HEBinaryNumericSource.greaterEqual.call left right) (.symbol "Bool") before
      [(.grounded (.bool (decide (left ≥ right))), before)] world (policy := policy) := by
  apply source_call minimal nativePolicy external active primitive subtypes world HEBinaryNumericSource.greaterEqual policy before
    live scope left right (.symbol "Bool") (by decide) (by decide)
  · rfl
  · exact same_symbol_type_match "Bool" before.bindings (by decide) (by decide)
  · simp [environment, HECollectionWorld.dispatch, HEBinaryNumericSource.greaterEqual]
  · simp [environment, HECollectionWorld.dispatch, HEBinaryNumericSource.greaterEqual, CollectionStdlibSource.appendName]
  · exact primitive_call minimal nativePolicy external active primitive subtypes world before live scope HEBinaryNumericSource.greaterEqual
      left right (by simp [HEBinaryNumericSource.greaterEqual]) (HEBinaryNumericSource.greaterEqual_executes left right)
  · exact boolean_source minimal nativePolicy external active primitive subtypes world policy live scope before (decide (left ≥ right))

def multiplication : Operation where
  name := "*"
  range := "Number"
  result := fun left right => .int (left * right)
  notEmpty := by decide
  notError := by decide
  rangeNotUndefined := by decide
  rangeNotAtom := by decide
  rangeNotGrounded := by decide
  rangeNotExpression := by decide
  resultType _ _ := rfl

theorem multiplication_source (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (left right : Int) :
    Stateful.AtomRel current label world live scope (multiplication.call left right) (.symbol "Number") before
      [(.grounded (.int (left * right)), before)] world (policy := policy) := by
  apply source_call minimal nativePolicy external active primitive subtypes world multiplication policy before
    live scope left right (.symbol "Number") (by decide) (by decide)
  · rfl
  · exact same_symbol_type_match "Number" before.bindings (by decide) (by decide)
  · simp [environment, HECollectionWorld.dispatch, multiplication]
  · simp [environment, HECollectionWorld.dispatch, multiplication, CollectionStdlibSource.appendName]
  · exact primitive_call minimal nativePolicy external active primitive subtypes world before live scope multiplication
      left right (by simp [multiplication]) rfl
  · exact number_source minimal nativePolicy external active primitive subtypes world policy live scope before (left * right)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionArithmetic
