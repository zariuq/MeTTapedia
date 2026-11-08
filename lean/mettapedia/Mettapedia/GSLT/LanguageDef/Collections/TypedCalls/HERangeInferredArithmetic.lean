import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeAdmissionBoundary

/-!
# Range arithmetic through actual inferred reads

The source composition reuses the existing scalar return, literal delivery,
and selected-call algebra. Only the reached typing/admission ports change;
addition and comparison remain the original local primitive operations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeInferredArithmetic

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type
open RetainedTypePayloads (ExternalView)
open HERangeAdmissionBoundary (environment lookup)
open HERangeSourceProgram (space)
open HEBinaryNumericSource (Operation)

theorem signature_query (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (scope : List String) (before : Frame) (operation : Operation) (expected : Atom)
    (declared : NativeTypeSourcePorts.rawDeclarations HERangeTypeReadPrimitives.source world (.symbol operation.name) =
      [operation.signature.functionType]) :
    HERangeArgumentQueryTransport.inferredRead currentOps world scope before.bindings
      (.symbol operation.name) expected [operation.signature.functionType] := by
  let supply : TypeReadSupply.Supply :=
    ⟨invocationTypeScope scope [] (.symbol operation.name) expected before.bindings, 0⟩
  exact ⟨supply, 1, fun _ member => member,
    HERangeTypeReadApplications.closed_symbol currentOps world 0 supply operation.name operation.signature.functionType
      declared rfl⟩

theorem number_admission (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (scope : List String) (policy : Policy) (before : Frame)
    (expression : Atom) (position : Nat) (value : Int) :
    KindArgumentAdmissionRel space (lookup currentOps world scope space) policy expression
      (.grounded (.int value)) (.symbol "Number") position before [before] [] := by
  apply HEArgumentMetatypeRole.singleton_inferred
  · intro kind _ cut
    have possible := HEArgumentMetatypeRole.native_cut cut
    have absent : TypeScopeMatcher.metaCheckAtom (.symbol "Number") kind = none := rfl
    rw [absent] at possible
    cases possible
  · exact HERangeAdmissionBoundary.number_query currentOps world scope before value _
  · exact .unchanged (before.preserved_type_match policy
      (same_symbol_type_match "Number" before.bindings (by decide) (by decide)))

theorem selection (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (operation : Operation) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (left right : Int) (expected : Atom)
    (declared : NativeTypeSourcePorts.rawDeclarations HERangeTypeReadPrimitives.source world (.symbol operation.name) =
      [operation.signature.functionType])
    (matched : TypeMatchRel expected (.symbol operation.range) before.bindings before.bindings) :
    kindArgumentService.selection space (lookup currentOps world) policy live scope
      (operation.call left right).erase (.symbol operation.name) expected before (.selected operation.signature [before]) := by
  let names := invocationTypeScope scope live (operation.call left right).erase expected before.bindings
  refine ⟨[operation.signature.functionType], signature_query currentOps world names before operation _ declared, ?_⟩
  apply AdmissionScanRel.selected (errors := []) ?_ (by simp)
  have args : AdmissionArgumentsRel KindArgumentAdmissionRel space (lookup currentOps world names space) policy
      (operation.call left right).erase 1 [.grounded (.int left), .grounded (.int right)]
      [.symbol "Number", .symbol "Number"] [before] [before] [] :=
    .cons (AdmissionFramesRel.single (number_admission currentOps world names policy before _ 1 left))
      (.cons (AdmissionFramesRel.single (number_admission currentOps world names policy before _ 2 right)) .nil)
  simpa [Operation.signature, checkedFrames, checkedFailures, names] using
    AdmissionApplicationRel.checked (admit := KindArgumentAdmissionRel)
      (expression := (operation.call left right).erase) (expected := expected) (selected := operation.signature)
      (before := before) (operator := .symbol operation.name)
      (arguments := [.grounded (.int left), .grounded (.int right)])
      (by simp [Operation.call, Entry.Value.erase]) args
      (List.Forall₂.cons (TypeCheckRel.accepted (.unchanged (before.preserved_type_match policy matched))) List.Forall₂.nil)

theorem source_call (minimal : Minimal.Services)
    (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom) (world : ExternalView)
    (operation : Operation) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (left right : Int) (expected : Atom)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (declared : NativeTypeSourcePorts.rawDeclarations HERangeTypeReadPrimitives.source world (.symbol operation.name) =
      [operation.signature.functionType])
    (matched : TypeMatchRel expected (.symbol operation.range) before.bindings before.bindings)
    (executable : HERangeSourceProgram.dispatch.executable (.symbol operation.name))
    (executed : HERangeSourceProgram.localPrimitive (operation.call left right) =
      .ok [(.grounded (operation.result left right), Bindings.empty)])
    (returned : Stateful.AtomRel (environment minimal currentOps world) space () live scope
      (.grounded (operation.result left right)) (.symbol operation.range) before
      [(.grounded (operation.result left right), before)] () (policy := policy)) :
    Stateful.AtomRel (environment minimal currentOps world) space () live scope
      (operation.call left right) expected before [(.grounded (operation.result left right), before)] () (policy := policy) := by
  let current := environment minimal currentOps world
  let output : Entry.Value := .grounded (operation.result left right)
  have called := HEContextualArithmeticSource.emitted_scalar_return_of_source current policy space () live scope before
    (operation.call left right) (.symbol operation.name) [.grounded (.int left), .grounded (.int right)]
    (operation.result left right) operation.range (by simp [Operation.call, Entry.Value.erase]) executable
    (by simp [Operation.call, Entry.Value.erase, IsErrorRel, operation.notError]) rfl rfl executed.symm returned
  have arguments := HEContextualArithmeticSource.numbers_arguments_of_literals current policy space () scope before
    [left, right] ((Entry.Value.symbol operation.name).erase :: invocationReturnType operation.signature :: live)
    (fun reachedLive value => HERangeAdmissionBoundary.number_source minimal currentOps world policy reachedLive scope before value)
  have calls : Stateful.CallsRel current space () live scope (invocationReturnType operation.signature)
      ([(Entry.Value.argumentPacket [.grounded (.int left), .grounded (.int right)], before)].map
        (functionAssemble (.symbol operation.name))) [(output, before)] () (policy := policy) := by
    simpa [HEBinaryNumericSource.return_demand, functionAssemble, Operation.call, output] using
      (Stateful.CallsRel.cons (head := (operation.call left right, before)) called .nil)
  have priority : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase)
      ([(output, before)].map (readResult policy)) [(output, before)] := by
    simpa [output, readResult, Frame.read, Entry.Value.substitute, Entry.Value.erase, isErrorAtom] using
      (Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.successes
        (isError := fun result : Result => isErrorAtom result.1.erase) (raw := [(output, before)])
        ⟨(output, before), by simp, by simp [output, Entry.Value.erase, isErrorAtom]⟩)
  have source := HEStatefulSelectedComposition.selected_of_parts current policy space () () () ()
    live scope (operation.call left right) expected before before before .active (.symbol operation.name) (.symbol operation.name)
    [.grounded (.int left), .grounded (.int right)] operation.signature
    [(Entry.Value.argumentPacket [.grounded (.int left), .grounded (.int right)], before)] [(output, before)] [(output, before)]
    (by
      rw [HEBinaryNumericSource.call_read]
      simpa [Operation.call, Entry.Value.erase, Entry.Value.status] using
        Entry.Rel.expression (policy := policy.reentry) (status := .active) (head := Atom.symbol operation.name)
          (tail := [Atom.grounded (.int left), Atom.grounded (.int right)]) (expected := expected)
          (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, operation.notError])
          (by
            rintro (asAtom | asExpression | impossible)
            · exact notAtom asAtom
            · exact notExpression asExpression
            · exact (by decide : Atom.expressionType ≠ Atom.variableType) impossible) (Or.inr rfl))
    (by rw [HEBinaryNumericSource.call_read]; rfl)
    (by simpa only [HEBinaryNumericSource.call_read, Entry.Value.erase, current, environment,
        HERangeSourceProgram.environment, id_eq] using
      selection currentOps world operation policy before live scope left right expected declared matched)
    rfl (HEBinaryNumericSource.operator_atom_of_query current operation policy space () _ _ before
      (signature_query currentOps world _ before operation _ declared))
    (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty, operation.notEmpty])
    arguments calls priority
  simpa [output, publishResult, Entry.Value.publish, Entry.Value.withStatus] using source

theorem addition_source (minimal : Minimal.Services)
    (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom) (world : ExternalView)
    (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) (left right : Int) :
    Stateful.AtomRel (environment minimal currentOps world) space () live scope
      (HEBinaryNumericSource.addition.call left right) Atom.undefinedType before
      [(.grounded (.int (left + right)), before)] () (policy := policy) := by
  apply source_call minimal currentOps world HEBinaryNumericSource.addition policy before live scope left right
    Atom.undefinedType (by decide) (by decide)
  · rw [HERangeTypeReadPrimitives.declarations_eq]
    rfl
  · exact .undefinedLeft _ _
  · exact Or.inl rfl
  · exact HERangeSourceProgram.addition_primitive left right
  · exact HERangeAdmissionBoundary.number_source minimal currentOps world policy live scope before (left + right)

theorem comparison_source (minimal : Minimal.Services)
    (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom) (world : ExternalView)
    (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) (left right : Int) :
    Stateful.AtomRel (environment minimal currentOps world) space () live scope
      (HEBinaryNumericSource.greaterEqual.call left right) (.symbol "Bool") before
      [(.grounded (.bool (decide (left ≥ right))), before)] () (policy := policy) := by
  apply source_call minimal currentOps world HEBinaryNumericSource.greaterEqual policy before live scope left right
    (.symbol "Bool") (by decide) (by decide)
  · rw [HERangeTypeReadPrimitives.declarations_eq]
    rfl
  · exact same_symbol_type_match "Bool" before.bindings (by decide) (by decide)
  · exact Or.inr (Or.inl rfl)
  · exact HERangeSourceProgram.comparison_primitive left right
  · exact HERangeAdmissionBoundary.boolean_source minimal currentOps world policy live scope before (decide (left ≥ right))

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeInferredArithmetic
