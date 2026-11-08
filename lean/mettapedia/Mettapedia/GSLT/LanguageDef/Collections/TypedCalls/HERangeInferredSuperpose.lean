import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeInferredIfSource
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSuperposeSource

/-!
# Inferred superpose entry and ordered recursive-child returns

The tuple operand is admitted and delivered as held expression data. Its
elements are evaluated only by the existing native return continuation,
under Undefined and with one source derivation per emitted occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeInferredSuperpose

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type Spec.Type.Presentation
open Mettapedia.Machines.OrderedProtocol.Completion
open RetainedTypePayloads (ExternalView)
open HERangeAdmissionBoundary (environment lookup)
open HERangeSourceProgram (space)
open HERangeSuperposeSource (NumericOrEmpty call signature)

theorem signature_query (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (scope : List String) (before : Frame) (expected : Atom) :
    HERangeArgumentQueryTransport.inferredRead currentOps world scope before.bindings
      (.symbol "superpose") expected [signature.functionType] := by
  let supply : TypeReadSupply.Supply :=
    ⟨invocationTypeScope scope [] (.symbol "superpose") expected before.bindings, 0⟩
  exact ⟨supply, 1, fun _ member => member, HERangeTypeReadApplications.superpose_head_type currentOps world 0 supply⟩

theorem selection (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (items : List Entry.Value) (expected : Atom) :
    kindArgumentService.selection space (lookup currentOps world) policy live scope (call items).erase
      (.symbol "superpose") expected before (.selected signature [before]) := by
  let names := invocationTypeScope scope live (call items).erase expected before.bindings
  refine ⟨[signature.functionType], signature_query currentOps world names before _, .selected (errors := []) ?_ (by simp)⟩
  have operand : KindArgumentAdmissionRel space (lookup currentOps world names space) policy
      (call items).erase (.expression (items.map Entry.Value.erase)) Atom.expressionType 1 before [before] [] :=
    .kind (.expression _) .expression
  have args : AdmissionArgumentsRel KindArgumentAdmissionRel space (lookup currentOps world names space) policy
      (call items).erase 1 [.expression (items.map Entry.Value.erase)] [Atom.expressionType] [before] [before] [] :=
    .cons (AdmissionFramesRel.single operand) .nil
  simpa [signature, checkedFrames, checkedFailures, names] using
    AdmissionApplicationRel.checked (admit := KindArgumentAdmissionRel) (expression := (call items).erase)
      (expected := expected) (selected := signature) (before := before) (operator := .symbol "superpose")
      (arguments := [.expression (items.map Entry.Value.erase)])
      (by simp [call, Entry.Value.erase]) args
      (List.Forall₂.cons (TypeCheckRel.accepted (.unchanged (before.preserved_type_match policy (.undefinedRight _ _)))) List.Forall₂.nil)

theorem number_undefined (minimal : Minimal.Services)
    (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom) (world : ExternalView)
    (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) (value : Int) :
    Stateful.AtomRel (environment minimal currentOps world) space () live scope (.grounded (.int value))
      Atom.undefinedType before [(.grounded (.int value), before)] () (policy := policy) :=
  HERangeSuperposeSource.number_undefined_of_query (environment minimal currentOps world) policy before live scope value
    (HERangeAdmissionBoundary.number_query currentOps world _ before value _)

theorem source (minimal : Minimal.Services)
    (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom) (world : ExternalView)
    (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (items : List Entry.Value) (outputs : List (List Result)) (expected : Atom)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (closed : TypeSubst.typeVarsList (items.map Entry.Value.erase) = []) (nonempty : items ≠ [])
    (children : List.Forall₂ (fun item rows =>
      ¬FunctionPending policy item ∧ item.erase ≠ Atom.notReducible ∧ ¬IsEmptyOrErrorRel item.erase ∧
      Stateful.AtomRel (environment minimal currentOps world) space () live scope item Atom.undefinedType before rows () (policy := policy)) items outputs)
    (numeric : ∀ row ∈ outputs.flatten, NumericOrEmpty row.1) :
    Stateful.AtomRel (environment minimal currentOps world) space () live scope (call items) expected before
      outputs.flatten () (policy := policy) := by
  let current := environment minimal currentOps world
  have native := HERangeSuperposeSource.native_call_in current policy before live scope items outputs nonempty children rfl
    (HERangeSourceProgram.superpose_primitive .active .active items).symm
  have calls : Stateful.CallsRel current space () live scope (invocationReturnType signature)
      ([(Entry.Value.argumentPacket [.expression .active items], before)].map (functionAssemble (.symbol "superpose")))
      outputs.flatten () (policy := policy) := by
    simpa [signature, invocationReturnType, Atom.undefinedType, Atom.expressionType, functionAssemble, call] using
      Stateful.CallsRel.cons native Stateful.CallsRel.nil
  have priority : SuccessPriorityRel (fun row : Result => isErrorAtom row.1.erase)
      (outputs.flatten.map (readResult policy)) outputs.flatten := by
    rw [HERangeSuperposeSource.numeric_reads policy _ numeric]
    exact HERangeSuperposeSource.numeric_priority _ numeric
  have complete := HEStatefulSelectedComposition.selected_of_parts current policy space () () () ()
    live scope (call items) expected before before before .active (.symbol "superpose") (.symbol "superpose")
    [.expression .active items] signature [(Entry.Value.argumentPacket [.expression .active items], before)]
    outputs.flatten outputs.flatten
    (by
      rw [HERangeSuperposeSource.call_read policy before items closed]
      simp only [call, Entry.Value.status, Entry.Value.erase, List.map_cons, List.map_nil]
      apply Entry.Rel.expression
      · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
      · rintro (asAtom | asExpression | impossible)
        · exact notAtom asAtom
        · exact notExpression asExpression
        · exact (by decide : Atom.expressionType ≠ Atom.variableType) impossible
      · exact Or.inr rfl)
    (by rw [HERangeSuperposeSource.call_read policy before items closed]; rfl)
    (by simpa only [HERangeSuperposeSource.call_read policy before items closed, Entry.Value.erase,
        current, environment, HERangeSourceProgram.environment, id_eq] using
      selection currentOps world policy before live scope items expected)
    rfl (HERangeSuperposeSource.operator_source_of_query current policy before _ _ (signature_query currentOps world _ before _))
    (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    (HERangeSuperposeSource.argument_source_in current policy before _ _ items closed) calls priority
  simpa only [HERangeSuperposeSource.numeric_publishes policy _ _ numeric] using complete

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeInferredSuperpose
