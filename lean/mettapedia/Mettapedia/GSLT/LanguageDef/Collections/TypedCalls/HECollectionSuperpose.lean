import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionIfActivation
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionAppendSource

/-! The collection world's superpose source path. Each emitted item has an
earned source derivation at Undefined; recursive range results are never
supplied to the host as a precomputed answer oracle. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSuperpose

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type Spec.Type.Presentation
open Mettapedia.Machines.OrderedProtocol.Completion
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment)
open HERangeSuperposeSource (NumericOrEmpty call signature)

variable (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
  (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)

local notation "current" => environment minimal nativePolicy external active primitive subtypes
local notation "ops" => HECollectionInferredQueries.currentOps external active primitive subtypes
local notation "sourceSpace" => HECollectionSpaceExtension.space

theorem selection (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (items : List Entry.Value) (expected : Atom) :
    (current).arguments.selection sourceSpace (current).lookup policy live scope (call items).erase
      (.symbol "superpose") expected before (.selected signature [before]) := by
  let names := invocationTypeScope scope live (call items).erase expected before.bindings
  refine ⟨[signature.functionType], HECollectionInferredQueries.closed_head ops external names before "superpose" _ _ rfl rfl,
    .selected (errors := []) ?_ (by simp)⟩
  have operand : KindArgumentAdmissionRel sourceSpace ((current).lookup names sourceSpace) policy
      (call items).erase (.expression (items.map Entry.Value.erase)) Atom.expressionType 1 before [before] [] :=
    .kind (.expression _) .expression
  have args : AdmissionArgumentsRel KindArgumentAdmissionRel sourceSpace ((current).lookup names sourceSpace) policy
      (call items).erase 1 [.expression (items.map Entry.Value.erase)] [Atom.expressionType] [before] [before] [] :=
    .cons (AdmissionFramesRel.single operand) .nil
  simpa [signature, checkedFrames, checkedFailures, names] using
    AdmissionApplicationRel.checked (admit := KindArgumentAdmissionRel) (expression := (call items).erase)
      (expected := expected) (selected := signature) (before := before) (operator := .symbol "superpose")
      (arguments := [.expression (items.map Entry.Value.erase)]) (by simp [call, Entry.Value.erase]) args
      (List.Forall₂.cons (TypeCheckRel.accepted (.unchanged (before.preserved_type_match policy (.undefinedRight _ _)))) .nil)

theorem argument_source (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (items : List Entry.Value) (closed : TypeSubst.typeVarsList (items.map Entry.Value.erase) = []) :
    Stateful.ArgumentsRel current sourceSpace world live scope [(.expression .active items, Atom.expressionType)] before
      [(Entry.Value.argumentPacket [.expression .active items], before)] world (policy := policy) := by
  apply Stateful.ArgumentsRel.cons
    (HECollectionAppendSource.expression_delivery current policy sourceSpace world _ scope before .active items closed)
  simpa only [List.map_cons, List.map_nil, List.append_nil, argumentPrepend_packet] using
    Stateful.ArgumentBranchesRel.continuing (head := (Entry.Value.expression .active items, before))
      (by simp [ArgumentStopped]) (Stateful.ArgumentsRel.nil (frame := before)) Stateful.ArgumentBranchesRel.nil

theorem native_rows (policy : Policy) (before : Frame) (arguments : List Atom) (items : List Entry.Value) :
    NativeRowsRel policy (current).dispatch (.symbol "superpose") arguments before
      (items.map fun item => (item, Bindings.empty)) (items.map fun item => (item, before)) := by
  induction items with
  | nil => exact .nil
  | cons item items ih =>
      simpa [nativeValue, environment, HECollectionWorld.dispatch] using
        (NativeRowsRel.cons (head := (item, Bindings.empty)) (Frame.NativeRenewRel.empty policy before) ih)

theorem item_returns (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (items : List Entry.Value) (outputs : List (List Result))
    (children : List.Forall₂ (fun item rows =>
      ¬FunctionPending policy item ∧ item.erase ≠ Atom.notReducible ∧ ¬IsEmptyOrErrorRel item.erase ∧
      Stateful.AtomRel current sourceSpace world live scope item Atom.undefinedType before rows world (policy := policy)) items outputs) :
    Stateful.BoundaryBatchRel current sourceSpace world live scope none
      (.native (call items) (some Atom.undefinedType) .emitted)
      (items.map fun item => (item, before)) outputs.flatten world (policy := policy) := by
  have build : ∀ {values replies}, List.Forall₂ (fun item rows =>
      ¬FunctionPending policy item ∧ item.erase ≠ Atom.notReducible ∧ ¬IsEmptyOrErrorRel item.erase ∧
      Stateful.AtomRel current sourceSpace world live scope item Atom.undefinedType before rows world (policy := policy)) values replies →
      Stateful.BoundaryBatchRel current sourceSpace world live scope none
        (.native (call items) (some Atom.undefinedType) .emitted)
        (values.map fun item => (item, before)) replies.flatten world (policy := policy) := by
    intro values replies related
    induction related with
    | nil => exact .nil
    | @cons item rows values replies child _ ih =>
        apply Stateful.BoundaryBatchRel.cons (children := rows)
        · apply Stateful.BoundaryRel.nativeEmittedReturn (produced := [(item, before)])
          · exact .producerRaw child.1
          · apply Stateful.BoundaryBatchRel.single_iff.mpr
            exact .returned (.evaluate child.2.1 child.2.2.1 child.2.2.2)
        · exact ih
  exact build children

theorem native_call (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (items : List Entry.Value) (outputs : List (List Result)) (nonempty : items ≠ [])
    (children : List.Forall₂ (fun item rows =>
      ¬FunctionPending policy item ∧ item.erase ≠ Atom.notReducible ∧ ¬IsEmptyOrErrorRel item.erase ∧
      Stateful.AtomRel current sourceSpace world live scope item Atom.undefinedType before rows world (policy := policy)) items outputs) :
    Stateful.CallRel current sourceSpace world live scope (call items) Atom.undefinedType before outputs.flatten world (policy := policy) := by
  have rows := native_rows minimal nativePolicy external active primitive subtypes policy before
    [Atom.expression (items.map Entry.Value.erase)] items
  have outcome : NativeOutcomeRel policy (current).dispatch (.symbol "superpose") [Atom.expression (items.map Entry.Value.erase)]
      (call items) (some Atom.undefinedType) before (.ok (items.map fun item => (item, Bindings.empty)))
      (.resume (items.map fun item => (item, before))) := by
    cases items with
    | nil => exact False.elim (nonempty rfl)
    | cons item rest => exact .success rows
  refine Stateful.CallRel.groundedResume (operator := .symbol "superpose")
    (arguments := [.expression (items.map Entry.Value.erase)])
    (outcome := .ok (items.map fun item => (item, Bindings.empty)))
    (rows := items.map fun item => (item, before)) (world1 := world)
    (by simp [call, Entry.Value.erase]) ?_ (by simp [call, Entry.Value.erase, IsErrorRel]) ?_ outcome ?_
  · simp [environment, HECollectionWorld.dispatch]
  · exact ⟨rfl, HECollectionWorld.Primitive.superpose .active .active items⟩
  · simpa [environment, HECollectionWorld.dispatch, CollectionStdlibSource.appendName] using
      item_returns minimal nativePolicy external active primitive subtypes world policy before live scope items outputs children

theorem source (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (items : List Entry.Value) (outputs : List (List Result)) (expected : Atom)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (closed : TypeSubst.typeVarsList (items.map Entry.Value.erase) = []) (nonempty : items ≠ [])
    (children : List.Forall₂ (fun item rows =>
      ¬FunctionPending policy item ∧ item.erase ≠ Atom.notReducible ∧ ¬IsEmptyOrErrorRel item.erase ∧
      Stateful.AtomRel current sourceSpace world live scope item Atom.undefinedType before rows world (policy := policy)) items outputs)
    (numeric : ∀ row ∈ outputs.flatten, NumericOrEmpty row.1) :
    Stateful.AtomRel current sourceSpace world live scope (call items) expected before outputs.flatten world (policy := policy) := by
  have native := native_call minimal nativePolicy external active primitive subtypes world policy before live scope items outputs nonempty children
  have calls : Stateful.CallsRel current sourceSpace world live scope (invocationReturnType signature)
      ([(Entry.Value.argumentPacket [.expression .active items], before)].map (functionAssemble (.symbol "superpose")))
      outputs.flatten world (policy := policy) := by
    simpa [signature, invocationReturnType, Atom.undefinedType, Atom.expressionType, functionAssemble, call] using
      Stateful.CallsRel.cons native Stateful.CallsRel.nil
  have priority : SuccessPriorityRel (fun row : Result => isErrorAtom row.1.erase)
      (outputs.flatten.map (readResult policy)) outputs.flatten := by
    rw [HERangeSuperposeSource.numeric_reads policy _ numeric]
    exact HERangeSuperposeSource.numeric_priority _ numeric
  have complete := HEStatefulSelectedComposition.selected_of_parts current policy sourceSpace world world world world
    live scope (call items) expected before before before .active (.symbol "superpose") (.symbol "superpose")
    [.expression .active items] signature [(Entry.Value.argumentPacket [.expression .active items], before)] outputs.flatten outputs.flatten
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
    (by simpa only [HERangeSuperposeSource.call_read policy before items closed, Entry.Value.erase, environment, id_eq] using
      selection minimal nativePolicy external active primitive subtypes policy before live scope items expected)
    rfl (HECollectionArithmetic.closed_operator minimal nativePolicy external active primitive subtypes world policy _ _ before
      "superpose" signature.functionType (by decide) (by decide) (by decide) rfl rfl)
    (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    (argument_source minimal nativePolicy external active primitive subtypes world policy before _ _ items closed) calls priority
  simpa only [HERangeSuperposeSource.numeric_publishes policy _ _ numeric] using complete

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSuperpose
