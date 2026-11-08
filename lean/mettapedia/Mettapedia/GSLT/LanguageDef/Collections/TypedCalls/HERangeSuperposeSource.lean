import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeConditionalActivation

/-!
# Ordered source composition for range's superpose producer

Each emitted item is evaluated under Undefined from the retained producer
frame. The composition consumes source derivations for those items, including
the recursive range call; it never accepts a finished-result array as an oracle.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSuperposeSource

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open Spec.Type Spec.Type.Presentation Spec.Type.Presentation.BindingTheory
open Spec.Match.Merge
open Mettapedia.Machines.OrderedProtocol.Completion
open HERangeSourceProgram (space environment)

inductive NumericOrEmpty : Entry.Value → Prop where
  | number (value : Int) : NumericOrEmpty (.grounded (.int value))
  | empty : NumericOrEmpty (.symbol "Empty")

theorem no_error {value : Entry.Value} (numeric : NumericOrEmpty value) : isErrorAtom value.erase = false := by
  cases numeric <;> simp [Entry.Value.erase, isErrorAtom]

theorem scalar_read {value : Entry.Value} (numeric : NumericOrEmpty value) (policy : Policy) (frame : Frame) :
    frame.read policy value = value := by
  cases numeric <;> simp [Frame.read, Entry.Value.substitute]

theorem scalar_publish {value : Entry.Value} (numeric : NumericOrEmpty value) (policy : Policy)
    (original : Atom) (frame : Frame) : publishResult policy original (value, frame) = (value, frame) := by
  cases numeric <;> simp [publishResult, Entry.Value.publish, Entry.Value.withStatus]

theorem numeric_reads (policy : Policy) (rows : List Result)
    (numeric : ∀ row ∈ rows, NumericOrEmpty row.1) : rows.map (readResult policy) = rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      have first := scalar_read (numeric row (by simp)) policy row.2
      have rest := ih (fun item present => numeric item (List.mem_cons_of_mem _ present))
      simp only [List.map_cons, readResult, first, rest, Prod.eta]

theorem numeric_publishes (policy : Policy) (original : Atom) (rows : List Result)
    (numeric : ∀ row ∈ rows, NumericOrEmpty row.1) : rows.map (publishResult policy original) = rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      have first : publishResult policy original row = row := by
        simpa only [Prod.eta] using scalar_publish (numeric row (by simp)) policy original row.2
      rw [List.map_cons, first, ih (fun item present => numeric item (List.mem_cons_of_mem _ present))]

theorem numeric_priority (rows : List Result) (numeric : ∀ row ∈ rows, NumericOrEmpty row.1) :
    SuccessPriorityRel (fun row : Result => isErrorAtom row.1.erase) rows rows := by
  cases rows with
  | nil => exact .allErrors (by simp)
  | cons row rest =>
      have keep : (row :: rest).filter (fun item => !isErrorAtom item.1.erase) = row :: rest :=
        List.filter_eq_self.mpr (fun item member => by simp [no_error (numeric item member)])
      simpa only [keep] using
        (SuccessPriorityRel.successes (isError := fun item : Result => isErrorAtom item.1.erase)
          (raw := row :: rest) ⟨row, by simp, no_error (numeric row (by simp))⟩)

theorem number_undefined_of_query (current : WorldEnvironment Space Unit) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (value : Int)
    (queried : current.lookup (invocationTypeScope scope live (.grounded (.int value)) Atom.undefinedType before.bindings)
      (current.view () space) before.bindings (.grounded (.int value)) Atom.undefinedType [.symbol "Number"]) :
    Stateful.AtomRel current space () live scope (.grounded (.int value)) Atom.undefinedType before
      [(.grounded (.int value), before)] () (policy := policy) := by
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
    apply TypeCastBatchRel.success (earlierTypes := []) (laterTypes := [])
    · exact queried
    · rfl
    · simp
    · exact before.preserved_type_match policy (.undefinedLeft _ _)
  · rw [read]
    exact .cons ⟨by simp [rawResult, Entry.Value.erase], .same before, by simp [Entry.Value.erase]⟩ .nil

theorem number_undefined (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (value : Int) :
    Stateful.AtomRel (environment minimal) space () live scope (.grounded (.int value)) Atom.undefinedType before
      [(.grounded (.int value), before)] () (policy := policy) :=
  number_undefined_of_query (environment minimal) policy before live scope value
    (HEContextualArithmeticSource.scalar_lookup _ _ before (.int value) "Number" _ rfl (by decide))

def call (items : List Entry.Value) : Entry.Value :=
  .expression .active [.symbol "superpose", .expression .active items]

def signature : SelectedTypePolicy :=
  ⟨HERangeSourceProgram.superposeType, [Atom.expressionType], Atom.undefinedType, rfl⟩

theorem native_rows (policy : Policy) (before : Frame) (arguments : List Atom) (items : List Entry.Value) :
    NativeRowsRel policy HERangeSourceProgram.dispatch (.symbol "superpose") arguments before
      (items.map fun item => (item, Bindings.empty)) (items.map fun item => (item, before)) := by
  induction items with
  | nil => exact .nil
  | cons item items ih =>
      simpa [nativeValue, HERangeSourceProgram.dispatch] using
        (NativeRowsRel.cons (head := (item, Bindings.empty)) (Frame.NativeRenewRel.empty policy before) ih)

/-- Local per-item source evaluations compose through the native producer's
ordinary return gate in their actual order. Each begins at the producer frame. -/
theorem item_returns_in (current : WorldEnvironment Space Unit) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (items : List Entry.Value) (outputs : List (List Result))
    (children : List.Forall₂ (fun item rows =>
      ¬FunctionPending policy item ∧ item.erase ≠ Atom.notReducible ∧ ¬IsEmptyOrErrorRel item.erase ∧
      Stateful.AtomRel current space () live scope item Atom.undefinedType before rows () (policy := policy)) items outputs) :
    Stateful.BoundaryBatchRel current space () live scope none
      (.native (call items) (some Atom.undefinedType) .emitted)
      (items.map fun item => (item, before)) outputs.flatten () (policy := policy) := by
  have build : ∀ {values replies}, List.Forall₂ (fun item rows =>
      ¬FunctionPending policy item ∧ item.erase ≠ Atom.notReducible ∧ ¬IsEmptyOrErrorRel item.erase ∧
      Stateful.AtomRel current space () live scope item Atom.undefinedType before rows () (policy := policy)) values replies →
      Stateful.BoundaryBatchRel current space () live scope none
        (.native (call items) (some Atom.undefinedType) .emitted)
        (values.map fun item => (item, before)) replies.flatten () (policy := policy) := by
    intro values replies related
    induction related with
    | nil => exact .nil
    | @cons item rows values replies child rest ih =>
        apply Stateful.BoundaryBatchRel.cons (children := rows)
        · apply Stateful.BoundaryRel.nativeEmittedReturn (produced := [(item, before)])
          · exact .producerRaw child.1
          · apply Stateful.BoundaryBatchRel.single_iff.mpr
            exact .returned (.evaluate child.2.1 child.2.2.1 child.2.2.2)
        · exact ih
  exact build children

theorem item_returns (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (items : List Entry.Value) (outputs : List (List Result))
    (children : List.Forall₂ (fun item rows =>
      ¬FunctionPending policy item ∧ item.erase ≠ Atom.notReducible ∧ ¬IsEmptyOrErrorRel item.erase ∧
      Stateful.AtomRel (environment minimal) space () live scope item Atom.undefinedType before rows () (policy := policy)) items outputs) :
    Stateful.BoundaryBatchRel (environment minimal) space () live scope none
      (.native (call items) (some Atom.undefinedType) .emitted)
      (items.map fun item => (item, before)) outputs.flatten () (policy := policy) :=
  item_returns_in (environment minimal) policy before live scope items outputs children

theorem native_call_in (current : WorldEnvironment Space Unit) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (items : List Entry.Value) (outputs : List (List Result))
    (nonempty : items ≠ [])
    (children : List.Forall₂ (fun item rows =>
      ¬FunctionPending policy item ∧ item.erase ≠ Atom.notReducible ∧ ¬IsEmptyOrErrorRel item.erase ∧
      Stateful.AtomRel current space () live scope item Atom.undefinedType before rows () (policy := policy)) items outputs)
    (dispatch_eq : current.dispatch = HERangeSourceProgram.dispatch)
    (executed : current.services.groundedAt space () live scope before (call items)
      (.ok (items.map fun item => (item, Bindings.empty))) ()) :
    Stateful.CallRel current space () live scope (call items) Atom.undefinedType before
      outputs.flatten () (policy := policy) := by
  apply Stateful.CallRel.groundedResume (operator := .symbol "superpose")
    (arguments := [.expression (items.map Entry.Value.erase)])
    (outcome := .ok (items.map fun item => (item, Bindings.empty)))
    (rows := items.map fun item => (item, before)) (world1 := ())
  · simp [call, Entry.Value.erase]
  · rw [dispatch_eq]; exact Or.inr (Or.inr rfl)
  · simp [call, Entry.Value.erase, IsErrorRel]
  · exact executed
  · cases items with
    | nil => exact (nonempty rfl).elim
    | cons item rest =>
        rw [dispatch_eq]
        exact .success (native_rows policy before _ (item :: rest))
  · simpa only [dispatch_eq, HERangeSourceProgram.dispatch] using item_returns_in current policy before live scope items outputs children

theorem native_call (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (items : List Entry.Value) (outputs : List (List Result))
    (nonempty : items ≠ [])
    (children : List.Forall₂ (fun item rows =>
      ¬FunctionPending policy item ∧ item.erase ≠ Atom.notReducible ∧ ¬IsEmptyOrErrorRel item.erase ∧
      Stateful.AtomRel (environment minimal) space () live scope item Atom.undefinedType before rows () (policy := policy)) items outputs) :
    Stateful.CallRel (environment minimal) space () live scope (call items) Atom.undefinedType before
      outputs.flatten () (policy := policy) :=
  native_call_in (environment minimal) policy before live scope items outputs nonempty children rfl
    (HERangeSourceProgram.superpose_primitive .active .active items).symm

theorem signature_match (bindings : Bindings) :
    TypeMatchRel signature.functionType signature.functionType bindings bindings := by
  have emptyMerge : MergeRel equalityGroundedSemantic Bindings.empty Bindings.empty Bindings.empty :=
    .mk (by simp [constraints, Bindings.empty]) .nil
  exact .structural (by decide) (by decide) (by decide) (by decide)
    (.expression (.cons (.symSym "->" semanticLoopFree_empty) emptyMerge
      (.cons (.symSym "Expression" semanticLoopFree_empty) emptyMerge
        (.cons (.symSym "%Undefined%" semanticLoopFree_empty) emptyMerge .nil))) semanticLoopFree_empty)
    (.mk (by simp [constraints, Bindings.empty]) .nil)

theorem signature_lookup (names : List String) (before : Frame) (expected : Atom) :
    scopedLookup names space before.bindings (.symbol "superpose") expected [signature.functionType] := by
  refine ⟨[signature.functionType], ?_, .cons ?_ (.nil _)⟩
  · simpa only [HERangeSourceProgram.superpose_declared, signature] using FirstSuccessSourceReplies.source_types space (.symbol "superpose")
  · exact ⟨id, Function.injective_id, by simp,
      by simp [signature, HERangeSourceProgram.superposeType, CompletedDelivery.arrowType,
        Atom.expressionType, Atom.undefinedType, TypeSubst.typeVars, TypeSubst.typeVarsList]⟩

theorem tuple_unknown (items : List Entry.Value) :
    getAtomTypes space (.expression (items.map Entry.Value.erase)) = [Atom.undefinedType] := by
  cases items <;> rfl

theorem selection (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (items : List Entry.Value) (expected : Atom) :
    InvocationSelectionRel space scopedLookup policy live scope (call items).erase (.symbol "superpose") expected before
      (.selected signature [before]) := by
  let names := invocationTypeScope scope live (call items).erase expected before.bindings
  have argument := HEIfSourceSelection.unknown_argument space names policy before (call items).erase
    (.expression (items.map Entry.Value.erase)) Atom.expressionType 1 (tuple_unknown items)
  have checked : ApplicationChecksRel space (scopedLookup names space) policy (call items).erase expected signature before [before] [] := by
    simpa [signature, checkedFrames, checkedFailures] using
      (ApplicationChecksRel.checked (expression := (call items).erase) (expected := expected) (selected := signature)
        (before := before) (operator := .symbol "superpose") (arguments := [.expression (items.map Entry.Value.erase)])
        (by simp [call, Entry.Value.erase]) (.cons argument .nil)
        (.cons (TypeCheckRel.accepted (.unchanged (before.preserved_type_match policy (.undefinedRight _ _)))) .nil))
  exact ⟨[signature.functionType], signature_lookup names before _, .selected checked (by simp)⟩

theorem operator_source_of_query (current : WorldEnvironment Space Unit) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String)
    (queried : current.lookup (invocationTypeScope scope live (.symbol "superpose") signature.functionType before.bindings)
      (current.view () space) before.bindings (.symbol "superpose") signature.functionType [signature.functionType]) :
    Stateful.AtomRel current space () live scope (.symbol "superpose") signature.functionType before
      [(.symbol "superpose", before)] () (policy := policy) := by
  have read : before.read policy (.symbol "superpose") = .symbol "superpose" := by simp [Frame.read, Entry.Value.substitute]
  apply Stateful.AtomRel.cast (raw := [(.symbol "superpose", before.bindings)])
  · rw [read]
    apply Entry.Rel.cast (metaType := Atom.symbolType)
    · simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · simpa only [Entry.Value.erase] using MetaTypeRel.symbol "superpose"
    · decide
    · exact Or.inl ⟨"superpose", by simp [Entry.Value.erase]⟩
    · simp [Entry.Value.erase, Atom.unit]
  · rw [read]
    simp only [Entry.Value.erase]
    exact TypeCastBatchRel.success (earlierTypes := []) (laterTypes := [])
      queried rfl (by simp) (before.preserved_type_match policy (signature_match before.bindings))
  · rw [read]
    exact .cons ⟨by simp [rawResult, Entry.Value.erase], .same before, by simp [Entry.Value.erase]⟩ .nil

theorem operator_source (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) :
    Stateful.AtomRel (environment minimal) space () live scope (.symbol "superpose") signature.functionType before
      [(.symbol "superpose", before)] () (policy := policy) :=
  operator_source_of_query (environment minimal) policy before live scope (signature_lookup _ before _)

theorem tuple_read (policy : Policy) (before : Frame) (items : List Entry.Value)
    (closed : TypeSubst.typeVarsList (items.map Entry.Value.erase) = []) :
    before.read policy (.expression .active items) = .expression .active items := by
  apply HEFreshSyntaxBinding.ground_substitution
  simpa only [Entry.Value.erase, TypeSubst.typeVars] using closed

theorem call_read (policy : Policy) (before : Frame) (items : List Entry.Value)
    (closed : TypeSubst.typeVarsList (items.map Entry.Value.erase) = []) :
    before.read policy (call items) = call items := by
  apply HEFreshSyntaxBinding.ground_substitution
  simpa only [call, Entry.Value.erase, List.map_cons, List.map_nil, TypeSubst.typeVars,
    TypeSubst.typeVarsList, List.nil_append, List.append_nil] using closed

theorem argument_source_in (current : WorldEnvironment Space Unit) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (items : List Entry.Value)
    (closed : TypeSubst.typeVarsList (items.map Entry.Value.erase) = []) :
    Stateful.ArgumentsRel current space () live scope [(.expression .active items, Atom.expressionType)] before
      [(Entry.Value.argumentPacket [.expression .active items], before)] () (policy := policy) := by
  have delivered : Stateful.AtomRel current space () (argumentScope [] ++ live) scope
      (.expression .active items) Atom.expressionType before [(.expression .active items, before)] () (policy := policy) := by
    have entry : Entry.Rel policy.reentry (Entry.Value.expression .active items).status
        (Entry.Value.expression .active items).erase Atom.expressionType .deliver := by
      by_cases stopped : IsEmptyOrErrorRel (Entry.Value.expression .active items).erase
      · exact .stopped stopped
      · apply Entry.Rel.pass stopped
        · simpa only [Entry.Value.erase] using MetaTypeRel.expression (items.map Entry.Value.erase)
        · exact Or.inr (Or.inl rfl)
    simpa only [tuple_read policy before items closed] using Stateful.AtomRel.delivered
      (environment := current) (label := space) (world0 := ()) (live := argumentScope [] ++ live)
      (scope := scope) (value := Entry.Value.expression .active items) (expected := Atom.expressionType) (frame := before) (policy := policy)
      (by simpa only [tuple_read policy before items closed] using entry)
  apply Stateful.ArgumentsRel.cons delivered
  simpa only [List.map_cons, List.map_nil, List.append_nil, argumentPrepend_packet] using
    Stateful.ArgumentBranchesRel.continuing (head := (Entry.Value.expression .active items, before))
      (by simp [ArgumentStopped]) (Stateful.ArgumentsRel.nil (frame := before)) Stateful.ArgumentBranchesRel.nil

theorem argument_source (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (items : List Entry.Value)
    (closed : TypeSubst.typeVarsList (items.map Entry.Value.erase) = []) :
    Stateful.ArgumentsRel (environment minimal) space () live scope [(.expression .active items, Atom.expressionType)] before
      [(Entry.Value.argumentPacket [.expression .active items], before)] () (policy := policy) :=
  argument_source_in (environment minimal) policy before live scope items closed

/-- Full source entry, application and native result dispatch from earned
per-item derivations. Numeric successes and final Empty keep their exact
order, multiplicity and per-item activation records. -/
theorem source (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (items : List Entry.Value) (outputs : List (List Result))
    (expected : Atom) (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (closed : TypeSubst.typeVarsList (items.map Entry.Value.erase) = []) (nonempty : items ≠ [])
    (children : List.Forall₂ (fun item rows =>
      ¬FunctionPending policy item ∧ item.erase ≠ Atom.notReducible ∧ ¬IsEmptyOrErrorRel item.erase ∧
      Stateful.AtomRel (environment minimal) space () live scope item Atom.undefinedType before rows () (policy := policy)) items outputs)
    (numeric : ∀ row ∈ outputs.flatten, NumericOrEmpty row.1) :
    Stateful.AtomRel (environment minimal) space () live scope (call items) expected before outputs.flatten () (policy := policy) := by
  have calls : Stateful.CallsRel (environment minimal) space () live scope (invocationReturnType signature)
      ([(Entry.Value.argumentPacket [.expression .active items], before)].map (functionAssemble (.symbol "superpose")))
      outputs.flatten () (policy := policy) := by
    simpa [signature, invocationReturnType, Atom.undefinedType, Atom.expressionType, functionAssemble, call] using
      (Stateful.CallsRel.cons (native_call minimal policy before live scope items outputs nonempty children) .nil)
  have priority : SuccessPriorityRel (fun row : Result => isErrorAtom row.1.erase)
      (outputs.flatten.map (readResult policy)) outputs.flatten := by
    rw [numeric_reads policy _ numeric]
    exact numeric_priority _ numeric
  have complete := HEStatefulSelectedComposition.selected_of_parts (environment minimal) policy space () () () ()
    live scope (call items) expected before before before .active (.symbol "superpose") (.symbol "superpose")
    [.expression .active items] signature [(Entry.Value.argumentPacket [.expression .active items], before)]
    outputs.flatten outputs.flatten
    (by
      rw [call_read policy before items closed]
      simp only [call, Entry.Value.status, Entry.Value.erase, List.map_cons, List.map_nil]
      apply Entry.Rel.expression
      · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
      · rintro (asAtom | asExpression | impossible)
        · exact notAtom asAtom
        · exact notExpression asExpression
        · exact (by decide : Atom.expressionType ≠ Atom.variableType) impossible
      · exact Or.inr rfl)
    (by rw [call_read policy before items closed]; rfl)
    (by simpa only [call_read policy before items closed, Entry.Value.erase, HERangeSourceProgram.environment, id_eq] using selection policy before live scope items expected)
    rfl (operator_source minimal policy before _ _)
    (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    (argument_source minimal policy before _ _ items closed) calls priority
  simpa only [numeric_publishes policy _ _ numeric] using complete

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSuperposeSource
