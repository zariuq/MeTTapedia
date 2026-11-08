import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedCallComposition

/-!
# A selected typed constructor with an absent equation call

The control is an actual source call of `hold : Number -> Box` with one
grounded operand. Its type selection, operator cast, checked argument and absent
ordinary call are derived separately, then composed without an equation body.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedCallComposition.Controls

open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open RecursiveTasks FirstSuccessRecursiveExecution FirstSuccessSourceExecution
open Spec.Eval Spec.Eval.Completed Spec.Type Spec.Type.Presentation
open Spec.Type.Presentation.BindingTheory Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation Spec.Match.Merge
open FirstSuccessScopedAdequacy FirstSuccessScopedAdequacy.ScopedRetainedRelation
open FirstSuccessScopedAdequacy.UniversalScopedPolymorphicApplication

def formal : Atom := .symbol "Number"
def returned : Atom := .symbol "Box"
def signature : SelectedTypePolicy :=
  ⟨.expression [.symbol "->", formal, returned], [formal], returned, rfl⟩
def space : Space := Space.ofList
  [.expression [.symbol ":", .symbol "hold", signature.functionType]]
def operator : Atom := .symbol "hold"
def operand : Atom := .grounded (.int 7)
def call : Atom := .expression [operator, operand]
def ctxOperator : Entry.Value := .symbol "hold"
def ctxOperand : Entry.Value := .grounded (.int 7)
def ctxCall : Entry.Value := .expression .active [ctxOperator, ctxOperand]
def host := Completed.Controls.typedDispatch

@[simp] theorem eraseOperator : ctxOperator.erase = operator := by
  simp [ctxOperator, operator, Entry.Value.erase]

@[simp] theorem eraseOperand : ctxOperand.erase = operand := by
  simp [ctxOperand, operand, Entry.Value.erase]

@[simp] theorem eraseCall : ctxCall.erase = call := by
  simp [ctxCall, call, Entry.Value.erase]

@[simp] theorem emptyBindings : Completed.Frame.empty.bindings = Bindings.empty := rfl

theorem actEmpty : ScopedActivationRel Bindings.empty Completed.Frame.empty :=
  SourceBindingComparison.FrameRelated.of_principal PrincipalBindingFrame.empty (.refl _)

theorem annotations_closed : ClosedTypeAnnotations space :=
  (closedColonAnnotations_of_bool (by decide +kernel)).closedTypeAnnotations

theorem emptyMerge : MergeRel equalityGroundedSemantic Bindings.empty Bindings.empty Bindings.empty :=
  .mk (by simp [constraints, Bindings.empty]) .nil

theorem numberMatch : TypeMatchRel formal formal Bindings.empty Bindings.empty :=
  .structural (by decide) (by decide) (by decide) (by decide)
    (.symSym "Number" semanticLoopFree_empty) emptyMerge

theorem arrowMatch : TypeMatchRel signature.functionType signature.functionType
    Bindings.empty Bindings.empty :=
  .structural (by decide) (by decide) (by decide) (by decide)
    (.expression
      (.cons (.symSym "->" semanticLoopFree_empty) emptyMerge
        (.cons (.symSym "Number" semanticLoopFree_empty) emptyMerge
          (.cons (.symSym "Box" semanticLoopFree_empty) emptyMerge .nil))) semanticLoopFree_empty)
    emptyMerge

theorem headQuery (protectedNames : List String) (expected : Atom) :
    Completed.scopedLookup protectedNames space Bindings.empty operator expected [signature.functionType] := by
  refine ⟨[signature.functionType], .symbolKnown (.hit .nil) (by simp), .cons ?_ (.nil _)⟩
  exact ⟨id, Function.injective_id, by simp,
    by simp [signature, formal, returned, TypeSubst.typeVars, TypeSubst.typeVarsList]⟩

theorem operandQuery (protectedNames : List String) (expected : Atom) :
    Completed.scopedLookup protectedNames space Bindings.empty operand expected [.symbol "Number"] := by
  refine ⟨[.symbol "Number"], .groundedKnown (.int 7) (by decide), .cons ?_ (.nil _)⟩
  exact ⟨id, Function.injective_id, by simp, by simp [TypeSubst.typeVars]⟩

theorem selectedSource (live : List Atom) (scope : List String) :
    Completed.InvocationSelectionRel space Completed.scopedLookup Policy.unmarked live scope
      call operator Atom.undefinedType Completed.Frame.empty
      (.selected signature [Completed.Frame.empty]) := by
  let lookup := Completed.scopedLookup
    (invocationTypeScope scope live call Atom.undefinedType Bindings.empty) space
  have accepted : TypeCheckRel Policy.unmarked formal Completed.Frame.empty
      (.symbol "Number") (.inr Completed.Frame.empty) :=
    .accepted (.unchanged (Completed.Frame.empty.preserved_type_match Policy.unmarked numberMatch))
  have checked : ArgumentChecksRel space lookup Policy.unmarked call operand formal 1
      [Completed.Frame.empty] [Completed.Frame.empty] [] := by
    simpa [checkedFrames, checkedFailures] using
      (ArgumentChecksRel.cons (expression := call) (position := 1)
        (operandQuery _ formal) (.cons accepted .nil) .nil)
  have returned : TypeCheckRel Policy.unmarked Atom.undefinedType Completed.Frame.empty
      returned (.inr Completed.Frame.empty) :=
    .accepted (.unchanged (Completed.Frame.empty.preserved_type_match Policy.unmarked (.undefinedLeft _ _)))
  have applicable : ApplicationChecksRel space lookup Policy.unmarked call Atom.undefinedType
      signature Completed.Frame.empty [Completed.Frame.empty] [] := by
    simpa [checkedFrames, checkedFailures, signature, call] using
      (ApplicationChecksRel.checked (selected := signature) (expected := Atom.undefinedType)
        (before := Completed.Frame.empty) (operator := operator) (arguments := [operand])
        rfl (.cons checked .nil) (.cons returned .nil))
  exact ⟨[signature.functionType], headQuery _ _, .selected applicable (by simp)⟩

theorem entry (stack : List RecursiveTasks.Frame) (emitted : ResultSet) :
    ScopedSelectedFunctionEntry space Policy.unmarked operator [operand] operator Atom.undefinedType
      Bindings.empty Bindings.empty 12 [] [] ctxCall ctxOperator [ctxOperand]
      Completed.Frame.empty Completed.Frame.empty .active signature [signature.functionType]
      stack emitted := by
  refine {
    entry_ready := by simpa only [eraseCall, call] using
      (ScopedAtomEntryReady.initial Policy.unmarked ctxCall (Or.inl rfl))
    read_shape := by simp [ctxCall]
    operator_erase := eraseOperator
    arguments_erase := by simp
    input_not_stopped := by decide
    expected_not_atom := by decide
    expected_not_expression := by decide
    candidate_eq := ?_
    selection_ready := ?_
    worker_selected := ?_
    contextual_selected := selectedSource [] []
    input_activation := actEmpty
    selected_activation := actEmpty
    arity_eq := rfl
    argument_types_eq := rfl
    operator_not_stopped := by decide }
  all_goals
    rw [invocationTypes_eq_rawTypeLookup_of_closed annotations_closed]
    dsimp only
    rfl

theorem operatorDerivation (wLive cLive : List Atom) (scope : List String)
    (wStack : List RecursiveTasks.Frame) (cStack : List RecursiveTasks.Contextual.Continuation)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result) :
    ScopedAtomDerivation space HE.GroundedDispatch.none host Policy.unmarked wEmitted cEmitted
      13 wLive cLive scope operator ctxOperator signature.functionType Bindings.empty
      Completed.Frame.empty wStack cStack 1 [(operator, Bindings.empty)]
      [(ctxOperator, Completed.Frame.empty)] := by
  have ready : ScopedAtomEntryReady Policy.unmarked operator ctxOperator Completed.Frame.empty := by
    simpa only [eraseOperator] using
      (ScopedAtomEntryReady.initial Policy.unmarked ctxOperator (Or.inl rfl))
  have entered : Entry.Rel Policy.unmarked.reentry
      (Completed.Frame.empty.read Policy.unmarked ctxOperator).status
      (Completed.Frame.empty.read Policy.unmarked ctxOperator).erase signature.functionType .cast := by
    simpa [ctxOperator, operator, Completed.Frame.read_empty, Entry.Value.erase, Entry.Value.status] using
      (Entry.Rel.cast (policy := Policy.unmarked.reentry) (status := .active)
        (atom := operator) (expected := signature.functionType)
        (by simp [IsEmptyOrErrorRel, IsErrorRel, operator, Atom.empty]) (.symbol "hold") (by decide)
        (Or.inl ⟨"hold", rfl⟩) (by intro impossible; cases impossible))
  have admissionRaw : ScopedCastAdmission space Policy.unmarked operator signature.functionType
      ctxOperator Bindings.empty Completed.Frame.empty 12 wLive cLive scope wStack wEmitted
      [(operator, Bindings.empty)]
      [((Completed.Frame.empty.read Policy.unmarked ctxOperator).erase, Completed.Frame.empty.bindings)]
      [(Completed.Frame.empty.read Policy.unmarked ctxOperator, Completed.Frame.empty)] := by
    apply ScopedCastAdmission.unchanged
    · exact ready
    · exact entered
    · rw [invocationTypes_eq_rawTypeLookup_of_closed annotations_closed]
      dsimp only
      decide +kernel
    · rw [invocationTypes_eq_rawTypeLookup_of_closed annotations_closed]
      dsimp only
      decide +kernel
    · simpa only [Completed.Frame.read_empty, eraseOperator, emptyBindings] using
        headQuery _ signature.functionType
    · exact Completed.Frame.empty.preserved_type_match Policy.unmarked arrowMatch
    · exact actEmpty
  have admission : ScopedCastAdmission space Policy.unmarked operator signature.functionType
      ctxOperator Bindings.empty Completed.Frame.empty 12 wLive cLive scope wStack wEmitted
      [(operator, Bindings.empty)] [(operator, Bindings.empty)]
      [(ctxOperator, Completed.Frame.empty)] := by
    simpa only [Completed.Frame.read_empty, eraseOperator, emptyBindings] using admissionRaw
  exact .cast 12 wLive cLive scope operator signature.functionType ctxOperator Bindings.empty
    Completed.Frame.empty wStack cStack [(operator, Bindings.empty)] [(operator, Bindings.empty)]
    [(ctxOperator, Completed.Frame.empty)] admission

theorem operandDerivation (wLive cLive : List Atom) (scope : List String)
    (wStack : List RecursiveTasks.Frame) (cStack : List RecursiveTasks.Contextual.Continuation)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result) :
    ScopedAtomDerivation space HE.GroundedDispatch.none host Policy.unmarked wEmitted cEmitted
      12 wLive cLive scope operand ctxOperand formal Bindings.empty
      Completed.Frame.empty wStack cStack 1 [(operand, Bindings.empty)]
      [(ctxOperand, Completed.Frame.empty)] := by
  have ready : ScopedAtomEntryReady Policy.unmarked operand ctxOperand Completed.Frame.empty := by
    simpa only [eraseOperand] using
      (ScopedAtomEntryReady.initial Policy.unmarked ctxOperand (Or.inl rfl))
  have entered : Entry.Rel Policy.unmarked.reentry
      (Completed.Frame.empty.read Policy.unmarked ctxOperand).status
      (Completed.Frame.empty.read Policy.unmarked ctxOperand).erase formal .cast := by
    simpa [ctxOperand, operand, Completed.Frame.read_empty, Entry.Value.erase, Entry.Value.status] using
      (Entry.Rel.cast (policy := Policy.unmarked.reentry) (status := .active)
        (atom := operand) (expected := formal)
        (by simp [IsEmptyOrErrorRel, IsErrorRel, operand, Atom.empty]) (.grounded (.int 7)) (by decide)
        (Or.inr (Or.inl ⟨.int 7, rfl⟩)) (by intro impossible; cases impossible))
  have admissionRaw : ScopedCastAdmission space Policy.unmarked operand formal
      ctxOperand Bindings.empty Completed.Frame.empty 11 wLive cLive scope wStack wEmitted
      [(operand, Bindings.empty)]
      [((Completed.Frame.empty.read Policy.unmarked ctxOperand).erase, Completed.Frame.empty.bindings)]
      [(Completed.Frame.empty.read Policy.unmarked ctxOperand, Completed.Frame.empty)] := by
    apply ScopedCastAdmission.unchanged
    · exact ready
    · exact entered
    · rw [invocationTypes_eq_rawTypeLookup_of_closed annotations_closed]
      dsimp only
      decide +kernel
    · rw [invocationTypes_eq_rawTypeLookup_of_closed annotations_closed]
      dsimp only
      decide +kernel
    · simpa only [Completed.Frame.read_empty, eraseOperand, emptyBindings, formal] using
        operandQuery _ formal
    · exact Completed.Frame.empty.preserved_type_match Policy.unmarked numberMatch
    · exact actEmpty
  have admission : ScopedCastAdmission space Policy.unmarked operand formal ctxOperand Bindings.empty
      Completed.Frame.empty 11 wLive cLive scope wStack wEmitted
      [(operand, Bindings.empty)] [(operand, Bindings.empty)] [(ctxOperand, Completed.Frame.empty)] := by
    simpa only [Completed.Frame.read_empty, eraseOperand, emptyBindings] using admissionRaw
  exact .cast 11 wLive cLive scope operand formal ctxOperand Bindings.empty
    Completed.Frame.empty wStack cStack [(operand, Bindings.empty)] [(operand, Bindings.empty)]
    [(ctxOperand, Completed.Frame.empty)] admission

theorem argumentsDerivation (live : List Atom) (scope : List String)
    (wStack : List RecursiveTasks.Frame) (cStack : List RecursiveTasks.Contextual.Continuation)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result) :
    ScopedArgsDerivation space HE.GroundedDispatch.none host Policy.unmarked wEmitted cEmitted
      scope 13 9 live [operand] [formal] [(ctxOperand, formal)] [operand] [ctxOperand]
      Bindings.empty Completed.Frame.empty Bindings.empty Completed.Frame.empty wStack cStack := by
  apply ScopedArgsDerivation.cons scope 12 1 1 live operand operand formal [] [] []
    ctxOperand ctxOperand [] [] Bindings.empty Bindings.empty Bindings.empty
    Completed.Frame.empty Completed.Frame.empty Completed.Frame.empty wStack cStack
    eraseOperand eraseOperand rfl rfl rfl (by decide) actEmpty actEmpty actEmpty
  · exact operandDerivation _ _ _ _ _ _ _
  · exact .nil scope 11 _ Bindings.empty Completed.Frame.empty _ _ actEmpty

theorem callDerivation (wStack : List RecursiveTasks.Frame)
    (cStack : List RecursiveTasks.Contextual.Continuation)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result) :
    ScopedOrdinaryCallDerivation space HE.GroundedDispatch.none host Policy.unmarked wEmitted cEmitted
      14 11 [] [] call ctxCall returned Bindings.empty Completed.Frame.empty
      wStack cStack [(call, Bindings.empty)] [(ctxCall, Completed.Frame.empty)] := by
  apply ScopedOrdinaryCallDerivation.absent 13 [] [] call returned ctxCall
    Bindings.empty Completed.Frame.empty wStack cStack
  exact ReadyConstructorBoundary.ready_source_admission returned Bindings.empty 13 []
    ctxCall Completed.Frame.empty (by decide +kernel) (by decide +kernel) eraseCall
    (by simp [NonGroundedCallRel, Minimal.HostCall, host, Completed.Controls.typedDispatch,
      Minimal.embeddedInstruction]) actEmpty

theorem typed_constructor_region (wStack : List RecursiveTasks.Frame)
    (cStack : List RecursiveTasks.Contextual.Continuation)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result) :
    ScopedTaskRun space HE.GroundedDispatch.none host Policy.unmarked
      (.atom call Atom.undefinedType Bindings.empty 16 [])
      (.atom [] [] ctxCall Atom.undefinedType Completed.Frame.empty)
      wStack cStack wEmitted cEmitted 41 [(call, Bindings.empty)]
      [(ctxCall, Completed.Frame.empty)] := by
  have composed := selected_of_derivations space HE.GroundedDispatch.none host Policy.unmarked
    operator operator Atom.undefinedType [operand] [operand] ctxCall ctxOperator ctxOperator
    [ctxOperand] [ctxOperand] Bindings.empty Bindings.empty Bindings.empty Bindings.empty
    Completed.Frame.empty Completed.Frame.empty Completed.Frame.empty Completed.Frame.empty
    signature [signature.functionType] [(call, Bindings.empty)] [(ctxCall, Completed.Frame.empty)]
    12 1 9 11 4 [] [] wStack cStack wEmitted cEmitted .active (entry wStack wEmitted)
    (operatorDerivation _ _ _ _ _ _ _) (argumentsDerivation _ _ _ _ _ _)
    (callDerivation _ _ _ _) (by decide +kernel) (by decide +kernel)
  simpa [signature, formal, returned, Completed.invocationReturnType,
    successPriority, completedSuccessPriority, Completed.readResult, Completed.Frame.read_empty,
    Completed.publishResult, Policy.unmarked, Entry.Value.publish, call, ctxCall, ctxOperator,
    ctxOperand, operator, operand, isErrorAtom, Entry.Value.erase, Entry.publish,
    Entry.Value.withStatus] using composed

theorem typed_constructor_source :
    Completed.AtomRel space host Completed.scopedLookup [] [] ctxCall Atom.undefinedType
      Completed.Frame.empty [(ctxCall, Completed.Frame.empty)] (policy := Policy.unmarked) := by
  have source := selectedSource_of_parts space host Policy.unmarked operator operator Atom.undefinedType
    [operand] ctxCall ctxOperator ctxOperator [ctxOperand] [ctxOperand]
    Bindings.empty Bindings.empty Bindings.empty Completed.Frame.empty Completed.Frame.empty
    Completed.Frame.empty Completed.Frame.empty signature [signature.functionType]
    [(ctxCall, Completed.Frame.empty)] 12 [] [] [] [] .active (entry [] [])
    ⟨eraseOperator.symm, actEmpty⟩
    (operatorDerivation [] _ _ [] [] [] []).to_completed_atomRel
    (argumentsDerivation _ _ [] [] [] []).to_completed_argumentsRel
    (callDerivation [] [] [] []).to_completed_callRel
  simpa [signature, formal, returned, Completed.invocationReturnType,
    completedSuccessPriority, Completed.readResult, Completed.Frame.read_empty,
    Completed.publishResult, Policy.unmarked, Entry.Value.publish, call, ctxCall, ctxOperator,
    ctxOperand, operator, operand, isErrorAtom, Entry.Value.erase, Entry.publish,
    Entry.Value.withStatus] using source

theorem typed_constructor_finishes :
    ((Checked.machine HE.GroundedDispatch.none scopedTypes).run 43
      ⟨space, .work (.atom call Atom.undefinedType Bindings.empty 16 []), [], []⟩).1 =
        [(call, Bindings.empty)] := by
  rw [show 43 = 41 + 2 from rfl, (typed_constructor_region [] [] [] []).worker_run 2]
  rfl

def changedSpace : Space := space.add
  (.expression [.symbol "=", call, .grounded (.int 9)])

theorem added_equation_invalidates_absence :
    HEConstructorAdmission.headAbsent changedSpace "hold" = false := by decide +kernel

theorem added_equation_changes_return :
    invoke changedSpace HE.GroundedDispatch.none (.ordinary returned) call Bindings.empty 14 ≠
      [(call, Bindings.empty)] := by decide +kernel

theorem added_equation_changes_selected_worker :
    ((Checked.machine HE.GroundedDispatch.none scopedTypes).run 80
      ⟨changedSpace, .work (.atom call Atom.undefinedType Bindings.empty 16 []), [], []⟩).1 ≠
        [(call, Bindings.empty)] := by decide +kernel

theorem ignoring_equation_would_change_answer :
    [(call, Bindings.empty)] ≠
      ((Checked.machine HE.GroundedDispatch.none scopedTypes).run 80
        ⟨changedSpace, .work (.atom call Atom.undefinedType Bindings.empty 16 []), [], []⟩).1 := by
  exact Ne.symm added_equation_changes_selected_worker

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedCallComposition.Controls
