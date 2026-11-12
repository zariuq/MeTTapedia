import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.IfEveryRun

/-!
# A condition other than `True` and `False`: HE returns the call, PeTTa takes the else branch

On HE's standard-library `if` (`IfEveryRun.ifProgram`), the condition `Foo` (an undeclared symbol)
meets the demand `Bool`, since its type is `%Undefined%`. HE's `if` has equations for `True` and
`False` only, so no equation matches `(if Foo yes no)`: every complete run of HE publishes the call
itself, and a complete run exists (`foo_every_run`). PeTTa's special form sends every answer other
than `True` to the else branch and yields `no` (`AtomDemands.Controls.petta_if_non_boolean`, here
`petta_foo` on the same program).

The smallest program for this difference is HE's three rows for `if` and the call `(if Foo yes no)`
(`if_non_boolean_differs`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace IfDifference

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel rawTypeLookupRel
  FunctionTypeRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings DeclaredHeads
  DeclaredEveryRun TypedEveryRun AtomDemands IfEveryRun
open AnswerBags.Controls (sym app rule rule_consFree)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-- `(if Foo yes no)`. -/
abbrev fooCall : Atom := app "if" [sym "Foo", sym "yes", sym "no"]

theorem foo_types : StorageTypesRel (Space.ofList ifProgram) (sym "Foo") [Atom.undefinedType] :=
  .symbolUndefined (.skip (fun _ same => by simp at same)
    (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same) .nil)))

theorem foo_data : DataAtom (sym "Foo") := .symbol (by decide) (by decide)

theorem bool_meets_undefined (frame : Frame) :
    ∃ output, policy.matching.Rel (sym "Bool") Atom.undefinedType frame.bindings output :=
  ⟨_, Completed.Frame.preserved_type_match policy frame (.undefinedRight _ _)⟩

/-! ## Every derivation -/

/-- **Every application check of `(if Foo yes no)` keeps exactly one activation, with no
bindings.** -/
theorem foo_checks {signature : SelectedTypePolicy} {frames : List Frame} {errors : List Atom}
    (functionType : signature.functionType = ifArrow)
    (checks : Completed.ApplicationChecksRel (Space.ofList ifProgram)
      (rawTypeLookupRel (Space.ofList ifProgram)) policy fooCall Atom.undefinedType signature
      Completed.Frame.empty frames errors) :
    ∃ after, frames = [after] ∧ after.bindings = Bindings.empty := by
  have projections := if_projections functionType
  cases checks with
  | wrongArity shaped arity =>
      simp only [fooCall, app, Atom.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl⟩ := shaped
      rw [projections.1] at arity
      exact absurd rfl arity
  | checked shaped arguments returned =>
      simp only [fooCall, app, Atom.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl⟩ := shaped
      rw [projections.1] at arguments
      obtain ⟨f1, same1, rest1⟩ := accepted_step foo_types (fun _ matched =>
        Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeMatchRel.wildcard_output matched
          (Or.inr (Or.inr (Or.inl rfl)))) (bool_meets_undefined _) arguments
      obtain ⟨f2, same2, rest2⟩ := accepted_step yes_types' (fun _ matched =>
        Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeMatchRel.wildcard_output matched
          (Or.inr (Or.inl rfl))) (atom_demand_accepts _ _) rest1
      obtain ⟨f3, same3, rest3⟩ := accepted_step no_types' (fun _ matched =>
        Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeMatchRel.wildcard_output matched
          (Or.inr (Or.inl rfl))) (atom_demand_accepts _ _) rest2
      cases rest3
      obtain ⟨returnCheck, rest', returnChecked, nilReturn, rfl⟩ :=
        List.forall₂_cons_left_iff.mp returned
      obtain rfl := List.forall₂_nil_left_iff.mp nilReturn
      cases returnChecked with
      | accepted renewed =>
          refine ⟨_, rfl, ?_⟩
          rw [Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeMatchRel.wildcard_output renewed.source
            (Or.inl rfl), same3, same2, same1]
          rfl
      | rejected rejectedAll =>
          obtain ⟨output, matched⟩ := undefined_accepts (policy := policy) _ f3
          exact (rejectedAll output matched).elim

/-- **Every admission of `(if Foo yes no)` selects `if`'s arrow**, with one activation and no
bindings: the type of `Foo` is `%Undefined%`, which `Bool` accepts. -/
theorem foo_selection {outcome : Completed.InvocationSelection}
    (chosenRel : Completed.InvocationSelectionRel (Space.ofList ifProgram) Completed.rawLookup policy
      [] [] fooCall (.symbol "if") Atom.undefinedType Completed.Frame.empty outcome) :
    ∃ (signature : SelectedTypePolicy) (after : Frame), signature.functionType = ifArrow ∧
      after.bindings = Bindings.empty ∧ outcome = .selected signature [after] := by
  obtain ⟨candidates, queried, scanned⟩ := chosenRel
  have same := StorageTypesRel.unique
    (show StorageTypesRel (Space.ofList ifProgram) (.symbol "if") candidates from queried) if_types
  cases scanned with
  | nil => cases same
  | nonFunction notArrow _ =>
      simp only [List.cons.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact absurd ⟨_, _, ifPolicy.isFunction⟩ notArrow
  | selected checks nonempty =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      obtain ⟨after, rfl, bindings⟩ := foo_checks functionType checks
      exact ⟨_, after, functionType, bindings, rfl⟩
  | rejected checks rest =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      obtain ⟨after, impossible, _⟩ := foo_checks functionType checks
      cases impossible

theorem foo_values :
    ∀ v ∈ [sym "Foo", sym "yes", sym "no"], NestedValues.Value dispatch ifProgram v := by
  intro v member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .data foo_data
  · exact .data (.symbol (by decide) (by decide))
  · exact .data (.symbol (by decide) (by decide))

theorem foo_instances : regionInstances ifProgram "if" [sym "Foo", sym "yes", sym "no"] = [] := by
  decide +kernel

/-- **Every derivation of the typed query of `(if Foo yes no)` returns the call itself**: no
equation of `if` matches. -/
theorem foo_call_source {live : List Atom} {scope : List String} {value : Entry.Value}
    {frame : Frame} {children : List Result} (erased : value.erase = fooCall)
    (called : Completed.CallRel (Space.ofList ifProgram) dispatch Completed.rawLookup live scope
      value (.var "t") frame children (policy := policy)) :
    children.map (fun r => r.1.erase) = [fooCall] := by
  have valsValues := foo_values (dispatch := dispatch)
  cases called with
  | error failed =>
      rw [erased] at failed
      obtain ⟨tail, same⟩ := failed
      simp at same
  | embedded _ _ instruction _ _ =>
      rw [erased] at instruction
      simp [Minimal.embeddedInstruction] at instruction
  | absent _ _ _ => simp [erased]
  | equations _ _ frontier nonempty _ =>
      rw [erased] at frontier
      have works := works_instances_K policy valsValues if_program frame.certified.satisfiable frontier
      rw [foo_instances] at works
      exact absurd (List.forall₂_nil_right_iff.mp works) nonempty

theorem foo_answerable : Answerable fooCall :=
  app_answerable if_data fun a member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact answerable_of_data (.symbol (by decide) (by decide))

/-- **Every derivation of HE's completed relation for `(if Foo yes no)` publishes the call
itself.** -/
theorem foo_source {results : List Result}
    (derived : Completed.AtomRel (Space.ofList ifProgram) dispatch Completed.rawLookup [] []
      (Entry.Value.ofAtom fooCall) Atom.undefinedType Completed.Frame.empty results
      (policy := policy)) :
    results.map (fun r => r.1.erase) = [fooCall] := by
  have entry := call_entry policy if_data [sym "Foo", sym "yes", sym "no"]
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom fooCall) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [sym "Foo", sym "yes", sym "no"].map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [fooCall, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have outcome : ∀ {result : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList ifProgram) Completed.rawLookup policy [] []
        (Completed.Frame.empty.read policy (Entry.Value.ofAtom fooCall)).erase
        (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType Completed.Frame.empty result →
      ∃ (signature : SelectedTypePolicy) (after : Frame), signature.functionType = ifArrow ∧
        after.bindings = Bindings.empty ∧ result = .selected signature [after] := by
    intro result chosenRel
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosenRel
    exact foo_selection chosenRel
  have readYes : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom (sym "yes")) =
      Entry.Value.ofAtom (sym "yes") := fun frame => HERuns.read_closed policy frame (closed_symbol _)
  have readNo : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom (sym "no")) =
      Entry.Value.ofAtom (sym "no") := fun frame => HERuns.read_closed policy frame (closed_symbol _)
  cases derived with
  | delivered entered => cases Entry.functional entered entry
  | cast entered => cases Entry.functional entered entry
  | tuple _ shaped occurs _ _ _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      rw [Entry.Value.erase_ofAtom] at occurs
      have same := Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel.unique occurs
        if_types.occurrences
      simp [Atom.undefinedType] at same
  | fallback _ shaped chosenRel _ _ _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      obtain ⟨_, _, _, _, impossible⟩ := outcome chosenRel
      cases impossible
  | selectionFailed _ shaped chosenRel _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      obtain ⟨_, _, _, _, impossible⟩ := outcome chosenRel
      cases impossible
  | function _ shaped chosenRel invoked priority =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, rfl⟩ := shaped
      obtain ⟨signature, after, functionType, afterBindings, selected⟩ := outcome chosenRel
      simp only [Completed.InvocationSelection.selected.injEq] at selected
      obtain ⟨rfl, rfl⟩ := selected
      have projections := if_projections functionType
      have returnTypeOf : ∀ {s : SelectedTypePolicy}, s.returnType = .var "t" →
          Completed.invocationReturnType s = .var "t" := by
        intro s same
        simp [Completed.invocationReturnType, same, Atom.expressionType]
      have returnType := returnTypeOf projections.2
      cases invoked with
      | cons function calls rest =>
          cases rest
          cases function with
          | evaluated _ operatorRel branches =>
              rw [functionType] at operatorRel
              obtain ⟨frF, rfl⟩ := typed_cast_source_at if_data
                (symbol_cast_entry (by decide) (by decide) (by decide +kernel)) if_types
                (ifArrow_accepts afterBindings) operatorRel
              rw [projections.1] at branches
              simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right]
                at branches
              cases branches with
              | stopped stopped _ =>
                  rw [Entry.Value.erase_ofAtom] at stopped
                  exact absurd stopped if_data.not_stopped
              | continuing _ arguments restBranches =>
                  cases restBranches
                  cases arguments with
                  | cons conditionRel conditionBranches =>
                      obtain ⟨fr1, rfl⟩ := typed_cast_source foo_data
                        (symbol_cast_entry (by decide) (by decide) (by decide +kernel)) foo_types
                        bool_meets_undefined conditionRel
                      cases conditionBranches with
                      | stopped stopped _ =>
                          obtain ⟨stoppedCondition, _⟩ := stopped
                          rw [Entry.Value.erase_ofAtom] at stoppedCondition
                          exact absurd stoppedCondition foo_data.not_stopped
                      | continuing _ yesArguments restCondition =>
                          cases restCondition
                          cases yesArguments with
                          | cons yesRel yesBranches =>
                              have yesDelivered := atom_demand_source yesRel
                              subst yesDelivered
                              rw [readYes] at yesBranches
                              cases yesBranches with
                              | stopped stopped _ =>
                                  obtain ⟨stoppedYes, _⟩ := stopped
                                  rw [Entry.Value.erase_ofAtom] at stoppedYes
                                  exact absurd stoppedYes
                                    (DataAtom.symbol (name := "yes") (by decide) (by decide)).not_stopped
                              | continuing _ noArguments restYes =>
                                  cases restYes
                                  cases noArguments with
                                  | cons noRel noBranches =>
                                      have noDelivered := atom_demand_source noRel
                                      subst noDelivered
                                      rw [readNo] at noBranches
                                      cases noBranches with
                                      | stopped stopped _ =>
                                          obtain ⟨stoppedNo, _⟩ := stopped
                                          rw [Entry.Value.erase_ofAtom] at stoppedNo
                                          exact absurd stoppedNo
                                            (DataAtom.symbol (name := "no") (by decide)
                                              (by decide)).not_stopped
                                      | continuing _ packets restNo =>
                                          cases restNo
                                          cases packets
                                          rw [returnType] at calls
                                          simp only [List.map_cons, List.map_nil, List.append_nil,
                                            Completed.argumentPrepend_packet] at calls
                                          cases calls with
                                          | cons callRel restCalls =>
                                              cases restCalls
                                              have assembled : ∀ frame : Frame,
                                                  (Completed.functionAssemble
                                                    (Entry.Value.ofAtom (.symbol "if"))
                                                    (Entry.Value.argumentPacket
                                                      [Entry.Value.ofAtom (sym "Foo"),
                                                        Entry.Value.ofAtom (sym "yes"),
                                                        Entry.Value.ofAtom (sym "no")], frame)).1.erase =
                                                    fooCall := fun frame => by
                                                simp [Completed.functionAssemble, Entry.Value.erase,
                                                  fooCall, app]
                                              have answered := foo_call_source (assembled _) callRel
                                              exact publish_answers
                                                (by simp only [List.append_nil]; exact answered)
                                                (fun a member => by
                                                  rw [List.mem_singleton] at member
                                                  subst member
                                                  exact foo_answerable)
                                                priority

/-! ## A complete run -/

theorem foo_arrow_selected (policy : Policy) :
    ∃ errors, Completed.ApplicationChecksRel (Space.ofList ifProgram)
      (rawTypeLookupRel (Space.ofList ifProgram)) policy fooCall Atom.undefinedType ifPolicy
      Completed.Frame.empty [Completed.Frame.empty] errors :=
  ⟨_, .checked (operator := sym "if") (arguments := [sym "Foo", sym "yes", sym "no"]) rfl
    (.cons (.cons foo_types
      (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy _
        (.undefinedRight _ _)))) .nil) .nil)
      (.cons (.cons yes_types'
        (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy _
          (.atomLeft _ _)))) .nil) .nil)
        (.cons (.cons no_types'
          (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy _
            (.atomLeft _ _)))) .nil) .nil) .nil)))
    (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy _
      (.undefinedLeft _ _)))) .nil)⟩

theorem foo_selection_succeeds (policy : Policy) :
    Completed.InvocationSelectionRel (Space.ofList ifProgram) Completed.rawLookup policy [] []
      fooCall (.symbol "if") Atom.undefinedType Completed.Frame.empty
      (.selected ifPolicy [Completed.Frame.empty]) := by
  obtain ⟨errors, checks⟩ := foo_arrow_selected policy
  exact ⟨[ifPolicy.functionType], if_types, .selected checks (List.cons_ne_nil _ _)⟩

/-- **The function application of `(if Foo yes no)`.** -/
theorem foo_function_segment (dispatch : GroundedDispatch) (policy : Policy)
    (stack : List Continuation) :
    ∃ results : List Result,
      HERuns.HESteps dispatch Completed.rawLookup policy
        ⟨Space.ofList ifProgram, .work (.function [Completed.invocationReturnType ifPolicy] []
          Atom.undefinedType ifPolicy (Entry.Value.ofAtom (.symbol "if"))
          [Entry.Value.ofAtom (sym "Foo"), Entry.Value.ofAtom (sym "yes"),
            Entry.Value.ofAtom (sym "no")] Completed.Frame.empty), stack, []⟩
        ⟨Space.ofList ifProgram, .returning results, stack, []⟩ ∧
      ∃ value activation, results = [(value, activation)] ∧ value.erase = fooCall := by
  obtain ⟨frF, renewal⟩ := if_operator_renewal policy
  have readYes : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom (sym "yes")) =
      Entry.Value.ofAtom (sym "yes") := fun frame => HERuns.read_closed policy frame (closed_symbol _)
  have readNo : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom (sym "no")) =
      Entry.Value.ofAtom (sym "no") := fun frame => HERuns.read_closed policy frame (closed_symbol _)
  have ifCast := renewed_cast_step dispatch policy (atom := .symbol "if") (closed_symbol "if")
    (symbol_cast_entry (by decide) (by decide) (by decide +kernel)) if_types Completed.Frame.empty frF
    renewal
  have fooCast := typed_cast dispatch policy (atom := sym "Foo") (expected := sym "Bool")
    (closed_symbol "Foo") (symbol_cast_entry (by decide) (by decide) (by decide +kernel)) foo_types
    frF (.undefinedRight _ _)
  apply Exists.intro
  refine ⟨?_, ?_⟩
  · refine .head (.internal (.functionStart rfl)) ?_
    refine .head (ifCast _ _ _ _) ?_
    refine .head (.internal .functionHeads) ?_
    refine .head (.internal (.functionBranchesContinue ?_)) ?_
    · simpa using if_data.not_stopped
    refine .head (.internal .argumentsCons) ?_
    refine .head (fooCast _ _ _ _) ?_
    refine .head (.internal .arguments) ?_
    refine .head (.internal (.argumentBranchesContinue ?_)) ?_
    · rintro ⟨stopped, _⟩
      exact foo_data.not_stopped (by simpa using stopped)
    refine .head (.internal .argumentsCons) ?_
    refine .head (.internal (.delivered (atom_demand_deliver _))) ?_
    refine .head (.internal .arguments) ?_
    refine .head (.internal (.argumentBranchesContinue ?_)) ?_
    · rintro ⟨stopped, _⟩
      rw [readYes] at stopped
      exact symbol_not_stopped "yes" (by decide) (by decide) (by simpa using stopped)
    refine .head (.internal .argumentsCons) ?_
    refine .head (.internal (.delivered (atom_demand_deliver _))) ?_
    refine .head (.internal .arguments) ?_
    refine .head (.internal (.argumentBranchesContinue ?_)) ?_
    · rintro ⟨stopped, _⟩
      rw [readNo] at stopped
      exact symbol_not_stopped "no" (by decide) (by decide) (by simpa using stopped)
    refine .head (.internal .argumentsNil) ?_
    refine .head (.internal .argumentTail) ?_
    refine .head (.internal .append) ?_
    refine .head (.internal .argumentBranchesNil) ?_
    refine .head (.internal .prepend) ?_
    refine .head (.internal .argumentTail) ?_
    refine .head (.internal .append) ?_
    refine .head (.internal .argumentBranchesNil) ?_
    refine .head (.internal .prepend) ?_
    refine .head (.internal .argumentTail) ?_
    refine .head (.internal .append) ?_
    refine .head (.internal .argumentBranchesNil) ?_
    refine .head (.internal .prepend) ?_
    refine .head (.internal .functionAssemble) ?_
    refine .head (.internal .append) ?_
    refine .head (.internal .functionBranchesNil) ?_
    exact .single (.internal .prepend)
  · refine ⟨_, _, rfl, ?_⟩
    simp [Entry.Value.erase, readYes, readNo, fooCall, app]

/-- **The typed query of `(if Foo yes no)` returns the call**: the frontier is empty. -/
theorem foo_query (dispatch : GroundedDispatch) (notHost : ¬ dispatch.executable (.symbol "if"))
    (policy : Policy) (value : Entry.Value) (erased : value.erase = fooCall) (activation : Frame)
    (stack : List Continuation) :
    HERuns.HESteps dispatch Completed.rawLookup policy
      ⟨Space.ofList ifProgram, .work (.call [] [] value (.var "t") activation), stack, []⟩
      ⟨Space.ofList ifProgram, .returning [(value, activation)], stack, []⟩ := by
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList ifProgram) [.var "t"] fooCall
    activation.bindings
  have instances := works_instances_K policy (foo_values (dispatch := dispatch)) if_program
    activation.certified.satisfiable frontier
  rw [foo_instances] at instances
  obtain rfl := List.forall₂_nil_right_iff.mp instances
  have frontier' : EquationFrontierRel (Space.ofList ifProgram) [.var "t"] value.erase
      activation.bindings [] := by
    rw [erased]
    exact frontier
  have notError : ¬ IsErrorRel value.erase := by
    rw [erased]
    rintro ⟨tail, same⟩
    simp at same
  have nonGrounded : NonGroundedCallRel dispatch value.erase := by
    rw [erased]
    refine And.intro ?_ (by decide +kernel)
    rintro ⟨operator, arguments, same, executable⟩
    simp only [fooCall, app, Atom.expression.injEq, List.cons.injEq] at same
    rw [← same.1] at executable
    exact notHost executable
  exact .single (.internal (.callAbsent notError nonGrounded frontier'))

/-- **A complete run of `(if Foo yes no)`, publishing the call itself.** -/
theorem he_foo_run (dispatch : GroundedDispatch) (notHost : ¬ dispatch.executable (.symbol "if"))
    (policy : Policy) :
    ∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList ifProgram) fooCall Atom.undefinedType)
          ⟨Space.ofList ifProgram, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [fooCall] := by
  have entry := call_entry policy if_data [sym "Foo", sym "yes", sym "no"]
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom fooCall) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [sym "Foo", sym "yes", sym "no"].map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [fooCall, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have selection : Completed.ArgumentService.historical.selection (Space.ofList ifProgram)
      Completed.rawLookup policy [] []
      (Completed.Frame.empty.read policy (Entry.Value.ofAtom fooCall)).erase
      (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType Completed.Frame.empty
      (.selected ifPolicy [Completed.Frame.empty]) := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
    exact foo_selection_succeeds policy
  have step := LocalStepWith.atomFunction (admission := .historical)
    (space := Space.ofList ifProgram) (dispatch := dispatch) (lookup := Completed.rawLookup)
    (live := []) (scope := []) (stack := []) entry shape selection
  have published : (Completed.Frame.empty.read policy (Entry.Value.ofAtom fooCall)).erase =
      fooCall := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom]
  rw [published] at step
  have returned : Completed.invocationReturnType ifPolicy = .var "t" := by
    simp [Completed.invocationReturnType, ifPolicy, Atom.expressionType]
  obtain ⟨F, pathF, value, activation, rfl, erased⟩ := foo_function_segment dispatch policy
    (.calls [] [] (Completed.invocationReturnType ifPolicy) ::
      .append (.invocations [] [] Atom.undefinedType ifPolicy (Entry.Value.ofAtom (.symbol "if"))
        [Entry.Value.ofAtom (sym "Foo"), Entry.Value.ofAtom (sym "yes"),
          Entry.Value.ofAtom (sym "no")] []) :: [.publish fooCall])
  have pathQ := foo_query dispatch notHost policy value erased activation
    (.append (.calls [] [] (.var "t") []) ::
      .append (.invocations [] [] Atom.undefinedType ifPolicy (Entry.Value.ofAtom (.symbol "if"))
        [Entry.Value.ofAtom (sym "Foo"), Entry.Value.ofAtom (sym "yes"),
          Entry.Value.ofAtom (sym "no")] []) :: [.publish fooCall])
  have clean : ∀ r ∈ ([(value, activation)] ++ []) ++ [], Answerable r.1.erase := by
    intro r member
    simp only [List.append_nil, List.mem_singleton] at member
    subst member
    rw [erased]
    exact foo_answerable
  obtain ⟨publishedAnswers, eraseP, pathP⟩ := NestedArguments.HENested.publish_step
    (dispatch := dispatch) (lookup := Completed.rawLookup) (policy := policy) (atoms := ifProgram)
    fooCall (([(value, activation)] ++ []) ++ []) clean [] []
  refine ⟨publishedAnswers, ?_, by rw [eraseP]; simp [erased]⟩
  refine .head (.internal step) ?_
  refine .head (.internal .invocationsCons) ?_
  refine .trans pathF ?_
  refine .head (.internal .calls) ?_
  rw [returned]
  refine .head (.internal .callsCons) ?_
  refine .trans pathQ ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .callsNil) ?_
  refine .head (.internal .prepend) ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .invocationsNil) ?_
  refine .head (.internal .prepend) ?_
  exact pathP.trans (HERuns.publish_all _ publishedAnswers [])

/-! ## PeTTa -/

/-- **PeTTa sends `Foo` to the else branch**, from fuel `10` on. -/
theorem petta_foo :
    ∀ n, 10 ≤ n → Streaming.values (Streaming.advance (translate ifProgram) n
      (Streaming.enter { state := store ifProgram } fooCall)) = [sym "no"] := by
  have done : (Streaming.advance (translate ifProgram) 10
      (Streaming.enter { state := store ifProgram } fooCall)).agenda.length = 0 := by
    decide +kernel
  have value : Streaming.values (Streaming.advance (translate ifProgram) 10
      (Streaming.enter { state := store ifProgram } fooCall)) = [sym "no"] := by
    decide +kernel
  intro n bigger
  rw [advance_stable (List.eq_nil_of_length_eq_zero done) n bigger]
  exact value

/-! ## The named difference -/

/-- **HE's `if` on a condition other than `True` and `False`, on every run.** A complete run of
`(if Foo yes no)` exists, and every complete run publishes the call itself. -/
theorem foo_every_run (dispatch : GroundedDispatch) (notHost : ¬ dispatch.executable (.symbol "if"))
    (policy : Policy) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList ifProgram) fooCall Atom.undefinedType)
          ⟨Space.ofList ifProgram, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
            (load (Space.ofList ifProgram) fooCall Atom.undefinedType)
            ⟨Space.ofList ifProgram, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = [fooCall] := by
  obtain ⟨heAnswers, path, _⟩ := he_foo_run dispatch notHost policy
  exact ⟨⟨heAnswers, path⟩, fun emitted run => foo_source (complete_source run)⟩

/-- **The named difference, smallest program**: on HE's three rows for `if`, every complete run of
HE publishes `(if Foo yes no)`, while PeTTa yields `no`; the two answers differ. -/
theorem if_non_boolean_differs (dispatch : GroundedDispatch)
    (notHost : ¬ dispatch.executable (.symbol "if")) (policy : Policy) :
    (∀ emitted : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList ifProgram) fooCall Atom.undefinedType)
          ⟨Space.ofList ifProgram, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [fooCall]) ∧
      (∀ n, 10 ≤ n → Streaming.values (Streaming.advance (translate ifProgram) n
        (Streaming.enter { state := store ifProgram } fooCall)) = [sym "no"]) ∧
      fooCall ≠ sym "no" :=
  ⟨(foo_every_run dispatch notHost policy).2, petta_foo, by simp [fooCall, app]⟩

#print axioms foo_checks
#print axioms foo_selection
#print axioms foo_call_source
#print axioms foo_source
#print axioms foo_function_segment
#print axioms foo_query
#print axioms he_foo_run
#print axioms petta_foo
#print axioms foo_every_run
#print axioms if_non_boolean_differs

end IfDifference

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
