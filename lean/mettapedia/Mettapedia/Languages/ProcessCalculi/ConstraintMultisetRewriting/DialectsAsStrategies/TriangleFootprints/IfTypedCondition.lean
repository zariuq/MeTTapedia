import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.IfAtFrames

/-!
# A named difference: a condition of a declared type other than `Bool`

`(if 5 yes no)` on HE's standard-library `if`: the condition `5` has the stored type `Number`, which
`Bool` does not match, so HE's admission rejects `if`'s only arrow (`BadArgType` at position 1) and
every complete run publishes the diagnostic `(Error (if 5 yes no) (BadArgType 1 Bool Number))`;
PeTTa's special form takes the else branch, `no`.

This is a different case from `IfDifference`, where the condition is an undeclared symbol: `Bool`
accepts `%Undefined%`, so HE admits the call, no row of `if` matches, and HE publishes the call
itself. Here the type check itself rejects the call.

* `bool_number_no_match`, `bool_number_rejected`: `Bool` matches `Number` under no bindings, under
  either matching policy;
* `five_checks`, `five_selection`: every admission of `(if 5 yes no)` is exhausted with exactly the
  one diagnostic and no tuple fallback;
* `five_source`: every derivation of HE's completed relation publishes the diagnostic;
* `five_run`: a complete run exists; `petta_five`: PeTTa yields `no` from fuel `8` on;
* `typed_condition_differs`: the three together.

## Controls

The positive control is `IfEveryRun` (`(if True yes no)` and `(if False yes no)` agree on every run):
there `Bool` accepts the condition's stored type. The negative control is the rejection itself,
`bool_number_no_match`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace IfTypedCondition

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom mkError ErrorCode)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel rawTypeLookupRel
  FunctionTypeRel)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Machines.OrderedProtocol.Completion (SuccessPriorityRel)
open ServiceFootprints EntryToQuery AnswerBags EveryRun NestedEveryRun IfEveryRun
open AnswerBags.Controls (sym app)
open WholeRunWords.Double (noHost)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-- `(if 5 yes no)`. -/
abbrev fiveCall : Atom := app "if" [.grounded (.int 5), sym "yes", sym "no"]

/-- HE's diagnostic `(Error (if 5 yes no) (BadArgType 1 Bool Number))`. -/
abbrev badArg : Atom := mkError fiveCall (.badArgType 1 (sym "Bool") (sym "Number"))

theorem five_types : StorageTypesRel (Space.ofList ifProgram) (.grounded (.int 5)) [sym "Number"] :=
  .groundedKnown (.int 5) (by simp [Atom.undefinedType])

/-- **`Bool` matches `Number` under no bindings.** -/
theorem bool_number_no_match (b out : Bindings) :
    ¬ TypeMatchRel (sym "Bool") (sym "Number") b out := by
  intro matched
  generalize sameE : sym "Bool" = E at matched
  generalize sameT : sym "Number" = T at matched
  cases matched with
  | undefinedLeft => simp [Atom.undefinedType] at sameE
  | atomLeft => simp [Atom.atomType] at sameE
  | undefinedRight => simp [Atom.undefinedType] at sameT
  | atomRight => simp [Atom.atomType] at sameT
  | structural _ _ _ _ inner _ =>
      subst sameE sameT
      generalize sameL : sym "Bool" = L at inner
      generalize sameR : sym "Number" = R at inner
      cases inner <;> (try simp_all); exact absurd (sameL.trans sameR.symm) (by decide)

theorem bool_number_rejected (frame : Frame) :
    ∀ output, ¬ policy.matching.Rel (sym "Bool") (sym "Number") frame.bindings output := by
  intro output matched
  cases matching : policy.matching with
  | raw =>
      rw [matching] at matched
      exact bool_number_no_match _ _ matched
  | finite =>
      rw [matching] at matched
      exact bool_number_no_match _ _ matched.1

/-- **Every application check of `(if 5 yes no)` rejects `if`'s arrow with the one diagnostic.** -/
theorem five_checks {signature : SelectedTypePolicy} {frame : Frame} {frames : List Frame}
    {errors : List Atom} (functionType : signature.functionType = ifArrow)
    (checks : Completed.ApplicationChecksRel (Space.ofList ifProgram)
      (rawTypeLookupRel (Space.ofList ifProgram)) policy fiveCall Atom.undefinedType signature
      frame frames errors) :
    frames = [] ∧ errors = [badArg] := by
  have projections := if_projections functionType
  cases checks with
  | wrongArity shaped arity =>
      simp only [fiveCall, app, Atom.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl⟩ := shaped
      rw [projections.1] at arity
      exact absurd rfl arity
  | checked shaped arguments returned =>
      simp only [fiveCall, app, Atom.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl⟩ := shaped
      rw [projections.1] at arguments
      cases arguments with
      | cons head later =>
          cases head with
          | cons queried paired nilChecks =>
              cases nilChecks
              have same := StorageTypesRel.unique
                (show StorageTypesRel (Space.ofList ifProgram) (.grounded (.int 5)) _ from queried)
                five_types
              subst same
              obtain ⟨check, checks, checkedOne, nilPaired, rfl⟩ :=
                List.forall₂_cons_left_iff.mp paired
              obtain rfl := List.forall₂_nil_left_iff.mp nilPaired
              cases checkedOne with
              | accepted renewed => exact (bool_number_no_match _ _ renewed.source).elim
              | rejected _ =>
                  simp only [Completed.checkedFrames, Completed.checkedFailures, List.filterMap_cons,
                    List.filterMap_nil, List.map_cons, List.map_nil, List.append_nil] at later ⊢
                  cases later with
                  | cons head2 later2 =>
                      cases head2
                      cases later2 with
                      | cons head3 later3 =>
                          cases head3
                          cases later3
                          cases returned
                          simp

/-- **Every admission of `(if 5 yes no)` is exhausted with the one diagnostic, without a tuple.** -/
theorem five_selection {live : List Atom} {scope : List String} {frame : Frame}
    {outcome : Completed.InvocationSelection}
    (chosenRel : Completed.InvocationSelectionRel (Space.ofList ifProgram) Completed.rawLookup policy
      live scope fiveCall (.symbol "if") Atom.undefinedType frame outcome) :
    outcome = .exhausted [badArg] false := by
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
      exact absurd (five_checks functionType checks).1 nonempty
  | rejected checks rest =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      obtain ⟨_, rfl⟩ := five_checks functionType checks
      cases rest
      rfl

theorem badArg_error : isErrorAtom badArg = true := rfl

theorem badArg_closed :
    ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs badArg name := by
  intro name occurs
  have member := (Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars _ _).mp
    occurs
  have none : Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVars badArg = [] := by
    decide
  rw [none] at member
  cases member

/-- **Every derivation of HE's completed relation for `(if 5 yes no)` publishes the diagnostic.** -/
theorem five_source {results : List Result}
    (derived : Completed.AtomRel (Space.ofList ifProgram) dispatch Completed.rawLookup [] []
      (Entry.Value.ofAtom fiveCall) Atom.undefinedType Completed.Frame.empty results
      (policy := policy)) :
    results.map (fun r => r.1.erase) = [badArg] := by
  have entry := call_entry policy if_data [.grounded (.int 5), sym "yes", sym "no"]
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom fiveCall) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [Atom.grounded (.int 5), sym "yes", sym "no"].map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [fiveCall, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have outcome : ∀ {result : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList ifProgram) Completed.rawLookup policy [] []
        (Completed.Frame.empty.read policy (Entry.Value.ofAtom fiveCall)).erase
        (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType Completed.Frame.empty result →
      result = .exhausted [badArg] false := by
    intro result chosenRel
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosenRel
    exact five_selection chosenRel
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
      cases outcome chosenRel
  | function _ shaped chosenRel _ _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      cases outcome chosenRel
  | selectionFailed _ shaped chosenRel priority =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      have exhausted := outcome chosenRel
      simp only [Completed.InvocationSelection.exhausted.injEq, and_true] at exhausted
      subst exhausted
      have readOne : (Completed.diagnosticResults [badArg] Completed.Frame.empty).map
          (Completed.readResult policy) =
          Completed.diagnosticResults [badArg] Completed.Frame.empty := by
        simp only [Completed.diagnosticResults, List.map_cons, List.map_nil]
        rw [HERuns.readResult_closed policy _ (by
          simpa [Entry.Value.erase_ofAtom] using badArg_closed)]
      rw [readOne] at priority
      have allErrors : SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
          (Completed.diagnosticResults [badArg] Completed.Frame.empty)
          (Completed.diagnosticResults [badArg] Completed.Frame.empty) :=
        .allErrors (fun item member => by
          simp only [Completed.diagnosticResults, List.map_cons, List.map_nil,
            List.mem_singleton] at member
          subst member
          simp [Entry.Value.erase_ofAtom, badArg_error])
      rw [SuccessPriorityRel.functional priority allErrors, publish_erase]
      simp [Completed.diagnosticResults, Entry.Value.erase_ofAtom]

/-- HE's admission of `(if 5 yes no)` exists: it rejects the arrow with the diagnostic. -/
theorem five_selection_exists (policy : Policy) :
    Completed.InvocationSelectionRel (Space.ofList ifProgram) Completed.rawLookup policy [] []
      fiveCall (.symbol "if") Atom.undefinedType Completed.Frame.empty
      (.exhausted [badArg] false) := by
  obtain ⟨errors, chosen⟩ : ∃ errors, Completed.InvocationSelectionRel (Space.ofList ifProgram)
      Completed.rawLookup policy [] [] fiveCall (.symbol "if") Atom.undefinedType
      Completed.Frame.empty (.exhausted errors false) :=
    ⟨_, [ifPolicy.functionType], if_types,
      .rejected (.checked (operator := sym "if") (arguments := [.grounded (.int 5), sym "yes", sym "no"])
        rfl
        (.cons (.cons five_types (.cons (.rejected (bool_number_rejected _)) .nil) .nil)
          (.cons .nil (.cons .nil .nil)))
        .nil) .nil⟩
  have same := five_selection chosen
  simp only [Completed.InvocationSelection.exhausted.injEq, and_true] at same
  subst same
  exact chosen

/-- **A complete run of `(if 5 yes no)` on HE's machine, publishing the diagnostic.** -/
theorem five_run (dispatch : GroundedDispatch) (policy : Policy) :
    ∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList ifProgram) fiveCall Atom.undefinedType)
          ⟨Space.ofList ifProgram, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [badArg] := by
  have entry := call_entry policy if_data [.grounded (.int 5), sym "yes", sym "no"]
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom fiveCall) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [Atom.grounded (.int 5), sym "yes", sym "no"].map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [fiveCall, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have selection : Completed.ArgumentService.historical.selection (Space.ofList ifProgram)
      Completed.rawLookup policy [] []
      (Completed.Frame.empty.read policy (Entry.Value.ofAtom fiveCall)).erase
      (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType Completed.Frame.empty
      (.exhausted [badArg] false) := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
    exact five_selection_exists policy
  have step := LocalStepWith.atomSelectionFailed (admission := .historical)
    (space := Space.ofList ifProgram) (dispatch := dispatch) (lookup := Completed.rawLookup)
    (live := []) (scope := []) (stack := []) entry shape selection
  have readOne : (Completed.diagnosticResults [badArg] Completed.Frame.empty).map
      (Completed.readResult policy) =
      Completed.diagnosticResults [badArg] Completed.Frame.empty := by
    simp only [Completed.diagnosticResults, List.map_cons, List.map_nil]
    rw [HERuns.readResult_closed policy _ (by
      simpa [Entry.Value.erase_ofAtom] using badArg_closed)]
  have allErrors : SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
      ((Completed.diagnosticResults [badArg] Completed.Frame.empty).map (Completed.readResult policy))
      (Completed.diagnosticResults [badArg] Completed.Frame.empty) := by
    rw [readOne]
    exact .allErrors (fun item member => by
      simp only [Completed.diagnosticResults, List.map_cons, List.map_nil,
        List.mem_singleton] at member
      subst member
      simp [Entry.Value.erase_ofAtom, badArg_error])
  refine ⟨(Completed.diagnosticResults [badArg] Completed.Frame.empty).map
    (Completed.publishResult policy
      (Completed.Frame.empty.read policy (Entry.Value.ofAtom fiveCall)).erase), ?_, ?_⟩
  · refine .head (.internal step) ?_
    refine .head (.internal (.publish allErrors)) ?_
    exact HERuns.publish_all _ _ []
  · rw [publish_erase]
    simp [Completed.diagnosticResults, Entry.Value.erase_ofAtom]

/-- **PeTTa on `(if 5 yes no)`**: the else branch, `no`, from fuel `8` on. -/
theorem petta_five :
    ∀ k, 8 ≤ k → Streaming.values (Streaming.advance (translate ifProgram) k
      (Streaming.enter { state := store ifProgram } fiveCall)) = [sym "no"] := by
  have done : (Streaming.advance (translate ifProgram) 8
      (Streaming.enter { state := store ifProgram } fiveCall)).agenda.length = 0 := by
    decide +kernel
  have value : Streaming.values (Streaming.advance (translate ifProgram) 8
      (Streaming.enter { state := store ifProgram } fiveCall)) = [sym "no"] := by
    decide +kernel
  intro k bigger
  rw [advance_stable (List.eq_nil_of_length_eq_zero done) k bigger]
  exact value

/-- **The named difference, on every run.** On HE's standard-library `if` alone, for `(if 5 yes no)`:
a complete HE run exists and every complete run publishes `(Error (if 5 yes no) (BadArgType 1 Bool
Number))`, while PeTTa's run yields `no` from fuel `8` on. -/
theorem typed_condition_differs (policy : Policy) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList ifProgram) fiveCall Atom.undefinedType)
          ⟨Space.ofList ifProgram, .returning [], [], heAnswers⟩) ∧
      (∀ emitted : List Result,
        Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
            (load (Space.ofList ifProgram) fiveCall Atom.undefinedType)
            ⟨Space.ofList ifProgram, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = [badArg]) ∧
      ∀ k, 8 ≤ k → Streaming.values (Streaming.advance (translate ifProgram) k
        (Streaming.enter { state := store ifProgram } fiveCall)) = [sym "no"] := by
  obtain ⟨heAnswers, path, _⟩ := five_run noHost policy
  exact ⟨⟨heAnswers, path⟩, fun emitted run => five_source (complete_source run), petta_five⟩

#print axioms bool_number_no_match
#print axioms five_checks
#print axioms five_selection
#print axioms five_source
#print axioms five_run
#print axioms petta_five
#print axioms typed_condition_differs

end IfTypedCondition

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
