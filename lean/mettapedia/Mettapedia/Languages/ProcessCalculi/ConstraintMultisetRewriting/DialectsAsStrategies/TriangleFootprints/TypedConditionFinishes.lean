import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.DeclaredBranchGap

/-!
# A named difference on the scoped lookup, every run finishing: a declared non-`Bool` condition

`IfTypedCondition` proved, on the historical lookup, that every complete HE run of `(if 5 yes no)`
publishes `(Error (if 5 yes no) (BadArgType 1 Bool Number))` while PeTTa answers `no`. Here the same
named difference holds on the scoped lookup, and **every run finishes**:

* `five_checks_scoped`, `five_selection_scoped`: every admission against any fresh copy of `if`'s
  arrow is exhausted with exactly that diagnostic, without a tuple fallback;
* `five_source_scoped`: every derivation publishes the diagnostic;
* `five_fine`: from the entry, the admission's failure is the only step, its publication the next, and
  every run ends there (`fine_publish_any`: a publication step whose stack ends is always followed by
  a final configuration, errors included);
* `typed_condition_finishes`: a complete run exists, every complete run publishes the diagnostic,
  every run finishes, and PeTTa yields `no` from fuel `8` on (`IfTypedCondition.petta_five`).

## Controls

The positive control is the literal condition on the same lookup (`IfInBodies.Controls.pick_every_run`,
`ScopedIf.if_source_scoped`), where `Bool` accepts the condition's type; the negative control is the
rejection itself (`IfTypedCondition.bool_number_no_match`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace TypedConditionFinishes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom mkError)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Machines.OrderedProtocol.Completion (SuccessPriorityRel)
open HEOnTheStep (HEConfig)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings DeclaredHeads
  DeclaredEveryRun TypedEveryRun AtomDemands IfEveryRun IfBranches EveryRunFinishes IfFinishes
  ScopedTransfer ScopedIf
open IfTypedCondition (fiveCall badArg five_types bool_number_no_match bool_number_rejected
  badArg_error badArg_closed petta_five)
open AnswerBags.Controls (sym app)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-- **Every application check of `(if 5 yes no)` against a fresh copy of the arrow rejects it with the
one diagnostic.** -/
theorem five_checks_scoped {P : List String} {signature : SelectedTypePolicy} {frame : Frame}
    {frames : List Frame} {errors : List Atom} {u : String}
    (functionType : signature.functionType = ifArrowV u)
    (checks : Completed.ApplicationChecksRel (Space.ofList ifProgram)
      (Completed.scopedLookup P (Space.ofList ifProgram)) policy fiveCall Atom.undefinedType
      signature frame frames errors) :
    frames = [] ∧ errors = [badArg] := by
  have projections := if_projections_v functionType
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
              have same := scoped_closed_answer five_types rfl queried
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

/-- **Every scoped admission of `(if 5 yes no)` is exhausted with the one diagnostic, without a
tuple.** -/
theorem five_selection_scoped {live : List Atom} {scope : List String} {frame : Frame}
    {outcome : Completed.InvocationSelection}
    (chosenRel : Completed.InvocationSelectionRel (Space.ofList ifProgram) Completed.scopedLookup
      policy live scope fiveCall (.symbol "if") Atom.undefinedType frame outcome) :
    outcome = .exhausted [badArg] false := by
  obtain ⟨candidates, queried, scanned⟩ := chosenRel
  obtain ⟨u, same, _⟩ := scoped_if_answers if_program_full queried
  cases scanned with
  | nil => cases same
  | nonFunction notArrow _ =>
      simp only [List.cons.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact absurd ⟨_, _, (ifPolicyV u).isFunction⟩ notArrow
  | selected checks nonempty =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      exact absurd (five_checks_scoped functionType checks).1 nonempty
  | rejected checks rest =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      obtain ⟨_, rfl⟩ := five_checks_scoped functionType checks
      cases rest
      rfl
where
  /-- HE's `if` program carries HE's `if`. -/
  if_program_full : IfProgram ifProgram := ⟨if_types, if_program⟩

/-- The diagnostic is answered as it is by every publication. -/
theorem diagnostic_published (policy : Policy) {selected : List Result}
    (priority : SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
      ((Completed.diagnosticResults [badArg] Completed.Frame.empty).map
        (Completed.readResult policy)) selected) :
    selected.map (fun r => r.1.erase) = [badArg] := by
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
  rw [SuccessPriorityRel.functional priority allErrors]
  simp [Completed.diagnosticResults, Entry.Value.erase_ofAtom]

theorem five_entry (policy : Policy) :
    Entry.Rel policy.reentry
      (Completed.Frame.empty.read policy (Entry.Value.ofAtom fiveCall)).status
      (Completed.Frame.empty.read policy (Entry.Value.ofAtom fiveCall)).erase Atom.undefinedType
      .interpret :=
  call_entry policy if_data [.grounded (.int 5), sym "yes", sym "no"]

theorem five_shape (policy : Policy) :
    Completed.Frame.empty.read policy (Entry.Value.ofAtom fiveCall) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [Atom.grounded (.int 5), sym "yes", sym "no"].map Entry.Value.ofAtom) := by
  rw [Completed.Frame.read_empty]
  simp only [fiveCall, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]

/-- **Every derivation of HE's completed relation for `(if 5 yes no)` publishes the diagnostic**, on
the scoped lookup. -/
theorem five_source_scoped {results : List Result}
    (derived : Completed.AtomRel (Space.ofList ifProgram) dispatch Completed.scopedLookup [] []
      (Entry.Value.ofAtom fiveCall) Atom.undefinedType Completed.Frame.empty results
      (policy := policy)) :
    results.map (fun r => r.1.erase) = [badArg] := by
  have entry := five_entry policy
  have shape := five_shape policy
  have outcome : ∀ {result : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList ifProgram) Completed.scopedLookup policy [] []
        (Completed.Frame.empty.read policy (Entry.Value.ofAtom fiveCall)).erase
        (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType Completed.Frame.empty result →
      result = .exhausted [badArg] false := by
    intro result chosenRel
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosenRel
    exact five_selection_scoped chosenRel
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
      rw [publish_erase]
      exact diagnostic_published policy priority

/-- HE's scoped admission of `(if 5 yes no)` exists. -/
theorem five_selection_exists (policy : Policy) :
    Completed.InvocationSelectionRel (Space.ofList ifProgram) Completed.scopedLookup policy [] []
      fiveCall (.symbol "if") Atom.undefinedType Completed.Frame.empty
      (.exhausted [badArg] false) := by
  obtain ⟨errors, chosen⟩ : ∃ errors, Completed.InvocationSelectionRel (Space.ofList ifProgram)
      Completed.scopedLookup policy [] [] fiveCall (.symbol "if") Atom.undefinedType
      Completed.Frame.empty (.exhausted errors false) := by
    refine ⟨_, [ifPolicy.functionType], ⟨[ifArrow], if_types, .cons ⟨id, Function.injective_id,
        (rename_ifArrow id).symm, fun name member => ?_⟩ (.nil _)⟩,
      .rejected (signature := ifPolicy)
        (.checked (operator := sym "if") (arguments := [.grounded (.int 5), sym "yes", sym "no"])
        rfl
        (.cons (.cons (scoped_closed_answers five_types rfl)
          (.cons (.rejected (bool_number_rejected _)) .nil) .nil)
          (.cons .nil (.cons .nil .nil)))
        .nil) .nil⟩
    rw [ifArrow_vars, List.mem_singleton] at member
    subst member
    decide
  have same := five_selection_scoped chosen
  simp only [Completed.InvocationSelection.exhausted.injEq, and_true] at same
  subst same
  exact chosen

/-- **A publication step whose stack then ends leads to a final configuration**, whatever the
published rows (errors included). -/
theorem fine_publish_any {lookup : CastLookup} {space : Space} {raw : List Result} {original : Atom}
    (emitted : List Result)
    (exists_selected : ∃ selected, SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
      (raw.map (Completed.readResult policy)) selected) :
    Fine dispatch lookup policy ⟨space, .returning raw, [.publish original], emitted⟩ := by
  obtain ⟨selected, chosen⟩ := exists_selected
  refine .step ⟨_, .internal (.publish chosen)⟩ ?_
  intro y step
  cases step with
  | internal l =>
      cases l with
      | publish _ => exact fine_top _ _

/-- **Every run of `(if 5 yes no)` from the entry finishes**, on the scoped lookup. -/
theorem five_fine (dispatch : GroundedDispatch) (policy : Policy) :
    Fine dispatch Completed.scopedLookup policy
      (load (Space.ofList ifProgram) fiveCall Atom.undefinedType) := by
  have entry := five_entry policy
  have shape := five_shape policy
  have selection : Completed.ArgumentService.historical.selection (Space.ofList ifProgram)
      Completed.scopedLookup policy [] []
      (Completed.Frame.empty.read policy (Entry.Value.ofAtom fiveCall)).erase
      (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType Completed.Frame.empty
      (.exhausted [badArg] false) := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
    exact five_selection_exists policy
  have outcome : ∀ {result : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList ifProgram) Completed.scopedLookup policy [] []
        (Completed.Frame.empty.read policy (Entry.Value.ofAtom fiveCall)).erase
        (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType Completed.Frame.empty result →
      result = .exhausted [badArg] false := by
    intro result chosenRel
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosenRel
    exact five_selection_scoped chosenRel
  have allErrors : ∃ selected, SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
      ((Completed.diagnosticResults [badArg] Completed.Frame.empty).map
        (Completed.readResult policy)) selected := by
    refine ⟨_, .allErrors (fun item member => ?_)⟩
    simp only [Completed.diagnosticResults, List.map_cons, List.map_nil,
      List.mem_singleton] at member
    subst member
    rw [HERuns.readResult_closed policy _ (by
      simpa [Entry.Value.erase_ofAtom] using badArg_closed)]
    simp [Entry.Value.erase_ofAtom, badArg_error]
  refine .step ⟨_, .internal (LocalStepWith.atomSelectionFailed (admission := .historical)
    entry shape selection)⟩ ?_
  intro y moved
  cases moved with
  | internal l =>
      cases l with
      | delivered entered => cases Entry.functional entered entry
      | cast entered => cases Entry.functional entered entry
      | atomTuple _ shaped occurs =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [Entry.Value.erase_ofAtom] at occurs
          have same := Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel.unique occurs
            if_types.occurrences
          simp [Atom.undefinedType] at same
      | atomFunction _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          cases outcome chosen
      | atomFallback _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          cases outcome chosen
      | atomSelectionFailed _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          have exhausted := outcome chosen
          simp only [Completed.InvocationSelection.exhausted.injEq, and_true] at exhausted
          subst exhausted
          exact fine_publish_any _ allErrors

/-- **The named difference on the scoped lookup, every run finishing.** On HE's standard-library
`if` alone, for `(if 5 yes no)`: a complete HE run exists and every complete run publishes
`(Error (if 5 yes no) (BadArgType 1 Bool Number))`; no run is infinite and every reachable
configuration steps or is final with it; PeTTa's run yields `no` from fuel `8` on. -/
theorem typed_condition_finishes (dispatch : GroundedDispatch) (policy : Policy) :
    Publishes dispatch Completed.scopedLookup policy (Space.ofList ifProgram) fiveCall [badArg] ∧
      Finishes dispatch Completed.scopedLookup policy (Space.ofList ifProgram) fiveCall [badArg] ∧
      ∀ k, 8 ≤ k → Streaming.values (Streaming.advance (translate ifProgram) k
        (Streaming.enter { state := store ifProgram } fiveCall)) = [sym "no"] := by
  have fine := five_fine dispatch policy
  have every : ∀ emitted : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.scopedLookup policy)
        (load (Space.ofList ifProgram) fiveCall Atom.undefinedType)
        (final (Space.ofList ifProgram) emitted) →
      emitted.map (fun r => r.1.erase) = [badArg] :=
    fun emitted run => five_source_scoped (complete_source run)
  refine ⟨⟨?_, every⟩, ⟨fine.acc, fun y path => ?_⟩, petta_five⟩
  · obtain ⟨space, emitted, path⟩ := IfAtFrames.Fine.exists_final fine
    have same : space = Space.ofList ifProgram := space_fixed path
    subst same
    exact ⟨emitted, path⟩
  · rcases (fine.reaches path).progress with moves | ⟨space, emitted, rfl⟩
    · exact Or.inl moves
    · have same : space = Space.ofList ifProgram := space_fixed path
      subst same
      exact Or.inr ⟨emitted, rfl, every emitted path⟩

#print axioms five_checks_scoped
#print axioms five_selection_scoped
#print axioms five_source_scoped
#print axioms five_selection_exists
#print axioms fine_publish_any
#print axioms five_fine
#print axioms typed_condition_finishes

end TypedConditionFinishes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
