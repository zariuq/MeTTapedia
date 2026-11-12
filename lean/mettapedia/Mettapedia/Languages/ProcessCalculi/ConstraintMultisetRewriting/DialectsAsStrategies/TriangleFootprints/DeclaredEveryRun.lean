import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.DeclaredHeads
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.EveryRun

/-!
# The declaration guard changes the answer on every run

`DeclaredHeads.declared_guard_differs` gives one complete run of HE's machine on
`{(: f (-> Number Number)), (: b Bool), (= (f $x) yes)}` that publishes the type error
`(Error (f b) (BadArgType 1 Number Bool))`, where PeTTa answers `yes`. Here every complete run is
covered, by the route of `EveryRun` (a complete run is a derivation of HE's completed relation):

* `no_success`: no applicability path of `(f b)` through `(-> Number Number)` exists, since the
  only type of `b` is `Bool` and `Number` does not match it;
* `argument_check`, `argument_checks`, `rejected_errors`: every argument check of `(f b)` against
  the arrow keeps no activation and reports exactly the one `BadArgType` error;
* `scan_outcome`: every scan of `f`'s declared types ends exhausted, with that error and without
  tuple fallback;
* `declared_source`: every derivation of HE's completed relation for `(f b)` publishes the error;
* `declared_every_run`: **every** complete run of HE publishes the error, and PeTTa answers `yes`.

## Controls

* `Controls.plain_every_run` (positive, without the declarations): every complete run of HE on
  `{(= (f $x) yes)}` publishes `yes`, as PeTTa does.
* `Controls.argument_declaration_agrees` (the guard is the head's): with `(: b Bool)` but no
  declaration of `f`, every complete run of HE publishes `yes`, as PeTTa does.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace DeclaredEveryRun

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom mkError)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel rawTypeLookupRel
  FunctionTypeRel ApplicationSuccessRel)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (load observe)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun DeclaredHeads
open AnswerBags.Controls (sym app rule rule_consFree)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-- `(-> Number Number)`. -/
abbrev arrowType : Atom := .expression [.symbol "->", sym "Number", sym "Number"]

theorem arrow_projections {argumentTypes : List Atom} {returnType : Atom}
    (projected : FunctionTypeRel arrowType argumentTypes returnType) :
    argumentTypes = [sym "Number"] ∧ returnType = sym "Number" :=
  Mettapedia.Languages.MeTTa.HE.Spec.Type.FunctionTypeRel.unique projected
    (show FunctionTypeRel arrowType [sym "Number"] (sym "Number") from rfl)

/-- **No applicability path of `(f b)` through `(-> Number Number)`**: `b`'s only type is `Bool`. -/
theorem no_success {expected : Atom} {bindings output : Bindings} :
    ¬ ApplicationSuccessRel (Space.ofList declaredRows)
      (lookup := rawTypeLookupRel (Space.ofList declaredRows)) declaredCall arrowType expected
      bindings output := by
  intro success
  cases success with
  | mk shaped projected applicable _ =>
      simp only [declaredCall, app, Atom.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl⟩ := shaped
      obtain ⟨rfl, _⟩ := arrow_projections projected
      cases applicable with
      | cons typed matched _ =>
          obtain ⟨candidates, queried, member⟩ := typed
          have same := StorageTypesRel.unique
            (show StorageTypesRel (Space.ofList declaredRows) (sym "b") candidates from queried)
            b_types
          subst same
          rw [List.mem_singleton] at member
          subst member
          exact number_bool_mismatch matched

/-- **The argument check of `b` against `Number`** keeps no activation and reports one error. -/
theorem argument_check {before : Frame} {next : List Frame} {errors : List Atom}
    (checked : Completed.ArgumentChecksRel (Space.ofList declaredRows)
      (rawTypeLookupRel (Space.ofList declaredRows)) policy declaredCall (sym "b") (sym "Number") 1
      [before] next errors) :
    next = [] ∧ errors = [badArgument] := by
  cases checked with
  | cons queried paired rest =>
      cases rest
      have same := StorageTypesRel.unique
        (show StorageTypesRel (Space.ofList declaredRows) (sym "b") _ from queried) b_types
      subst same
      obtain ⟨check, checks, checkedOne, restPaired, rfl⟩ := List.forall₂_cons_left_iff.mp paired
      obtain rfl := List.forall₂_nil_left_iff.mp restPaired
      cases checkedOne with
      | accepted renewed =>
          exfalso
          cases renewed with
          | unchanged matched => exact number_rejects_bool policy _ _ matched
          | unified matched _ => exact number_rejects_bool policy _ _ matched
      | rejected _ =>
          simp [Completed.checkedFrames, Completed.checkedFailures]

theorem argument_checks {before : Frame} {after : List Frame} {errors : List Atom}
    (checked : Completed.ApplicabilityArgumentsRel (Space.ofList declaredRows)
      (rawTypeLookupRel (Space.ofList declaredRows)) policy declaredCall 1 [sym "b"]
      [sym "Number"] [before] after errors) :
    after = [] ∧ errors = [badArgument] := by
  cases checked with
  | cons head rest =>
      cases rest
      obtain ⟨rfl, rfl⟩ := argument_check head
      exact ⟨rfl, rfl⟩

/-- **A rejected arrow reports exactly the one `BadArgType` error.** -/
theorem rejected_errors {signature : SelectedTypePolicy} {before : Frame} {frames : List Frame}
    {errors : List Atom} (functionType : signature.functionType = arrowType) (noFrames : frames = [])
    (checks : Completed.ApplicationChecksRel (Space.ofList declaredRows)
      (rawTypeLookupRel (Space.ofList declaredRows)) policy declaredCall Atom.undefinedType
      signature before frames errors) :
    errors = [badArgument] := by
  have projections := arrow_projections (functionType ▸ signature.isFunction)
  cases checks with
  | wrongArity shaped arity =>
      simp only [declaredCall, app, Atom.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl⟩ := shaped
      rw [projections.1] at arity
      exact absurd rfl arity
  | checked shaped arguments returned =>
      simp only [declaredCall, app, Atom.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl⟩ := shaped
      rw [projections.1] at arguments
      obtain ⟨rfl, rfl⟩ := argument_checks arguments
      cases returned
      simp [Completed.checkedFailures]

/-- **Every scan of `f`'s declared types ends exhausted**, with the one error and no tuple
fallback. -/
theorem scan_outcome {before : Frame} {candidates : List Atom}
    {outcome : Completed.InvocationSelection} (same : candidates = [arrowType])
    (scanned : Completed.InvocationScanRel (Space.ofList declaredRows)
      (rawTypeLookupRel (Space.ofList declaredRows)) policy declaredCall Atom.undefinedType before
      candidates outcome) :
    outcome = .exhausted [badArgument] false := by
  cases scanned with
  | nil => cases same
  | nonFunction notArrow _ =>
      simp only [List.cons.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact absurd ⟨[sym "Number"], sym "Number", rfl⟩ notArrow
  | selected checks nonempty =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      obtain ⟨after, member⟩ := List.exists_mem_of_ne_nil _ nonempty
      have success := checks.source_member member
      rw [functionType] at success
      exact absurd success no_success
  | rejected checks rest =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      cases rest
      rw [rejected_errors functionType rfl checks]
      rfl

/-- **Every derivation of HE's completed relation for `(f b)` publishes the type error.** -/
theorem declared_source {results : List Result}
    (derived : Completed.AtomRel (Space.ofList declaredRows) dispatch Completed.rawLookup [] []
      (Entry.Value.ofAtom declaredCall) Atom.undefinedType Completed.Frame.empty results
      (policy := policy)) :
    results.map (fun r => r.1.erase) = [badArgument] := by
  have headData : DataAtom (.symbol "f") := .symbol (by decide) (by decide)
  have entry := call_entry policy headData [sym "b"]
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom declaredCall) =
      .expression .active (Entry.Value.ofAtom (.symbol "f") :: [sym "b"].map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [declaredCall, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have outcome : ∀ {result : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList declaredRows) Completed.rawLookup policy [] []
        (Completed.Frame.empty.read policy (Entry.Value.ofAtom declaredCall)).erase
        (Entry.Value.ofAtom (.symbol "f")).erase Atom.undefinedType Completed.Frame.empty result →
      result = .exhausted [badArgument] false := by
    intro result chosen
    obtain ⟨candidates, queried, scanned⟩ := chosen
    rw [Entry.Value.erase_ofAtom] at queried
    have same := StorageTypesRel.unique
      (show StorageTypesRel (Space.ofList declaredRows) (.symbol "f") candidates from queried)
      f_types
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom] at scanned
    exact scan_outcome same scanned
  cases derived with
  | delivered entered => cases Entry.functional entered entry
  | cast entered => cases Entry.functional entered entry
  | tuple _ shaped occurs _ _ _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      rw [Entry.Value.erase_ofAtom] at occurs
      have same := Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel.unique occurs
        f_types.occurrences
      simp [Atom.undefinedType] at same
  | function _ shaped chosen _ _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      cases outcome chosen
  | fallback _ shaped chosen _ _ _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      cases outcome chosen
  | selectionFailed _ shaped chosen selected =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      have exhausted := outcome chosen
      simp only [Completed.InvocationSelection.exhausted.injEq] at exhausted
      obtain ⟨rfl, _⟩ := exhausted
      have unread : (Completed.diagnosticResults [badArgument] Completed.Frame.empty).map
          (Completed.readResult policy) =
          Completed.diagnosticResults [badArgument] Completed.Frame.empty := by
        simp [Completed.diagnosticResults, Completed.readResult]
      rw [unread] at selected
      have same := Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.functional
        selected (.allErrors fun item member => by
          simp only [Completed.diagnosticResults, List.map_cons, List.map_nil,
            List.mem_singleton] at member
          subst member
          simp [badArgument, Mettapedia.Languages.MeTTa.HE.mkError, Atom.error, isErrorAtom])
      subst same
      simp [Completed.diagnosticResults, Completed.publishResult]

/-- **The declaration guard changes the answer on every run.** On
`{(: f (-> Number Number)), (: b Bool), (= (f $x) yes)}`, with HE's historical lookup, any policy and
any dispatch: every complete run of HE from the entry configuration of `(f b)` publishes exactly
`(Error (f b) (BadArgType 1 Number Bool))`, an error, while PeTTa's run yields `yes` from fuel `40`
on. -/
theorem declared_every_run (dispatch : GroundedDispatch) (policy : Policy) :
    (∀ emitted : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList declaredRows) declaredCall Atom.undefinedType)
          ⟨Space.ofList declaredRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [badArgument]) ∧
      isErrorAtom badArgument = true ∧
      ∀ n, 40 ≤ n → Streaming.values (Streaming.advance (translate declaredRows) n
        (Streaming.enter { state := store declaredRows } declaredCall)) = [sym "yes"] :=
  ⟨fun _ run => declared_source (complete_source run), (declared_guard_differs dispatch policy).2⟩

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)
open DeclaredHeads.Controls (plainRows)

/-- **Positive control: without the declarations, every complete run of HE publishes `yes`**, as
PeTTa does. -/
theorem plain_every_run (policy : Policy) (emitted : List Result)
    (run : Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
      (load (Space.ofList plainRows) declaredCall Atom.undefinedType)
      ⟨Space.ofList plainRows, .returning [], [], emitted⟩) :
    emitted.map (fun r => r.1.erase) = [sym "yes"] := by
  have program : ∀ row ∈ plainRows, RegionsWithVariables.ConsFreeHeads row := by
    intro row member
    simp only [List.mem_singleton] at member
    subst member
    exact rule_consFree fun a member => by
      simp only [List.mem_singleton] at member
      subst member
      exact .var _
  have ordinary : Ordinary noHost plainRows "f" [sym "b"] :=
    ⟨.symbol (by decide) (by decide), fun a member => by
      simp only [List.mem_singleton] at member
      subst member
      exact .symbol (by decide) (by decide), by decide +kernel, fun impossible => impossible,
      by decide +kernel, by decide, by decide, by decide +kernel, by decide, by decide⟩
  have bodies : regionBodies plainRows "f" [sym "b"] = [sym "yes"] := by decide +kernel
  have settles : Settles noHost plainRows declaredCall := by
    refine .call ordinary (by rw [bodies]; simp) ?_
    rw [bodies]
    intro b member
    rw [List.mem_singleton] at member
    subst member
    exact .data (.symbol (by decide) (by decide)) (by decide)
  have computed : Streaming.values (Streaming.advance (translate plainRows) 40
      (Streaming.enter { state := store plainRows } declaredCall)) = [sym "yes"] := by
    decide +kernel
  have finished : (Streaming.advance (translate plainRows) 40
      (Streaming.enter { state := store plainRows } declaredCall)).agenda.length = 0 := by
    decide +kernel
  obtain ⟨N, every⟩ := every_complete_run noHost policy program settles
  rw [← every (max N 40) (le_max_left _ _) emitted run,
    advance_stable (List.eq_nil_of_length_eq_zero finished) (max N 40) (le_max_right _ _),
    computed]

/-- `{(: b Bool), (= (f $x) yes)}`: the argument is declared, the head is not. -/
abbrev argumentRows : List Atom :=
  [.expression [.symbol ":", sym "b", sym "Bool"], rule (app "f" [.var "x"]) (sym "yes")]

/-- **Control: a declaration of the argument alone does not change the answer.** With `(: b Bool)`
but no declaration of `f`, every complete run of HE on `(f b)` publishes `yes`, as PeTTa does: HE
casts `b` under `%Undefined%` demand, which accepts every type. It is the declaration of the head
that changes the answer (`declared_every_run`). -/
theorem argument_declaration_agrees (policy : Policy) (emitted : List Result)
    (run : Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
      (load (Space.ofList argumentRows) declaredCall Atom.undefinedType)
      ⟨Space.ofList argumentRows, .returning [], [], emitted⟩) :
    emitted.map (fun r => r.1.erase) = [sym "yes"] ∧
      Streaming.values (Streaming.advance (translate argumentRows) 40
        (Streaming.enter { state := store argumentRows } declaredCall)) = [sym "yes"] := by
  have program : ∀ row ∈ argumentRows, RegionsWithVariables.ConsFreeHeads row := by
    intro row member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · intro lhs rhs same
      simp at same
    · exact rule_consFree fun a member => by
        simp only [List.mem_singleton] at member
        subst member
        exact .var _
  have ordinary : Ordinary noHost argumentRows "f" [sym "b"] :=
    ⟨.symbol (by decide) (by decide), fun a member => by
      simp only [List.mem_singleton] at member
      subst member
      exact .symbol (by decide) (by decide), by decide +kernel, fun impossible => impossible,
      by decide +kernel, by decide, by decide, by decide +kernel, by decide, by decide⟩
  have bodies : regionBodies argumentRows "f" [sym "b"] = [sym "yes"] := by decide +kernel
  have settles : Settles noHost argumentRows declaredCall := by
    refine .call ordinary (by rw [bodies]; simp) ?_
    rw [bodies]
    intro b member
    rw [List.mem_singleton] at member
    subst member
    exact .data (.symbol (by decide) (by decide)) (by decide)
  have computed : Streaming.values (Streaming.advance (translate argumentRows) 40
      (Streaming.enter { state := store argumentRows } declaredCall)) = [sym "yes"] := by
    decide +kernel
  have finished : (Streaming.advance (translate argumentRows) 40
      (Streaming.enter { state := store argumentRows } declaredCall)).agenda.length = 0 := by
    decide +kernel
  obtain ⟨N, every⟩ := every_complete_run noHost policy program settles
  refine ⟨?_, computed⟩
  rw [← every (max N 40) (le_max_left _ _) emitted run,
    advance_stable (List.eq_nil_of_length_eq_zero finished) (max N 40) (le_max_right _ _),
    computed]

end Controls

#print axioms no_success
#print axioms argument_check
#print axioms argument_checks
#print axioms rejected_errors
#print axioms scan_outcome
#print axioms declared_source
#print axioms declared_every_run
#print axioms Controls.plain_every_run
#print axioms Controls.argument_declaration_agrees

end DeclaredEveryRun

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
