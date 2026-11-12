import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.NestedArguments

/-!
# Declared heads: HE's declaration guards change the answer, PeTTa's do not

`AnswerBags` left heads with a type declaration out: with `(: f T)` in the space HE does not take
the tuple entry (`EntryToQuery.Controls.declared_head_blocks_tuple`), it takes the argument
admission of `f`'s declared types (`atomFunction`, `atomFallback` or `atomSelectionFailed`). PeTTa
reads declarations only to decide raw (`Atom`-typed) arguments; it never checks a declared type.

Here the admission is followed on a program where the guard decides the answer:

    (: f (-> Number Number))   (: b Bool)   (= (f $x) yes)        query (f b)

* HE: the only candidate type of `f` is `(-> Number Number)`; the argument `b` has the declared
  type `Bool`, which does not match `Number` under any type-matching policy
  (`number_rejects_bool`), so the candidate is rejected with the error
  `(Error (f b) (BadArgType 1 Number Bool))`, no candidate remains and no tuple fallback is eligible
  (`atomSelectionFailed`). HE's complete run publishes that error (`he_declared_error`).
* PeTTa: the call selects `(= (f $x) yes)` and answers `yes` (`petta_declared_yes`).

The difference is the declaration guard (`declared_guard_differs`): without the two declarations
both dialects answer `yes` (`Controls.undeclared_agrees`, an instance of
`AnswerBags.answers_agree`).

When the guard passes, HE's `atomFunction` path is followed to its answer on the same program:
for `(f 4)` the admission selects the arrow (`selection_succeeds`, `well_typed_takes_function`), the
operator is cast against its arrow and `4` against `Number`, the call value `(f 4)` is assembled
(`function_segment`), the equation query runs with the return type `Number` as demand and the body
`yes` meets it (`typed_query`), and HE publishes `yes` (`he_typed_yes`), as PeTTa does
(`typed_agrees`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace DeclaredHeads

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom mkError)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel AnnotationTypesRel
  rawTypeLookupRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (MatchRel equalityGroundedSemantic)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load observe)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags
open AnswerBags.Controls (sym app rule rule_consFree)

/-! ## `Number` does not accept `Bool` -/

theorem symbols_do_not_match {a b : String} {out : Bindings} (different : a ≠ b) :
    ¬ MatchRel equalityGroundedSemantic (.symbol a) (.symbol b) out := by
  intro matched
  generalize sameLeft : Atom.symbol a = left at matched
  generalize sameRight : Atom.symbol b = right at matched
  cases matched <;> simp_all

theorem number_bool_mismatch {bindings output : Bindings} :
    ¬ TypeMatchRel (sym "Number") (sym "Bool") bindings output := by
  intro matched
  generalize sameLeft : sym "Number" = left at matched
  generalize sameRight : sym "Bool" = right at matched
  cases matched with
  | undefinedLeft => simp [Atom.undefinedType] at sameLeft
  | atomLeft => simp [Atom.atomType] at sameLeft
  | undefinedRight => simp [Atom.undefinedType] at sameRight
  | atomRight => simp [Atom.atomType] at sameRight
  | structural _ _ _ _ matchedAtoms _ =>
      subst sameLeft
      subst sameRight
      exact symbols_do_not_match (by decide) matchedAtoms

/-- **The declaration guard rejects**: under either type-matching policy, demand `Number` accepts no
`Bool`. -/
theorem number_rejects_bool (policy : Policy) (bindings : Bindings) :
    ∀ output, ¬ policy.matching.Rel (sym "Number") (sym "Bool") bindings output := by
  intro output matched
  have core : TypeMatchRel (sym "Number") (sym "Bool") bindings output := by
    cases same : policy.matching with
    | raw =>
        rw [same] at matched
        exact matched
    | finite =>
        rw [same] at matched
        exact matched.1
  exact number_bool_mismatch core

/-! ## The program -/

/-- `{(: f (-> Number Number)), (: b Bool), (= (f $x) yes)}`. -/
abbrev declaredRows : List Atom :=
  [.expression [.symbol ":", sym "f", .expression [.symbol "->", sym "Number", sym "Number"]],
   .expression [.symbol ":", sym "b", sym "Bool"],
   rule (app "f" [.var "x"]) (sym "yes")]

/-- `(f b)`. -/
abbrev declaredCall : Atom := app "f" [sym "b"]

/-- The type error HE reports. -/
abbrev badArgument : Atom := mkError declaredCall (.badArgType 1 (sym "Number") (sym "Bool"))

theorem f_types : StorageTypesRel (Space.ofList declaredRows) (.symbol "f")
    [.expression [.symbol "->", sym "Number", sym "Number"]] :=
  .symbolKnown (.hit (.skip (fun _ same => by simp at same)
    (.skip (fun _ same => by simp at same) .nil))) (by simp)

theorem b_types : StorageTypesRel (Space.ofList declaredRows) (.symbol "b") [sym "Bool"] :=
  .symbolKnown (.skip (fun _ same => by simp at same)
    (.hit (.skip (fun _ same => by simp at same) .nil))) (by simp)

/-- `f`'s one candidate, `(-> Number Number)`. -/
def arrow : SelectedTypePolicy :=
  ⟨.expression [.symbol "->", sym "Number", sym "Number"], [sym "Number"], sym "Number", rfl⟩

/-- **The candidate is rejected**: its one argument check fails with `BadArgType`, so no activation
survives. -/
theorem arrow_rejected (policy : Policy) :
    Completed.ApplicationChecksRel (Space.ofList declaredRows)
      (rawTypeLookupRel (Space.ofList declaredRows))
      policy declaredCall Atom.undefinedType arrow Completed.Frame.empty []
      ((([badArgument] ++ []) ++ []) ++ []) :=
  .checked (operator := sym "f") (arguments := [sym "b"]) rfl
    (.cons (.cons b_types
      (.cons (.rejected (number_rejects_bool policy Completed.Frame.empty.bindings)) .nil) .nil) .nil)
    .nil

/-- **HE's admission of `(f b)` fails**: the scan of `f`'s declared types ends with the error and
no tuple fallback. -/
theorem selection_failed (policy : Policy) :
    Completed.InvocationSelectionRel (Space.ofList declaredRows) Completed.rawLookup policy [] []
      declaredCall (.symbol "f") Atom.undefinedType Completed.Frame.empty
      (.exhausted (((([badArgument] ++ []) ++ []) ++ []) ++ []) false) :=
  ⟨[arrow.functionType], f_types, .rejected (arrow_rejected policy) .nil⟩

/-- **HE's complete run of `(f b)` publishes the type error.** With HE's raw lookup, any policy and
any dispatch: the entry interprets the call, the admission of `f`'s declared types fails, and the
error is the one published answer. -/
theorem he_declared_error (dispatch : GroundedDispatch) (policy : Policy) :
    ∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList declaredRows) declaredCall Atom.undefinedType)
          ⟨Space.ofList declaredRows, .returning [], [], heAnswers⟩ ∧
        observe ⟨Space.ofList declaredRows, .returning [], [], heAnswers⟩ = some heAnswers ∧
        heAnswers.map (fun r => r.1.erase) = [badArgument] := by
  have headData : DataAtom (.symbol "f") := .symbol (by decide) (by decide)
  have entry := call_entry policy headData [sym "b"]
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom declaredCall) =
      .expression .active (Entry.Value.ofAtom (.symbol "f") :: [sym "b"].map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [declaredCall, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have selection : Completed.ArgumentService.historical.selection (Space.ofList declaredRows)
      Completed.rawLookup policy [] []
      (Completed.Frame.empty.read policy (Entry.Value.ofAtom declaredCall)).erase
      (Entry.Value.ofAtom (.symbol "f")).erase Atom.undefinedType Completed.Frame.empty
      (.exhausted (((([badArgument] ++ []) ++ []) ++ []) ++ []) false) := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
    exact selection_failed policy
  have step := LocalStepWith.atomSelectionFailed (admission := .historical)
    (space := Space.ofList declaredRows) (dispatch := dispatch) (lookup := Completed.rawLookup)
    (live := []) (scope := []) (stack := []) entry shape selection
  have published : (Completed.Frame.empty.read policy (Entry.Value.ofAtom declaredCall)).erase =
      declaredCall := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom]
  rw [published] at step
  set raw := Completed.diagnosticResults (((([badArgument] ++ []) ++ []) ++ []) ++ [])
    Completed.Frame.empty with rawEq
  have unread : raw.map (Completed.readResult policy) = raw := by
    rw [rawEq]
    simp [Completed.diagnosticResults, Completed.readResult]
  have allErrors : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase) (raw.map (Completed.readResult policy))
      raw := by
    rw [unread]
    exact .allErrors fun item member => by
      rw [rawEq] at member
      simp only [Completed.diagnosticResults, List.append_nil, List.map_cons, List.map_nil,
        List.mem_singleton] at member
      subst member
      simp [badArgument, Mettapedia.Languages.MeTTa.HE.mkError, Atom.error, isErrorAtom]
  refine ⟨raw.map (Completed.publishResult policy declaredCall), ?_, rfl, ?_⟩
  · refine .head (.internal step) ?_
    refine .head (.internal (.publish allErrors)) ?_
    exact HERuns.publish_all _ _ []
  · rw [rawEq]
    simp [Completed.diagnosticResults, Completed.publishResult]

/-- **PeTTa answers `yes`**: the call selects `(= (f $x) yes)`; PeTTa checks no declared type. -/
theorem petta_declared_yes :
    Streaming.values (Streaming.advance (translate declaredRows) 40
      (Streaming.enter { state := store declaredRows } declaredCall)) = [sym "yes"] ∧
    (Streaming.advance (translate declaredRows) 40
      (Streaming.enter { state := store declaredRows } declaredCall)).agenda.length = 0 := by
  constructor <;> decide +kernel

/-- **The declaration guard changes the answer.** On `{(: f (-> Number Number)), (: b Bool),
(= (f $x) yes)}` the query `(f b)` gets HE's answer `(Error (f b) (BadArgType 1 Number Bool))`, an
error, and PeTTa's answer `yes`, from every fuel on at which PeTTa's run has finished. -/
theorem declared_guard_differs (dispatch : GroundedDispatch) (policy : Policy) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList declaredRows) declaredCall Atom.undefinedType)
          ⟨Space.ofList declaredRows, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [badArgument]) ∧
      isErrorAtom badArgument = true ∧
      ∀ n, 40 ≤ n → Streaming.values (Streaming.advance (translate declaredRows) n
        (Streaming.enter { state := store declaredRows } declaredCall)) = [sym "yes"] := by
  obtain ⟨R, path, _, erased⟩ := he_declared_error dispatch policy
  refine ⟨⟨R, path, erased⟩,
    by simp [badArgument, Mettapedia.Languages.MeTTa.HE.mkError, Atom.error, isErrorAtom], ?_⟩
  intro n bigger
  rw [advance_stable (List.eq_nil_of_length_eq_zero petta_declared_yes.2) n bigger]
  exact petta_declared_yes.1

/-! ## A well-typed argument: HE takes the `atomFunction` path -/

/-- `(f 4)`: an argument of the declared type. -/
abbrev typedCall : Atom := app "f" [.grounded (.int 4)]

theorem four_types : StorageTypesRel (Space.ofList declaredRows) (.grounded (.int 4)) [sym "Number"] :=
  .groundedKnown (.int 4) (by simp [Atom.undefinedType])

/-- `Number` accepts `Number`, with the bindings unchanged. -/
theorem number_matches (bindings : Bindings) :
    TypeMatchRel (sym "Number") (sym "Number") bindings bindings :=
  .structural (by simp [Atom.undefinedType]) (by simp [Atom.atomType]) (by simp [Atom.undefinedType])
    (by simp [Atom.atomType]) (.symSym "Number" Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.semanticLoopFree_empty)
    (Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.MergeRel.mk (order := [])
      (by simp [Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.constraints, Bindings.empty]) .nil)

/-- **The candidate is selected**: the argument check and the return check both pass, keeping the
activation. -/
theorem arrow_selected (policy : Policy) :
    Completed.ApplicationChecksRel (Space.ofList declaredRows)
      (rawTypeLookupRel (Space.ofList declaredRows))
      policy typedCall Atom.undefinedType arrow Completed.Frame.empty
      (Completed.checkedFrames [.inr Completed.Frame.empty])
      ((([] ++ []) ++ []) ++ (Completed.checkedFailures [.inr Completed.Frame.empty]).map
        fun actual => mkError typedCall (.badType Atom.undefinedType actual)) :=
  .checked (operator := sym "f") (arguments := [.grounded (.int 4)]) rfl
    (.cons (.cons four_types
      (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy _
        (number_matches _)))) .nil) .nil) .nil)
    (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy _
      (.undefinedLeft _ _)))) .nil)

/-- **HE's admission of `(f 4)` selects `f`'s arrow**, with one activation. -/
theorem selection_succeeds (policy : Policy) :
    Completed.InvocationSelectionRel (Space.ofList declaredRows) Completed.rawLookup policy [] []
      typedCall (.symbol "f") Atom.undefinedType Completed.Frame.empty
      (.selected arrow [Completed.Frame.empty]) :=
  ⟨[arrow.functionType], f_types, .selected (arrow_selected policy) (List.cons_ne_nil _ _)⟩

/-- **The first step of HE's run of `(f 4)` is `atomFunction`**: the declared arrow is selected and
HE goes on to its invocations, under the publication continuation; the tuple entry of undeclared
heads is not available (`EntryToQuery.Controls.declared_head_blocks_tuple`). -/
theorem well_typed_takes_function (dispatch : GroundedDispatch) (policy : Policy) :
    HEStep dispatch Completed.rawLookup policy
      (load (Space.ofList declaredRows) typedCall Atom.undefinedType)
      ⟨Space.ofList declaredRows,
        .work (.invocations [] [] Atom.undefinedType arrow (Entry.Value.ofAtom (.symbol "f"))
          [Entry.Value.ofAtom (.grounded (.int 4))] [Completed.Frame.empty]),
        [.publish typedCall], []⟩ ∧
      ¬ Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel
        ((Space.ofList declaredRows).atoms : Multiset Atom) (.symbol "f") {Atom.undefinedType} := by
  have headData : DataAtom (.symbol "f") := .symbol (by decide) (by decide)
  have entry := call_entry policy headData [.grounded (.int 4)]
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom typedCall) =
      .expression .active (Entry.Value.ofAtom (.symbol "f") ::
        [Atom.grounded (.int 4)].map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [typedCall, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have selection : Completed.ArgumentService.historical.selection (Space.ofList declaredRows)
      Completed.rawLookup policy [] []
      (Completed.Frame.empty.read policy (Entry.Value.ofAtom typedCall)).erase
      (Entry.Value.ofAtom (.symbol "f")).erase Atom.undefinedType Completed.Frame.empty
      (.selected arrow [Completed.Frame.empty]) := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
    exact selection_succeeds policy
  have step := LocalStepWith.atomFunction (admission := .historical)
    (space := Space.ofList declaredRows) (dispatch := dispatch) (lookup := Completed.rawLookup)
    (live := []) (scope := []) (stack := []) entry shape selection
  have published : (Completed.Frame.empty.read policy (Entry.Value.ofAtom typedCall)).erase =
      typedCall := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom]
  rw [published] at step
  refine ⟨.internal step, fun collected => ?_⟩
  have actual := Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel.symbol
    (atoms := ((Space.ofList declaredRows).atoms : Multiset Atom)) "f"
  have same := collected.unique actual
  have found : declaredRows.filterMap (Mettapedia.Languages.MeTTa.HE.Spec.Type.annotationType?
      (.symbol "f")) = [.expression [.symbol "->", sym "Number", sym "Number"]] := by
    decide +kernel
  have occurrences : Mettapedia.Languages.MeTTa.HE.Spec.Type.annotationOccurrences
      ((Space.ofList declaredRows).atoms : Multiset Atom) (.symbol "f") =
      {.expression [.symbol "->", sym "Number", sym "Number"]} := by
    unfold Mettapedia.Languages.MeTTa.HE.Spec.Type.annotationOccurrences
    rw [show (Space.ofList declaredRows).atoms = declaredRows from rfl, Multiset.filterMap_coe, found]
    exact Multiset.coe_singleton _
  rw [occurrences] at same
  simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.withUndefined, Atom.undefinedType] at same

/-! ## The well-typed run of `(f 4)` to its answer -/

theorem ofAtom_status (a : Atom) : (Entry.Value.ofAtom a).status = .active := by
  cases a <;> simp [Entry.Value.ofAtom, Entry.Value.status]

/-- **A cast under a typed demand**: the first stored type of the atom is accepted, so the cast
returns the atom with its activation. -/
theorem typed_cast (dispatch : GroundedDispatch) (policy : Policy) {space : Space}
    {atom expected actual : Atom} {rest : List Atom}
    (closed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs atom name)
    (entry : Entry.Rel policy.reentry .active atom expected .cast)
    (queried : StorageTypesRel space atom (actual :: rest)) (frame : Frame)
    (matched : TypeMatchRel expected actual frame.bindings frame.bindings) (live : List Atom)
    (scope : List String) (stack : List Continuation) (emitted : List Result) :
    HEStep dispatch Completed.rawLookup policy
      ⟨space, .work (.atom live scope (Entry.Value.ofAtom atom) expected frame), stack, emitted⟩
      ⟨space, .returning [(Entry.Value.ofAtom atom, frame)], stack, emitted⟩ := by
  have readAtom := HERuns.read_closed policy frame closed
  refine .internal (LocalStepWith.cast (raw := [(atom, frame.bindings)]) ?_ ?_ ?_)
  · rw [readAtom, Entry.Value.erase_ofAtom, ofAtom_status]
    exact entry
  · rw [readAtom, Entry.Value.erase_ofAtom]
    exact Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeCastBatchRel.success (earlierTypes := [])
      queried rfl (fun _ member => by simp at member)
      (Completed.Frame.preserved_type_match policy frame matched)
  · rw [readAtom, Entry.Value.erase_ofAtom]
    exact .cons ⟨by simp [Completed.rawResult], .same _, by simp⟩ .nil

/-- `(-> Number Number)` matches itself, with the bindings unchanged. -/
theorem arrow_matches (bindings : Bindings) :
    TypeMatchRel arrow.functionType arrow.functionType bindings bindings :=
  .structural (by simp [arrow, Atom.undefinedType]) (by simp [arrow, Atom.atomType])
    (by simp [arrow, Atom.undefinedType]) (by simp [arrow, Atom.atomType])
    (.expression
      (.cons (.symSym "->" Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.semanticLoopFree_empty)
        (.mk (by simp [Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.constraints, Bindings.empty])
          .nil)
        (.cons (.symSym "Number" Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.semanticLoopFree_empty)
          (.mk (by simp [Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.constraints, Bindings.empty])
            .nil)
          (.cons
            (.symSym "Number" Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.semanticLoopFree_empty)
            (.mk (by simp [Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.constraints,
              Bindings.empty]) .nil) .nil)))
      Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.semanticLoopFree_empty)
    (Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.MergeRel.mk (order := [])
      (by simp [Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.constraints, Bindings.empty]) .nil)

theorem yes_types : StorageTypesRel (Space.ofList declaredRows) (.symbol "yes") [Atom.undefinedType] :=
  .symbolUndefined (.skip (fun _ same => by simp at same)
    (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same) .nil)))

/-- **The function application of `(f 4)`**: the operator is cast against its arrow, the argument
`4` against `Number`, and the call value `(f 4)` is assembled. -/
theorem function_segment (dispatch : GroundedDispatch) (policy : Policy) (stack : List Continuation) :
    ∃ results : List Result,
      HERuns.HESteps dispatch Completed.rawLookup policy
        ⟨Space.ofList declaredRows, .work (.function [Completed.invocationReturnType arrow] []
          Atom.undefinedType arrow (Entry.Value.ofAtom (.symbol "f"))
          [Entry.Value.ofAtom (.grounded (.int 4))] Completed.Frame.empty), stack, []⟩
        ⟨Space.ofList declaredRows, .returning results, stack, []⟩ ∧
      ∃ value activation, results = [(value, activation)] ∧ value.erase = typedCall := by
  have fCast := typed_cast dispatch policy (atom := .symbol "f") (expected := arrow.functionType)
    (fun _ occurs => by cases occurs)
    (.cast (DataAtom.symbol (name := "f") (by decide) (by decide)).not_stopped (.symbol _)
      (by decide +kernel) (Or.inl ⟨_, rfl⟩) (fun _ => Or.inr rfl)) f_types Completed.Frame.empty
    (arrow_matches _)
  have fourCast := typed_cast dispatch policy (atom := .grounded (.int 4))
    (expected := sym "Number") (fun _ occurs => by cases occurs)
    (.cast (DataAtom.grounded (.int 4)).not_stopped (.grounded _) (by decide +kernel)
      (Or.inr (Or.inl ⟨_, rfl⟩)) (fun _ => Or.inr rfl)) four_types Completed.Frame.empty
    (number_matches _)
  refine ⟨(([(Entry.Value.argumentPacket [], Completed.Frame.empty)].map
      (Completed.argumentPrepend (Entry.Value.ofAtom (.grounded (.int 4)))) ++ []).map
        (Completed.functionAssemble (Entry.Value.ofAtom (.symbol "f")))) ++ [], ?_,
    .expression .active [Entry.Value.ofAtom (.symbol "f"), Entry.Value.ofAtom (.grounded (.int 4))],
    Completed.Frame.empty, by simp [Completed.functionAssemble, Completed.argumentPrepend],
    by simp [Entry.Value.erase, typedCall, app]⟩
  refine .head (.internal (.functionStart rfl)) ?_
  refine .head (fCast _ _ _ _) ?_
  refine .head (.internal .functionHeads) ?_
  refine .head (.internal (.functionBranchesContinue ?_)) ?_
  · simpa using (DataAtom.symbol (name := "f") (by decide) (by decide)).not_stopped
  refine .head (.internal .argumentsCons) ?_
  refine .head (fourCast _ _ _ _) ?_
  refine .head (.internal .arguments) ?_
  refine .head (.internal (.argumentBranchesContinue ?_)) ?_
  · rintro ⟨stopped, _⟩
    exact (DataAtom.grounded (.int 4)).not_stopped (by simpa using stopped)
  refine .head (.internal .argumentsNil) ?_
  refine .head (.internal .argumentTail) ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .argumentBranchesNil) ?_
  refine .head (.internal .prepend) ?_
  refine .head (.internal .functionAssemble) ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .functionBranchesNil) ?_
  refine .single (.internal .prepend)

/-- **The typed equation query of `(f 4)`**: the query selects `(= (f $x) yes)`, and the body `yes`
is cast against the return type `Number`, which an undeclared symbol meets. -/
theorem typed_query (dispatch : GroundedDispatch) (notHost : ¬ dispatch.executable (.symbol "f"))
    (policy : Policy) (value : Entry.Value) (erased : value.erase = typedCall) (activation : Frame)
    (stack : List Continuation) :
    ∃ results : List Result,
      HERuns.HESteps dispatch Completed.rawLookup policy
        ⟨Space.ofList declaredRows, .work (.call [] [] value (sym "Number") activation), stack, []⟩
        ⟨Space.ofList declaredRows, .returning results, stack, []⟩ ∧
      results.map (fun r => r.1.erase) = [sym "yes"] := by
  have program : ∀ row ∈ declaredRows, RegionsWithVariables.ConsFreeHeads row := by
    intro row member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · intro lhs rhs same
      simp at same
    · intro lhs rhs same
      simp at same
    · exact rule_consFree fun a member => by
        simp only [List.mem_singleton] at member
        subst member
        exact .var _
  have bodies : regionBodies declaredRows "f" [.grounded (.int 4)] = [sym "yes"] := by decide +kernel
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList declaredRows) [sym "Number"]
    typedCall activation.bindings
  have fixed : ∀ b ∈ regionBodies declaredRows "f" [.grounded (.int 4)], ∀ rename : String → String,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b := by
    rw [bodies]
    intro b member rename
    rw [List.mem_singleton] at member
    subst member
    simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars]
  have bodiesEq := HERuns.frontier_bodies (fun _ member => by
      simp only [List.mem_singleton] at member
      subst member
      rfl) activation.certified.satisfiable program fixed frontier
  rw [bodies] at bodiesEq
  obtain ⟨work, rfl⟩ : ∃ work, works = [work] := by
    cases works with
    | nil => simp at bodiesEq
    | cons work rest =>
        cases rest with
        | nil => exact ⟨work, rfl⟩
        | cons _ _ => simp at bodiesEq
  have body : work.body = sym "yes" := by
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at bodiesEq
    exact bodiesEq
  have frontier' : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.EquationFrontierRel
      (Space.ofList declaredRows) [sym "Number"] value.erase activation.bindings [work] := by
    rw [erased]
    exact frontier
  obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) activation.certified frontier'
  obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired work List.mem_cons_self
  let output : Frame := ⟨work.bindings, after, certificate⟩
  have closedYes : ∀ name,
      ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs work.body name := by
    rw [body]
    intro name occurs
    cases occurs
  have readBody := HERuns.read_closed policy output closedYes
  have yesCast := typed_cast dispatch policy (atom := sym "yes") (expected := sym "Number")
    (fun _ occurs => by cases occurs)
    (.cast (DataAtom.symbol (name := "yes") (by decide) (by decide)).not_stopped (.symbol _)
      (by decide +kernel) (Or.inl ⟨_, rfl⟩) (fun _ => Or.inr rfl)) yes_types output
    (.undefinedRight _ _)
  have notError : ¬ IsErrorRel value.erase := by
    rw [erased]
    rintro ⟨tail, same⟩
    simp at same
  have nonGrounded : NonGroundedCallRel dispatch value.erase := by
    rw [erased]
    refine And.intro ?_ (by decide +kernel)
    rintro ⟨operator, arguments, same, executable⟩
    simp only [typedCall, app, Atom.expression.injEq, List.cons.injEq] at same
    rw [← same.1] at executable
    exact notHost executable
  refine ⟨(([(Entry.Value.ofAtom (sym "yes"), output)] ++ []) ++ []), ?_, by simp⟩
  refine .head (.internal (.callEquations notError nonGrounded frontier' (List.cons_ne_nil _ _))) ?_
  refine .head (.internal (.equationsCons (output := output) rfl unified)) ?_
  rw [readBody, body]
  refine .head (.internal (.boundaryProducerRaw ?_)) ?_
  · rintro ⟨⟨inner, same⟩, _⟩
    simp [Entry.Value.erase_ofAtom] at same
  refine .head (.internal .boundaryBatch) ?_
  refine .head (.internal .boundaryBatchCons) ?_
  refine .head (.internal .boundaryReturned) ?_
  refine .head (.internal (.returnEvaluate ?_ ?_)) ?_
  · simp [Entry.Value.erase_ofAtom, Atom.notReducible]
  · rw [Entry.Value.erase_ofAtom]
    exact (DataAtom.symbol (name := "yes") (by decide) (by decide)).not_stopped
  refine .head (yesCast _ _ _ _) ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .boundaryBatchNil) ?_
  refine .head (.internal .prepend) ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .equationsNil) ?_
  exact .single (.internal .prepend)

/-- **HE's complete run of the well-typed `(f 4)` answers `yes`**: the admission selects `f`'s arrow
(`atomFunction`), the application assembles `(f 4)`, the query selects the equation, and the body
meets the return type. -/
theorem he_typed_yes (dispatch : GroundedDispatch) (notHost : ¬ dispatch.executable (.symbol "f"))
    (policy : Policy) :
    ∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList declaredRows) typedCall Atom.undefinedType)
          ⟨Space.ofList declaredRows, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [sym "yes"] := by
  have returned : Completed.invocationReturnType arrow = sym "Number" := by
    simp [Completed.invocationReturnType, arrow, Atom.expressionType]
  obtain ⟨F, pathF, value, activation, rfl, erased⟩ := function_segment dispatch policy
    (.calls [] [] (Completed.invocationReturnType arrow) ::
      .append (.invocations [] [] Atom.undefinedType arrow (Entry.Value.ofAtom (.symbol "f"))
        [Entry.Value.ofAtom (.grounded (.int 4))] []) :: [.publish typedCall])
  obtain ⟨Q, pathQ, eraseQ⟩ := typed_query dispatch notHost policy value erased activation
    (.append (.calls [] [] (sym "Number") []) ::
      .append (.invocations [] [] Atom.undefinedType arrow (Entry.Value.ofAtom (.symbol "f"))
        [Entry.Value.ofAtom (.grounded (.int 4))] []) :: [.publish typedCall])
  have clean : ∀ r ∈ (Q ++ []) ++ [], Answerable r.1.erase := by
    intro r member
    simp only [List.append_nil] at member
    have inQ : r.1.erase ∈ [sym "yes"] := by
      rw [← eraseQ]
      exact List.mem_map.mpr ⟨r, member, rfl⟩
    rw [List.mem_singleton] at inQ
    rw [inQ]
    exact answerable_of_data (.symbol (by decide) (by decide))
  obtain ⟨published, eraseP, pathP⟩ := NestedArguments.HENested.publish_step (dispatch := dispatch)
    (lookup := Completed.rawLookup) (policy := policy) (atoms := declaredRows) typedCall
    ((Q ++ []) ++ []) clean [] []
  refine ⟨published, ?_, by rw [eraseP]; simpa using eraseQ⟩
  refine .head (well_typed_takes_function dispatch policy).1 ?_
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
  exact pathP.trans (HERuns.publish_all _ published [])

/-- **When the guard passes, the answers agree**: on the same program, the well-typed `(f 4)` gets
`yes` from HE's `atomFunction` path and `yes` from PeTTa. -/
theorem typed_agrees (dispatch : GroundedDispatch) (notHost : ¬ dispatch.executable (.symbol "f"))
    (policy : Policy) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList declaredRows) typedCall Atom.undefinedType)
          ⟨Space.ofList declaredRows, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [sym "yes"]) ∧
      Streaming.values (Streaming.advance (translate declaredRows) 40
        (Streaming.enter { state := store declaredRows } typedCall)) = [sym "yes"] ∧
      (Streaming.advance (translate declaredRows) 40
        (Streaming.enter { state := store declaredRows } typedCall)).agenda.length = 0 :=
  ⟨he_typed_yes dispatch notHost policy, by decide +kernel, by decide +kernel⟩

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)

/-- `{(= (f $x) yes)}`: the same equation, no declaration. -/
abbrev plainRows : List Atom := [rule (app "f" [.var "x"]) (sym "yes")]

/-- **Positive control: without the declarations both dialects answer `yes`** (an instance of
`AnswerBags.answers_agree`). -/
theorem undeclared_agrees {lookup : CastLookup} (answers : AnswersUndefined lookup)
    (policy : Policy) :
    ∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep noHost lookup policy)
          (load (Space.ofList plainRows) declaredCall Atom.undefinedType)
          ⟨Space.ofList plainRows, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [sym "yes"] := by
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
  obtain ⟨R, N, path, _, agree⟩ := answers_agree noHost answers policy program settles
  refine ⟨R, path, ?_⟩
  have later := agree (max N 40) (le_max_left _ _)
  rw [advance_stable (List.eq_nil_of_length_eq_zero finished) _ (le_max_right _ _), computed] at later
  exact later.symm

/-- **Negative control: the guard is the declarations.** The two declaration rows are what
`declaredRows` adds to `plainRows`, and they are not equations: PeTTa's translation has the same
equations for both programs. -/
theorem only_declarations_added :
    declaredRows = [.expression [.symbol ":", sym "f", .expression [.symbol "->", sym "Number",
      sym "Number"]], .expression [.symbol ":", sym "b", sym "Bool"]] ++ plainRows ∧
    (translate declaredRows).equations = (translate plainRows).equations := by
  refine ⟨rfl, ?_⟩
  rw [translate_equations, translate_equations]
  rfl

end Controls

#print axioms symbols_do_not_match
#print axioms number_bool_mismatch
#print axioms number_rejects_bool
#print axioms arrow_rejected
#print axioms selection_failed
#print axioms he_declared_error
#print axioms petta_declared_yes
#print axioms declared_guard_differs
#print axioms arrow_selected
#print axioms selection_succeeds
#print axioms well_typed_takes_function
#print axioms typed_cast
#print axioms arrow_matches
#print axioms function_segment
#print axioms typed_query
#print axioms he_typed_yes
#print axioms typed_agrees
#print axioms Controls.undeclared_agrees
#print axioms Controls.only_declarations_added

end DeclaredHeads

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
