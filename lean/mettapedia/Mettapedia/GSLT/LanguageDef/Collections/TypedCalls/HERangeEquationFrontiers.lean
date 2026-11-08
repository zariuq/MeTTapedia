import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSourceProgram

/-!
# Complete equation frontiers for the authored range and empty calls

Every physical row of the source slice is accounted for. Fixed differing
heads cannot become matches by freshening, substitution or caller merging.
The empty case is an authored equation with an ordinary stopped return.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeEquationFrontiers

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps
open Spec.Type.Presentation Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation
open Spec.Match.Merge
open HERangeSourceProgram (space emptyPattern emptyRule)

theorem annotation_irrelevant (live : List Atom) (query : Atom) (before : Bindings)
    (position : Nat) (subject type : Atom) :
    EquationRowResultsRel live query before position (.expression [.symbol ":", subject, type]) [] :=
  .irrelevant position _ (by intro left right; simp)

theorem different_head_miss (live : List Atom) (before : Bindings) (position : Nat)
    (queryHead ruleHead : String) (queryArguments ruleArguments : List Atom) (rhs : Atom)
    (different : queryHead ≠ ruleHead) :
    EquationRowResultsRel live (.expression (.symbol queryHead :: queryArguments)) before position
      (.expression [.symbol "=", .expression (.symbol ruleHead :: ruleArguments), rhs]) [] := by
  let query := Atom.expression (.symbol queryHead :: queryArguments)
  let lhs := Atom.expression (.symbol ruleHead :: ruleArguments)
  let chosen := EquationFreshening.freshRule (EquationScope.visibleNames live query before) position lhs rhs
  have alpha := EquationFreshening.freshRule_alphaVariant live query lhs rhs before position
  change AlphaVariantRel live query before lhs rhs chosen.1 chosen.2 at alpha
  apply EquationRowResultsRel.miss position lhs rhs chosen.1 chosen.2 alpha
  intro otherPattern otherBody variant matched output candidate
  obtain ⟨rename, _, renamed, _, _⟩ := variant
  have shape := EquationFreshening.alphaRename_eq renamed
  obtain ⟨valuation, model⟩ := candidate.2.2
  have equal := ((UnifyCandidateRel.solutions ⟨matched, candidate.1, candidate.2⟩ valuation).mp model).1
  rw [shape] at equal
  have heads := congrArg (fun atom : Atom => match atom with
    | .expression (.symbol head :: _) => some head
    | _ => none) equal
  exact different (by simpa [query, lhs, applyTypeValuation, renameTypeVars] using heads)

theorem empty_alpha (live : List Atom) (before : Bindings) :
    AlphaVariantRel live emptyPattern before emptyPattern (.symbol "Empty") emptyPattern (.symbol "Empty") := by
  refine ⟨id, Function.injective_id, .expression (.cons (.symbol "empty") .nil), .symbol "Empty", ?_⟩
  intro name occurs
  rcases occurs with first | second
  · have used := atomOccurs_mem_typeVars first
    simp [emptyPattern, TypeSubst.typeVars, TypeSubst.typeVarsList] at used
  · have used := atomOccurs_mem_typeVars second
    simp [TypeSubst.typeVars] at used

def emptyWork (before : Frame) : EquationWork :=
  ⟨7, emptyPattern, .symbol "Empty", emptyPattern, .symbol "Empty", before.bindings⟩

theorem empty_frontier (live : List Atom) (before : Frame) :
    EquationFrontierRel space live emptyPattern before.bindings [emptyWork before] := by
  have matching : MatchRel equalityGroundedSemantic emptyPattern emptyPattern Bindings.empty :=
    .expression (.cons (.symSym "empty" semanticLoopFree_empty)
      (.mk (by simp [constraints, Bindings.empty]) .nil) .nil) semanticLoopFree_empty
  have merged : LogicalMergeRel Bindings.empty before.bindings before.bindings :=
    ⟨BindingSourceAgreement.refl _, before.certified.satisfiable⟩
  have hit : EquationRowResultsRel live emptyPattern before.bindings 7 emptyRule [emptyWork before] :=
    .hit 7 emptyPattern (.symbol "Empty") emptyPattern (.symbol "Empty") Bindings.empty before.bindings
      (empty_alpha live before.bindings) matching merged
  have scanned : EquationFrontierRel space live emptyPattern before.bindings
      ([[], [], [], [], [], [], [], [emptyWork before]] : List (List EquationWork)).flatten := by
    apply EquationFrontierRel.completed
    simp only [HERangeSourceProgram.space, HERangeSourceProgram.declaredSpace, HEIfSourceSelection.Range.space,
      Space.ofList, List.cons_append, List.nil_append, List.zipIdx_cons, List.zipIdx_nil]
    exact .cons (annotation_irrelevant _ _ _ _ _ _)
      (.cons (annotation_irrelevant _ _ _ _ _ _)
        (.cons (annotation_irrelevant _ _ _ _ _ _)
          (.cons (different_head_miss live before.bindings 3 "empty" "range" [] _ _ (by decide))
            (.cons (different_head_miss live before.bindings 4 "empty" "if" [] _ _ (by decide))
              (.cons (different_head_miss live before.bindings 5 "empty" "if" [] _ _ (by decide))
                (.cons (HERangeSourceProgram.declaration_irrelevant _ _ _ _) (.cons hit .nil)))))))
  simpa using scanned

def emptyCall : Entry.Value := Entry.Value.ofAtom emptyPattern

/-- The source empty equation returns the actual Empty occurrence under
every caller demand, including retained private range variables. -/
theorem empty_call_from_frontier {World : Type} (current : WorldEnvironment Space World)
    (label : Space) (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (expected : Atom) (work : EquationWork)
    (frontier : EquationFrontierRel (current.view world label) (expected :: live) emptyPattern before.bindings [work])
    (pattern : work.pattern = emptyPattern) (body : work.body = .symbol "Empty") (bindings : work.bindings = before.bindings)
    (owned : NonGroundedCallRel current.dispatch emptyCall.erase) :
    Stateful.CallRel current label world live scope emptyCall expected before
      [(.symbol "Empty", before)] world (policy := policy) := by
  have read : before.read policy (.symbol "Empty") = .symbol "Empty" := by simp [Frame.read, Entry.Value.substitute]
  have unified : Entry.Value.UnifyRel policy.rebuilding before.environment emptyCall
      (Entry.Value.ofAtom work.pattern) before.environment := by
    rw [pattern]
    exact .ordinary (.identical rfl)
  have producer : Stateful.BoundaryRel current label world (expected :: live) scope
      (some emptyCall.erase) .producer (before.read policy (Entry.Value.ofAtom work.body)) before
      [(.symbol "Empty", before)] world (policy := policy) := by
    simpa [body, Entry.Value.ofAtom, read] using
      (Stateful.BoundaryRel.producerRaw (environment := current)
        (value := Entry.Value.symbol "Empty") (frame := before)
        (by simp [FunctionPending, Minimal.IsFunction, Entry.Value.erase]))
  have returned : Stateful.BoundaryBatchRel current label world live scope none
      (.returned emptyCall expected) [(.symbol "Empty", before)] [(.symbol "Empty", before)] world (policy := policy) := by
    apply Stateful.BoundaryBatchRel.single_iff.mpr
    exact .returned (.stopped (by simp [Entry.Value.erase, IsEmptyOrErrorRel, Atom.empty]))
  apply Stateful.CallRel.equations (works := [work])
  · simp [emptyCall, emptyPattern, Entry.Value.erase_ofAtom, IsErrorRel]
  · exact owned
  · simpa only [emptyCall, Entry.Value.erase_ofAtom] using frontier
  · simp
  · simpa only [List.append_nil] using
      Stateful.EquationBodiesRel.cons (work := work) bindings.symm unified producer returned Stateful.EquationBodiesRel.nil

theorem empty_call_in (current : WorldEnvironment Space Unit)
    (view : current.view () space = space) (dispatch : current.dispatch = HERangeSourceProgram.dispatch) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (expected : Atom) :
    Stateful.CallRel (current) space () live scope emptyCall expected before
      [(.symbol "Empty", before)] () (policy := policy) := by
  apply empty_call_from_frontier current space () policy before live scope expected (emptyWork before)
  · simpa only [view] using empty_frontier (expected :: live) before
  · rfl
  · rfl
  · rfl
  · simp [NonGroundedCallRel, Minimal.HostCall, dispatch, HERangeSourceProgram.dispatch,
      emptyCall, emptyPattern, Entry.Value.erase_ofAtom, Minimal.embeddedInstruction]

theorem empty_call (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (expected : Atom) :
    Stateful.CallRel (HERangeSourceProgram.environment minimal) space () live scope emptyCall expected before
      [(.symbol "Empty", before)] () (policy := policy) :=
  empty_call_in (HERangeSourceProgram.environment minimal) rfl rfl policy before live scope expected

/-- The authored range call has one actual physical source occurrence in
the full slice, with every other equation and declaration accounted for. -/
theorem range_frontier (policy : Policy) (live : List Atom) (before : Frame) (lower upper : Int) :
    ∃ (work : EquationWork) (after : Frame),
      EquationFrontierRel space live (HEFreshEquationFrames.Range.call lower upper) before.bindings [work] ∧
      after.bindings = work.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding before.environment
        (Entry.Value.ofAtom (HEFreshEquationFrames.Range.call lower upper)) (Entry.Value.ofAtom work.pattern) after.environment ∧
      after.read policy (Entry.Value.ofAtom work.body) =
        Entry.Value.ofAtom (HEFreshEquationFrames.Range.bodyAt (HEFreshEquationFrames.Range.number lower)
          (HEFreshEquationFrames.Range.number upper)) := by
  obtain ⟨freshPattern, freshBody, matched, output, occurrence⟩ :=
    HEFreshEquationFrames.Range.fresh_occurrence space live before lower upper 3 rfl
  let work : EquationWork := ⟨3, HEFreshEquationFrames.Range.pattern, HEFreshEquationFrames.Range.body,
    freshPattern, freshBody, output⟩
  have hit : EquationRowResultsRel live (HEFreshEquationFrames.Range.call lower upper) before.bindings 3
      (.expression [.symbol "=", HEFreshEquationFrames.Range.pattern, HEFreshEquationFrames.Range.body]) [work] :=
    .hit 3 _ _ freshPattern freshBody matched output occurrence.selected.1 occurrence.selected.2 occurrence.result.1
  have scanned : EquationFrontierRel space live (HEFreshEquationFrames.Range.call lower upper) before.bindings
      ([[], [], [], [work], [], [], [], []] : List (List EquationWork)).flatten := by
    apply EquationFrontierRel.completed
    simp only [HERangeSourceProgram.space, HERangeSourceProgram.declaredSpace, HEIfSourceSelection.Range.space,
      Space.ofList, List.cons_append, List.nil_append, List.zipIdx_cons, List.zipIdx_nil]
    exact .cons (annotation_irrelevant _ _ _ _ _ _)
      (.cons (annotation_irrelevant _ _ _ _ _ _)
        (.cons (annotation_irrelevant _ _ _ _ _ _)
          (.cons hit
            (.cons (different_head_miss live before.bindings 4 "range" "if" _ _ _ (by decide))
              (.cons (different_head_miss live before.bindings 5 "range" "if" _ _ _ (by decide))
                (.cons (HERangeSourceProgram.declaration_irrelevant _ _ _ _)
                  (.cons (HERangeSourceProgram.empty_miss live "range" _ before.bindings 7 (by decide)) .nil)))))))
  have frontier : EquationFrontierRel space live (HEFreshEquationFrames.Range.call lower upper) before.bindings [work] := by
    simpa using scanned
  have candidate : UnifyCandidateRel (Entry.Value.ofAtom (HEFreshEquationFrames.Range.call lower upper)).erase
      (Entry.Value.ofAtom work.pattern).erase before.bindings work.bindings := by
    simpa only [Entry.Value.erase_ofAtom, work] using
      (show UnifyCandidateRel (HEFreshEquationFrames.Range.call lower upper) freshPattern before.bindings output from
        ⟨matched, occurrence.selected.2, occurrence.result.1⟩)
  obtain ⟨table, unified, certified⟩ := Entry.Value.UnifyRel.of_source_candidate (policy := policy.rebuilding) before.certified candidate
  let after : Frame := ⟨work.bindings, table, certified⟩
  exact ⟨work, after, frontier, rfl, unified,
    HEFreshEquationFrames.Range.selected_body_readback space policy live before after lower upper [work] work
      frontier (by simp) rfl rfl unified⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeEquationFrontiers
