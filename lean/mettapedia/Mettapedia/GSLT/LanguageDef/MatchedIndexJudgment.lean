import Mettapedia.GSLT.Core.JudgmentComposition
import Mettapedia.GSLT.LanguageDef.BindingDecisionAdequacy

/-!
# Pattern selection followed by a dependent index judgment

The existing matcher first selects a binding occurrence. A separate executable
service then checks a vector payload and an index into its actual length.
Its evidence contains a `Fin values.length`, not merely a successful match.

The combined evaluator is exact for the two-stage judgment, for arbitrary
patterns and subjects. Binding occurrences retain their list positions; the
evaluator keeps duplicate answers. The first-order compiler connection is
stated separately at its existing result-support boundary.

This is a concrete judgment-integration contract, not a general DTT checker,
an implementation of source parsing, or a CeTTa C realization.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MatchedIndexJudgment

open Mettapedia.GSLT.ProofRelevantJudgment
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-- The original pattern and subject remain available to later judgments. -/
abbrev Query := Pattern × Pattern

/-- Select one occurrence in the actual matcher's list, not just its binding
value. Equal bindings at different positions remain distinct evidence. -/
def matching : Judgment Query Bindings where
  Evidence query bindings :=
    {position : Fin (matchPattern query.1 query.2).length //
      (matchPattern query.1 query.2).get position = bindings}

theorem matching_nonempty_iff (query : Query) (bindings : Bindings) :
    Nonempty (matching.Evidence query bindings) ↔
      bindings ∈ matchPattern query.1 query.2 := by
  constructor
  · rintro ⟨position, found⟩
    exact List.mem_iff_get.mpr ⟨position, found⟩
  · intro member
    obtain ⟨position, found⟩ := List.mem_iff_get.mp member
    exact ⟨position, found⟩

/-- A proof-relevant bounded lookup, including the actual payload recovered
from the selected bindings. -/
def IndexEvidence (position : Nat) (bindings : Bindings) (output : Pattern) : Type :=
  Sigma fun values : List Pattern =>
    PLift (bindings.lookup "items" = some (.collection .vec values none)) ×
      Sigma fun index : Fin values.length =>
        PLift (index.val = position ∧ values.get index = output)

def indexPremise (position : Nat) : Continuation matching Pattern :=
  fun _ bindings _ output => IndexEvidence position bindings output

/-- A terminating local service; non-vector, open-rest and out-of-range
requests produce no answer. Failure is not a proof of a mathematical negation. -/
def checkIndex (position : Nat) (bindings : Bindings) : Option Pattern :=
  match bindings.lookup "items" with
  | some (.collection .vec values none) => getElem? values position
  | _ => none

private theorem getElem?_iff_fin (values : List Pattern) (position : Nat)
    (output : Pattern) :
    getElem? values position = some output ↔
      ∃ index : Fin values.length, index.val = position ∧ values.get index = output := by
  rw [List.getElem?_eq_some_iff]
  constructor
  · rintro ⟨bound, found⟩
    exact ⟨⟨position, bound⟩, rfl, found⟩
  · rintro ⟨⟨index, bound⟩, equal, found⟩
    subst position
    exact ⟨bound, found⟩

/-- The actual checker produces an answer exactly when bounded lookup
evidence exists. Neither direction is assumed as a service field. -/
theorem checkIndex_eq_some_iff (position : Nat) (bindings : Bindings)
    (output : Pattern) :
    checkIndex position bindings = some output ↔
      Nonempty (IndexEvidence position bindings output) := by
  constructor
  · intro checked
    unfold checkIndex at checked
    split at checked
    next values found =>
      obtain ⟨index, same, result⟩ := (getElem?_iff_fin values position output).mp checked
      exact ⟨values, ⟨found⟩, index, ⟨same, result⟩⟩
    next => cases checked
  · rintro ⟨values, ⟨found⟩, index, ⟨same, result⟩⟩
    unfold checkIndex
    rw [found]
    exact (getElem?_iff_fin values position output).mpr ⟨index, same, result⟩

/-- Enumerate all match occurrences, invoking the independent local checker
at each. `flatMap` intentionally retains repeated successful outputs. -/
def evaluate (query : Query) (position : Nat) : List Pattern :=
  (matchPattern query.1 query.2).flatMap
    (fun bindings => (checkIndex position bindings).toList)

/-- Each successful binding occurrence contributes once, including repeated
equal answers. The checker does not identify distinct match positions. -/
theorem evaluate_count (query : Query) (position : Nat) (output : Pattern) :
    (evaluate query position).count output =
      ((matchPattern query.1 query.2).filter
        (fun bindings => checkIndex position bindings == some output)).length := by
  unfold evaluate
  generalize matchPattern query.1 query.2 = candidates
  induction candidates with
  | nil => rfl
  | cons bindings rest ih =>
      cases checked : checkIndex position bindings with
      | none => simpa [checked] using ih
      | some answer =>
          by_cases equal : answer = output
          · subst answer
            simp [checked, ih]
          · simp [checked, ih, equal]

/-- Exact operational admission for the concrete composition of matching and
dependent checking, not merely a forward simulation. -/
theorem mem_evaluate_iff_run (query : Query) (position : Nat) (output : Pattern) :
    output ∈ evaluate query position ↔
      Nonempty (Sequential.Run matching (indexPremise position) query output) := by
  simp only [evaluate, List.mem_flatMap, Option.mem_toList]
  constructor
  · rintro ⟨bindings, member, checked⟩
    obtain ⟨selected⟩ := (matching_nonempty_iff query bindings).mpr member
    obtain ⟨evidence⟩ := (checkIndex_eq_some_iff position bindings output).mp checked
    exact ⟨Sequential.runOfEvidence matching (indexPremise position)
      ⟨bindings, selected, evidence⟩⟩
  · rintro ⟨run⟩
    rcases Sequential.evidenceOfRun matching (indexPremise position) run with
      ⟨bindings, selected, evidence⟩
    exact ⟨bindings, (matching_nonempty_iff query bindings).mp ⟨selected⟩,
      (checkIndex_eq_some_iff position bindings output).mpr ⟨evidence⟩⟩

/-- Every successful composed query carries an index into the recovered
vector, and its answer is the element at that very index. -/
theorem evaluate_answer_has_bounded_index {query : Query} {position : Nat}
    {output : Pattern} (accepted : output ∈ evaluate query position) :
    ∃ (bindings : Bindings) (values : List Pattern) (index : Fin values.length),
      bindings ∈ matchPattern query.1 query.2 ∧
      bindings.lookup "items" = some (.collection .vec values none) ∧
      index.val = position ∧ values.get index = output := by
  obtain ⟨run⟩ := (mem_evaluate_iff_run query position output).mp accepted
  rcases Sequential.evidenceOfRun matching (indexPremise position) run with
    ⟨bindings, selected, values, ⟨found⟩, index, ⟨same, result⟩⟩
  exact ⟨bindings, values, index,
    (matching_nonempty_iff query bindings).mp ⟨selected⟩, found, same, result⟩

/-! ## Connection to the existing compiled matcher -/

open Mettapedia.GSLT.LanguageDef.BindingDecisionLanguage
open Mettapedia.GSLT.LanguageDef.PatternPlanBindingDecisionCompilation

/-- For the existing first-order compiler's scope, matching support is
exactly the language run followed by the independently checked premise.
This theorem does not assert equality of internal machine paths. -/
theorem compiled_matcher_then_check_iff
    (plan : FirstOrder.PatternPlan) (subject : Pattern) (position : Nat)
    (output : Pattern) :
    output ∈ evaluate (plan.erase, subject) position ↔
      ∃ bindings,
        LanguageReaches (encodeState (.run (compile plan) subject []))
          (encodeState (.done bindings)) ∧
        checkIndex position bindings = some output := by
  simp only [evaluate, List.mem_flatMap, Option.mem_toList]
  constructor
  · rintro ⟨bindings, member, checked⟩
    exact ⟨bindings,
      (languageReaches_compile_iff_mem_matchPattern plan subject bindings).mpr member, checked⟩
  · rintro ⟨bindings, run, checked⟩
    exact ⟨bindings,
      (languageReaches_compile_iff_mem_matchPattern plan subject bindings).mp run, checked⟩

/-! ## General vector interface and negative controls -/

def vectorQuery (values : List Pattern) : Query :=
  (.fvar "items", .collection .vec values none)

theorem evaluate_vector (values : List Pattern) (position : Nat) :
    evaluate (vectorQuery values) position = (getElem? values position).toList := by
  simp [evaluate, vectorQuery, matchPattern, checkIndex, Bindings.lookup]

theorem vector_run_iff (values : List Pattern) (position : Nat) (output : Pattern) :
    Nonempty (Sequential.Run matching (indexPremise position) (vectorQuery values) output) ↔
      ∃ index : Fin values.length, index.val = position ∧ values.get index = output := by
  rw [← mem_evaluate_iff_run, evaluate_vector, Option.mem_toList, getElem?_iff_fin]

theorem valid_index_runs (values : List Pattern) (index : Fin values.length) :
    Nonempty (Sequential.Run matching (indexPremise index.val)
      (vectorQuery values) (values.get index)) :=
  (vector_run_iff values index.val (values.get index)).mpr ⟨index, rfl, rfl⟩

/-- Structural matching succeeds even at an out-of-range index, but the
composed judgment has no accepted result. -/
theorem out_of_range_no_run (values : List Pattern) (position : Nat)
    (outside : values.length ≤ position) (output : Pattern) :
    ¬ Nonempty (Sequential.Run matching (indexPremise position) (vectorQuery values) output) := by
  intro run
  obtain ⟨index, same, _⟩ := (vector_run_iff values position output).mp run
  have bound := index.isLt
  rw [same] at bound
  exact Nat.not_lt_of_ge outside bound

theorem non_vector_rejected (position : Nat) :
    evaluate (.fvar "items", .apply "opaque" []) position = [] := by
  simp [evaluate, matchPattern, checkIndex, Bindings.lookup]

/-- The proof carries length dependence even though the surface matcher
merely binds one metavariable. -/
theorem integration_controls :
    evaluate (vectorQuery [.apply "a" [], .apply "b" []]) 1 = [.apply "b" []] ∧
      evaluate (vectorQuery [.apply "a" [], .apply "b" []]) 2 = [] ∧
      evaluate (.fvar "items", .apply "opaque" []) 0 = [] := by
  constructor
  · rw [evaluate_vector]
    rfl
  constructor
  · rw [evaluate_vector]
    rfl
  · exact non_vector_rejected 0

/-- Two different bag positions can supply equal vectors and equal answers.
The evaluator retains both occurrences rather than deduplicating them. -/
theorem duplicate_match_controls :
    evaluate
      (.collection .hashBag [.fvar "items"] (some "rest"),
        .collection .hashBag
          [.collection .vec [.apply "a" []] none,
           .collection .vec [.apply "a" []] none] none) 0 =
      [.apply "a" [], .apply "a" []] := by
  simp [evaluate, matchPattern, matchBag, mergeBindings, checkIndex, Bindings.lookup]

#print axioms matching_nonempty_iff
#print axioms checkIndex_eq_some_iff
#print axioms evaluate_count
#print axioms mem_evaluate_iff_run
#print axioms evaluate_answer_has_bounded_index
#print axioms compiled_matcher_then_check_iff
#print axioms vector_run_iff
#print axioms valid_index_runs
#print axioms out_of_range_no_run
#print axioms integration_controls
#print axioms duplicate_match_controls

end Mettapedia.GSLT.LanguageDef.MatchedIndexJudgment
