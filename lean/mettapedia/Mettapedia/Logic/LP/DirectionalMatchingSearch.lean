import Mettapedia.Logic.LP.DirectionalMatchingScope
import Mettapedia.Data.List.OrderedOccurrenceCursor

/-!
# Ordered directional joins and their residuals

Candidate rows here have already crossed the native freshening boundary.
Each row carries an occurrence identity; equal terms are not deduplicated.
The join retains the original pairs and checks the whole prefix, as the native
directional-query continuation does. Its pruning theorem compares this algorithm
with exhaustive enumeration, not with a second spelling of the same algorithm.

The bounded cursor counts candidate inspections. It is not a model of the C
machine's finer transition budget or a claim of whole-program C verification.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP.DirectionalMatching

open Mettapedia.Data.List.OrderedOccurrenceCursor

universe u v
variable {σ : LPSignature.{u, u, v, u}} [DecidableEq σ.vars]
  [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- Adding constraints cannot repair an already impossible protected match.
This uses the original subjects, not subjects rewritten by an earlier answer. -/
theorem matchMany_prefix_rejected (initial suffix : List (Term σ × Term σ))
    (rejected : matchMany initial = none) : matchMany (initial ++ suffix) = none := by
  apply (matchMany_none_iff _).mpr
  rintro ⟨answer, fixed, matched⟩
  apply (matchMany_none_iff _).mp rejected
  refine ⟨answer, ?_, ?_⟩
  · intro name member
    obtain ⟨pair, present, inVars⟩ := (mem_subjectVars initial name).mp member
    exact fixed name ((mem_subjectVars _ name).mpr
      ⟨pair, List.mem_append_left _ present, inVars⟩)
  · exact fun pair present => matched pair (List.mem_append_left _ present)

abbrev Selection (σ : LPSignature) := List (Term σ × Occurrence (Term σ))
abbrev Column (σ : LPSignature) := Term σ × List (Occurrence (Term σ))
abbrev Hit (σ : LPSignature) := Selection σ × Subst σ

def selectionPairs (selected : Selection σ) : List (Term σ × Term σ) :=
  selected.map fun entry => (entry.1, entry.2.value)

def checkSelection (selected : Selection σ) : Option (Hit σ) :=
  (matchMany (selectionPairs selected)).map fun answer => (selected, answer)

/-- Every row combination in premise order, without semantic pruning. -/
def enumerate : List (Column σ) → Selection σ → List (Selection σ)
  | [], selected => [selected]
  | (pattern, rows) :: rest, selected =>
      rows.flatMap fun row => enumerate rest (selected ++ [(pattern, row)])

/-- Reject a failed prefix before opening the next occurrence column. -/
def join : List (Column σ) → Selection σ → List (Hit σ)
  | columns, selected =>
    match matchMany (selectionPairs selected) with
    | none => []
    | some answer =>
      match columns with
      | [] => [(selected, answer)]
      | (pattern, rows) :: rest =>
          rows.flatMap fun row => join rest (selected ++ [(pattern, row)])

theorem checkSelection_sound (selected : Selection σ) (hit : Hit σ)
    (accepted : checkSelection selected = some hit) :
    hit.1 = selected ∧
      RigidUnification.Fixes (fun name => name ∈ subjectVars (selectionPairs selected))
        hit.2 ∧ Matches hit.2 (selectionPairs selected) := by
  cases h : matchMany (selectionPairs selected) with
  | none => simp [checkSelection, h] at accepted
  | some answer =>
      have equal : (selected, answer) = hit := by
        simpa [checkSelection, h] using accepted
      subst hit
      exact ⟨rfl, matchMany_sound _ _ h⟩

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem enumerate_extends (columns : List (Column σ))
    (selected result : Selection σ) (present : result ∈ enumerate columns selected) :
    ∃ suffix, result = selected ++ suffix := by
  induction columns generalizing selected with
  | nil =>
      have equal : result = selected := by simpa [enumerate] using present
      exact ⟨[], by simpa using equal⟩
  | cons column rest ih =>
      obtain ⟨row, _, included⟩ := List.mem_flatMap.mp present
      obtain ⟨suffix, equal⟩ := ih _ included
      exact ⟨(column.1, row) :: suffix, by simpa [List.append_assoc] using equal⟩

theorem rejected_prefix_has_no_hits (columns : List (Column σ))
    (selected : Selection σ) (rejected : matchMany (selectionPairs selected) = none) :
    (enumerate columns selected).filterMap checkSelection = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro result present
  obtain ⟨suffix, rfl⟩ := enumerate_extends columns selected result present
  have failed := matchMany_prefix_rejected (selectionPairs selected)
    (selectionPairs suffix) rejected
  simpa [checkSelection, selectionPairs, List.map_append] using
    congrArg (Option.map fun answer => (selected ++ suffix, answer)) failed

/-- Prefix pruning preserves the entire ordered list: multiplicity, occurrence
identities, and the witness associated with each complete row combination. -/
theorem join_eq_exhaustive (columns : List (Column σ)) (selected : Selection σ) :
    join columns selected = (enumerate columns selected).filterMap checkSelection := by
  induction columns generalizing selected with
  | nil => cases h : matchMany (selectionPairs selected) <;>
      simp [join, enumerate, checkSelection, h]
  | cons column rest ih =>
      cases h : matchMany (selectionPairs selected) with
      | none =>
          rw [join, h, rejected_prefix_has_no_hits _ _ h]
      | some answer =>
          rw [join, h]
          simp only [enumerate, List.filterMap_flatMap]
          exact List.flatMap_congr fun row _ => ih (selected ++ [(column.1, row)])

theorem join_hit_sound (columns : List (Column σ)) (selected : Selection σ)
    (hit : Hit σ) (present : hit ∈ join columns selected) :
    hit.1 ∈ enumerate columns selected ∧
      RigidUnification.Fixes (fun name => name ∈ subjectVars (selectionPairs hit.1))
        hit.2 ∧ Matches hit.2 (selectionPairs hit.1) := by
  rw [join_eq_exhaustive] at present
  obtain ⟨candidate, included, accepted⟩ := List.mem_filterMap.mp present
  obtain ⟨same, fixed, matched⟩ := checkSelection_sound candidate hit accepted
  exact ⟨same ▸ included, same ▸ fixed, same ▸ matched⟩

/-- Every enumerated row combination with an allowed solution contributes an
answer. This states existence without insisting on arbitrary unobserved images. -/
theorem join_candidate_complete (columns : List (Column σ))
    (selected candidate : Selection σ) (included : candidate ∈ enumerate columns selected)
    (answer : Subst σ)
    (fixed : RigidUnification.Fixes
      (fun name => name ∈ subjectVars (selectionPairs candidate)) answer)
    (matched : Matches answer (selectionPairs candidate)) :
    ∃ result, (candidate, result) ∈ join columns selected := by
  obtain ⟨result, accepted⟩ := matchMany_complete _ answer fixed matched
  refine ⟨result, ?_⟩
  rw [join_eq_exhaustive]
  exact List.mem_filterMap.mpr ⟨candidate, included, by simp [checkSelection, accepted]⟩

/-- An occurrence cursor over complete candidates can be consumed in bounded
chunks. Rejected candidates consume a step but publish no answer. -/
def run (fuel : Nat) (cursor : Cursor (Selection σ)) :
    List (Occurrence (Hit σ)) × Cursor (Selection σ) :=
  match fuel with
  | 0 => ([], cursor)
  | fuel + 1 =>
    match cursor.step with
    | none => ([], cursor)
    | some (candidate, next) =>
      let (answers, residual) := run fuel next
      match checkSelection candidate.value with
      | none => (answers, residual)
      | some hit => (⟨candidate.identity, hit⟩ :: answers, residual)

def checkOccurrence (candidate : Occurrence (Selection σ)) :
    Option (Occurrence (Hit σ)) :=
  (checkSelection candidate.value).map fun hit => ⟨candidate.identity, hit⟩

theorem run_exact (fuel : Nat) (cursor : Cursor (Selection σ)) :
    run fuel cursor =
      ((cursor.remaining.take fuel).filterMap checkOccurrence,
        ⟨cursor.captured, cursor.remaining.drop fuel⟩) := by
  induction fuel generalizing cursor with
  | zero => cases cursor; simp [run]
  | succ fuel ih =>
      rcases cursor with ⟨captured, remaining⟩
      cases remaining with
      | nil => simp [run, Cursor.step]
      | cons candidate rest =>
          simp only [run, Cursor.step, ih, List.take_succ_cons, List.drop_succ_cons]
          cases h : checkSelection candidate.value <;>
            simp [checkOccurrence, h]

/-- Concatenating already emitted answers with the residual's observation
recovers the original observation exactly; no failed or pending candidate is
silently promoted to a successful match. -/
theorem run_residual_exact (fuel : Nat) (cursor : Cursor (Selection σ)) :
    (run fuel cursor).1 ++
        (run fuel cursor).2.remaining.filterMap checkOccurrence =
      cursor.remaining.filterMap checkOccurrence := by
  rw [run_exact]
  simpa only [List.filterMap_append] using
    congrArg (List.filterMap checkOccurrence)
      (List.take_append_drop fuel cursor.remaining)

theorem run_preserves_capture (fuel : Nat) (cursor : Cursor (Selection σ)) :
    (run fuel cursor).2.captured = cursor.captured := by rw [run_exact]

/-- Resuming with another budget gives the same answers and residual as one
combined budget, including when either budget stops on a rejected candidate. -/
theorem run_add (first second : Nat) (cursor : Cursor (Selection σ)) :
    run (first + second) cursor =
      ((run first cursor).1 ++ (run second (run first cursor).2).1,
        (run second (run first cursor).2).2) := by
  simp only [run_exact, List.drop_drop]
  congr 1
  rw [← List.filterMap_append]
  exact congrArg (List.filterMap checkOccurrence)
    (List.take_add : cursor.remaining.take (first + second) =
      cursor.remaining.take first ++ (cursor.remaining.drop first).take second)

theorem run_rejected_publishes_nothing (fuel : Nat)
    (cursor : Cursor (Selection σ))
    (allRejected : ∀ candidate ∈ cursor.remaining, checkSelection candidate.value = none) :
    (run fuel cursor).1 = [] := by
  rw [run_exact]
  apply List.filterMap_eq_nil_iff.mpr
  intro candidate present
  simp [checkOccurrence, allRejected candidate (List.mem_of_mem_take present)]

end Mettapedia.Logic.LP.DirectionalMatching

#print axioms Mettapedia.Logic.LP.DirectionalMatching.join_eq_exhaustive
#print axioms Mettapedia.Logic.LP.DirectionalMatching.join_hit_sound
#print axioms Mettapedia.Logic.LP.DirectionalMatching.join_candidate_complete
#print axioms Mettapedia.Logic.LP.DirectionalMatching.run_exact
#print axioms Mettapedia.Logic.LP.DirectionalMatching.run_residual_exact
#print axioms Mettapedia.Logic.LP.DirectionalMatching.run_add
