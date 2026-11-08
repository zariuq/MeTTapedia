import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEMatchedReturnBoundary
import Mettapedia.Machines.HEFrontierNormalization

/-!
# Completed invocation frontiers with retained result records

The existing three-class frontier normalizer is instantiated on real HE
result pairs. Classification reads the atom; forwarding retains the complete
pair, including bindings. Successful occurrences stream immediately. Errors
and Empty are released only after the call node's alternatives have finished.

This is the native output-frontier policy, not a replacement for operand or
control frontiers. Its difference from the historical executable evaluator's
binary error selection is explicit. The policies agree without Empty, and
also on batches consisting entirely of Empty. Mixed batches can distinguish
them. The actual native classifier, ownership and producer completion events
must instantiate this adapter; no C lifetime or effect scheduling claim is made.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEInvocationFrontier

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.HEFrontierNormalization

def classify (reply : ResultPair) : Kind :=
  if isEmptyAtom reply.1 then .empty
  else if isErrorAtom reply.1 then .error else .success

theorem empty_not_error {value : Atom} (empty : isEmptyAtom value = true) :
    isErrorAtom value = false := by
  have valueEq : value = Atom.empty := by simpa [isEmptyAtom] using empty
  rw [valueEq]
  rfl

theorem classified_empty (reply : ResultPair) : isEmpty classify reply = isEmptyAtom reply.1 := by
  unfold isEmpty classify
  cases isEmptyAtom reply.1 <;> cases isErrorAtom reply.1 <;> rfl

theorem classified_error (reply : ResultPair) : isError classify reply = isErrorAtom reply.1 := by
  unfold isError classify
  cases empty : isEmptyAtom reply.1 with
  | false => cases isErrorAtom reply.1 <;> rfl
  | true => rw [empty_not_error empty]; rfl

theorem classified_success (reply : ResultPair) : isSuccess classify reply = !isEmptyOrError reply.1 := by
  unfold isSuccess classify isEmptyOrError
  cases isEmptyAtom reply.1 <;> cases isErrorAtom reply.1 <;> rfl

/-- The independent two-pass reference and the native three-priority formula
select precisely the same occurrences, not merely equal answer sets. -/
theorem reference_eq_frontier (rows : ResultSet) :
    reference classify rows = HEDispatchDeopt.frontierKeep rows := by
  rw [reference_priority]
  rw [show isSuccess classify = (fun reply => !isEmptyOrError reply.1) from funext classified_success,
    show isError classify = (fun reply => isErrorAtom reply.1) from funext classified_error,
    show isEmpty classify = (fun reply => isEmptyAtom reply.1) from funext classified_empty]
  simp only [HEDispatchDeopt.frontierKeep,
    empty_filter_iff_no_any, Bool.not_not]

def normalize (rows : ResultSet) : ResultSet :=
  let processed := Retired.feed classify rows Retired.initial
  processed.2 ++ (Retired.complete processed.1).2

theorem normalize_eq_frontier (rows : ResultSet) :
    normalize rows = HEDispatchDeopt.frontierKeep rows :=
  (Retired.completed_frontier_refines classify rows).trans (reference_eq_frontier rows)

theorem normalize_eq_model_of_no_empty (rows : ResultSet)
    (noneEmpty : ∀ reply ∈ rows, isEmptyAtom reply.1 = false) :
    normalize rows = HEReturns.keep rows := by
  rw [normalize_eq_frontier]
  exact HEDispatchDeopt.frontierKeep_eq_keep rows noneEmpty

theorem normalize_all_empty (rows : ResultSet)
    (allEmpty : ∀ reply ∈ rows, isEmptyAtom reply.1 = true) :
    normalize rows = rows ∧ HEReturns.keep rows = rows := by
  have errors : ∀ reply ∈ rows, isErrorAtom reply.1 = false :=
    fun reply member => empty_not_error (allEmpty reply member)
  have noGood : rows.filter (fun reply => !isEmptyOrError reply.1) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro reply member
    simp [isEmptyOrError, allEmpty reply member]
  have noErrors : rows.filter (fun reply => isErrorAtom reply.1) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro reply member
    simp [errors reply member]
  have empties : rows.filter (fun reply => isEmptyAtom reply.1) = rows :=
    List.filter_eq_self.mpr allEmpty
  refine ⟨?_, HEReturns.keep_clean errors⟩
  rw [normalize_eq_frontier]
  simp [HEDispatchDeopt.frontierKeep, noGood, noErrors, empties]

theorem model_keeps_empty {rows : ResultSet} {reply : ResultPair}
    (present : reply ∈ rows) (empty : isEmptyAtom reply.1 = true) :
    reply ∈ HEReturns.keep rows := by
  have clean := empty_not_error empty
  have selected : reply ∈ rows.filter (fun current => !isErrorAtom current.1) := by
    simp [present, clean]
  have nonempty : (rows.filter fun current => !isErrorAtom current.1).isEmpty = false :=
    List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem selected)
  simpa [HEReturns.keep, nonempty] using selected

theorem native_drops_empty_of_nonempty {rows : ResultSet} {reply nonempty : ResultPair}
    (empty : isEmptyAtom reply.1 = true) (present : nonempty ∈ rows)
    (different : isEmptyAtom nonempty.1 = false) : reply ∉ normalize rows := by
  rw [normalize_eq_frontier]
  unfold HEDispatchDeopt.frontierKeep
  dsimp only
  have noGood : (fun current : ResultPair => !isEmptyOrError current.1) reply = false := by
    simp [isEmptyOrError, empty]
  have noError := empty_not_error empty
  split
  · simp [noGood]
  · split
    · simp [noError]
    · rename_i noSuccess noErrors
      have successEmpty : rows.filter (fun current => !isEmptyOrError current.1) = [] := by
        simpa using noSuccess
      have errorsEmpty : rows.filter (fun current => isErrorAtom current.1) = [] := by
        simpa using noErrors
      cases failed : isErrorAtom nonempty.1 with
      | false =>
          have member : nonempty ∈ rows.filter (fun current => !isEmptyOrError current.1) := by
            simp [present, isEmptyOrError, different, failed]
          rw [successEmpty] at member
          contradiction
      | true =>
          have member : nonempty ∈ rows.filter (fun current => isErrorAtom current.1) := by
            simp [present, failed]
          rw [errorsEmpty] at member
          contradiction

/-- The exact compatibility condition for these two output policies. It is
not enough that an error exists or that one successful value is available:
any mixture of Empty with a nonempty occurrence distinguishes the policies. -/
theorem native_eq_model_iff (rows : ResultSet) :
    normalize rows = HEReturns.keep rows ↔
      (∀ reply ∈ rows, isEmptyAtom reply.1 = false) ∨
        (∀ reply ∈ rows, isEmptyAtom reply.1 = true) := by
  constructor
  · intro same
    by_cases noEmpty : ∀ reply ∈ rows, isEmptyAtom reply.1 = false
    · exact Or.inl noEmpty
    · right
      push Not at noEmpty
      obtain ⟨emptyReply, present, notFalse⟩ := noEmpty
      have empty : isEmptyAtom emptyReply.1 = true := by cases h : isEmptyAtom emptyReply.1 <;> simp_all
      intro reply member
      cases kind : isEmptyAtom reply.1 with
      | true => rfl
      | false =>
          have kept := model_keeps_empty present empty
          rw [← same] at kept
          exact False.elim (native_drops_empty_of_nonempty empty member kind kept)
  · rintro (noEmpty | allEmpty)
    · exact normalize_eq_model_of_no_empty rows noEmpty
    · obtain ⟨native, model⟩ := normalize_all_empty rows allEmpty
      exact native.trans model.symm

/-- A successful prefix is stable under every future extension of this same
call-node frontier. Its result pairs are never rebuilt from just their atoms. -/
theorem forwarded_prefix_stable (before later : ResultSet) :
    ∃ suffix, normalize (before ++ later) =
      (Retired.feed classify before Retired.initial).2 ++ suffix := by
  rw [normalize_eq_frontier, ← reference_eq_frontier]
  exact Retired.forwarded_prefix_is_stable classify before later

theorem retained_pending_after_success (rows : ResultSet)
    (success : rows.any (fun reply => !isEmptyOrError reply.1) = true) :
    Retired.retainedPending (Retired.feed classify rows Retired.initial).1 = 0 := by
  rw [Retired.retained_pending_exact]
  rw [show isSuccess classify = (fun reply => !isEmptyOrError reply.1) from funext classified_success,
    success]
  rfl

/-- Splitting arrival processing retains exactly the same normalizer state
and newly emitted chronology. This does not close either input prefix. -/
theorem continue_without_replay (before later : ResultSet) (state : Retired.State ResultPair) :
    Retired.feed classify (before ++ later) state =
      let first := Retired.feed classify before state
      let second := Retired.feed classify later first.1
      (second.1, first.2 ++ second.2) :=
  Retired.split_execution classify before later state

/-- If every optional delivery is the derived matched-only boundary, the
whole call node's native selection is unchanged. Selection stays outside
the alternatives; it is not performed separately at each dispatch. -/
theorem matched_deliveries_frontier (space : Space) (dispatch : GroundedDispatch)
    (expected : Atom) (depth : Nat) (live : List Atom) (delivered : ResultSet) :
    normalize (delivered.flatMap fun reply =>
      HEDispatchDeopt.tiered
        (fun call bindings => invoke space dispatch (.ordinary expected) call bindings (depth + 2) live)
        (HEMatchedReturnBoundary.prepared space dispatch expected depth live) reply.1 reply.2) =
      normalize (delivered.flatMap fun reply =>
        invoke space dispatch (.ordinary expected) reply.1 reply.2 (depth + 2) live) := by
  congr 1
  apply List.flatMap_congr
  intro reply _
  exact HEDispatchDeopt.tiered_eq _ _
    (HEMatchedReturnBoundary.prepared_sound space dispatch expected depth live) reply.1 reply.2

namespace Controls

def record (n : Int) : Bindings := Bindings.empty.assign "retained" (.grounded (.int n))
def ok (n : Int) : ResultPair := (.grounded (.int 4), record n)
def empty (n : Int) : ResultPair := (Atom.empty, record n)
def failed (n : Int) : ResultPair := (Atom.error (.symbol "call") (.symbol "BadType"), record n)

theorem equal_values_keep_distinct_records_and_occurrences :
    normalize [empty 0, ok 1, failed 2, ok 3, ok 1] = [ok 1, ok 3, ok 1] := by decide +kernel

theorem fallback_errors_keep_records_and_duplicates :
    normalize [empty 0, failed 1, empty 2, failed 1, failed 3] =
      [failed 1, failed 1, failed 3] := by decide +kernel

theorem all_empty_is_not_no_answer :
    normalize [empty 1, empty 2] = [empty 1, empty 2] ∧ normalize [] = [] := by decide +kernel

theorem errors_wait_for_completion :
    (Retired.feed classify [failed 1, empty 2] Retired.initial).2 = [] ∧
      (Retired.complete (Retired.feed classify [failed 1, empty 2] Retired.initial).1).2 =
        [failed 1] := by decide +kernel

theorem early_close_changes_later_result :
    normalize [failed 1] ++ normalize [ok 2] ≠ normalize [failed 1, ok 2] := by decide +kernel

theorem empty_error_policy_difference :
    normalize [empty 1, failed 2] = [failed 2] ∧
      HEReturns.keep [empty 1, failed 2] = [empty 1] := by decide +kernel

theorem empty_success_policy_difference :
    normalize [empty 1, ok 2] = [ok 2] ∧
      HEReturns.keep [empty 1, ok 2] = [empty 1, ok 2] := by decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEInvocationFrontier
