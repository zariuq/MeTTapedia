import Mettapedia.Languages.MeTTa.TermView

/-!
# Support-directed scalar observation before structural matching

The source pattern determines which query child supplies one guard slot.
Exact source support selects its first occurrence; only that structural spine
is observed. An unresolved demanded child declines, even if a later occurrence
is already known. Unrelated query fields may remain open.

The observation theorem is proved from structural instantiation and open
substitution, rather than assuming that a projected slot is stable. Its guard
corollary removes only an empty contribution, preserving every answer
occurrence. Physical adapters must separately establish ordinary structural
matching, scalar interpretation, current source authority, ownership, and the
absence of observable matching effects. This module admits integer leaves;
floating-point and foreign values require their own interpretation boundary.
The answer theorem concerns finite structural match occurrences. Skipping an
effectful or diverging head computation needs a stronger observation contract.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GuardSupportProjectionCompilation

open CompiledPlanAdmission
open CompiledPlanActivationViewCompilation
open CompiledPlanOpenActivationViewCompilation
open Mettapedia.Languages.MeTTa.TermViewCompilation

def sourceArity : Terms -> Nat
  | .nil => 0
  | .cons _ tail => 1 + sourceArity tail

def queryArity : OpenTerms -> Nat
  | .nil => 0
  | .cons _ tail => 1 + queryArity tail

/-- Read one known scalar without forcing an open term. -/
def integer? : OpenTerm -> Option Int64
  | .integer value => some value
  | _ => none

mutual

/-- Follow the first authored occurrence of a slot. The exact support test is
the semantic counterpart of a compiled subtree variable mask. -/
def projectSlot? (slot : UInt32) : Term -> OpenTerm -> Option Int64
  | .variable sourceSlot, query =>
      if sourceSlot = slot then integer? query else none
  | .application sourceHead sources, .application queryHead queries =>
      if sourceHead = queryHead ∧ sourceArity sources = queryArity queries then
        projectSlotTerms? slot sources queries
      else none
  | _, _ => none

def projectSlotTerms? (slot : UInt32) : Terms -> OpenTerms -> Option Int64
  | .cons sourceHead sourceTail, .cons queryHead queryTail =>
      if slot ∈ usedSlots sourceHead then
        projectSlot? slot sourceHead queryHead
      else
        projectSlotTerms? slot sourceTail queryTail
  | _, _ => none

end

mutual

/-- Success names a real source occurrence. A support mask cannot invent a
slot that is absent from its pattern. -/
theorem projectSlot?_used
    (slot : UInt32) (source : Term) (query : OpenTerm) (value : Int64)
    (observed : projectSlot? slot source query = some value) :
    slot ∈ usedSlots source := by
  cases source with
  | symbol name => simp [projectSlot?] at observed
  | string text => simp [projectSlot?] at observed
  | integer number => simp [projectSlot?] at observed
  | «variable» sourceSlot =>
      simp only [projectSlot?] at observed
      split at observed
      · rename_i same
        simp [usedSlots, same]
      · contradiction
  | application sourceHead sources =>
      cases query <;> simp only [projectSlot?] at observed
      all_goals try contradiction
      split at observed
      · exact projectSlotTerms?_used slot sources _ value observed
      · contradiction

theorem projectSlotTerms?_used
    (slot : UInt32) (sources : Terms) (queries : OpenTerms) (value : Int64)
    (observed : projectSlotTerms? slot sources queries = some value) :
    slot ∈ usedSlotsTerms sources := by
  cases sources with
  | nil => cases queries <;> simp [projectSlotTerms?] at observed
  | cons sourceHead sourceTail =>
      cases queries with
      | nil => simp [projectSlotTerms?] at observed
      | cons queryHead queryTail =>
          simp only [projectSlotTerms?] at observed
          split at observed
          · rename_i used
            simp [usedSlotsTerms, used]
          · have used :=
              projectSlotTerms?_used slot sourceTail queryTail value observed
            simp [usedSlotsTerms, used]

end

private theorem integer?_substitution
    (substitution : OpenSubstitution) (query : OpenTerm) (value : Int64)
    (observed : integer? query = some value) :
    substituteOpen substitution query = .integer value := by
  cases query <;> simp [integer?] at observed
  case integer number =>
    cases observed
    rfl

mutual

/-- Every structural match assigns an observed guard slot the same integer.
The unobserved fields may contain arbitrary open logic variables. Repeated
source variables retain all of their matching equations. -/
theorem projectSlot?_sound
    (slot : UInt32) (source : Term) (query : OpenTerm) (value : Int64)
    (generation : UInt32) (environment : OpenEnvironment)
    (substitution : OpenSubstitution)
    (observed : projectSlot? slot source query = some value)
    (matched : instantiateOpen generation environment source =
      substituteOpen substitution query) :
    environment slot = some (.integer value) := by
  cases source with
  | symbol name => simp [projectSlot?] at observed
  | string text => simp [projectSlot?] at observed
  | integer number => simp [projectSlot?] at observed
  | «variable» sourceSlot =>
      simp only [projectSlot?] at observed
      split at observed
      · rename_i same
        subst sourceSlot
        rw [integer?_substitution substitution query value observed] at matched
        simp only [instantiateOpen] at matched
        cases present : environment slot with
        | none => simp [present] at matched
        | some bound => simpa [present] using matched
      · contradiction
  | application sourceHead sources =>
      cases query <;> simp only [projectSlot?] at observed
      all_goals try contradiction
      case application queryHead queries =>
        split at observed
        · simp only [instantiateOpen, substituteOpen,
            OpenTerm.application.injEq] at matched
          exact projectSlotTerms?_sound slot sources queries value
            generation environment substitution observed matched.2
        · contradiction

theorem projectSlotTerms?_sound
    (slot : UInt32) (sources : Terms) (queries : OpenTerms) (value : Int64)
    (generation : UInt32) (environment : OpenEnvironment)
    (substitution : OpenSubstitution)
    (observed : projectSlotTerms? slot sources queries = some value)
    (matched : instantiateOpenTerms generation environment sources =
      substituteOpenTerms substitution queries) :
    environment slot = some (.integer value) := by
  cases sources with
  | nil => cases queries <;> simp [projectSlotTerms?] at observed
  | cons sourceHead sourceTail =>
      cases queries with
      | nil => simp [projectSlotTerms?] at observed
      | cons queryHead queryTail =>
          simp only [instantiateOpenTerms, substituteOpenTerms,
            OpenTerms.cons.injEq] at matched
          simp only [projectSlotTerms?] at observed
          split at observed
          · exact projectSlot?_sound slot sourceHead queryHead value
              generation environment substitution observed matched.1
          · exact projectSlotTerms?_sound slot sourceTail queryTail value
              generation environment substitution observed matched.2

end

/-- The sparse environment contains only integers obtained by source-directed
observation. It records no solution for the remaining logical bindings. -/
def projectedEnvironment (source : Term) (query : OpenTerm) : OpenEnvironment :=
  fun slot => (projectSlot? slot source query).map OpenTerm.integer

/-- All guard slots being observable is a decidable admission condition.
The existing frozen-support law is reused at the projected environment. -/
def guardReady? (source guard : Term) (query : OpenTerm) : Bool :=
  frozen? (projectedEnvironment source query) guard

/-- Support-directed observations agree with every successful matching
environment on the guard's entire support. -/
theorem projectedEnvironment_agrees
    (source guard : Term) (query : OpenTerm) (generation : UInt32)
    (environment : OpenEnvironment) (substitution : OpenSubstitution)
    (ready : guardReady? source guard query = true)
    (matched : instantiateOpen generation environment source =
      substituteOpen substitution query) :
    AgreesOn guard (projectedEnvironment source query) environment := by
  intro slot used
  obtain ⟨bound, observed⟩ :=
    frozen?_sound (projectedEnvironment source query) guard ready slot used
  cases projected : projectSlot? slot source query with
  | none => simp [projectedEnvironment, projected] at observed
  | some value =>
      have assigned := projectSlot?_sound slot source query value
        generation environment substitution projected matched
      simp [projectedEnvironment, projected, assigned]

/-- A total pure guard sees the same instantiated term before and after the
remaining structural match. This derives its invariant from the actual
projection algorithm, rather than postulating a guard-stability certificate. -/
theorem guard_observation_eq
    (source guard : Term) (query : OpenTerm) (generation : UInt32)
    (environment : OpenEnvironment) (substitution : OpenSubstitution)
    (ready : guardReady? source guard query = true)
    (matched : instantiateOpen generation environment source =
      substituteOpen substitution query) :
    instantiateOpen generation (projectedEnvironment source query) guard =
      instantiateOpen generation environment guard :=
  instantiateOpen_eq_of_agreesOn generation
    (projectedEnvironment source query) environment guard
    (projectedEnvironment_agrees source guard query generation environment
      substitution ready matched)

/-! ## Empty contributions and answer occurrences -/

/-- An unresolved guard is a decline, not a false guard or an empty answer. -/
def guardValue? (source guard : Term) (query : OpenTerm)
    (generation : UInt32) (evaluate : OpenTerm -> Bool) : Option Bool :=
  if guardReady? source guard query then
    some (evaluate
      (instantiateOpen generation (projectedEnvironment source query) guard))
  else none

theorem guardValue?_sound
    (source guard : Term) (query : OpenTerm) (generation : UInt32)
    (evaluate : OpenTerm -> Bool) (result : Bool)
    (environment : OpenEnvironment) (substitution : OpenSubstitution)
    (observed : guardValue? source guard query generation evaluate = some result)
    (matched : instantiateOpen generation environment source =
      substituteOpen substitution query) :
    evaluate (instantiateOpen generation environment guard) = result := by
  simp only [guardValue?] at observed
  split at observed
  · rename_i ready
    rw [guard_observation_eq source guard query generation environment
      substitution ready matched] at observed
    exact Option.some.inj observed
  · contradiction

/-- One occurrence of a successful structural match. Distinct occurrences
may have equal environments; the answer sequence does not deduplicate them. -/
structure MatchOccurrence where
  environment : OpenEnvironment
  substitution : OpenSubstitution

def Matches (source : Term) (query : OpenTerm) (generation : UInt32)
    (occurrence : MatchOccurrence) : Prop :=
  instantiateOpen generation occurrence.environment source =
    substituteOpen occurrence.substitution query

/-- The authored guard has one empty branch and one arbitrary answer body.
`emptyWhen` chooses which Boolean result selects the empty branch. -/
def guardedAnswers {Answer : Type}
    (guard : Term) (generation : UInt32) (evaluate : OpenTerm -> Bool)
    (emptyWhen : Bool) (body : OpenEnvironment -> List Answer)
    (occurrences : List MatchOccurrence) : List Answer :=
  occurrences.flatMap fun occurrence =>
    if evaluate (instantiateOpen generation occurrence.environment guard) =
        emptyWhen then
      []
    else body occurrence.environment

/-- The source-directed observer skips the match search only when it proves
that every matching occurrence contributes the authored empty branch. -/
def earlyGuardedAnswers {Answer : Type}
    (source guard : Term) (query : OpenTerm) (generation : UInt32)
    (evaluate : OpenTerm -> Bool) (emptyWhen : Bool)
    (body : OpenEnvironment -> List Answer)
    (occurrences : List MatchOccurrence) : List Answer :=
  if guardValue? source guard query generation evaluate = some emptyWhen then
    []
  else guardedAnswers guard generation evaluate emptyWhen body occurrences

/-- Early empty-guard pruning preserves the complete answer-occurrence list.
This is stronger than bag preservation for this one local rewrite; it does
not impose a global answer enumeration order on the source language. -/
theorem earlyGuardedAnswers_eq {Answer : Type}
    (source guard : Term) (query : OpenTerm) (generation : UInt32)
    (evaluate : OpenTerm -> Bool) (emptyWhen : Bool)
    (body : OpenEnvironment -> List Answer)
    (occurrences : List MatchOccurrence)
    (sound : ∀ occurrence ∈ occurrences,
      Matches source query generation occurrence) :
    earlyGuardedAnswers source guard query generation evaluate emptyWhen
        body occurrences =
      guardedAnswers guard generation evaluate emptyWhen body occurrences := by
  unfold earlyGuardedAnswers
  split
  · rename_i observed
    induction occurrences with
    | nil => rfl
    | cons occurrence rest inductionHypothesis =>
        have same := guardValue?_sound source guard query generation evaluate
          emptyWhen occurrence.environment occurrence.substitution observed
          (sound occurrence (by simp))
        have tailSound : ∀ member ∈ rest,
            Matches source query generation member := by
          intro member present
          exact sound member (by simp [present])
        simpa [guardedAnswers, same] using inductionHypothesis tailSound
  · rfl

/-! ## Discriminating examples -/

namespace Canaries

private def nestedSource : Term :=
  .application [10]
    (.cons (.application [11] (.cons (.variable 0) .nil))
      (.cons (.variable 1) .nil))

private def nestedQuery : OpenTerm :=
  .application [10]
    (.cons (.application [11] (.cons (.integer 2) .nil))
      (.cons (.variable { generation := 7, slot := 8 }) .nil))

private def largerThanTwo : Term :=
  .application [12] (.cons (.integer 2) (.cons (.variable 0) .nil))

private def integerLess : OpenTerm -> Bool
  | .application [12] (.cons (.integer left) (.cons (.integer right) .nil)) =>
      left < right
  | _ => false

/-- Nested source support can supply a guard while another query field is
still a generation-qualified logic variable. -/
theorem nested_open_sibling_observed :
    projectSlot? 0 nestedSource nestedQuery = some 2 := by
  decide

theorem nested_false_guard_observed :
    guardValue? nestedSource largerThanTwo nestedQuery 9 integerLess =
      some false := by
  decide

/-- Demanding the still-open field declines; an unknown integer is not zero. -/
theorem demanded_unknown_declines :
    projectSlot? 1 nestedSource nestedQuery = none := by
  decide

theorem unresolved_guard_is_not_false :
    guardValue? nestedSource (.variable 1) nestedQuery 9 integerLess = none ∧
      guardValue? nestedSource (.variable 1) nestedQuery 9 integerLess ≠
        some false := by
  decide

private def repeatedSource : Term :=
  .application [13] (.cons (.variable 0) (.cons (.variable 0) .nil))

/-- One known first occurrence is sufficient for a safe rejection even when
the later repeated occurrence still requires ordinary unification. -/
theorem repeated_slot_first_observed :
    projectSlot? 0 repeatedSource
      (.application [13] (.cons (.integer 2)
        (.cons (.variable { generation := 7, slot := 8 }) .nil))) =
      some 2 := by
  decide

/-- The implementation uses the first support path deterministically. It does
not try a later occurrence when the selected one is unresolved. -/
theorem repeated_slot_unknown_first_declines :
    projectSlot? 0 repeatedSource
      (.application [13]
        (.cons (.variable { generation := 7, slot := 8 })
          (.cons (.integer 2) .nil))) = none := by
  decide

/-- Observing one repeated slot does not establish a successful head match:
two inconsistent rigid occurrences still cannot match any environment. -/
theorem repeated_slot_conflict_has_no_match
    (generation : UInt32) (environment : OpenEnvironment) :
    instantiateOpen generation environment repeatedSource ≠
      .application [13] (.cons (.integer 2) (.cons (.integer 3) .nil)) := by
  intro matched
  simp only [repeatedSource, instantiateOpen, instantiateOpenTerms,
    OpenTerm.application.injEq, OpenTerms.cons.injEq] at matched
  cases present : environment 0 with
  | none => simp [present] at matched
  | some value =>
      simp [present] at matched
      have distinct : OpenTerm.integer 2 ≠ .integer 3 := by decide
      exact distinct (matched.1.symm.trans matched.2)

/-- A missing child and a different rigid head both decline before observing
the sought slot. Neither shape is treated as an empty successful match. -/
theorem incompatible_spines_decline :
    projectSlot? 0 nestedSource
      (.application [10]
        (.cons (.application [11] (.cons (.integer 2) .nil)) .nil)) = none ∧
    projectSlot? 0 nestedSource
      (.application [10]
        (.cons (.application [99] (.cons (.integer 2) .nil))
          (.cons (.integer 3) .nil))) = none := by
  decide

end Canaries

#print axioms projectSlot?_sound
#print axioms projectedEnvironment_agrees
#print axioms guard_observation_eq
#print axioms guardValue?_sound
#print axioms earlyGuardedAnswers_eq
#print axioms Canaries.repeated_slot_conflict_has_no_match

end Mettapedia.GSLT.LanguageDef.GuardSupportProjectionCompilation
