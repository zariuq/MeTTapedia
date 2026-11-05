import Std

/-!
# Incremental normalization of an HE output frontier

The batch reference removes Empty when any nonempty occurrence exists, then
removes Error when any nonempty, nonerror occurrence exists. The history model
scans completed occurrences into three banks, forwarding successes immediately and
releasing fallback Error/Empty occurrences only at producer completion.

Arrival prefixes permit arbitrary future alternatives. Finite input lists are
reference arrival traces, not requirements to precompute a native frontier.
Payloads may include opaque bindings/delays and are never reconstructed here.
Caller forwarding must be a pure fixed per-occurrence transformation; source
operand/control frontiers remain closed under their separate HE policy.
Classification must be exclusive and stable for each completed occurrence.

The Retired target keeps fallback candidates only until success or completion.
After success it retains no payload in the normalizer state; emitted packets remain
owned by their consumers. Only completed output buffers qualify for this
retirement, never operand/control frontiers or pending computation. Payload
counts below do not establish native root lifetimes, buffer capacity or bytes.

The existing HEProducerCompletion provides separate binary-priority background;
this three-class domain fold does not introduce another generic scheduler.
No source/effect scheduling, native cursor, source debit, classifier, C lifetime
or provider no-replay theorem is asserted.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.HEFrontierNormalization

variable {Value : Type}

inductive Kind where
  | empty
  | error
  | success
  deriving DecidableEq, Repr

def isEmpty (classify : Value → Kind) (row : Value) : Bool := classify row == .empty
def isError (classify : Value → Kind) (row : Value) : Bool := classify row == .error
def isSuccess (classify : Value → Kind) (row : Value) : Bool := classify row == .success

def removeEmpty (classify : Value → Kind) (rows : List Value) : List Value :=
  if rows.any (fun row => !isEmpty classify row) then rows.filter fun row => !isEmpty classify row
  else rows

/-- These are the two ordered whole-frontier passes of the source policy. -/
def reference (classify : Value → Kind) (rows : List Value) : List Value :=
  let nonempty := removeEmpty classify rows
  if nonempty.any (isSuccess classify) then nonempty.filter fun row => !isError classify row
  else nonempty

theorem success_any_after_empty (classify : Value → Kind) (rows : List Value) :
    (removeEmpty classify rows).any (isSuccess classify) = rows.any (isSuccess classify) := by
  cases found : rows.any (fun row => !isEmpty classify row) with
  | false => simp [removeEmpty, found]
  | true =>
      simp only [removeEmpty, found, if_true, List.any_filter]
      apply congrArg (fun predicate => rows.any predicate)
      funext row
      cases classified : classify row <;> simp [isEmpty, isSuccess, classified]

theorem removing_empty_then_error_keeps_successes (classify : Value → Kind) (rows : List Value) :
    (rows.filter fun row => !isEmpty classify row).filter (fun row => !isError classify row) =
      rows.filter (isSuccess classify) := by
  rw [List.filter_filter]
  apply congrArg (fun predicate => rows.filter predicate)
  funext row
  cases classified : classify row <;> simp [isEmpty, isError, isSuccess, classified]

theorem reference_when_success (classify : Value → Kind) (rows : List Value)
    (found : rows.any (isSuccess classify) = true) :
    reference classify rows = rows.filter (isSuccess classify) := by
  obtain ⟨row, member, success⟩ := List.any_eq_true.mp found
  have nonempty : rows.any (fun row => !isEmpty classify row) = true := by
    apply List.any_eq_true.mpr
    refine ⟨row, member, ?_⟩
    cases classified : classify row <;> simp [isSuccess, isEmpty, classified] at *
  simp only [reference, success_any_after_empty, found, if_true]
  rw [removeEmpty, if_pos nonempty]
  exact removing_empty_then_error_keeps_successes classify rows

theorem reference_priority (classify : Value → Kind) (rows : List Value) :
    reference classify rows =
      if rows.any (isSuccess classify) then rows.filter (isSuccess classify)
      else if rows.any (isError classify) then rows.filter (isError classify)
      else rows.filter (isEmpty classify) := by
  cases success : rows.any (isSuccess classify) with
  | true => exact reference_when_success classify rows success
  | false =>
      have noSuccess := List.any_eq_false.mp success
      cases error : rows.any (isError classify) with
      | true =>
          obtain ⟨row, member, failed⟩ := List.any_eq_true.mp error
          have nonempty : rows.any (fun row => !isEmpty classify row) = true := by
            apply List.any_eq_true.mpr
            refine ⟨row, member, ?_⟩
            cases classified : classify row <;> simp [isError, isEmpty, classified] at *
          have selected : rows.filter (fun row => !isEmpty classify row) = rows.filter (isError classify) := by
            apply List.filter_congr
            intro current present
            have absent := noSuccess current present
            cases classified : classify current <;> simp [isSuccess, isEmpty, isError, classified] at *
          simp only [reference, success_any_after_empty, success, Bool.false_eq_true, if_false]
          rw [removeEmpty, if_pos nonempty]
          exact selected
      | false =>
          have noError := List.any_eq_false.mp error
          have allEmpty : ∀ row ∈ rows, classify row = .empty := by
            intro row member
            have absentSuccess := noSuccess row member
            have absentError := noError row member
            cases classified : classify row <;> simp [isSuccess, isError, classified] at *
          have nonempty : rows.any (fun row => !isEmpty classify row) = false := by
            apply List.any_eq_false.mpr
            intro row member
            simp [isEmpty, allEmpty row member]
          have selected : rows.filter (isEmpty classify) = rows := by
            apply List.filter_eq_self.mpr
            intro row member
            simp [isEmpty, allEmpty row member]
          simp only [reference, success_any_after_empty, success, Bool.false_eq_true, if_false]
          simp only [removeEmpty, nonempty, Bool.false_eq_true, if_false]
          exact selected.symm

structure State (Value : Type) where
  successRev : List Value
  errorRev : List Value
  emptyRev : List Value
  closed : Bool
  deriving DecidableEq, Repr

def initial : State Value := ⟨[], [], [], false⟩

/-- This domain transition returns only newly forwarded occurrences. -/
def accept (classify : Value → Kind) (state : State Value) (row : Value) : State Value × List Value :=
  if state.closed then (state, []) else
    match classify row with
    | .success => ({state with successRev := row :: state.successRev}, [row])
    | .error => ({state with errorRev := row :: state.errorRev}, [])
    | .empty => ({state with emptyRev := row :: state.emptyRev}, [])

def feed (classify : Value → Kind) : List Value → State Value → State Value × List Value
  | [], state => (state, [])
  | row :: rest, state =>
      let current := accept classify state row
      let later := feed classify rest current.1
      (later.1, current.2 ++ later.2)

def closeOutput (state : State Value) : List Value :=
  if state.successRev.isEmpty then
    if state.errorRev.isEmpty then state.emptyRev.reverse else state.errorRev.reverse
  else []

def finish (state : State Value) : List Value :=
  if state.successRev.isEmpty then
    if state.errorRev.isEmpty then state.emptyRev.reverse else state.errorRev.reverse
  else state.successRev.reverse

/-- Completion releases only fallback candidates, never prior successes. -/
def complete (state : State Value) : State Value × List Value :=
  if state.closed then (state, []) else ({state with closed := true}, closeOutput state)

def Represents (rows : List Value) (state : State Value) (classify : Value → Kind) : Prop :=
  state.closed = false ∧ state.successRev.reverse = rows.filter (isSuccess classify) ∧
    state.errorRev.reverse = rows.filter (isError classify) ∧
      state.emptyRev.reverse = rows.filter (isEmpty classify)

theorem accept_represents (classify : Value → Kind) (rows : List Value) (state : State Value)
    (represented : Represents rows state classify) (row : Value) :
    Represents (rows ++ [row]) (accept classify state row).1 classify ∧
      (accept classify state row).2 = if isSuccess classify row then [row] else [] := by
  obtain ⟨openState, successes, errors, empties⟩ := represented
  cases classified : classify row <;>
    simp [Represents, accept, openState, classified, isSuccess, isError, isEmpty,
      List.filter_append, List.reverse_cons, successes, errors, empties]

theorem feed_represents (classify : Value → Kind) (before rows : List Value) (state : State Value)
    (represented : Represents before state classify) :
    Represents (before ++ rows) (feed classify rows state).1 classify ∧
      (feed classify rows state).2 = rows.filter (isSuccess classify) := by
  induction rows generalizing before state with
  | nil => exact ⟨by simpa [feed] using represented, rfl⟩
  | cons row rest ih =>
      obtain ⟨first, emitted⟩ := accept_represents classify before state represented row
      obtain ⟨later, tail⟩ := ih (before ++ [row]) (accept classify state row).1 first
      refine ⟨by simpa [feed, List.append_assoc] using later, ?_⟩
      simp only [feed, emitted, tail]
      cases selected : isSuccess classify row <;> simp [selected]

theorem empty_filter_iff_no_any (predicate : Value → Bool) (rows : List Value) :
    (rows.filter predicate).isEmpty = !(rows.any predicate) := by
  induction rows with
  | nil => rfl
  | cons row rest ih => cases selected : predicate row <;> simp [selected, ih]

theorem finish_represents (classify : Value → Kind) (rows : List Value) (state : State Value)
    (represented : Represents rows state classify) : finish state = reference classify rows := by
  obtain ⟨_, successes, errors, empties⟩ := represented
  have reverseEmpty (values : List Value) : values.reverse.isEmpty = values.isEmpty := by
    cases values <;> simp
  have successEmpty := congrArg List.isEmpty successes
  have errorEmpty := congrArg List.isEmpty errors
  simp only [reverseEmpty, empty_filter_iff_no_any] at successEmpty errorEmpty
  rw [reference_priority]
  cases success : rows.any (isSuccess classify) <;> cases error : rows.any (isError classify) <;>
    simp [finish, successEmpty, errorEmpty, success, error, successes, errors, empties]

theorem completion_appends_only_fallback (state : State Value) (openState : state.closed = false) :
    state.successRev.reverse ++ (complete state).2 = finish state := by
  cases successes : state.successRev <;> simp [complete, openState, closeOutput, finish, successes]

theorem completed_frontier_refines (classify : Value → Kind) (rows : List Value) :
    let processed := feed classify rows initial
    processed.2 ++ (complete processed.1).2 = reference classify rows := by
  obtain ⟨represented, emitted⟩ := feed_represents classify [] rows initial (by simp [Represents, initial])
  have normalized := finish_represents classify rows (feed classify rows initial).1 (by simpa using represented)
  have openState := represented.1
  have history : (feed classify rows initial).1.successRev.reverse = rows.filter (isSuccess classify) := by
    simpa using represented.2.1
  dsimp only
  rw [emitted, ← history, completion_appends_only_fallback _ openState, normalized]

/-- Future alternatives cannot invalidate already forwarded successes. -/
theorem success_prefix_is_stable (classify : Value → Kind) (before later : List Value) :
    ∃ suffix, reference classify (before ++ later) = before.filter (isSuccess classify) ++ suffix := by
  cases found : before.any (isSuccess classify) with
  | true =>
      have all : (before ++ later).any (isSuccess classify) = true := by simp [List.any_append, found]
      rw [reference_when_success classify _ all, List.filter_append]
      exact ⟨later.filter (isSuccess classify), rfl⟩
  | false =>
      have none : before.filter (isSuccess classify) = [] := by
        apply List.isEmpty_iff.mp
        simp only [empty_filter_iff_no_any, found, Bool.not_false]
      exact ⟨reference classify (before ++ later), by simp [none]⟩

theorem forwarded_prefix_is_stable (classify : Value → Kind) (before later : List Value) :
    ∃ suffix, reference classify (before ++ later) = (feed classify before initial).2 ++ suffix := by
  have emitted := (feed_represents classify [] before initial (by simp [Represents, initial])).2
  rw [emitted]
  exact success_prefix_is_stable classify before later

theorem split_execution (classify : Value → Kind) (first later : List Value) (state : State Value) :
    feed classify (first ++ later) state =
      let before := feed classify first state
      let after := feed classify later before.1
      (after.1, before.2 ++ after.2) := by
  induction first generalizing state with
  | nil => simp [feed]
  | cons row rest ih => simp [feed, ih, List.append_assoc]

/-- A processing allowance partitions arrivals; the retained domain state
and exact output chronology agree with processing the same trace at once. -/
theorem split_at_allowance (classify : Value → Kind) (allowance : Nat)
    (rows : List Value) (state : State Value) :
    feed classify rows state =
      let before := feed classify (rows.take allowance) state
      let after := feed classify (rows.drop allowance) before.1
      (after.1, before.2 ++ after.2) := by
  simpa only [List.take_append_drop] using
    split_execution classify (rows.take allowance) (rows.drop allowance) state

theorem completion_is_idempotent (state : State Value) :
    complete (complete state).1 = ((complete state).1, []) := by
  cases closed : state.closed <;> simp [complete, closed]

theorem completed_state_rejects_new_arrivals (classify : Value → Kind) (rows : List Value)
    (state : State Value) (closed : state.closed = true) : feed classify rows state = (state, []) := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp [feed, accept, closed, ih]

namespace Retired

/-- No field stores an emitted successful payload or a publication history. -/
structure State (Value : Type) where
  errorRev : List Value
  emptyRev : List Value
  hasSuccess : Bool
  closed : Bool
  deriving DecidableEq, Repr

def initial : State Value := ⟨[], [], false, false⟩

def accept (classify : Value → Kind) (state : State Value) (row : Value) : State Value × List Value :=
  if state.closed then (state, []) else
    match classify row with
    | .success => ({state with errorRev := [], emptyRev := [], hasSuccess := true}, [row])
    | .error => if state.hasSuccess then (state, [])
        else ({state with errorRev := row :: state.errorRev}, [])
    | .empty => if state.hasSuccess then (state, [])
        else ({state with emptyRev := row :: state.emptyRev}, [])

def feed (classify : Value → Kind) : List Value → State Value → State Value × List Value
  | [], state => (state, [])
  | row :: rest, state =>
      let current := accept classify state row
      let later := feed classify rest current.1
      (later.1, current.2 ++ later.2)

def complete (state : State Value) : State Value × List Value :=
  if state.closed then (state, []) else
    let output := if state.hasSuccess then []
      else if state.errorRev.isEmpty then state.emptyRev.reverse else state.errorRev.reverse
    ({state with errorRev := [], emptyRev := [], closed := true}, output)

/-- Closed or successful histories make both fallback banks unobservable.
Otherwise every pending occurrence, including its opaque context, is retained. -/
def Relates (history : HEFrontierNormalization.State Value) (state : State Value) : Prop :=
  state.closed = history.closed ∧ state.hasSuccess = !history.successRev.isEmpty ∧
    state.errorRev = (if history.closed || !history.successRev.isEmpty then [] else history.errorRev) ∧
      state.emptyRev = (if history.closed || !history.successRev.isEmpty then [] else history.emptyRev)

theorem initial_relates : Relates (HEFrontierNormalization.initial : HEFrontierNormalization.State Value) initial := by
  simp [Relates, HEFrontierNormalization.initial, initial]

theorem accept_refines (classify : Value → Kind) (history : HEFrontierNormalization.State Value)
    (state : State Value) (related : Relates history state) (row : Value) :
    Relates (HEFrontierNormalization.accept classify history row).1 (accept classify state row).1 ∧
      (accept classify state row).2 = (HEFrontierNormalization.accept classify history row).2 := by
  rcases history with ⟨successes, errors, empties, closed⟩
  rcases state with ⟨pendingErrors, pendingEmpties, seen, retiredClosed⟩
  change retiredClosed = closed ∧ seen = !successes.isEmpty ∧
    pendingErrors = (if closed || !successes.isEmpty then [] else errors) ∧
      pendingEmpties = (if closed || !successes.isEmpty then [] else empties) at related
  obtain ⟨rfl, rfl, rfl, rfl⟩ := related
  cases retiredClosed <;> cases successes <;> cases classified : classify row <;>
    simp [Relates, accept, HEFrontierNormalization.accept, classified]

theorem feed_refines (classify : Value → Kind) (rows : List Value)
    (history : HEFrontierNormalization.State Value) (state : State Value)
    (related : Relates history state) :
    Relates (HEFrontierNormalization.feed classify rows history).1 (feed classify rows state).1 ∧
      (feed classify rows state).2 = (HEFrontierNormalization.feed classify rows history).2 := by
  induction rows generalizing history state with
  | nil => exact ⟨related, rfl⟩
  | cons row rest ih =>
      obtain ⟨next, emitted⟩ := accept_refines classify history state related row
      obtain ⟨later, remaining⟩ := ih _ _ next
      exact ⟨later, by simp only [feed, HEFrontierNormalization.feed, emitted, remaining]⟩

theorem complete_refines (history : HEFrontierNormalization.State Value) (state : State Value)
    (related : Relates history state) :
    Relates (HEFrontierNormalization.complete history).1 (complete state).1 ∧
      (complete state).2 = (HEFrontierNormalization.complete history).2 := by
  rcases history with ⟨successes, errors, empties, closed⟩
  rcases state with ⟨pendingErrors, pendingEmpties, seen, retiredClosed⟩
  change retiredClosed = closed ∧ seen = !successes.isEmpty ∧
    pendingErrors = (if closed || !successes.isEmpty then [] else errors) ∧
      pendingEmpties = (if closed || !successes.isEmpty then [] else empties) at related
  obtain ⟨rfl, rfl, rfl, rfl⟩ := related
  cases retiredClosed <;> cases successes <;>
    simp [Relates, complete, HEFrontierNormalization.complete, HEFrontierNormalization.closeOutput]

theorem completed_frontier_refines (classify : Value → Kind) (rows : List Value) :
    let processed := feed classify rows initial
    processed.2 ++ (complete processed.1).2 = reference classify rows := by
  obtain ⟨related, emitted⟩ := feed_refines classify rows HEFrontierNormalization.initial initial initial_relates
  have closing := (complete_refines _ _ related).2
  dsimp only
  rw [emitted, closing]
  exact HEFrontierNormalization.completed_frontier_refines classify rows

theorem forwarded_prefix_is_stable (classify : Value → Kind) (before later : List Value) :
    ∃ suffix, reference classify (before ++ later) = (feed classify before initial).2 ++ suffix := by
  rw [(feed_refines classify before HEFrontierNormalization.initial initial initial_relates).2]
  exact HEFrontierNormalization.forwarded_prefix_is_stable classify before later

theorem split_execution (classify : Value → Kind) (first later : List Value) (state : State Value) :
    feed classify (first ++ later) state =
      let before := feed classify first state
      let after := feed classify later before.1
      (after.1, before.2 ++ after.2) := by
  induction first generalizing state with
  | nil => simp [feed]
  | cons row rest ih => simp [feed, ih, List.append_assoc]

theorem split_at_allowance (classify : Value → Kind) (allowance : Nat)
    (rows : List Value) (state : State Value) :
    feed classify rows state =
      let before := feed classify (rows.take allowance) state
      let after := feed classify (rows.drop allowance) before.1
      (after.1, before.2 ++ after.2) := by
  simpa only [List.take_append_drop] using
    split_execution classify (rows.take allowance) (rows.drop allowance) state

theorem completion_is_idempotent (state : State Value) :
    complete (complete state).1 = ((complete state).1, []) := by
  cases closed : state.closed <;> simp [complete, closed]

theorem completed_state_rejects_new_arrivals (classify : Value → Kind) (rows : List Value)
    (state : State Value) (closed : state.closed = true) : feed classify rows state = (state, []) := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp [feed, accept, closed, ih]

def retainedPending (state : State Value) : Nat := state.errorRev.length + state.emptyRev.length

/-- Retained payloads are the fallback candidates before success.
No emitted output list is included in the target state. -/
theorem retained_state_exact (classify : Value → Kind) (rows : List Value) :
    let state := (feed classify rows initial).1
    state.closed = false ∧ state.hasSuccess = rows.any (isSuccess classify) ∧
      state.errorRev.reverse = (if rows.any (isSuccess classify) then [] else rows.filter (isError classify)) ∧
        state.emptyRev.reverse = (if rows.any (isSuccess classify) then [] else rows.filter (isEmpty classify)) := by
  obtain ⟨related, _⟩ := feed_refines classify rows HEFrontierNormalization.initial initial initial_relates
  have history : Represents rows (HEFrontierNormalization.feed classify rows HEFrontierNormalization.initial).1 classify := by
    simpa using (feed_represents classify [] rows HEFrontierNormalization.initial
      (by simp [Represents, HEFrontierNormalization.initial])).1
  obtain ⟨openState, successes, errors, empties⟩ := history
  have reverseEmpty (values : List Value) : values.reverse.isEmpty = values.isEmpty := by cases values <;> simp
  have successEmpty := congrArg List.isEmpty successes
  simp only [reverseEmpty, empty_filter_iff_no_any] at successEmpty
  obtain ⟨closed, seen, pendingErrors, pendingEmpties⟩ := related
  dsimp only
  refine ⟨closed.trans openState, ?_, ?_, ?_⟩
  · simp [seen, successEmpty]
  · rw [pendingErrors, openState, successEmpty]
    cases rows.any (isSuccess classify) <;> simp [errors]
  · rw [pendingEmpties, openState, successEmpty]
    cases rows.any (isSuccess classify) <;> simp [empties]

theorem special_partition_length (classify : Value → Kind) (rows : List Value)
    (absent : rows.any (isSuccess classify) = false) :
    (rows.filter (isError classify)).length + (rows.filter (isEmpty classify)).length = rows.length := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      cases classified : classify row with
      | success => simp [isSuccess, classified] at absent
      | error =>
          have later := ih (by simpa [isSuccess, classified] using absent)
          simp [isError, isEmpty, classified] at later ⊢
          omega
      | empty =>
          have later := ih (by simpa [isSuccess, classified] using absent)
          simp [isError, isEmpty, classified] at later ⊢
          omega

/-- This is an exact payload-count bound for the persistent normalizer state,
not a byte/RSS bound or a claim about consumer/producer/caller roots. -/
theorem retained_pending_exact (classify : Value → Kind) (rows : List Value) :
    retainedPending (feed classify rows initial).1 =
      if rows.any (isSuccess classify) then 0 else rows.length := by
  obtain ⟨_, _, errors, empties⟩ := retained_state_exact classify rows
  have errorCount := congrArg List.length errors
  have emptyCount := congrArg List.length empties
  simp only [List.length_reverse] at errorCount emptyCount
  unfold retainedPending
  cases found : rows.any (isSuccess classify) with
  | true =>
      simp only [found, if_true, List.length_nil] at errorCount emptyCount ⊢
      omega
  | false =>
      simp [found] at errorCount emptyCount ⊢
      rw [errorCount, emptyCount]
      exact special_partition_length classify rows found

theorem state_after_success_has_no_payloads (classify : Value → Kind) (rows : List Value)
    (found : rows.any (isSuccess classify) = true) :
    (feed classify rows initial).1 = ⟨[], [], true, false⟩ := by
  obtain ⟨closed, seen, errors, empties⟩ := retained_state_exact classify rows
  have noErrors := List.reverse_eq_nil_iff.mp (by simpa [found] using errors)
  have noEmpties := List.reverse_eq_nil_iff.mp (by simpa [found] using empties)
  cases current : (feed classify rows initial).1
  simp_all

theorem completion_retires_pending (classify : Value → Kind) (rows : List Value) :
    retainedPending (complete (feed classify rows initial).1).1 = 0 := by
  have openState := (retained_state_exact classify rows).1
  simp [complete, openState, retainedPending]

end Retired

namespace Controls

inductive Sample where
  | empty (payload : Nat)
  | error (payload : Nat)
  | success (payload : Nat)
  deriving DecidableEq, Repr

def classify : Sample → Kind
  | .empty _ => .empty
  | .error _ => .error
  | .success _ => .success

theorem premature_error_is_not_a_stable_prefix :
    reference classify [.error 7, .success 1] = [.success 1] ∧
      ¬ ∃ suffix, reference classify [.error 7, .success 1] = [.error 7] ++ suffix := by
  constructor
  · decide
  · rintro ⟨suffix, same⟩
    change [Sample.success 1] = Sample.error 7 :: suffix at same
    cases same

theorem successes_keep_order_and_duplicates :
    (feed classify [.empty 0, .success 2, .error 7, .success 2, .success 1] initial).2 =
      [.success 2, .success 2, .success 1] := by decide

theorem lost_duplicate_is_observable :
    (feed classify [.success 2, .success 2] initial).2 ≠ [.success 2] := by decide

theorem errors_displace_empty_without_deduplication :
    (complete (feed classify [.empty 0, .error 7, .empty 1, .error 7, .error 9] initial).1).2 =
      [.error 7, .error 7, .error 9] := by decide

theorem only_empty_occurrences_survive_and_zero_frontier_stays_zero :
    reference classify [.empty 1, .empty 1, .empty 2] = [.empty 1, .empty 1, .empty 2] ∧
      reference classify [] = [] := by decide

theorem specials_at_end_are_not_dropped :
    (complete (feed classify [.error 7] initial).1).2 = [.error 7] ∧
      (complete (feed classify [.empty 3] initial).1).2 = [.empty 3] := by decide

theorem no_fallback_is_released_before_completion :
    (feed classify [.empty 3, .error 7] initial).2 = [] ∧
      (complete (feed classify [.empty 3, .error 7] initial).1).2 = [.error 7] := by decide

theorem finalization_does_not_republish_successes :
    (feed classify [.success 1, .error 7] initial).2 = [.success 1] ∧
      (complete (feed classify [.success 1, .error 7] initial).1).2 = [] := by decide

theorem future_alternatives_extend_an_open_output_prefix :
    let earlier := feed classify [.error 7, .success 1] initial
    let later := feed classify [.empty 3, .success 2] earlier.1
    earlier.2 = [.success 1] ∧ earlier.1.closed = false ∧ later.2 = [.success 2] ∧
      (complete later.1).2 = [] := by decide

theorem opaque_context_and_delays_remain_attached :
    (feed (fun row : Sample × Nat × Option Nat => classify row.1)
      [(.success 1, 11, some 5), (.error 7, 22, none),
       (.success 1, 11, some 5), (.success 1, 13, none)] initial).2 =
        [(.success 1, 11, some 5), (.success 1, 11, some 5), (.success 1, 13, none)] := by decide

/-- This mutant has the correct new output but keeps dead fallback payloads. -/
def omitRetirement (state : Retired.State Sample) (row : Sample) : Retired.State Sample × List Sample :=
  if state.closed then (state, []) else
    match classify row with
    | .success => ({state with hasSuccess := true}, [row])
    | _ => Retired.accept classify state row

theorem omitted_retirement_is_not_caught_by_output_alone :
    let pending := (Retired.feed classify [.error 7, .empty 3] Retired.initial).1
    let faulty := omitRetirement pending (.success 1)
    let correct := Retired.accept classify pending (.success 1)
    faulty.2 = correct.2 ∧ Retired.retainedPending faulty.1 = 2 ∧
      Retired.retainedPending correct.1 = 0 ∧ faulty.1 ≠ correct.1 := by decide

theorem first_success_retires_prior_fallbacks :
    let processed := Retired.feed classify [.error 7, .empty 3, .success 1] Retired.initial
    processed.2 = [.success 1] ∧ processed.1 = ⟨[], [], true, false⟩ ∧
      (Retired.complete processed.1).2 = [] := by decide

theorem later_specials_do_not_retain_new_payloads :
    let processed := Retired.feed classify [.success 1, .error 7, .empty 3, .success 2] Retired.initial
    processed.2 = [.success 1, .success 2] ∧ processed.1 = ⟨[], [], true, false⟩ := by decide

theorem distinct_emitted_histories_have_the_same_payload_free_state :
    (Retired.feed classify [.success 1, .success 2] Retired.initial).1 =
      (Retired.feed classify [.success 999] Retired.initial).1 ∧
    (Retired.feed classify [.success 1, .success 2] Retired.initial).2 = [.success 1, .success 2] ∧
      (Retired.feed classify [.success 999] Retired.initial).2 = [.success 999] := by decide

theorem pending_specials_keep_multiplicity_until_completion :
    let processed := Retired.feed classify [.error 7, .empty 3, .error 7] Retired.initial
    processed.2 = [] ∧ Retired.retainedPending processed.1 = 3 ∧
      (Retired.complete processed.1).2 = [.error 7, .error 7] ∧
        Retired.retainedPending (Retired.complete processed.1).1 = 0 := by decide

theorem empty_fallbacks_are_retired_after_being_emitted :
    let processed := Retired.feed classify [.empty 1, .empty 1] Retired.initial
    (Retired.complete processed.1).2 = [.empty 1, .empty 1] ∧
      Retired.retainedPending (Retired.complete processed.1).1 = 0 ∧
        (Retired.complete (Retired.complete processed.1).1).2 = [] := by decide

theorem split_across_first_success_keeps_outputs_and_retires_pending :
    let earlier := Retired.feed classify [.error 7, .empty 3] Retired.initial
    let later := Retired.feed classify [.success 1, .error 9, .success 1] earlier.1
    earlier.2 = [] ∧ Retired.retainedPending earlier.1 = 2 ∧
      later.2 = [.success 1, .success 1] ∧ Retired.retainedPending later.1 = 0 := by decide

theorem opaque_pending_carriers_are_kept_until_unobservable :
    let inspect := fun row : Sample × Nat × Option Nat => classify row.1
    let pending := (Retired.feed inspect [(.error 7, 22, some 5), (.empty 3, 23, none)] Retired.initial).1
    let next := Retired.accept inspect pending (.success 1, 11, some 9)
    pending.errorRev = [(.error 7, 22, some 5)] ∧ pending.emptyRev = [(.empty 3, 23, none)] ∧
      next.2 = [(.success 1, 11, some 9)] ∧ Retired.retainedPending next.1 = 0 := by decide

end Controls
end Mettapedia.Machines.HEFrontierNormalization
