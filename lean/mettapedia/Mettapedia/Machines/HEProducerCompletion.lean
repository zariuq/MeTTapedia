import Mettapedia.Machines.OrderedProtocol
import Mettapedia.Machines.ResumableRegion

/-!
# HE preferred-success producer completion

The independent batch reference normalizes an already completed finite frontier.
The incremental implementation streams successes and retains fallback errors.
Both buffered readout and the empty-bank last-alternative shortcut use the same
visibility predicate. An empty bank need not mean that no success was published.

Input occurrences have already passed the owning dialect's omission checks.
Classification is supplied over the complete occurrence carrier, so bindings,
delayed checks and native fault payloads can remain opaque parts of each value.
This is pure, unmetered whole-frontier completion. It neither identifies early
stream prefixes or effectful consumers with batch execution nor certifies source
exhaustion, source charging, native classifier correctness or provider no-replay.
The physical processing bounds count this completion adapter's transitions.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HEProducerCompletion

variable {Value Other : Type}

/-- The source first asks the whole frontier whether any success exists. -/
def reference (isError : Value → Bool) (prefer : Bool) (rows : List Value) : List Value :=
  if prefer && rows.any (fun row => !isError row) then
    rows.filter fun row => !isError row
  else rows

/-- The same presentation decision is consumed by buffered and direct paths. -/
def visible (isError : Value → Bool) (prefer hasSuccess : Bool) (row : Value) : Bool :=
  !(prefer && hasSuccess && isError row)

structure Bank (Value : Type) where
  streamedRev : List Value
  fallbackRev : List Value
  hasSuccess : Bool
  deriving DecidableEq, Repr

def empty : Bank Value := ⟨[], [], false⟩

/-- Streaming is used in the preferred-success mode. With preference disabled
all occurrences are buffered, preserving their original interleaving. -/
def ingest (isError : Value → Bool) (prefer : Bool) (bank : Bank Value) (row : Value) : Bank Value :=
  if prefer && !isError row then
    { bank with streamedRev := row :: bank.streamedRev, hasSuccess := true }
  else { bank with
    fallbackRev := row :: bank.fallbackRev,
    hasSuccess := bank.hasSuccess || !isError row }

def collect (isError : Value → Bool) (prefer : Bool) : List Value → Bank Value → Bank Value
  | [], bank => bank
  | row :: rest, bank => collect isError prefer rest (ingest isError prefer bank row)

def present (isError : Value → Bool) (prefer : Bool) (bank : Bank Value) : List Value :=
  bank.streamedRev.reverse ++ bank.fallbackRev.reverse.filter
    (visible isError prefer bank.hasSuccess)

/-- The last value can avoid the bank, but must still use its owner's success
history. No source syntax is inspected and successful values keep their carrier. -/
def tail (isError : Value → Bool) (prefer : Bool) (bank : Bank Value) (row : Value) : List Value :=
  bank.streamedRev.reverse ++ if visible isError prefer bank.hasSuccess row then [row] else []

def Represents (isError : Value → Bool) (prefer : Bool) (rows : List Value) (bank : Bank Value) : Prop :=
  bank.streamedRev.reverse = (if prefer then rows.filter fun row => !isError row else []) ∧
  bank.fallbackRev.reverse = (if prefer then rows.filter isError else rows) ∧
  bank.hasSuccess = rows.any (fun row => !isError row)

theorem ingest_represents (isError : Value → Bool) (prefer : Bool)
    (rows : List Value) (bank : Bank Value) (row : Value)
    (represents : Represents isError prefer rows bank) :
    Represents isError prefer (rows ++ [row]) (ingest isError prefer bank row) := by
  rcases represents with ⟨streamed, fallback, success⟩
  cases prefer <;> cases error : isError row <;>
    simp [Represents, ingest, error, List.reverse_cons, List.filter_append,
      List.any_append, streamed, fallback, success]

theorem collect_represents (isError : Value → Bool) (prefer : Bool)
    (prior rows : List Value) (bank : Bank Value)
    (represents : Represents isError prefer prior bank) :
    Represents isError prefer (prior ++ rows) (collect isError prefer rows bank) := by
  induction rows generalizing prior bank with
  | nil => simpa [collect] using represents
  | cons row rest ih =>
      simpa [collect, List.append_assoc] using
        ih (prior ++ [row]) (ingest isError prefer bank row)
          (ingest_represents isError prefer prior bank row represents)

theorem no_success_filters (isError : Value → Bool) (rows : List Value)
    (absent : rows.any (fun row => !isError row) = false) :
    rows.filter (fun row => !isError row) = [] ∧ rows.filter isError = rows := by
  induction rows with
  | nil => exact ⟨rfl, rfl⟩
  | cons row rest ih =>
      cases error : isError row with
      | false =>
          have impossible : (true : Bool) = false := by
            simpa only [List.any_cons, error, Bool.not_false, Bool.true_or] using absent
          cases impossible
      | true =>
          have later : rest.any (fun row => !isError row) = false := by
            simpa only [List.any_cons, error, Bool.not_true, Bool.false_or] using absent
          obtain ⟨none, all⟩ := ih later
          simpa only [List.filter_cons, error, Bool.not_true, Bool.false_eq_true,
            if_false, if_true] using And.intro none (congrArg (row :: ·) all)

theorem present_represents (isError : Value → Bool) (prefer : Bool)
    (rows : List Value) (bank : Bank Value)
    (represents : Represents isError prefer rows bank) :
    present isError prefer bank = reference isError prefer rows := by
  rcases represents with ⟨streamed, fallback, success⟩
  cases prefer with
  | false => simp [present, visible, reference, streamed, fallback]
  | true =>
      cases found : rows.any (fun row => !isError row) with
      | false =>
          obtain ⟨none, all⟩ := no_success_filters isError rows found
          simp [present, visible, reference, streamed, fallback, success, found, none, all]
      | true =>
          simp [present, visible, reference, streamed, fallback, success, found, List.filter_filter]

theorem collection_refines (isError : Value → Bool) (prefer : Bool) (rows : List Value) :
    present isError prefer (collect isError prefer rows empty) = reference isError prefer rows := by
  apply present_represents
  simpa using collect_represents isError prefer [] rows empty (by simp [Represents, empty])

/-- This joins normalization to the maintained completed-phase judgment.
It does not assert that a raw source prefix was an exhausted frontier. -/
theorem reference_success_priority (isError : Value → Bool) (rows : List Value) :
    OrderedProtocol.Completion.SuccessPriorityRel isError rows (reference isError true rows) := by
  cases found : rows.any (fun row => !isError row) with
  | false =>
      simp only [reference, found, Bool.and_false, Bool.false_eq_true, if_false]
      apply OrderedProtocol.Completion.SuccessPriorityRel.allErrors
      intro row member
      have all := (no_success_filters isError rows found).2
      have retained : row ∈ rows.filter isError := all.symm ▸ member
      exact (List.mem_filter.mp retained).2
  | true =>
      simp only [reference, found, Bool.and_true, if_true]
      obtain ⟨row, member, successful⟩ := List.any_eq_true.mp found
      exact .successes ⟨row, member, by simpa using successful⟩

/-- Bank emptiness alone does not discharge preferred-success filtering.
The direct path agrees with inserting the occurrence and then presenting it. -/
theorem tail_refines (isError : Value → Bool) (prefer : Bool)
    (bank : Bank Value) (row : Value) (emptyBank : bank.fallbackRev = []) :
    tail isError prefer bank row = present isError prefer (ingest isError prefer bank row) := by
  cases prefer <;> cases error : isError row <;> cases success : bank.hasSuccess <;>
    simp [tail, present, ingest, visible, error, success, emptyBank, List.reverse_cons]

/-- Prior successes do not disable the valid direct-success path. -/
theorem tail_success_keeps_value (isError : Value → Bool) (prefer : Bool)
    (bank : Bank Value) (row : Value) (success : isError row = false) :
    tail isError prefer bank row = bank.streamedRev.reverse ++ [row] := by
  simp [tail, visible, success]

theorem tail_error_after_success_is_suppressed (isError : Value → Bool)
    (bank : Bank Value) (row : Value) (error : isError row = true)
    (earlier : bank.hasSuccess = true) :
    tail isError true bank row = bank.streamedRev.reverse := by
  simp [tail, visible, error, earlier]

structure State (Value : Type) where
  remaining : List Value
  bank : Bank Value
  completed : Option (List Value)
  deriving DecidableEq, Repr

def initial (rows : List Value) : State Value := ⟨rows, empty, none⟩

/-- Final output is a whole-frontier observation, including the occurrences
already streamed. This field does not publish those occurrences a second time. -/
def step (isError : Value → Bool) (prefer : Bool) (state : State Value) : Option (State Value) :=
  if state.completed.isSome then none
  else match state.remaining with
    | [] => some { state with completed := some (present isError prefer state.bank) }
    | [row] =>
        if state.bank.fallbackRev.isEmpty then
          some { state with remaining := [], completed := some (tail isError prefer state.bank row) }
        else some { state with remaining := [], bank := ingest isError prefer state.bank row }
    | row :: next :: rest => some { state with
        remaining := next :: rest, bank := ingest isError prefer state.bank row }

def residual (isError : Value → Bool) (prefer : Bool) (state : State Value) : List Value :=
  match state.completed with
  | some rows => rows
  | none => present isError prefer (collect isError prefer state.remaining state.bank)

def core (isError : Value → Bool) (prefer : Bool) : MachineCore (List Value) where
  State := State Value
  load := initial
  step := step isError prefer

theorem step_preserves_completion (isError : Value → Bool) (prefer : Bool)
    (state next : State Value) (advanced : step isError prefer state = some next) :
    residual isError prefer next = residual isError prefer state := by
  rcases state with ⟨remaining, bank, completed⟩
  cases completed with
  | some rows => simp [step] at advanced
  | none =>
      cases remaining with
      | nil => cases advanced; rfl
      | cons row rest =>
          cases rest with
          | nil =>
              by_cases emptyBank : bank.fallbackRev.isEmpty = true
              · have empty : bank.fallbackRev = [] := List.isEmpty_iff.mp emptyBank
                simp only [step, Option.isSome_none, Bool.false_eq_true, if_false, emptyBank,
                  if_true, Option.some.injEq] at advanced
                subst next
                simpa [residual, collect] using tail_refines isError prefer bank row empty
              · simp only [step, Option.isSome_none, Bool.false_eq_true, if_false, emptyBank,
                  Option.some.injEq] at advanced
                subst next
                rfl
          | cons following later => cases advanced; rfl

/-- Every administrative cut retains the same whole-frontier completion.
The streamed prefix is deliberately not identified with that completion. -/
theorem every_slice_preserves_completion (isError : Value → Bool) (prefer : Bool)
    (allowance : Nat) (state : State Value) :
    residual isError prefer ((core isError prefer).runSlice allowance state).1 =
      residual isError prefer state :=
  MachineCore.runSlice_preserves (core isError prefer) (residual isError prefer)
    (step_preserves_completion isError prefer) allowance state

theorem initial_completion_refines (isError : Value → Bool) (prefer : Bool) (rows : List Value) :
    residual isError prefer (initial rows) = reference isError prefer rows :=
  collection_refines isError prefer rows

/-- Splitting physical processing keeps the complete live state and the exact
number of transitions actually performed, including the direct final shortcut. -/
theorem split_processing (isError : Value → Bool) (prefer : Bool)
    (first later : Nat) (state : State Value) :
    (core isError prefer).runSlice (first + later) state =
      let before := (core isError prefer).runSlice first state
      let after := (core isError prefer).runSlice later before.1
      (after.1, before.2 + after.2) :=
  MachineCore.runSlice_add (core isError prefer) first later state

/-- This finality is exhaustion of the completion adapter, not permission to
force a returned payload or an assertion about an effectful source prefix. -/
theorem completed_is_final (isError : Value → Bool) (prefer : Bool)
    (state : State Value) (rows : List Value) (finished : state.completed = some rows) :
    step isError prefer state = none := by simp [step, finished]

/-- The finite frontier is consumed once, with at most one additional closing
transition. Empty-bank direct completion may finish sooner. -/
theorem completes_in_budget (isError : Value → Bool) (prefer : Bool)
    (rows : List Value) (bank : Bank Value) :
    ((core isError prefer).runSlice (rows.length + 1) ⟨rows, bank, none⟩).1.completed =
      some (present isError prefer (collect isError prefer rows bank)) := by
  induction rows generalizing bank with
  | nil => rfl
  | cons row rest ih =>
      cases rest with
      | nil =>
          by_cases emptyBank : bank.fallbackRev.isEmpty = true
          · have empty : bank.fallbackRev = [] := List.isEmpty_iff.mp emptyBank
            simpa [core, MachineCore.runSlice, step, emptyBank, collect] using
              congrArg some (tail_refines isError prefer bank row empty)
          · simp [core, MachineCore.runSlice, step, emptyBank, collect]
      | cons following later =>
          simpa [core, MachineCore.runSlice, step, collect] using
            ih (ingest isError prefer bank row)

theorem completed_frontier_refines (isError : Value → Bool) (prefer : Bool) (rows : List Value) :
    ((core isError prefer).runSlice (rows.length + 1) (initial rows)).1.completed =
      some (reference isError prefer rows) := by
  rw [initial, completes_in_budget, collection_refines]

/-- Already completed presentation is inert under every later physical
allowance. This proves no replay of the adapter; source invocation is separate. -/
theorem completed_processing_inert (isError : Value → Bool) (prefer : Bool)
    (state : State Value) (rows : List Value) (finished : state.completed = some rows)
    (allowance : Nat) :
    (core isError prefer).runSlice allowance state = (state, 0) :=
  MachineCore.runSlice_of_final (core isError prefer) state
    (completed_is_final isError prefer state rows finished) allowance

/-- Representation changes may identify payloads but not their occurrences.
The existing priority relation transports opaque binding/fault carriers. -/
theorem reference_map (isError : Value → Bool) (otherError : Other → Bool)
    (represent : Value → Other) (classification : ∀ row, otherError (represent row) = isError row)
    (prefer : Bool) (rows : List Value) :
    reference otherError prefer (rows.map represent) = (reference isError prefer rows).map represent := by
  cases prefer with
  | false => rfl
  | true =>
      exact OrderedProtocol.Completion.SuccessPriorityRel.functional
        (reference_success_priority otherError (rows.map represent))
        ((reference_success_priority isError rows).map represent classification)

namespace Controls

inductive Sample where
  | good (value : Nat)
  | fault (payload : Nat)
  deriving DecidableEq, Repr

def isError : Sample → Bool
  | .good _ => false
  | .fault _ => true

def streamed : Bank Sample := ⟨[.good 1], [], true⟩

/-- The historical shortcut mistook an empty retained bank for no prior
success. It emitted the last value without applying the owner's predicate. -/
def oldTail (bank : Bank Sample) (row : Sample) : List Sample := bank.streamedRev.reverse ++ [row]

theorem empty_bank_can_have_prior_streamed_success :
    streamed.fallbackRev = [] ∧ streamed.hasSuccess = true ∧
      tail isError true streamed (.fault 7) = [.good 1] := by decide

theorem old_shortcut_publishes_a_suppressed_error :
    oldTail streamed (.fault 7) = [.good 1, .fault 7] ∧
      oldTail streamed (.fault 7) ≠ reference isError true [.good 1, .fault 7] ∧
      tail isError true streamed (.fault 7) = reference isError true [.good 1, .fault 7] := by decide

theorem direct_success_remains_enabled_after_success :
    tail isError true streamed (.good 2) = [.good 1, .good 2] := by decide

theorem all_errors_keep_order_and_duplicates :
    ((core isError true).runSlice 4 (initial [.fault 7, .fault 7, .fault 9])).1.completed =
      some [.fault 7, .fault 7, .fault 9] := by decide

theorem successes_keep_order_and_duplicates :
    ((core isError true).runSlice 5 (initial [.fault 7, .good 1, .good 1, .good 2])).1.completed =
      some [.good 1, .good 1, .good 2] := by decide

theorem disabled_preference_keeps_original_interleaving :
    ((core isError false).runSlice 4 (initial [.good 1, .fault 7, .good 2])).1.completed =
      some [.good 1, .fault 7, .good 2] := by decide

theorem classifier_role_is_not_inferred_from_payload :
    reference (fun _ : Sample => false) true [.fault 7, .good 1] = [.fault 7, .good 1] := by decide

theorem bound_contexts_and_duplicate_occurrences_remain_attached :
    reference (fun row : Sample × Nat => isError row.1) true
      [(.good 1, 11), (.fault 7, 22), (.good 1, 11), (.good 1, 13)] =
        [(.good 1, 11), (.good 1, 11), (.good 1, 13)] := by decide

theorem physical_split_keeps_streamed_history_and_final_suppression :
    let first := (core isError true).runSlice 1 (initial [.good 1, .fault 7])
    first.1.bank.fallbackRev = [] ∧ first.1.bank.hasSuccess = true ∧
      first.1.completed = none ∧
      ((core isError true).runSlice 1 first.1).1.completed = some [.good 1] := by decide

theorem zero_allowance_keeps_the_untouched_frontier :
    (core isError true).runSlice 0 (initial [.good 1, .fault 7]) =
      (initial [.good 1, .fault 7], 0) := rfl

theorem empty_and_single_error_frontiers_complete :
    ((core isError true).runSlice 1 (initial [])).1.completed = some [] ∧
      ((core isError true).runSlice 1 (initial [.fault 7])).1.completed = some [.fault 7] := by decide

end Controls

end Mettapedia.Machines.HEProducerCompletion
