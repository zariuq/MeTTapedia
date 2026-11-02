import Mettapedia.Machines.NativeCallReturn

/-!
# Sequential callback completion before row publication

This models the non-HE callback document loop. Each source occurrence is parsed
when reached; a standalone bang marker skips evaluation. Evaluation changes
the actual world before its completion and raised-control tags are inspected.
Completed payloads, including Error-shaped data and empty answer rows, are data.

The reference constructs successful rows while returning through recursion.
The target retains an array of rows and an ordered event history. An exception
discards that array but retains the reached world, exact history and unentered
source suffix. The independent definitions agree for arbitrary callback world
transitions, parser failures, producer interruptions and publication failures.

Native text-to-occurrence parsing, evaluator tag correctness, Python conversion,
allocation, lifetime and exception correspondence are separate obligations.
The HE document runner is outside this model.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CallbackCompletion

variable {Source Expression World Value Fault Cause : Type}

inductive Failure (Fault Cause : Type) where
  | parse (fault : Fault)
  | incomplete (cause : Cause)
  | raised (fault : Fault)
  | publication (fault : Fault)
  deriving DecidableEq, Repr

/-- Partial values do not certify completion. The raised tag records control
provenance independently of the syntax of the values. -/
structure Outcome (Value Fault Cause : Type) where
  values : List Value
  incomplete : Option Cause
  /-- Present exactly when the evaluator reports known raised control. -/
  raised : Option Fault
  deriving DecidableEq, Repr

structure Program (Source Expression World Value Fault Cause : Type) where
  parse : Source → Except Fault (Option Expression)
  evaluate : World → Expression → World × Outcome Value Fault Cause
  publish : List Value → Option Fault

/-- An evaluator's completed row is one completed packet, even when empty.
Its producer-owned raised flag, rather than the row's shape, selects control. -/
def packet (outcome : Outcome Value Fault Cause) :
    NativeCallReturn.Packet (List Value) Fault Empty :=
  match outcome.raised with
  | none => .value .completed outcome.values
  | some fault => .raised fault

/-- Direct reference inspection uses the evaluator's fields. -/
def referenceRow (publish : List Value → Option Fault)
    (outcome : Outcome Value Fault Cause) : Except (Failure Fault Cause) (List Value) :=
  match outcome.incomplete, outcome.raised with
  | some cause, _ => .error (.incomplete cause)
  | none, some fault => .error (.raised fault)
  | none, none =>
      match publish outcome.values with
      | some fault => .error (.publication fault)
      | none => .ok outcome.values

/-- The target checks completion before consuming a maintained native packet
or admitting the row to the publication operation. -/
def targetRow (publish : List Value → Option Fault)
    (outcome : Outcome Value Fault Cause) : Except (Failure Fault Cause) (List Value) :=
  match outcome.incomplete with
  | some cause => .error (.incomplete cause)
  | none =>
      match packet outcome with
      | .raised fault => .error (.raised fault)
      | .value _ row =>
          match publish row with
          | some fault => .error (.publication fault)
          | none => .ok row
      | .conditional _ impossible => nomatch impossible

theorem row_projection_refines (publish : List Value → Option Fault)
    (outcome : Outcome Value Fault Cause) :
    targetRow publish outcome = referenceRow publish outcome := by
  rcases outcome with ⟨values, incomplete, raised⟩
  cases incomplete <;> cases raised <;> rfl

inductive Event (Source Expression World Value : Type) where
  | parsed (source : Source)
  | evaluated (expression : Expression) (before after : World)
  | published (row : List Value)
  deriving DecidableEq, Repr

structure Report (Source Expression World Value Fault Cause : Type) where
  world : World
  events : List (Event Source Expression World Value)
  reply : Except (Failure Fault Cause) (List (List Value))
  pending : List Source
  deriving DecidableEq, Repr

/-- Prior rows survive only a successful whole callback. Its committed effects
and event history survive both success and failure. -/
def extend (rows : List (List Value))
    (events : List (Event Source Expression World Value))
    (result : Report Source Expression World Value Fault Cause) :
    Report Source Expression World Value Fault Cause :=
  { result with
    events := events ++ result.events
    reply := match result.reply with
      | .error fault => .error fault
      | .ok later => .ok (rows ++ later) }

@[simp] private theorem extend_empty
    (result : Report Source Expression World Value Fault Cause) :
    extend [] [] result = result := by
  rcases result with ⟨world, events, reply, pending⟩
  cases reply <;> rfl

private theorem extend_extend (rows laterRows : List (List Value))
    (events laterEvents : List (Event Source Expression World Value))
    (result : Report Source Expression World Value Fault Cause) :
    extend rows events (extend laterRows laterEvents result) =
      extend (rows ++ laterRows) (events ++ laterEvents) result := by
  rcases result with ⟨world, history, reply, pending⟩
  cases reply <;> simp [extend, List.append_assoc]

/-- The reference only constructs a row in its final answer after the suffix
has itself succeeded. It never evaluates a source following a failed one. -/
def reference (program : Program Source Expression World Value Fault Cause) :
    List Source → World → Report Source Expression World Value Fault Cause
  | [], world => ⟨world, [], .ok [], []⟩
  | source :: rest, world =>
      match program.parse source with
      | .error fault => ⟨world, [.parsed source], .error (.parse fault), rest⟩
      | .ok none => extend [] [.parsed source] (reference program rest world)
      | .ok (some expression) =>
          let next := program.evaluate world expression
          match referenceRow program.publish next.2 with
          | .error fault =>
              ⟨next.1, [.parsed source, .evaluated expression world next.1],
                .error fault, rest⟩
          | .ok row =>
              extend [row]
                [.parsed source, .evaluated expression world next.1, .published row]
                (reference program rest next.1)

/-- The target commits the current evaluation world once, then either stops
or appends exactly one row before consuming the remaining source occurrences. -/
def targetLoop (program : Program Source Expression World Value Fault Cause) :
    List Source → World → Array (List Value) →
      List (Event Source Expression World Value) →
      Report Source Expression World Value Fault Cause
  | [], world, rows, events => ⟨world, events, .ok rows.toList, []⟩
  | source :: rest, world, rows, events =>
      let parsed := events ++ [.parsed source]
      match program.parse source with
      | .error fault => ⟨world, parsed, .error (.parse fault), rest⟩
      | .ok none => targetLoop program rest world rows parsed
      | .ok (some expression) =>
          let next := program.evaluate world expression
          let entered := parsed ++ [.evaluated expression world next.1]
          match targetRow program.publish next.2 with
          | .error fault => ⟨next.1, entered, .error fault, rest⟩
          | .ok row =>
              targetLoop program rest next.1 (rows.push row) (entered ++ [.published row])

def run (program : Program Source Expression World Value Fault Cause)
    (sources : List Source) (world : World) :
    Report Source Expression World Value Fault Cause :=
  targetLoop program sources world #[] []

/-- Array accumulation refines the independent recursive reference, including
actual worlds, ordered occurrences, publication, failure and exact residual.
The arbitrary initial buffer is discarded on any later failure. -/
theorem sequence_refines (program : Program Source Expression World Value Fault Cause)
    (sources : List Source) (world : World) (rows : Array (List Value))
    (events : List (Event Source Expression World Value)) :
    targetLoop program sources world rows events =
      extend rows.toList events (reference program sources world) := by
  induction sources generalizing world rows events with
  | nil => simp [targetLoop, reference, extend]
  | cons source rest ih =>
      cases parsed : program.parse source with
      | error fault => simp [targetLoop, reference, parsed, extend]
      | ok expression =>
          cases expression with
          | none =>
              simp only [targetLoop, reference, parsed, ih, extend_extend]
              simp
          | some expression =>
              rcases evaluated : program.evaluate world expression with ⟨after, outcome⟩
              cases checked : referenceRow program.publish outcome with
              | error fault =>
                  simp [targetLoop, reference, parsed, evaluated,
                    row_projection_refines, checked, extend, List.append_assoc]
              | ok row =>
                  simp [targetLoop, reference, parsed, evaluated,
                    row_projection_refines, checked, ih, extend_extend, List.append_assoc]

/-- A continuation consumes only the suffix and the actual completed world.
A failed prefix contributes no rows and does not enter the appended suffix. -/
def continueWith (program : Program Source Expression World Value Fault Cause)
    (later : List Source) (result : Report Source Expression World Value Fault Cause) :
    Report Source Expression World Value Fault Cause :=
  match result.reply with
  | .error _ => { result with pending := result.pending ++ later }
  | .ok rows => extend rows result.events (reference program later result.world)

private theorem continue_extend (program : Program Source Expression World Value Fault Cause)
    (later : List Source) (rows : List (List Value))
    (events : List (Event Source Expression World Value))
    (result : Report Source Expression World Value Fault Cause) :
    continueWith program later (extend rows events result) =
      extend rows events (continueWith program later result) := by
  rcases result with ⟨world, history, reply, pending⟩
  cases reply with
  | error fault => rfl
  | ok value =>
      change extend (rows ++ value) (events ++ history) (reference program later world) =
        extend rows events (extend value history (reference program later world))
      rw [extend_extend]

theorem reference_append (program : Program Source Expression World Value Fault Cause)
    (first later : List Source) (world : World) :
    reference program (first ++ later) world =
      continueWith program later (reference program first world) := by
  induction first generalizing world with
  | nil => simp [reference, continueWith]
  | cons source rest ih =>
      cases parsed : program.parse source with
      | error fault => simp [reference, parsed, continueWith]
      | ok expression =>
          cases expression with
          | none => simp [reference, parsed, ih, continue_extend]
          | some expression =>
              rcases evaluated : program.evaluate world expression with ⟨after, outcome⟩
              cases checked : referenceRow program.publish outcome with
              | error fault => simp [reference, parsed, evaluated, checked, continueWith]
              | ok row => simp [reference, parsed, evaluated, checked, ih, continue_extend]

/-- A successful prefix is neither reparsed nor reevaluated. Its completed rows
and history compose with execution of the suffix from its committed world. -/
theorem success_prefix_not_replayed
    (program : Program Source Expression World Value Fault Cause)
    (first later : List Source) (world after : World)
    (rows : List (List Value)) (events : List (Event Source Expression World Value))
    (completed : reference program first world = ⟨after, events, .ok rows, []⟩) :
    run program (first ++ later) world = extend rows events (run program later after) := by
  simp only [run, sequence_refines, extend_empty]
  rw [reference_append, completed]
  rfl

/-- A failed prefix retains its world and complete event history, exports no
partial rows, and leaves every appended occurrence unentered. -/
theorem failure_prefix_stops
    (program : Program Source Expression World Value Fault Cause)
    (first later : List Source) (world after : World)
    (events : List (Event Source Expression World Value))
    (fault : Failure Fault Cause) (pending : List Source)
    (failed : reference program first world = ⟨after, events, .error fault, pending⟩) :
    run program (first ++ later) world =
      ⟨after, events, .error fault, pending ++ later⟩ := by
  simp only [run, sequence_refines, extend_empty]
  rw [reference_append, failed]
  rfl

theorem parse_failure_retains_world
    (program : Program Source Expression World Value Fault Cause)
    (source : Source) (later : List Source) (world : World) (fault : Fault)
    (failed : program.parse source = .error fault) :
    run program (source :: later) world =
      ⟨world, [.parsed source], .error (.parse fault), later⟩ := by
  simp [run, targetLoop, failed]

/-- Completion wins even when a partial row also carries a raised tag and the
publisher would reject it. None of those later decisions can mask the cause. -/
theorem incomplete_precedes_raise_and_publication
    (publish : List Value → Option Fault) (values : List Value)
    (cause : Cause) (raised : Option Fault) :
    targetRow publish (⟨values, some cause, raised⟩ : Outcome Value Fault Cause) =
      .error (.incomplete cause) := rfl

def parsedSources (events : List (Event Source Expression World Value)) : List Source :=
  events.filterMap fun event => match event with
    | .parsed source => some source
    | _ => none

def evaluatedExpressions (events : List (Event Source Expression World Value)) :
    List Expression :=
  events.filterMap fun event => match event with
    | .evaluated expression _ _ => some expression
    | _ => none

namespace Controls

inductive Payload where
  | number (value : Nat)
  | error (value : Nat)
  deriving DecidableEq, Repr

inductive StopCause where
  | fuel
  deriving DecidableEq, Repr

def program : Program Nat Nat (List Nat) Payload String StopCause where
  parse source :=
    if source = 99 then .error "parse"
    else if source = 98 then .ok none else .ok (some source)
  evaluate world expression :=
    (world ++ [expression],
      if expression = 0 then ⟨[.error 0], none, some "raised"⟩
      else if expression = 6 then ⟨[.number 6], some .fuel, some "raised"⟩
      else if expression = 8 then ⟨[], none, none⟩
      else if expression = 9 then ⟨[.error 9], none, none⟩
      else if expression = 10 then ⟨[.error 0], none, none⟩
      else ⟨[.number expression], none, none⟩)
  publish _ := none

theorem completed_error_data_and_raised_control_separate :
    (run program [9, 10] []).reply = .ok [[.error 9], [.error 0]] ∧
    (run program [0] []).reply = .error (.raised "raised") ∧
    packet (⟨[.error 0], none, none⟩ : Outcome Payload String StopCause) ≠
      packet (⟨[.error 0], none, some "raised"⟩ : Outcome Payload String StopCause) := by
  decide +kernel

theorem empty_complete_and_partial_incomplete_separate :
    (run program [8, 7] []).reply = .ok [[], [.number 7]] ∧
    (run program [6, 7] []).reply = .error (.incomplete .fuel) ∧
    (run program [6, 7] []).world = [6] ∧
    (run program [6, 7] []).pending = [7] := by
  decide +kernel

theorem committed_effects_and_duplicate_order :
    (run program [7, 7, 9] []).reply = .ok [[.number 7], [.number 7], [.error 9]] ∧
    (run program [1, 1, 0, 2] []).world = [1, 1, 0] ∧
    evaluatedExpressions (run program [1, 1, 0, 2] []).events = [1, 1, 0] ∧
    (run program [1, 1, 0, 2] []).reply = .error (.raised "raised") ∧
    (run program [1, 1, 0, 2] []).pending = [2] := by
  decide +kernel

theorem parse_failure_is_reached :
    (run program [1, 98, 99, 2] []).world = [1] ∧
    parsedSources (run program [1, 98, 99, 2] []).events = [1, 98, 99] ∧
    evaluatedExpressions (run program [1, 98, 99, 2] []).events = [1] ∧
    (run program [1, 98, 99, 2] []).reply = .error (.parse "parse") ∧
    (run program [1, 98, 99, 2] []).pending = [2] := by
  decide +kernel

theorem publication_failure_discards_prior_rows :
    let rejecting := { program with publish := fun row =>
      if row = [.number 7] then some "publish" else none }
    (run rejecting [1, 7, 2] []).world = [1, 7] ∧
    evaluatedExpressions (run rejecting [1, 7, 2] []).events = [1, 7] ∧
    (run rejecting [1, 7, 2] []).reply = .error (.publication "publish") ∧
    (run rejecting [1, 7, 2] []).pending = [2] := by
  decide +kernel

end Controls
end Mettapedia.Machines.CallbackCompletion

#print axioms Mettapedia.Machines.CallbackCompletion.row_projection_refines
#print axioms Mettapedia.Machines.CallbackCompletion.sequence_refines
#print axioms Mettapedia.Machines.CallbackCompletion.reference_append
#print axioms Mettapedia.Machines.CallbackCompletion.success_prefix_not_replayed
#print axioms Mettapedia.Machines.CallbackCompletion.failure_prefix_stops
#print axioms Mettapedia.Machines.CallbackCompletion.parse_failure_retains_world
#print axioms Mettapedia.Machines.CallbackCompletion.incomplete_precedes_raise_and_publication
#print axioms Mettapedia.Machines.CallbackCompletion.Controls.completed_error_data_and_raised_control_separate
#print axioms Mettapedia.Machines.CallbackCompletion.Controls.empty_complete_and_partial_incomplete_separate
#print axioms Mettapedia.Machines.CallbackCompletion.Controls.committed_effects_and_duplicate_order
#print axioms Mettapedia.Machines.CallbackCompletion.Controls.parse_failure_is_reached
#print axioms Mettapedia.Machines.CallbackCompletion.Controls.publication_failure_discards_prior_rows
