import Mettapedia.Machines.OwnedBind
import Mettapedia.Machines.ContextualCBPV

/-!
# Completion before publication of an ordinary residual's private buffer

The source reads established ordinary results recursively. The leaf algorithm
walks them with an accumulator; the owned cursor independently indexes the
original array. Both use the maintained native packet meaning for value,
conditional and already-classified zero rows. An incomplete producer publishes none of its
private rows. Already published earlier frames and the producer's actual world
are retained. The leaf need not use the generic child driver to obey this law.

This starts at the ordinary evaluator's established buffer and its OWN observed
completion. An earlier parent's diagnostic reason is not substituted for this
producer's outcome. Parent first-cause and credit settlement remain separate
maintained episode laws, not a fixed price invented by this adapter. Native evaluator-to-buffer correspondence, exact dialect-zero
recognition, allocation and pointer lifetime remain implementation obligations.
The source evaluator owns its debit; cursor/leaf adapters add no source charge.

`NativeEntry` separately checks startup around provider invocation and delivery.
It distinguishes absent, weak-diagnostic and strongly interrupted parents, and
gates both the terminal packet cursor and buffered rows on own completion.
Entry-controller completion does not certify exhaustion of its output cursor.

`EpisodeReuse` compares a synchronous phase under a fresh child with that
phase under an existing clean unlimited parent. Effects, branches, actual debit
admissions and nested child settlements are preserved. The semantic observer
includes own diagnostics and active finite credit; scope identity, paused-parent
introspection and inactive accounting words are outside the phase observer.
All final parent fields, including inactive words, still agree exactly.

`CallbackDisposition` checks the provider's own completion before its handled
flag. A complete false reply transfers no packet and permits ordinary fallback;
a complete true reply transfers the exact entered packet. Its explicit client
refines independent source execution with actual world/effect chronology.
The law does not erase effects made by a declined provider. Flag truthfulness,
unused-storage safety and evaluator-to-callback correspondence remain native
contracts, separate from this disposition algorithm.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.BufferedResidualReturn

open OwnedPullDriver

variable {Value Context Delay Cause : Type}

/-- Zero is a prior dialect classification, separate from a row established
as data. PeTTa's private marker and HE ordinary source completion need different
native classifiers. Malformed materialization is not logical failure. -/
inductive Row (Value Context Delay : Type) where
  | zero
  | data (value : Value) (context : Context) (delay : Option Delay)
  | malformed
  deriving DecidableEq, Repr

abbrev Packet (Value Context Delay : Type) :=
  NativeCallReturn.Returned Value Empty Delay Context

inductive Exit (Cause : Type) where
  | complete
  | incomplete (cause : Cause)
  | hostFailure
  deriving DecidableEq, Repr

structure Buffer (Value Context Delay Cause : Type) where
  rows : Array (Row Value Context Delay)
  incomplete : Option Cause

/-- The runtime row adapter uses the maintained native occurrence protocol. -/
def rowSource : Row Value Context Delay → NativeCallReturn.Source Value Empty Delay
  | .zero => .failure
  | .malformed => .invalid
  | .data value _ none => .one (.value .completed value)
  | .data value _ (some check) => .one (.conditional value check)

def rowContext (fallback : Context) : Row Value Context Delay → Context
  | .data _ context _ => context
  | _ => fallback

/-- No result-shape rule enters this projection. -/
def nativeRow (fallback : Context) (row : Row Value Context Delay) :
    List (Packet Value Context Delay) × NativeCallReturn.Stop :=
  NativeCallReturn.meaning (rowSource row) (rowContext fallback row)

/-- Independent recursive source publication, preserving the prefix before a
reached materialization fault. A classified zero contributes no occurrence. -/
def sourceRows : List (Row Value Context Delay) → List (Packet Value Context Delay) × Exit Cause
  | [] => ([], .complete)
  | .zero :: rest => sourceRows rest
  | .malformed :: _ => ([], .hostFailure)
  | .data value context check :: rest =>
      let later := sourceRows rest
      ((context, match check with
        | none => .value .completed value
        | some delayed => .conditional value delayed) :: later.1, later.2)

/-- An incomplete producer's partial array is never admitted to row publication. -/
def source (buffer : Buffer Value Context Delay Cause) :
    List (Packet Value Context Delay) × Exit Cause :=
  match buffer.incomplete with
  | some cause => ([], .incomplete cause)
  | none => sourceRows buffer.rows.toList

/-- Direct leaf traversal accumulates projected rows, without child machinery. -/
def leafRows (fallback : Context) : List (Row Value Context Delay) →
    List (Packet Value Context Delay) → List (Packet Value Context Delay) × Exit Cause
  | [], published => (published, .complete)
  | row :: rest, published =>
      let selected := nativeRow fallback row
      match selected.2 with
      | .complete => leafRows fallback rest (published ++ selected.1)
      | .hostFailure => (published, .hostFailure)
      | .cancelled => (published, .hostFailure)

def leaf (fallback : Context) (buffer : Buffer Value Context Delay Cause) :
    List (Packet Value Context Delay) × Exit Cause :=
  match buffer.incomplete with
  | some cause => ([], .incomplete cause)
  | none => leafRows fallback buffer.rows.toList []

theorem leaf_rows_refine (fallback : Context) (rows : List (Row Value Context Delay))
    (published : List (Packet Value Context Delay)) :
    leafRows (Cause := Cause) fallback rows published =
      (published ++ (sourceRows rows : _ × Exit Cause).1, (sourceRows (Cause := Cause) rows).2) := by
  induction rows generalizing published with
  | nil => simp [leafRows, sourceRows]
  | cons row rows ih =>
      cases row with
      | zero => simpa [leafRows, nativeRow, rowSource, rowContext,
          NativeCallReturn.meaning, sourceRows] using ih published
      | malformed => simp [leafRows, nativeRow, rowSource,
          NativeCallReturn.meaning, sourceRows]
      | data value context check =>
          cases check <;>
            simp [leafRows, nativeRow, rowSource, rowContext,
              NativeCallReturn.meaning, sourceRows, ih, List.append_assoc]

theorem leaf_refines (fallback : Context) (buffer : Buffer Value Context Delay Cause) :
    leaf fallback buffer = source buffer := by
  cases buffer with
  | mk rows incomplete =>
      cases incomplete <;> simp [leaf, source, leaf_rows_refine]

/-- A cursor program indexes the unchanged backing array. `remaining` bounds
native polls, not semantic source fuel. Zero rows are silent cursor advances. -/
def cursorRows (fallback : Context) (rows : Array (Row Value Context Delay))
    (position : Nat) : Nat → Program (Exit Cause) (Packet Value Context Delay)
  | 0 => .done .complete
  | remaining + 1 =>
      match rows[position]? with
      | none => .done .complete
      | some row =>
          let selected := nativeRow fallback row
          match selected.2, selected.1 with
          | .complete, [] => cursorRows fallback rows (position + 1) remaining
          | .complete, first :: _ => .emit first
              (cursorRows fallback rows (position + 1) remaining)
          | _, _ => .done .hostFailure

/-- Source-side list lowering uses established row tags directly, independently
of the cursor and native packet adapter. -/
def sourceProgram : List (Row Value Context Delay) →
    Program (Exit Cause) (Packet Value Context Delay)
  | [] => .done .complete
  | .zero :: rest => sourceProgram rest
  | .malformed :: _ => .done .hostFailure
  | .data value context check :: rest =>
      .emit (context, match check with
        | none => .value .completed value
        | some delayed => .conditional value delayed) (sourceProgram rest)

theorem cursor_rows_refine (fallback : Context) (rows : Array (Row Value Context Delay))
    (remaining position : Nat) :
    (cursorRows fallback rows position remaining : Program (Exit Cause) _) =
      sourceProgram ((rows.toList.drop position).take remaining) := by
  induction remaining generalizing position with
  | zero => simp [cursorRows, sourceProgram]
  | succ remaining ih =>
      cases found : rows[position]? with
      | none =>
          have empty : rows.toList.drop position = [] := by
            apply List.drop_eq_nil_iff.mpr
            simpa using (Array.getElem?_eq_none_iff.mp found)
          simp [cursorRows, found, empty, sourceProgram]
      | some row =>
          have listFound : rows.toList[position]? = some row := by simpa using found
          obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp listFound
          have head := List.drop_eq_getElem_cons bound
          rw [equal] at head
          cases row with
          | zero => simpa [cursorRows, found, nativeRow, rowSource, rowContext,
              NativeCallReturn.meaning, head, sourceProgram] using ih (position + 1)
          | malformed => simp [cursorRows, found, nativeRow, rowSource,
              NativeCallReturn.meaning, head, sourceProgram]
          | data value context check =>
              cases check <;>
                simp [cursorRows, found, nativeRow, rowSource, rowContext,
                  NativeCallReturn.meaning, head, sourceProgram, ih]

def cursor (fallback : Context) (buffer : Buffer Value Context Delay Cause) :
    Program (Exit Cause) (Packet Value Context Delay) :=
  match buffer.incomplete with
  | some cause => .done (.incomplete cause)
  | none => cursorRows fallback buffer.rows 0 buffer.rows.size

theorem source_program_runs (rows : List (Row Value Context Delay)) :
    Runs (sourceProgram rows : Program (Exit Cause) _)
      (sourceRows (Cause := Cause) rows).1 (sourceRows (Cause := Cause) rows).2 := by
  induction rows with
  | nil => exact .done
  | cons row rows ih =>
      cases row with
      | zero => exact ih
      | malformed => exact .done
      | data value context check => exact .emit ih

theorem cursor_runs (fallback : Context) (buffer : Buffer Value Context Delay Cause) :
    Runs (cursor fallback buffer) (source buffer).1 (source buffer).2 := by
  cases buffer with
  | mk rows incomplete =>
      cases incomplete with
      | some cause => exact .done
      | none =>
          have enough : rows.toList.take rows.size = rows.toList :=
            List.take_of_length_le (by simp)
          simpa [cursor, source, cursor_rows_refine, enough] using
            (source_program_runs (Cause := Cause) rows.toList)

/-- The indexed adapter is an actual program of the maintained owned driver. -/
theorem owned_driver_refines (fallback : Context) (buffer : Buffer Value Context Delay Cause) :
    ∃ allowance, advance allowance ⟨cursor fallback buffer, []⟩ =
      ((source buffer).1, ⟨.done (source buffer).2, []⟩) :=
  advance_refines_runs (cursor_runs fallback buffer)

/-- Physical slicing retains the exact driver residual; it does not evaluate
or charge the producer again. -/
theorem owned_driver_split (fallback : Context) (buffer : Buffer Value Context Delay Cause)
    (first second : Nat) :
    advance (first + second) ⟨cursor fallback buffer, []⟩ =
      let earlier := advance first ⟨cursor fallback buffer, []⟩
      let suffix := advance second earlier.2
      (earlier.1 ++ suffix.1, suffix.2) :=
  advance_add first second _


/-- Incomplete completion is authoritative even when the private array is
nonempty, malformed, or contains data that looks executable. -/
theorem incomplete_source (rows : Array (Row Value Context Delay)) (cause : Cause) :
    source (⟨rows, some cause⟩ : Buffer Value Context Delay Cause) =
      ([], .incomplete cause) := rfl

theorem incomplete_leaf (fallback : Context) (rows : Array (Row Value Context Delay))
    (cause : Cause) :
    leaf fallback (⟨rows, some cause⟩ : Buffer Value Context Delay Cause) =
      ([], .incomplete cause) := by
  rw [leaf_refines]
  rfl

theorem incomplete_cursor (fallback : Context) (rows : Array (Row Value Context Delay))
    (cause : Cause) (allowance : Nat) :
    advance allowance ⟨cursor fallback (⟨rows, some cause⟩ :
      Buffer Value Context Delay Cause), []⟩ =
        ([], ⟨.done (.incomplete cause), []⟩) := by
  cases allowance <;> rfl

/-- A concrete row read creates the exact pending packet. No interpretation
of its payload is part of creating or retaining this loan. -/
theorem cursor_pending_packet (fallback : Context)
    (rows : Array (Row Value Context Delay)) (position remaining : Nat)
    (value : Value) (context : Context) (check : Option Delay)
    (found : rows[position]? = some (.data value context check)) :
    (cursorRows fallback rows position (remaining + 1) : Program (Exit Cause) _) =
      .emit (context, match check with
        | none => .value .completed value
        | some delayed => .conditional value delayed)
        (cursorRows fallback rows (position + 1) remaining) := by
  cases check <;>
    simp [cursorRows, found, nativeRow, rowSource, rowContext, NativeCallReturn.meaning]

/-- Refusing an already-offered packet performs no driver transition and
keeps that same packet and suffix available. This is a publication allowance,
not a source-fuel assertion. -/
theorem refused_pending_keeps_packet (packet : Packet Value Context Delay)
    (later : Program (Exit Cause) (Packet Value Context Delay)) :
    advance 0 (⟨.emit packet later, []⟩ : State (Exit Cause) _) =
      ([], ⟨.emit packet later, []⟩) := rfl

/-- Accepting the retained occurrence once publishes precisely that
occurrence; a later slice starts at the existing suffix. -/
theorem accept_pending_once (packet : Packet Value Context Delay)
    (later : Program (Exit Cause) (Packet Value Context Delay)) :
    advance 1 (⟨.emit packet later, []⟩ : State (Exit Cause) _) =
      ([packet], ⟨later, []⟩) := rfl

variable {World : Type}

/-- The world supplied here is the actual world after the ordinary producer.
Earlier caller publications are an independent committed prefix. -/
structure FrameReport (World Packet Cause : Type) where
  world : World
  publications : List Packet
  exit : Exit Cause

def sourceFrame (action : Packet Value Context Delay → World → World)
    (world : World) (earlier : List (Packet Value Context Delay))
    (buffer : Buffer Value Context Delay Cause) :
    FrameReport World (Packet Value Context Delay) Cause :=
  let result := source buffer
  ⟨interpret action result.1 world, earlier ++ result.1, result.2⟩

def leafFrame (action : Packet Value Context Delay → World → World)
    (fallback : Context) (world : World) (earlier : List (Packet Value Context Delay))
    (buffer : Buffer Value Context Delay Cause) :
    FrameReport World (Packet Value Context Delay) Cause :=
  let result := leaf fallback buffer
  ⟨interpret action result.1 world, earlier ++ result.1, result.2⟩

theorem leaf_frame_refines (action : Packet Value Context Delay → World → World)
    (fallback : Context) (world : World) (earlier : List (Packet Value Context Delay))
    (buffer : Buffer Value Context Delay Cause) :
    leafFrame action fallback world earlier buffer = sourceFrame action world earlier buffer := by
  simp only [leafFrame, leaf_refines, sourceFrame]

/-- Reached producer effects survive, while no private row or child reaches
an arbitrary publication action. Previously published frames remain intact. -/
theorem incomplete_frame_preserves_world_and_prefix
    (action : Packet Value Context Delay → World → World)
    (fallback : Context) (world : World) (earlier : List (Packet Value Context Delay))
    (rows : Array (Row Value Context Delay)) (cause : Cause) :
    leafFrame action fallback world earlier ⟨rows, some cause⟩ =
      (⟨world, earlier, .incomplete cause⟩ : FrameReport World _ _) := by
  simp [leafFrame, incomplete_leaf, interpret]

/-- The exact cursor trace has the same arbitrary publication effects as the
source, while interpreting none of the producer's earlier effects again. -/
theorem owned_world_refines (action : Packet Value Context Delay → World → World)
    (fallback : Context) (world : World) (buffer : Buffer Value Context Delay Cause) :
    ∃ allowance, interpret action
      (advance allowance ⟨cursor fallback buffer, []⟩).1 world =
      interpret action (source buffer).1 world := by
  obtain ⟨allowance, equal⟩ := owned_driver_refines fallback buffer
  exact ⟨allowance, by rw [equal]⟩

/-- This exact two-stage world law prevents reinterpreting an earlier slice's
publications on resumption, even when the action has non-idempotent effects. -/
theorem split_world_effects (action : Packet Value Context Delay → World → World)
    (fallback : Context) (world : World) (buffer : Buffer Value Context Delay Cause)
    (first second : Nat) :
    interpret action (advance (first + second) ⟨cursor fallback buffer, []⟩).1 world =
      interpret action (advance second (advance first ⟨cursor fallback buffer, []⟩).2).1
        (interpret action (advance first ⟨cursor fallback buffer, []⟩).1 world) := by
  rw [owned_driver_split]
  exact interpret_append _ _ _ _


/-- A pending packet is obtained from the actual array index before a caller
can refuse it. Refusal retains that exact contextual packet and array suffix. -/
theorem refused_array_packet (fallback : Context)
    (rows : Array (Row Value Context Delay)) (position remaining : Nat)
    (value : Value) (context : Context) (check : Option Delay)
    (found : rows[position]? = some (.data value context check)) :
    advance 0 (⟨cursorRows fallback rows position (remaining + 1), []⟩ :
      State (Exit Cause) _) =
      ([], ⟨.emit (context, match check with
        | none => .value .completed value
        | some delayed => .conditional value delayed)
        (cursorRows fallback rows (position + 1) remaining), []⟩) := by
  rw [cursor_pending_packet fallback rows position remaining value context check found]
  rfl

/-- This is the earlier producer phase of the maintained native completion
model. Producer faults keep their actual effects and suppress private row
publication; the packet adapters below this boundary cannot consume those rows. -/
theorem producer_fault_precedes_projection {Effect : Type}
    (components : List (OwnedBind.NativeCompletion.Component Effect
      (Row Value Context Delay) Cause)) (cause : Cause)
    (failed : (OwnedBind.NativeCompletion.reference components).2 = .error cause) :
    ∃ allowance, advance allowance
      ⟨OwnedBind.NativeCompletion.lowerWith
        id [] components, []⟩ =
      ((OwnedBind.NativeCompletion.reference components).1,
        ⟨.done (.error cause), []⟩) := by
  obtain ⟨allowance, exactRun⟩ := OwnedBind.NativeCompletion.driverWith_refines
    id components
  exact ⟨allowance, by simpa [failed, Except.map] using exactRun⟩

/-- A normal form for a driver word containing only pending publication
operations. It is derived below from the indexed algorithm, not its definition. -/
def publicationWord (packets : List (Packet Value Context Delay)) (exit : Exit Cause) :
    Program (Exit Cause) (Packet Value Context Delay) :=
  packets.foldr Program.emit (.done exit)

theorem source_program_publication_word (rows : List (Row Value Context Delay)) :
    (sourceProgram rows : Program (Exit Cause) _) =
      publicationWord (sourceRows (Cause := Cause) rows).1
        (sourceRows (Cause := Cause) rows).2 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      cases row with
      | zero => exact ih
      | malformed => rfl
      | data value context check =>
          have mapped := congrArg (Program.emit (context, match check with
            | none => .value .completed value
            | some delayed => .conditional value delayed)) ih
          simpa [sourceProgram, sourceRows, publicationWord] using mapped

theorem cursor_publication_word (fallback : Context)
    (buffer : Buffer Value Context Delay Cause) :
    cursor fallback buffer = publicationWord (source buffer).1 (source buffer).2 := by
  cases buffer with
  | mk rows incomplete =>
      cases incomplete with
      | some cause => rfl
      | none =>
          have enough : rows.toList.take rows.size = rows.toList :=
            List.take_of_length_le (by simp)
          simpa [cursor, source, cursor_rows_refine, enough] using
            (source_program_publication_word (Cause := Cause) rows.toList)

theorem publication_word_prefix (packets : List (Packet Value Context Delay))
    (exit : Exit Cause) (allowance : Nat) :
    advance allowance ⟨publicationWord packets exit, []⟩ =
      (packets.take allowance, ⟨publicationWord (packets.drop allowance) exit, []⟩) := by
  induction allowance generalizing packets with
  | zero => rfl
  | succ allowance ih =>
      cases packets with
      | nil => rfl
      | cons packet packets =>
          simpa [publicationWord, advance, transition] using
            congrArg (fun pair => (packet :: pair.1, pair.2)) (ih packets)

/-- Every accepted-prefix budget returns exactly its source prefix and keeps
precisely the undelivered suffix, including its original terminal cause. -/
theorem cursor_prefix_exact (fallback : Context)
    (buffer : Buffer Value Context Delay Cause) (allowance : Nat) :
    advance allowance ⟨cursor fallback buffer, []⟩ =
      ((source buffer).1.take allowance,
        ⟨publicationWord ((source buffer).1.drop allowance) (source buffer).2, []⟩) := by
  rw [cursor_publication_word, publication_word_prefix]

/-- A direct leaf may keep its fast acceptance loop. A receiver that accepts
this many values then refuses produces exactly the same prefix as the cursor.
Zero rows do not consume the publication quota. -/
def leafQuota (fallback : Context) : Nat → List (Row Value Context Delay) →
    List (Packet Value Context Delay)
  | _, [] => []
  | quota, row :: rest =>
      let selected := nativeRow fallback row
      match selected.2, selected.1 with
      | .complete, [] => leafQuota fallback quota rest
      | .complete, packet :: _ => match quota with
        | 0 => []
        | next + 1 => packet :: leafQuota fallback next rest
      | _, _ => []

theorem leaf_quota_refines (fallback : Context) (quota : Nat)
    (rows : List (Row Value Context Delay)) :
    leafQuota fallback quota rows = (sourceRows (Cause := Cause) rows).1.take quota := by
  induction rows generalizing quota with
  | nil => simp [leafQuota, sourceRows]
  | cons row rows ih =>
      cases row with
      | zero => simpa [leafQuota, nativeRow, rowSource, rowContext,
          NativeCallReturn.meaning, sourceRows] using ih quota
      | malformed => simp [leafQuota, nativeRow, rowSource,
          NativeCallReturn.meaning, sourceRows]
      | data value context check =>
          cases check <;> cases quota <;>
            simp [leafQuota, nativeRow, rowSource, rowContext,
              NativeCallReturn.meaning, sourceRows, ih]

namespace Controls

abbrev TestRow := Row String Nat String
abbrev TestBuffer := Buffer String Nat String String

def completeData : TestBuffer :=
  ⟨#[.data "Empty" 7 none, .zero, .data "Error" 9 (some "check"),
    .data "(readln!)" 7 none, .data "Empty" 7 none], none⟩

/-- Payloads established as data keep zero/error/code-shaped syntax;
classified zero alone disappears and duplicate occurrences remain separate. -/
theorem data_roles_and_multiplicity :
    (source completeData).1 =
      [(7, .value .completed "Empty"), (9, .conditional "Error" "check"),
       (7, .value .completed "(readln!)"), (7, .value .completed "Empty")] := by decide

def interruptedData : TestBuffer := { completeData with incomplete := some "cancelled" }

theorem buffered_prefix_is_not_completed_publication :
    source interruptedData = ([], .incomplete "cancelled") ∧
    (sourceRows (Cause := String) interruptedData.rows.toList).1 ≠ [] := by decide

theorem complete_zero_differs_from_interruption :
    source (⟨#[.zero], none⟩ : TestBuffer) = ([], .complete) ∧
    source (⟨#[], some "cancelled"⟩ : TestBuffer) = ([], .incomplete "cancelled") := by decide

theorem malformed_row_is_not_logical_failure :
    source (⟨#[.data "kept" 3 none, .malformed], none⟩ : TestBuffer) =
      ([(3, .value .completed "kept")], .hostFailure) := by decide

/-- A consumer can have a visible effect. Gating after publication would
increment this world and disclose a packet from the incomplete buffer. -/
theorem late_completion_check_changes_world :
    interpret (fun _ : Packet String Nat String => Nat.succ)
      (sourceRows (Cause := String) interruptedData.rows.toList).1 2 ≠
      (leafFrame (fun _ : Packet String Nat String => Nat.succ)
        0 2 [] interruptedData).world := by decide

end Controls

namespace NativeEntry

variable {World Fault : Type}

abbrev NativeSource (Value Fault Delay : Type) := NativeCallReturn.Source Value Fault Delay

inductive Parent (Cause : Type) where
  | absent
  | clean
  | diagnostic (cause : Cause)
  | stopped (cause : Cause)
  deriving DecidableEq, Repr

def inherited : Parent Cause → Option Cause
  | .stopped cause => some cause
  | _ => none

/-- The child's own completion and the parent's diagnostic state are different
observations. An absent parent has no state to settle into. -/
def settleParent : Parent Cause → Option Cause → Option (Option Cause)
  | .absent, _ => none
  | .clean, own => some own
  | .diagnostic old, own | .stopped old, own =>
      some (NativeCallReturn.recordCompletion (some old) own)

inductive Input (Value Fault Delay : Type) where
  | deferred
  | entered (packet : NativeSource Value Fault Delay)

structure Invoked (World Value Fault Delay Cause : Type) where
  world : World
  packet : NativeSource Value Fault Delay
  own : Option Cause

structure Delivered (World Value Context Delay Cause : Type) where
  world : World
  buffer : Buffer Value Context Delay Cause

structure Services (World Value Context Fault Delay Cause : Type) where
  invoke : World → Invoked World Value Fault Delay Cause
  deliver : World → NativeSource Value Fault Delay → Delivered World Value Context Delay Cause
  hostFailure : Cause
  cancelled : Cause

inductive Image (Value Context Fault Delay Cause : Type) where
  | native (packet : NativeSource Value Fault Delay)
  | buffered (buffer : Buffer Value Context Delay Cause)

inductive Event where
  | scope | invoke | deliver | settle
  deriving DecidableEq, Repr

structure Report (World Value Context Fault Delay Cause : Type) where
  world : World
  image : Option (Image Value Context Fault Delay Cause)
  own : Option Cause
  parent : Option (Option Cause)
  trace : List Event

/-- Source completion after a successful provider entry; invocation's own
failure is checked by reference before this decoder is ever reached. -/
def referencePacket (services : Services World Value Context Fault Delay Cause)
    (parent : Parent Cause) (world : World) (packet : NativeSource Value Fault Delay)
    (trace : List Event) : Report World Value Context Fault Delay Cause :=
  match packet with
  | .invalid => ⟨world, none, some services.hostFailure,
      settleParent parent (some services.hostFailure), trace ++ [.settle]⟩
  | .interrupted | .one (.raised _) =>
      ⟨world, some (.native packet), none, settleParent parent none, trace ++ [.settle]⟩
  | _ =>
      let delivered := services.deliver world packet
      ⟨delivered.world, some (.buffered delivered.buffer), delivered.buffer.incomplete,
        settleParent parent delivered.buffer.incomplete, trace ++ [.deliver, .settle]⟩

/-- Source workflow after strong inherited interruption has been ruled out. -/
def referenceActive (services : Services World Value Context Fault Delay Cause)
    (parent : Parent Cause) (input : Input Value Fault Delay) (world : World) :
    Report World Value Context Fault Delay Cause :=
  match input with
  | .entered packet => referencePacket services parent world packet [.scope]
  | .deferred =>
      let invoked := services.invoke world
      match invoked.own with
      | some cause => ⟨invoked.world, none, some cause,
          settleParent parent (some cause), [.scope, .invoke, .settle]⟩
      | none => referencePacket services parent invoked.world invoked.packet [.scope, .invoke]

/-- Independent recursive entry specification. Strong inherited interruption
stops both callbacks; weak earlier diagnostics do not replace own completion. -/
def reference (services : Services World Value Context Fault Delay Cause)
    (parent : Parent Cause) (input : Input Value Fault Delay) (world : World) :
    Report World Value Context Fault Delay Cause :=
  match parent with
  | .stopped cause => ⟨world, none, some cause, settleParent parent (some cause),
      [.scope, .settle]⟩
  | _ => referenceActive services parent input world

inductive Phase (Value Fault Delay : Type) where
  | enter (input : Input Value Fault Delay)
  | invoke
  | packet (packet : NativeSource Value Fault Delay)
  | deliver (packet : NativeSource Value Fault Delay)
  | finish
  | done

structure State (World Value Context Fault Delay Cause : Type) where
  world : World
  phase : Phase Value Fault Delay
  own : Option Cause
  image : Option (Image Value Context Fault Delay Cause)
  parent : Option (Option Cause)
  trace : List Event

/-- The target opens one local episode before invoking or completing work,
even without a parent tracker. Purse borrowing/settlement is a separate law. -/
def initial (parent : Parent Cause) (input : Input Value Fault Delay) (world : World) :
    State World Value Context Fault Delay Cause :=
  ⟨world, .enter input, inherited parent, none, settleParent parent none, [.scope]⟩

def transition (services : Services World Value Context Fault Delay Cause)
    (parent : Parent Cause) (state : State World Value Context Fault Delay Cause) :
    Option (State World Value Context Fault Delay Cause) :=
  match state.phase with
  | .done => none
  | .enter input => some { state with phase :=
      if state.own.isSome then .finish else match input with
        | .deferred => .invoke
        | .entered packet => .packet packet }
  | .invoke =>
      let result := services.invoke state.world
      let own := NativeCallReturn.recordCompletion state.own result.own
      some { state with
        world := result.world, own := own,
        phase := if own.isSome then .finish else .packet result.packet,
        trace := state.trace ++ [.invoke] }
  | .packet packet => some (match packet with
      | .invalid => { state with own := some services.hostFailure, phase := .finish }
      | .interrupted | .one (.raised _) =>
          { state with image := some (.native packet), phase := .finish }
      | _ => { state with phase := .deliver packet })
  | .deliver packet =>
      let result := services.deliver state.world packet
      some { state with
        world := result.world, image := some (.buffered result.buffer),
        own := NativeCallReturn.recordCompletion state.own result.buffer.incomplete,
        phase := .finish, trace := state.trace ++ [.deliver] }
  | .finish => some { state with
      phase := .done,
      parent := settleParent parent state.own, trace := state.trace ++ [.settle] }

def advance (services : Services World Value Context Fault Delay Cause)
    (parent : Parent Cause) : Nat → State World Value Context Fault Delay Cause →
    State World Value Context Fault Delay Cause
  | 0, state => state
  | remaining + 1, state => match transition services parent state with
    | none => state
    | some next => advance services parent remaining next

def view (state : State World Value Context Fault Delay Cause) :
    Report World Value Context Fault Delay Cause :=
  ⟨state.world, state.image, state.own, state.parent, state.trace⟩

def execute (services : Services World Value Context Fault Delay Cause)
    (parent : Parent Cause) (input : Input Value Fault Delay) (world : World) :=
  advance services parent 5 (initial parent input world)

theorem execute_active_exact (services : Services World Value Context Fault Delay Cause)
    (parent : Parent Cause) (input : Input Value Fault Delay) (world : World)
    (active : inherited parent = none) :
    (view (execute services parent input world), (execute services parent input world).phase) =
      (referenceActive services parent input world, .done) := by
  cases input with
  | entered packet =>
      cases packet with
      | one native =>
          cases native <;> simp [execute, initial, active, advance, transition,
            referenceActive, referencePacket, view, NativeCallReturn.recordCompletion]
      | frontier role values =>
          simp [execute, initial, active, advance, transition,
            referenceActive, referencePacket, view, NativeCallReturn.recordCompletion]
      | failure | interrupted | invalid =>
          simp [execute, initial, active, advance, transition,
            referenceActive, referencePacket, view, NativeCallReturn.recordCompletion]
  | deferred =>
      cases received : services.invoke world with
      | mk calledWorld packet own =>
          cases own with
          | some cause =>
              simp [execute, initial, active, advance, transition, referenceActive,
                received, view, NativeCallReturn.recordCompletion]
          | none =>
              cases packet with
              | one native =>
                  cases native <;> simp [execute, initial, active, advance, transition,
                    referenceActive, referencePacket, received, view,
                    NativeCallReturn.recordCompletion]
              | frontier role values =>
                  simp [execute, initial, active, advance, transition,
                    referenceActive, referencePacket, received, view,
                    NativeCallReturn.recordCompletion]
              | failure | interrupted | invalid =>
                  simp [execute, initial, active, advance, transition,
                    referenceActive, referencePacket, received, view,
                    NativeCallReturn.recordCompletion]

theorem execute_active_refines (services : Services World Value Context Fault Delay Cause)
    (parent : Parent Cause) (input : Input Value Fault Delay) (world : World)
    (active : inherited parent = none) :
    view (execute services parent input world) = referenceActive services parent input world :=
  congrArg Prod.fst (execute_active_exact services parent input world active)

/-- The complete explicit invoke/packet/delivery/settlement machine refines
recursive entry for arbitrary native effects and independently tagged causes. -/
theorem execute_refines (services : Services World Value Context Fault Delay Cause)
    (parent : Parent Cause) (input : Input Value Fault Delay) (world : World) :
    view (execute services parent input world) = reference services parent input world := by
  cases parent with
  | stopped cause =>
      cases input <;> simp [execute, initial, inherited, advance, transition, reference, view]
  | absent => exact execute_active_refines services .absent input world rfl
  | clean => exact execute_active_refines services .clean input world rfl
  | diagnostic cause => exact execute_active_refines services (.diagnostic cause) input world rfl


theorem strong_parent_stops_before_work
    (services : Services World Value Context Fault Delay Cause) (cause : Cause)
    (input : Input Value Fault Delay) (world : World) :
    view (execute services (.stopped cause) input world) =
      ⟨world, none, some cause, some (some cause), [.scope, .settle]⟩ := by
  rw [execute_refines]
  rfl

/-- Replacing the provider by arbitrary different work has no effect on an
already-entered packet. The entry controller never invokes that provider again. -/
theorem entered_skips_invoke
    (services : Services World Value Context Fault Delay Cause)
    (replacement : World → Invoked World Value Fault Delay Cause)
    (parent : Parent Cause) (packet : NativeSource Value Fault Delay) (world : World) :
    view (execute { services with invoke := replacement } parent (.entered packet) world) =
      view (execute services parent (.entered packet) world) := by
  rw [execute_refines, execute_refines]
  cases parent <;> simp [reference, referenceActive, referencePacket]

/-- A provider's actual own failure takes precedence over packet shape and
fallback. Neither delivery nor private publication is reached. -/
theorem invoke_failure_keeps_own_cause
    (services : Services World Value Context Fault Delay Cause)
    (parent : Parent Cause) (world : World) (cause : Cause)
    (active : inherited parent = none)
    (failed : (services.invoke world).own = some cause) :
    view (execute services parent .deferred world) =
      ⟨(services.invoke world).world, none, some cause,
        settleParent parent (some cause), [.scope, .invoke, .settle]⟩ := by
  rw [execute_refines]
  cases parent <;> simp_all [reference, referenceActive, inherited]

/-- A weak earlier diagnostic does not prevent the new source's invoke and
delivery phases. It survives separately as the parent's first diagnostic. -/
theorem weak_parent_keeps_own_completion
    (services : Services World Value Context Fault Delay Cause)
    (old : Cause) (world : World) :
    (view (execute services (.diagnostic old) .deferred world)).own =
      (view (execute services .absent .deferred world)).own := by
  rw [execute_refines, execute_refines]
  cases invoked : (services.invoke world).own with
  | some cause => simp [reference, referenceActive, invoked]
  | none =>
      cases packet : (services.invoke world).packet with
      | one native => cases native <;> simp [reference, referenceActive, invoked,
          referencePacket, packet]
      | frontier role values => simp [reference, referenceActive, invoked, referencePacket, packet]
      | failure | interrupted | invalid =>
          simp [reference, referenceActive, invoked, referencePacket, packet]

theorem parent_first_cause_survives (old : Cause) (observed : Option Cause) :
    settleParent (.diagnostic old) observed = some (some old) := rfl

abbrev NativePull (Value Context Fault Delay : Type) :=
  NativeCallReturn.Pull (NativeCallReturn.Returned Value Fault Delay Context)
    (NativeCallReturn.Cursor Value Fault Delay Context)

/-- Completion gates the terminal cursor as well as the buffered path.
Unknown interruption fallback is consulted only when no own cause exists. -/
def terminalLoan (services : Services World Value Context Fault Delay Cause)
    (context : Context) (result : Report World Value Context Fault Delay Cause) :
    Except Cause (Option (NativePull Value Context Fault Delay)) :=
  match result.own with
  | some cause => .error cause
  | none => match result.image with
    | some (.native packet) =>
        match NativeCallReturn.read ⟨packet, context, 0⟩ with
        | .stopped .cancelled => .error services.cancelled
        | .stopped .hostFailure => .error services.hostFailure
        | selected => .ok (some selected)
    | _ => .ok none

def bufferedImage (result : Report World Value Context Fault Delay Cause) :
    Option (Buffer Value Context Delay Cause) :=
  match result.image with
  | some (.buffered buffer) => some { buffer with
      incomplete := NativeCallReturn.recordCompletion result.own buffer.incomplete }
  | _ => none

theorem own_cause_blocks_terminal
    (services : Services World Value Context Fault Delay Cause) (context : Context)
    (result : Report World Value Context Fault Delay Cause) (cause : Cause)
    (failed : result.own = some cause) :
    terminalLoan services context result = .error cause := by
  simp [terminalLoan, failed]

/-- A value-looking buffered packet cannot bypass the same gate. -/
theorem own_cause_blocks_buffer
    (result : Report World Value Context Fault Delay Cause) (cause : Cause)
    (buffer : Buffer Value Context Delay Cause)
    (failed : result.own = some cause) (held : result.image = some (.buffered buffer)) :
    (bufferedImage result).map source = some ([], .incomplete cause) := by
  simp [bufferedImage, held, failed, NativeCallReturn.recordCompletion, source]

/-- A terminal raised packet retains the precise fault and binding context;
it is never converted into an ordinary Error-shaped data value. -/
theorem raised_terminal_keeps_packet
    (services : Services World Value Context Fault Delay Cause) (context : Context)
    (world : World) (fault : Fault) (parent : Option (Option Cause)) (trace : List Event) :
    terminalLoan services context
      ⟨world, some (.native (.one (.raised fault))), none, parent, trace⟩ =
      .ok (some (.returned (context, .raised fault)
        ⟨.one (.raised fault), context, 1⟩)) := rfl

theorem uncategorized_interruption_uses_fallback
    (services : Services World Value Context Fault Delay Cause) (context : Context)
    (world : World) (parent : Option (Option Cause)) (trace : List Event) :
    terminalLoan services context
      ⟨world, some (.native .interrupted), none, parent, trace⟩ =
      .error services.cancelled := rfl


theorem execute_done (services : Services World Value Context Fault Delay Cause)
    (parent : Parent Cause) (input : Input Value Fault Delay) (world : World) :
    (execute services parent input world).phase = .done := by
  cases parent with
  | stopped cause =>
      cases input <;> simp [execute, initial, inherited, advance, transition]
  | absent => exact congrArg Prod.snd (execute_active_exact services .absent input world rfl)
  | clean => exact congrArg Prod.snd (execute_active_exact services .clean input world rfl)
  | diagnostic cause =>
      exact congrArg Prod.snd (execute_active_exact services (.diagnostic cause) input world rfl)

theorem advance_done (services : Services World Value Context Fault Delay Cause)
    (parent : Parent Cause) (state : State World Value Context Fault Delay Cause)
    (terminal : state.phase = .done) (allowance : Nat) :
    advance services parent allowance state = state := by
  cases allowance <;> simp [advance, transition, terminal]

/-- This is the maintained packet driver's complete initial-loan refinement.
The captured context and conditional checks survive the entry adapter unchanged. -/
theorem native_packet_driver_refines (context : Context)
    (packet : NativeSource Value Fault Delay) :
    (NativeCallReturn.read (⟨packet, context, 0⟩ :
      NativeCallReturn.Cursor Value Fault Delay Context)).mapState NativeCallReturn.residual =
      NativeCallReturn.referenceRead (NativeCallReturn.meaning packet context) := by
  simpa [NativeCallReturn.residual] using
    (NativeCallReturn.read_refines (⟨packet, context, 0⟩ :
      NativeCallReturn.Cursor Value Fault Delay Context))


/-- Resuming the retained completed entry controller repeats neither provider work,
delivery, nor parent settlement. This is not a fresh call of execute. -/
theorem retained_execution_does_not_replay
    (services : Services World Value Context Fault Delay Cause)
    (parent : Parent Cause) (input : Input Value Fault Delay) (world : World)
    (allowance : Nat) :
    advance services parent allowance (execute services parent input world) =
      execute services parent input world :=
  advance_done services parent _ (execute_done services parent input world) allowance

namespace Controls

abbrev TestServices := Services Nat String Nat String String String

def failedProvider : TestServices where
  invoke := fun world => ⟨world + 1, .interrupted, some "fuel"⟩
  deliver := fun world _ => ⟨world + 100,
    ⟨#[.data "unpermitted" 7 (some "check")], none⟩⟩
  hostFailure := "host"
  cancelled := "cancelled"

def successfulProvider : TestServices :=
  { failedProvider with
    invoke := fun world => ⟨world + 1, .one (.value .expression "body"), none⟩
    deliver := fun world _ => ⟨world + 10,
      ⟨#[.data "result" 7 (some "check")], none⟩⟩ }

theorem missing_parent_preserves_actual_native_reason :
    let result := view (execute failedProvider .absent .deferred 0)
    result.world = 1 ∧ result.own = some "fuel" ∧ result.parent = none ∧
      result.trace = [.scope, .invoke, .settle] ∧
      terminalLoan failedProvider 7 result = .error "fuel" := by decide

/-- A provider may leave a value-looking packet while reporting incomplete.
The packet cannot authorize another interpretation phase. -/
theorem value_looking_incomplete_does_not_deliver :
    let services : TestServices := { failedProvider with
      invoke := fun world => ⟨world + 1, .one (.value .expression "body"), some "fuel"⟩ }
    let result := view (execute services .absent .deferred 0)
    result.world = 1 ∧ result.own = some "fuel" ∧ result.image = none ∧
      result.trace = [.scope, .invoke, .settle] := by decide

theorem weak_parent_cannot_replace_own_reason :
    let result := view (execute failedProvider (.diagnostic "host") .deferred 0)
    result.own = some "fuel" ∧ result.parent = some (some "host") ∧
      terminalLoan failedProvider 7 result = .error "fuel" := by decide

theorem weak_parent_does_not_spoil_success :
    let result := view (execute successfulProvider (.diagnostic "host") .deferred 0)
    result.world = 11 ∧ result.own = none ∧ result.parent = some (some "host") ∧
      (bufferedImage result).map (leaf 0) =
        some ([(7, .conditional "result" "check")], .complete) := by decide

theorem entered_packet_skips_original_effect :
    let result := view (execute successfulProvider .clean
      (.entered (.one (.value .expression "body"))) 0)
    result.world = 10 ∧ result.own = none ∧
      result.trace = [.scope, .deliver, .settle] := by decide

theorem strong_parent_enters_no_new_work :
    let result := view (execute successfulProvider (.stopped "host") .deferred 0)
    result.world = 0 ∧ result.own = some "host" ∧
      result.trace = [.scope, .settle] := by decide


/-- Opening the completion scope after invocation loses the explicitly
reported cause, causing the terminal packet's generic fallback to win. -/
theorem invocation_outside_scope_loses_cause :
    let invoked := failedProvider.invoke 0
    let wrong := referencePacket failedProvider .absent invoked.world invoked.packet
      [.invoke, .scope]
    terminalLoan failedProvider 7 wrong = .error "cancelled" ∧
      terminalLoan failedProvider 7 (view (execute failedProvider .absent .deferred 0)) =
        .error "fuel" := by exact ⟨rfl, rfl⟩

/-- Copying a weak parent's diagnostic into an otherwise successful child
would discard its result and its still-live delayed check. -/
theorem copying_parent_diagnostic_spoils_child :
    let correct := view (execute successfulProvider (.diagnostic "host") .deferred 0)
    let wrong := { correct with own := some "host" }
    (bufferedImage correct).map (leaf 0) =
      some ([(7, .conditional "result" "check")], .complete) ∧
      (bufferedImage wrong).map (leaf 0) = some ([], .incomplete "host") := by exact ⟨rfl, rfl⟩

end Controls

end NativeEntry


namespace CallbackDisposition

open NativeEntry (Parent Input NativeSource settleParent inherited)

variable {World Value Fault Delay Cause Context : Type}

/-- The Boolean classifies admission; it does not classify the output storage.
The actual world is retained even when the provider reports decline. -/
structure Reply (World Value Fault Delay Cause : Type) where
  world : World
  handled : Bool
  packet : NativeSource Value Fault Delay
  own : Option Cause
  deriving DecidableEq, Repr

/-- Own interruption is read before the handled flag or unused packet.
The maintained deferred/entered vocabulary needs no additional value tag. -/
def classify (reply : Reply World Value Fault Delay Cause) :
    Except Cause (Input Value Fault Delay) :=
  match reply.own with
  | some cause => .error cause
  | none => if reply.handled then .ok (.entered reply.packet) else .ok .deferred

structure Services (World Value Fault Delay Cause : Type) where
  invoke : World → Reply World Value Fault Delay Cause
  ordinary : World → NativeEntry.Invoked World Value Fault Delay Cause

inductive Event where
  | native | ordinary | settle
  deriving DecidableEq, Repr

structure Report (World Value Fault Delay Cause : Type) where
  world : World
  packet : Option (NativeSource Value Fault Delay)
  own : Option Cause
  parent : Option (Option Cause)
  events : List Event
  deriving DecidableEq, Repr

/-- Independent source workflow: a complete decline calls ordinary evaluation
at the world the provider actually reached. There is no packet read in that
branch and no premise erasing declined-provider effects. -/
def referenceActive (services : Services World Value Fault Delay Cause)
    (parent : Parent Cause) (world : World) : Report World Value Fault Delay Cause :=
  let reply := services.invoke world
  match reply.own with
  | some cause => ⟨reply.world, none, some cause, settleParent parent (some cause),
      [.native, .settle]⟩
  | none =>
      if reply.handled then
        ⟨reply.world, some reply.packet, none, settleParent parent none, [.native, .settle]⟩
      else
        let fallback := services.ordinary reply.world
        ⟨fallback.world, if fallback.own.isSome then none else some fallback.packet,
          fallback.own, settleParent parent fallback.own, [.native, .ordinary, .settle]⟩

def reference (services : Services World Value Fault Delay Cause)
    (parent : Parent Cause) (world : World) : Report World Value Fault Delay Cause :=
  match inherited parent with
  | some cause => ⟨world, none, some cause, settleParent parent (some cause), [.settle]⟩
  | none => referenceActive services parent world

inductive Phase (World Value Fault Delay Cause : Type) where
  | invoke
  | classify (reply : Reply World Value Fault Delay Cause)
  | ordinary
  | finish
  | done

structure State (World Value Fault Delay Cause : Type) where
  world : World
  phase : Phase World Value Fault Delay Cause
  packet : Option (NativeSource Value Fault Delay)
  own : Option Cause
  parent : Option (Option Cause)
  events : List Event

def initial (parent : Parent Cause) (world : World) : State World Value Fault Delay Cause :=
  ⟨world, if (inherited parent).isSome then .finish else .invoke,
    none, inherited parent, settleParent parent none, []⟩

/-- The client stores the reply and only then dispatches its classification.
Provider work, fallback work and first-cause settlement are separate transitions. -/
def transition (services : Services World Value Fault Delay Cause)
    (parent : Parent Cause) (state : State World Value Fault Delay Cause) :
    Option (State World Value Fault Delay Cause) :=
  match state.phase with
  | .done => none
  | .invoke =>
      let reply := services.invoke state.world
      some { state with
        world := reply.world, phase := .classify reply,
        events := state.events ++ [.native] }
  | .classify reply =>
      some (match classify reply with
        | .error cause => { state with own := some cause, packet := none, phase := .finish }
        | .ok .deferred => { state with phase := .ordinary }
        | .ok (.entered packet) => { state with packet := some packet, phase := .finish })
  | .ordinary =>
      let fallback := services.ordinary state.world
      some { state with
        world := fallback.world, own := fallback.own,
        packet := if fallback.own.isSome then none else some fallback.packet,
        phase := .finish, events := state.events ++ [.ordinary] }
  | .finish => some { state with
      parent := settleParent parent state.own,
      phase := .done, events := state.events ++ [.settle] }

def advance (services : Services World Value Fault Delay Cause)
    (parent : Parent Cause) : Nat → State World Value Fault Delay Cause →
    State World Value Fault Delay Cause
  | 0, state => state
  | remaining + 1, state => match transition services parent state with
    | none => state
    | some next => advance services parent remaining next

def view (state : State World Value Fault Delay Cause) : Report World Value Fault Delay Cause :=
  ⟨state.world, state.packet, state.own, state.parent, state.events⟩

def execute (services : Services World Value Fault Delay Cause)
    (parent : Parent Cause) (world : World) : State World Value Fault Delay Cause :=
  advance services parent 4 (initial parent world)

/-- The independent source and explicit client agree for arbitrary providers
and ordinary evaluators, including their actual effects and own causes. -/
theorem execute_exact (services : Services World Value Fault Delay Cause)
    (parent : Parent Cause) (world : World) :
    (view (execute services parent world), (execute services parent world).phase) =
      (reference services parent world, .done) := by
  cases strong : inherited parent with
  | some cause =>
      simp [execute, initial, strong, advance, transition, reference, view]
  | none =>
      cases reply : services.invoke world with
      | mk reached handled packet own =>
          cases own <;> cases handled <;>
            simp [execute, initial, strong, advance, transition, classify,
              reference, referenceActive, reply, view]

theorem execute_refines (services : Services World Value Fault Delay Cause)
    (parent : Parent Cause) (world : World) :
    view (execute services parent world) = reference services parent world :=
  congrArg Prod.fst (execute_exact services parent world)

theorem own_cause_dominates (reply : Reply World Value Fault Delay Cause)
    (cause : Cause) (observed : reply.own = some cause) :
    classify reply = .error cause := by simp [classify, observed]

theorem complete_decline_has_no_packet (world : World)
    (unused : NativeSource Value Fault Delay) :
    classify (⟨world, false, unused, none⟩ : Reply World Value Fault Delay Cause) =
      .ok .deferred := rfl

theorem complete_entry_keeps_packet (world : World)
    (packet : NativeSource Value Fault Delay) :
    classify (⟨world, true, packet, none⟩ : Reply World Value Fault Delay Cause) =
      .ok (.entered packet) := rfl

/-- Unused output storage, of ANY native packet role, is observationally
irrelevant after a complete decline. No permanent refusal is installed. -/
theorem declined_storage_irrelevant (services : Services World Value Fault Delay Cause)
    (parent : Parent Cause) (world : World) (replacement : NativeSource Value Fault Delay)
    (declined : (services.invoke world).handled = false)
    (complete : (services.invoke world).own = none) :
    view (execute { services with invoke := fun before =>
      { services.invoke before with packet := replacement } } parent world) =
      view (execute services parent world) := by
  rw [execute_refines, execute_refines]
  cases stopped : inherited parent <;>
    simp [reference, stopped, referenceActive, declined, complete]

theorem ordinary_fallback_iff (services : Services World Value Fault Delay Cause)
    (parent : Parent Cause) (world : World) (active : inherited parent = none) :
    Event.ordinary ∈ (view (execute services parent world)).events ↔
      (services.invoke world).own = none ∧ (services.invoke world).handled = false := by
  rw [execute_refines]
  cases own : (services.invoke world).own <;>
    cases handled : (services.invoke world).handled <;>
      simp [reference, active, referenceActive, own, handled]

/-- A callback's own interruption forbids fallback even when it returned false.
Changing the ordinary evaluator therefore changes no observation. -/
theorem interrupted_never_falls_back (services : Services World Value Fault Delay Cause)
    (parent : Parent Cause) (world : World) (cause : Cause)
    (failed : (services.invoke world).own = some cause)
    (replacement : World → NativeEntry.Invoked World Value Fault Delay Cause) :
    view (execute { services with ordinary := replacement } parent world) =
      view (execute services parent world) := by
  rw [execute_refines, execute_refines]
  cases stopped : inherited parent <;> simp [reference, stopped, referenceActive, failed]

theorem active_provider_invoked_once (services : Services World Value Fault Delay Cause)
    (parent : Parent Cause) (world : World) (active : inherited parent = none) :
    (view (execute services parent world)).events.count .native = 1 := by
  rw [execute_refines]
  cases own : (services.invoke world).own <;>
    cases handled : (services.invoke world).handled <;>
      (simp only [reference, active, referenceActive, own, handled]; rfl)

/-- Interrupted work retains the exact world reached by the callback and the
actual own cause, while the parent's old first diagnostic stays separate. -/
theorem interruption_keeps_reached_world (services : Services World Value Fault Delay Cause)
    (parent : Parent Cause) (world : World) (cause : Cause)
    (active : inherited parent = none) (failed : (services.invoke world).own = some cause) :
    view (execute services parent world) =
      ⟨(services.invoke world).world, none, some cause, settleParent parent (some cause),
        [.native, .settle]⟩ := by
  rw [execute_refines]
  simp [reference, active, referenceActive, failed]

/-- For entered complete work the classifier transfers the packet without
interpreting it; the maintained occurrence reader owns the next boundary. -/
theorem entered_packet_driver_refines (services : Services World Value Fault Delay Cause)
    (parent : Parent Cause) (world : World) (context : Context)
    (active : inherited parent = none) (complete : (services.invoke world).own = none)
    (entered : (services.invoke world).handled = true) :
    (view (execute services parent world)).packet.map (fun packet =>
        (NativeCallReturn.read (⟨packet, context, 0⟩ :
          NativeCallReturn.Cursor Value Fault Delay Context)).mapState NativeCallReturn.residual) =
      some (NativeCallReturn.referenceRead
        (NativeCallReturn.meaning (services.invoke world).packet context)) := by
  rw [execute_refines]
  simp only [reference, active, referenceActive, complete, entered, if_true, Option.map_some]
  exact congrArg some (NativeEntry.native_packet_driver_refines context (services.invoke world).packet)

/-- Completing a retained classification never repeats provider, fallback or
settlement. A separate later request starts a fresh invocation instead. -/
theorem retained_execution_inert (services : Services World Value Fault Delay Cause)
    (parent : Parent Cause) (world : World) (allowance : Nat) :
    advance services parent allowance (execute services parent world) =
      execute services parent world := by
  have finished : (execute services parent world).phase = .done :=
    congrArg Prod.snd (execute_exact services parent world)
  cases allowance <;> simp [advance, transition, finished]

/-- The diagnostic retained by the parent is independent of whether this
callback declined, entered, completed ordinary fallback or was interrupted. -/
theorem prior_parent_cause_preserved (services : Services World Value Fault Delay Cause)
    (old : Cause) (world : World) :
    (view (execute services (.diagnostic old) world)).parent = some (some old) := by
  rw [execute_refines]
  cases own : (services.invoke world).own <;>
    cases handled : (services.invoke world).handled <;>
      simp [reference, inherited, referenceActive, own, handled, settleParent,
        NativeCallReturn.recordCompletion]

namespace Controls

abbrev TestServices := Services (List String) String String String String
abbrev TestReply := Reply (List String) String String String String

def ordinaryValue : NativeSource String String String := .one (.value .completed "fallback")

def declining : TestServices where
  invoke := fun world => ⟨world ++ ["native"], false, .failure, none⟩
  ordinary := fun world => ⟨world ++ ["ordinary"], ordinaryValue, none⟩

def failedDecline : TestServices :=
  { declining with invoke := fun world =>
    ⟨world ++ ["native"], false, .one (.value .expression "unused"), some "fuel"⟩ }

/-- Checking the cause only under true discards it on a false reply and
performs an ordinary effect which should never have been reached. -/
theorem ignoring_false_cause_runs_forbidden_fallback :
    let correct := view (execute failedDecline .clean [])
    let wrong := failedDecline.ordinary (failedDecline.invoke []).world
    correct.world = ["native"] ∧ correct.own = some "fuel" ∧
      wrong.world = ["native", "ordinary"] ∧ wrong.own = none := by decide

theorem false_poisoned_failure_is_not_logical_zero :
    let result := view (execute declining .clean [])
    result.packet = some ordinaryValue ∧ result.own = none ∧
      result.world = ["native", "ordinary"] := by decide

theorem false_poisoned_interruption_is_not_cancellation :
    let services : TestServices := { declining with invoke := fun world =>
      ⟨world ++ ["native"], false, .interrupted, none⟩ }
    let result := view (execute services .clean [])
    result.packet = some ordinaryValue ∧ result.own = none ∧
      result.events = [.native, .ordinary, .settle] := by decide

theorem false_poisoned_raise_and_data_are_ignored :
    let raised : TestServices := { declining with invoke := fun world =>
      ⟨world ++ ["native"], false, .one (.raised "unused"), none⟩ }
    let data : TestServices := { declining with invoke := fun world =>
      ⟨world ++ ["native"], false, .one (.value .completed "unused"), none⟩ }
    view (execute raised .clean []) = view (execute data .clean []) ∧
      (view (execute raised .clean [])).packet = some ordinaryValue := by decide

theorem true_logical_zero_is_distinct_from_decline :
    let entered : TestServices := { declining with invoke := fun world =>
      ⟨world ++ ["native"], true, .failure, none⟩ }
    (view (execute entered .clean [])).packet = some .failure ∧
      (view (execute entered .clean [])).world = ["native"] ∧
      (view (execute declining .clean [])).packet = some ordinaryValue ∧
      (view (execute declining .clean [])).world = ["native", "ordinary"] := by decide

theorem classification_distinguishes_zero_from_refusal :
    classify (⟨[], true, .failure, none⟩ : TestReply) ≠
      classify (⟨[], false, .failure, none⟩ : TestReply) := by
  intro impossible
  cases impossible

theorem true_packet_cannot_hide_own_interruption :
    let services : TestServices := { failedDecline with invoke := fun world =>
      ⟨world ++ ["native"], true, .one (.conditional "value" "delay"), some "fuel"⟩ }
    let result := view (execute services (.diagnostic "host") [])
    result.packet = none ∧ result.own = some "fuel" ∧ result.parent = some (some "host") ∧
      result.world = ["native"] := by decide

/-- A complete decline does not cache a permanent refusal: a separately
requested call consults the provider afresh in the actual reached world. -/
theorem explicit_fresh_request_after_decline_is_possible :
    let services : TestServices := { declining with invoke := fun world =>
      ⟨world ++ ["native"], !world.isEmpty, .one (.conditional "later" "check"), none⟩ }
    let first := view (execute services .clean [])
    let second := view (execute services .clean first.world)
    first.world = ["native", "ordinary"] ∧ first.packet = some ordinaryValue ∧
      second.world = ["native", "ordinary", "native"] ∧
      second.packet = some (.one (.conditional "later" "check")) ∧
      second.events = [.native, .settle] := by decide

/-- Ordinary fallback's own failure also gates its value-looking output,
without undoing the provider and fallback effects already committed. -/
theorem ordinary_failure_keeps_chronology_without_packet :
    let services : TestServices := { declining with ordinary := fun world =>
      ⟨world ++ ["ordinary"], ordinaryValue, some "capacity"⟩ }
    let result := view (execute services .clean [])
    result.world = ["native", "ordinary"] ∧ result.own = some "capacity" ∧
      result.packet = none ∧ result.parent = some (some "capacity") := by decide

end Controls

end CallbackDisposition


namespace EpisodeReuse

open ContextualCBPV.EpisodeAccounting

variable {World Item Cause : Type}

/-- The inactive word fields are retained, even for an unlimited episode. -/
@[ext] structure Episode (Cause : Type) where
  completion : Option Cause
  interrupted : Bool
  limited : Bool
  initial : Nat
  purse : Purse
  deriving DecidableEq, Repr

structure View (Cause : Type) where
  completion : Option Cause
  interrupted : Bool
  budget : Option (Nat × Purse)
  deriving DecidableEq, Repr

/-- Providers observe completion and active credit. Tracker address, scope
ancestry and inactive accounting words are outside this semantic view. -/
def observe (episode : Episode Cause) : View Cause :=
  ⟨episode.completion, episode.interrupted,
    if episode.limited then some (episode.initial, episode.purse) else none⟩

def eligible (episode : Episode Cause) : Bool :=
  episode.completion.isNone && !episode.interrupted && !episode.limited

def begin (parent : Episode Cause) (request : Option Nat) : Episode Cause :=
  let granted := grant request (if parent.limited then some parent.purse.remaining else none)
  ⟨if parent.interrupted then parent.completion else none, parent.interrupted,
    granted.isSome, granted.getD 0, ⟨granted.getD 0, 0⟩⟩

def finish (maximum : Nat) (parent child : Episode Cause) : Episode Cause :=
  { parent with
    completion := NativeCallReturn.recordCompletion parent.completion child.completion
    interrupted := parent.interrupted || child.interrupted
    purse := if parent.limited then nativeSettle maximum parent.purse child.purse else parent.purse }

def mark (cause : Cause) (strong : Bool) (episode : Episode Cause) : Episode Cause :=
  { episode with
    completion := NativeCallReturn.recordCompletion episode.completion (some cause)
    interrupted := episode.interrupted || strong }

/-- This is the native debit algorithm: strong interruption refuses before
charging; unlimited steps do not update the inactive accounting words. -/
def debitStep (maximum : Nat) (fuel : Cause) (cost : Nat) (episode : Episode Cause) :
    Bool × Episode Cause :=
  if episode.interrupted then (false, episode)
  else if episode.limited then
    match nativeDebit maximum cost episode.purse with
    | none => (false, mark fuel false episode)
    | some paid => (true, { episode with purse := paid })
  else (true, episode)

/-- Finite synchronous phase interactions. Effects can inspect the semantic
view and return arbitrary native packets; nested scopes use explicit requests.
Neither allocation nor scope identity is a language observation here. -/
inductive Phase (World Item Cause : Type) where
  | effect (apply : View Cause → World → World × Item)
  | native (invoke : View Cause → World → World × Item × Option Cause × Bool)
  | mark (cause : Cause) (strong : Bool)
  | debit (cost : Nat)
  | sequence (first later : Phase World Item Cause)
  | branch (select : View Cause → World → Bool) (yes no : Phase World Item Cause)
  | child (request : Option Nat) (body : Phase World Item Cause)

inductive Event (Item : Type) where
  | effect (item : Item)
  | debit (admitted : Bool)
  deriving DecidableEq, Repr

structure Result (World Item Cause : Type) where
  world : World
  episode : Episode Cause
  events : List (Event Item)
  deriving DecidableEq, Repr

/-- Interpretation follows actual debit, diagnostic and nested-settlement
transitions. Sequential effects retain production chronology. -/
def run (maximum : Nat) (fuel : Cause) : Phase World Item Cause →
    Episode Cause → World → Result World Item Cause
  | .effect apply, episode, world =>
      let result := apply (observe episode) world
      ⟨result.1, episode, [.effect result.2]⟩
  | .native invoke, episode, world =>
      let result := invoke (observe episode) world
      ⟨result.1, { episode with
        completion := NativeCallReturn.recordCompletion episode.completion result.2.2.1
        interrupted := episode.interrupted || result.2.2.2 }, [.effect result.2.1]⟩
  | .mark cause strong, episode, world => ⟨world, mark cause strong episode, []⟩
  | .debit cost, episode, world =>
      let result := debitStep maximum fuel cost episode
      ⟨world, result.2, [.debit result.1]⟩
  | .sequence first later, episode, world =>
      let before := run maximum fuel first episode world
      let after := run maximum fuel later before.episode before.world
      ⟨after.world, after.episode, before.events ++ after.events⟩
  | .branch select yes no, episode, world =>
      if select (observe episode) world then run maximum fuel yes episode world
      else run maximum fuel no episode world
  | .child request body, episode, world =>
      let child := run maximum fuel body (begin episode request) world
      ⟨child.world, finish maximum episode child.episode, child.events⟩

theorem begin_respects_view (first second : Episode Cause)
    (same : observe first = observe second) (request : Option Nat) :
    begin first request = begin second request := by
  rcases first with ⟨fc, fi, fl, fb, fp⟩
  rcases second with ⟨sc, si, sl, sb, sp⟩
  cases fl <;> cases sl <;> simp_all [observe, begin]

theorem mark_respects_view (first second : Episode Cause)
    (same : observe first = observe second) (cause : Cause) (strong : Bool) :
    observe (mark cause strong first) = observe (mark cause strong second) := by
  rcases first with ⟨fc, fi, fl, fb, fp⟩
  rcases second with ⟨sc, si, sl, sb, sp⟩
  cases fl <;> cases sl <;> simp_all [observe, mark]

theorem debit_respects_view (first second : Episode Cause)
    (same : observe first = observe second) (maximum cost : Nat) (fuel : Cause) :
    (debitStep maximum fuel cost first).1 = (debitStep maximum fuel cost second).1 ∧
      observe (debitStep maximum fuel cost first).2 =
        observe (debitStep maximum fuel cost second).2 := by
  rcases first with ⟨fc, fi, fl, fb, fp⟩
  rcases second with ⟨sc, si, sl, sb, sp⟩
  cases fl <;> cases sl <;> cases fi <;> cases si <;>
    simp_all [observe, debitStep, mark]

theorem finish_respects_parent_view (first second child : Episode Cause)
    (same : observe first = observe second) (maximum : Nat) :
    observe (finish maximum first child) = observe (finish maximum second child) := by
  rcases first with ⟨fc, fi, fl, fb, fp⟩
  rcases second with ⟨sc, si, sl, sb, sp⟩
  cases fl <;> cases sl <;> simp_all [observe, finish]

/-- The two phase runs execute the same branches, effects and source debits,
including arbitrary nested child requests and first-cause updates. -/
theorem phase_respects_view (maximum : Nat) (fuel : Cause)
    (phase : Phase World Item Cause) (first second : Episode Cause)
    (same : observe first = observe second) (world : World) :
    let left := run maximum fuel phase first world
    let right := run maximum fuel phase second world
    left.world = right.world ∧ left.events = right.events ∧
      observe left.episode = observe right.episode := by
  induction phase generalizing first second world with
  | effect apply => simp [run, same]
  | native invoke =>
      have completion := congrArg View.completion same
      have interruption := congrArg View.interrupted same
      have budget := congrArg View.budget same
      simp only [observe] at completion interruption budget
      simp [run, observe, completion, interruption, budget]
      rfl
  | mark cause strong => exact ⟨rfl, rfl, mark_respects_view first second same cause strong⟩
  | debit cost =>
      obtain ⟨admission, view⟩ := debit_respects_view first second same maximum cost fuel
      exact ⟨rfl, by simp [run, admission], view⟩
  | sequence firstPhase laterPhase ihFirst ihLater =>
      obtain ⟨worlds, events, views⟩ := ihFirst first second same world
      obtain ⟨laterWorlds, laterEvents, laterViews⟩ :=
        ihLater (run maximum fuel firstPhase first world).episode
          (run maximum fuel firstPhase second world).episode views
          (run maximum fuel firstPhase first world).world
      simp only [run]
      rw [← worlds]
      exact ⟨laterWorlds, by rw [events, laterEvents], laterViews⟩
  | branch select yes no ihYes ihNo =>
      simp only [run, same]
      split <;> first | exact ihYes first second same world | exact ihNo first second same world
  | child request body _ =>
      have starts := begin_respects_view first second same request
      simpa only [run, starts, true_and] using
        finish_respects_parent_view first second
          (run maximum fuel body (begin second request) world).episode same maximum

/-- Inactive accounting words never change during an unlimited phase, even
when nested limited children do real work and settle their local accounts. -/
theorem unlimited_fields_preserved (maximum : Nat) (fuel : Cause)
    (phase : Phase World Item Cause) (episode : Episode Cause)
    (unlimited : episode.limited = false) (world : World) :
    let after := (run maximum fuel phase episode world).episode
    after.limited = false ∧ after.initial = episode.initial ∧ after.purse = episode.purse := by
  induction phase generalizing episode world with
  | effect apply => exact ⟨unlimited, rfl, rfl⟩
  | native invoke => exact ⟨unlimited, rfl, rfl⟩
  | mark cause strong => exact ⟨unlimited, rfl, rfl⟩
  | debit cost =>
      cases interrupted : episode.interrupted <;>
        simp [run, debitStep, interrupted, unlimited]
  | sequence first later ihFirst ihLater =>
      obtain ⟨limit, initial, purse⟩ := ihFirst episode unlimited world
      obtain ⟨finalLimit, finalInitial, finalPurse⟩ :=
        ihLater (run maximum fuel first episode world).episode limit
          (run maximum fuel first episode world).world
      exact ⟨finalLimit, finalInitial.trans initial, finalPurse.trans purse⟩
  | branch select yes no ihYes ihNo =>
      simp only [run]
      split <;> first | exact ihYes episode unlimited world | exact ihNo episode unlimited world
  | child request body ih => simp [run, finish, unlimited]

@[ext] structure Observation (World Item Cause : Type) where
  world : World
  own : Option Cause
  parent : Episode Cause
  events : List (Event Item)
  deriving DecidableEq, Repr

/-- The reference creates a private child, then settles that child's actual
outcome into the paused parent. Own completion is retained separately. -/
def isolated (maximum : Nat) (fuel : Cause) (phase : Phase World Item Cause)
    (parent : Episode Cause) (world : World) : Observation World Item Cause :=
  let result := run maximum fuel phase (begin parent none) world
  ⟨result.world, result.episode.completion, finish maximum parent result.episode, result.events⟩

/-- The specialization leaves the active tracker in place and reads its own
phase completion before returning to the enclosing body episode. -/
def reused (maximum : Nat) (fuel : Cause) (phase : Phase World Item Cause)
    (parent : Episode Cause) (world : World) : Observation World Item Cause :=
  let result := run maximum fuel phase parent world
  ⟨result.world, result.episode.completion, result.episode, result.events⟩

theorem clean_unlimited_reuse (maximum : Nat) (fuel : Cause)
    (phase : Phase World Item Cause) (parent : Episode Cause)
    (admitted : eligible parent = true) (world : World) :
    reused maximum fuel phase parent world = isolated maximum fuel phase parent world := by
  have clean : parent.completion = none := by
    simpa [eligible] using (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp admitted).1).1
  have uninterrupted : parent.interrupted = false := by
    simpa [eligible] using (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp admitted).1).2
  have unlimited : parent.limited = false := by
    simpa [eligible] using (Bool.and_eq_true_iff.mp admitted).2
  have starts : observe parent = observe (begin parent none) := by
    simp [observe, begin, grant, clean, uninterrupted, unlimited]
  obtain ⟨worlds, events, views⟩ := phase_respects_view maximum fuel phase parent
    (begin parent none) starts world
  obtain ⟨unlimitedAfter, initialAfter, purseAfter⟩ :=
    unlimited_fields_preserved maximum fuel phase parent unlimited world
  have completion := congrArg View.completion views
  have interrupted := congrArg View.interrupted views
  simp only [observe] at completion interrupted
  dsimp only [reused, isolated]
  apply Observation.ext
  · exact worlds
  · exact completion
  · apply Episode.ext
    · simpa [finish, clean, NativeCallReturn.recordCompletion] using completion
    · simpa [finish, uninterrupted] using interrupted
    · simpa [finish] using unlimitedAfter.trans unlimited.symm
    · exact initialAfter
    · simpa [finish, unlimited] using purseAfter
  · exact events

/-- An existing diagnostic remains the first cause through every later phase,
regardless of nested effects, budget refusal, or stronger interruption. -/
theorem first_cause_preserved (maximum : Nat) (fuel : Cause)
    (phase : Phase World Item Cause) (episode : Episode Cause) (cause : Cause)
    (recorded : episode.completion = some cause) (world : World) :
    (run maximum fuel phase episode world).episode.completion = some cause := by
  induction phase generalizing episode world with
  | effect apply => exact recorded
  | native invoke => simp [run, recorded, NativeCallReturn.recordCompletion]
  | mark observed strong => simp [run, mark, recorded, NativeCallReturn.recordCompletion]
  | debit cost =>
      simp only [run, debitStep]
      split
      · exact recorded
      · split
        · split <;> simp_all [mark, NativeCallReturn.recordCompletion]
        · exact recorded
  | sequence first later ihFirst ihLater =>
      exact ihLater _ (ihFirst episode recorded world) _
  | branch select yes no ihYes ihNo =>
      simp only [run]
      split <;> first | exact ihYes episode recorded world | exact ihNo episode recorded world
  | child request body _ => simp [run, finish, recorded, NativeCallReturn.recordCompletion]

/-- The conservative dispatcher retains child isolation whenever the full
reuse guard is unavailable. Its active-parent argument establishes existence. -/
def selected (maximum : Nat) (fuel : Cause) (phase : Phase World Item Cause)
    (parent : Episode Cause) (world : World) : Observation World Item Cause :=
  if eligible parent then reused maximum fuel phase parent world
  else isolated maximum fuel phase parent world

theorem selected_refines (maximum : Nat) (fuel : Cause)
    (phase : Phase World Item Cause) (parent : Episode Cause) (world : World) :
    selected maximum fuel phase parent world = isolated maximum fuel phase parent world := by
  unfold selected
  split
  · exact clean_unlimited_reuse maximum fuel phase parent ‹_› world
  · rfl

namespace Controls

abbrev TestPhase := Phase Nat (View String) String

/-- These inactive fields deliberately differ from the fresh child's zeros. -/
def clean : Episode String := ⟨none, false, false, 91, ⟨37, 29⟩⟩
def weak : Episode String := { clean with completion := some "host" }
def limited : Episode String := ⟨none, false, true, 15, ⟨10, 5⟩⟩
def inspectView : TestPhase := .effect fun view world => (world + 1, view)

def nativePhase : TestPhase :=
  .sequence (.child (some 4) (.sequence (.debit 3)
      (.sequence (.mark "fuel" false) inspectView)))
    (.sequence (.mark "cancelled" true) inspectView)

/-- Outcome and cause can be selected by the provider's arbitrary effect,
rather than by a fixed sequence of diagnostic labels. -/
theorem dynamic_native_outcome_is_preserved :
    let phase : TestPhase := .native fun view world =>
      (world + 3, view, if world = 0 then some "fuel" else none, world = 0)
    reused 255 "fuel" phase clean 0 = isolated 255 "fuel" phase clean 0 ∧
      (reused 255 "fuel" phase clean 0).world = 3 ∧
      (reused 255 "fuel" phase clean 0).own = some "fuel" ∧
      (reused 255 "fuel" phase clean 0).parent.interrupted = true := by decide

theorem nested_effects_causes_and_inactive_words_agree :
    reused 255 "fuel" nativePhase clean 0 = isolated 255 "fuel" nativePhase clean 0 ∧
      (reused 255 "fuel" nativePhase clean 0).world = 2 ∧
      (reused 255 "fuel" nativePhase clean 0).own = some "fuel" ∧
      (reused 255 "fuel" nativePhase clean 0).parent.interrupted = true ∧
      (reused 255 "fuel" nativePhase clean 0).parent.initial = 91 ∧
      (reused 255 "fuel" nativePhase clean 0).parent.purse = ⟨37, 29⟩ := by decide

/-- Reusing a weak parent substitutes its old diagnostic for a successful
phase's own completion, although its committed effects still happened. -/
theorem weak_parent_reuse_spoils_success :
    (reused 255 "fuel" inspectView weak 0).own = some "host" ∧
      (isolated 255 "fuel" inspectView weak 0).own = none ∧
      (reused 255 "fuel" inspectView weak 0).world = 1 ∧
      (isolated 255 "fuel" inspectView weak 0).world = 1 := by decide

theorem weak_parent_reuse_loses_new_own_cause :
    (reused 255 "fuel" (.mark "fuel" false : TestPhase) weak 0).own = some "host" ∧
      (isolated 255 "fuel" (.mark "fuel" false : TestPhase) weak 0).own = some "fuel" ∧
      (isolated 255 "fuel" (.mark "fuel" false : TestPhase) weak 0).parent.completion =
        some "host" := by decide

/-- A limited tracker can have the same final account under this very small
phase. Finiteness alone is not a universal semantic counterexample. -/
theorem limited_single_debit_can_agree :
    reused 255 "fuel" (.debit 3 : TestPhase) limited 0 =
      isolated 255 "fuel" (.debit 3 : TestPhase) limited 0 := by decide

/-- The actual distinguishing observation is the active phase-local account:
the child starts at zero while direct reuse carries its parent's old spend. -/
theorem limited_phase_local_spend_distinguishes_reuse :
    let phase : TestPhase := .sequence (.debit 3) inspectView
    (reused 255 "fuel" phase limited 0).parent.purse = ⟨7, 8⟩ ∧
      (isolated 255 "fuel" phase limited 0).parent.purse = ⟨7, 8⟩ ∧
      (reused 255 "fuel" phase limited 0).events ≠
        (isolated 255 "fuel" phase limited 0).events := by decide

/-- Inactive-word introspection distinguishes even a clean unlimited phase.
That observation requires retaining the isolated child accounting context. -/
theorem inactive_counter_introspection_is_outside_the_quotient :
    clean.purse.spent = 29 ∧ (begin clean none).purse.spent = 0 ∧
      observe clean = observe (begin clean none) := by decide

theorem guard_excludes_weak_limited_and_strong_parents :
    eligible clean = true ∧ eligible weak = false ∧ eligible limited = false ∧
      eligible { clean with interrupted := true } = false := by decide

theorem limited_nested_overdraw_keeps_actual_debit_and_first_cause :
    let phase : TestPhase := .child (some 4)
      (.sequence (.debit 3) (.sequence (.debit 2) (.mark "cancelled" true)))
    let result := isolated 255 "fuel" phase limited 0
    result.own = some "fuel" ∧ result.parent.completion = some "fuel" ∧
      result.parent.purse = ⟨7, 8⟩ ∧
      result.events = [.debit true, .debit false] := by decide

end Controls

end EpisodeReuse


end Mettapedia.Machines.BufferedResidualReturn
