import Mettapedia.Languages.MeTTa.PeTTa.LibTransform

/-!
# A transform branch retains its computed let choice

The existing shared-world search trace supplies the source computation.
Capturing its results retains the complete bindings and a derived occurrence
ordinal. Firing uses that packet; it does not run the producer again. The
refinement preserves the whole future trace, including world changes between
answers, unsuccessful continuations, and duplicate result values.

This law does not move evaluation from firing to entry preparation. Either
phase can use it at its declared evaluation boundary. Occurrence ordinals
here distinguish the model's results; the counter-erasure law does not require
a native implementation to allocate an extra identifier for each result.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.LetChoicePackets

open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Trace Search)

variable {World Bindings Value Answer : Type}

structure Packet (Bindings Value : Type) where
  occurrence : Nat
  bindings : Bindings
  value : Value
  deriving Repr, DecidableEq

def capture (observe : Bindings → Value) (first : Nat) :
    Trace World Bindings → Trace World (Packet Bindings Value)
  | .done world => .done world
  | .answer bindings world later =>
      .answer ⟨first, bindings, observe bindings⟩ world
        (fun next => capture observe (first + 1) (later next))

def fire (captured : Trace World (Packet Bindings Value))
    (consume : Bindings → Search World Answer) : Trace World Answer :=
  captured.bind (fun packet => consume packet.bindings)

/-- Full retained-choice execution equals ordinary binding of the source
producer, for every continuation and every world the consumer leaves. -/
theorem fire_capture (observe : Bindings → Value) (first : Nat)
    (source : Trace World Bindings) (consume : Bindings → Search World Answer) :
    fire (capture observe first source) consume = source.bind consume := by
  induction source generalizing first with
  | done world => rfl
  | answer bindings world later ih =>
      simp only [capture, fire, Trace.bind]
      apply congrArg ((consume bindings world).append)
      funext next
      exact ih next (first + 1)

/-- The ordinal is proof/accounting metadata when firing observes only the
bindings. It can be erased without changing execution or adding a scan. -/
theorem counter_erasure (observe : Bindings → Value) (first second : Nat)
    (source : Trace World Bindings) (consume : Bindings → Search World Answer) :
    fire (capture observe first source) consume = fire (capture observe second source) consume := by
  rw [fire_capture, fire_capture]

theorem captured_first (observe : Bindings → Value) (first : Nat)
    (bindings : Bindings) (world : World) (later : World → Trace World Bindings) :
    (capture observe first (.answer bindings world later)).first? =
      some (⟨first, bindings, observe bindings⟩, world) := rfl

/-- A continuation that refuses the selected branch does not undo producer
effects. Later production resumes from the resulting shared world. -/
theorem refused_choice_keeps_world (observe : Bindings → Value) (first : Nat)
    (bindings : Bindings) (world : World) (later : World → Trace World Bindings)
    (consume : Bindings → Search World Answer)
    (refused : consume bindings world = .done world) :
    fire (capture observe first (.answer bindings world later)) consume =
      fire (capture observe (first + 1) (later world)) consume := by
  simp only [capture, fire, Trace.bind, refused, Trace.append]

namespace Controls

def pureChoices : Search Nat (Nat × Nat) :=
  Search.superpose [(7, 10), (7, 20)]

def readBinding (bindings : Nat × Nat) (world : Nat) : Trace Nat Nat :=
  .answer bindings.2 world .done

/-- Equal displayed values may carry different bindings required by the
continuation. The packet cannot in general be replaced by its value alone. -/
theorem equal_values_distinct_bindings :
    ((capture Prod.fst 0 (pureChoices 0)).drain.1.map Packet.value) = [7, 7] ∧
      (fire (capture Prod.fst 0 (pureChoices 0)) readBinding).drain = ([10, 20], 0) := by decide

theorem distinct_occurrences :
    ((capture Prod.fst 17 (pureChoices 0)).drain.1.map Packet.occurrence) = [17, 18] := by decide

def lostChoice (bindings : List (Nat × Nat)) : List Nat :=
  bindings.map (fun _ => bindings.head?.map Prod.snd |>.getD 0)

theorem replaying_first_is_wrong :
    lostChoice [(7, 10), (7, 20)] = [10, 10] ∧
      lostChoice [(7, 10), (7, 20)] ≠ [10, 20] := by decide

def consuming (value : Nat) (available : Bool) : Trace Bool Nat :=
  if available then .answer value false .done else .done available

/-- Without consumption both let results are answers; a shared linear take
can admit the first and refuse the later result after the resource is spent. -/
theorem take_changes_later_validation :
    (fire (capture id 0 (Search.superpose [1, 2] true)) consuming).drain = ([1], false) ∧
      (fire (capture id 0 (Search.superpose [1, 2] true))
        (fun value world => .answer value world .done)).drain = ([1, 2], true) := by decide

def effectful : Search Nat Nat := fun world =>
  .answer world (world + 1) (fun next => .answer (next + 10) (next + 1) .done)

theorem effects_run_once :
    (fire (capture id 0 (effectful 0)) (fun value world => .answer value world .done)).drain =
      ([0, 11], 2) := by decide

def startAgain (world : Nat) : Trace Nat Nat :=
  match effectful world with
  | .done final => .done final
  | .answer first reached _ =>
      .answer first reached (fun next => match effectful next with
        | .done final => .done final
        | .answer second final _ => .answer second final .done)

theorem replay_can_change_values : (startAgain 0).drain = ([0, 1], 2) := by decide

/-- Retaining a choice does not decide when it should have been produced.
An external write between entry and firing distinguishes the two policies. -/
theorem evaluation_phase_is_observable :
    (capture id 0 (effectful 0)).first? = some (⟨0, 0, 0⟩, 1) ∧
      (capture id 0 (effectful 42)).first? = some (⟨0, 42, 42⟩, 43) := by decide

end Controls

end Mettapedia.Machines.Cursor.LetChoicePackets
