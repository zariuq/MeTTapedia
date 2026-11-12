import Mettapedia.Machines.Cursor.LetChoicePackets
import Mettapedia.Machines.Cursor.LetEffectProfiles
import Mettapedia.Machines.ScopedCommit

/-!
# Choice does not distribute a shared effect prefix for free

A producer can execute a common prefix once and then yield several values.
Distributing that effect into the continuation of every outgoing alternative
is a different program. Capturing and retaining the actual producer preserves
its prefix; publishing a copied prepared prefix per result need not do so.

The second distinction is linear consumption before versus after choice:
ordinary per-result validation can admit only the first result from one token,
whereas one grouped firing may consume once and emit all its values. Neither
atomicity nor retained choice alone selects one of these source disciplines.
These are finite shared-world search laws, not a C or language-default theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.LetChoiceEffects

open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Trace Search)

variable {World Value : Type}

def sharedPrefix (action : World → World) (values : List Value) : Search World Value :=
  fun world => Search.superpose values (action world)

def distributedPrefix (action : World → World) (values : List Value) : Search World Value :=
  (Search.superpose values).bind fun value world => .answer value (action world) .done

def repeatAction (action : World → World) : Nat → World → World
  | 0, world => world
  | amount + 1, world => repeatAction action amount (action world)

theorem shared_prefix_drain (action : World → World) (values : List Value) (world : World) :
    (sharedPrefix action values world).drain = (values, action world) :=
  Search.drain_superpose values (action world)

theorem distributed_cons (action : World → World) (first : Value) (later : List Value)
    (world : World) :
    distributedPrefix action (first :: later) world =
      (Trace.answer first (action world) Trace.done).append (distributedPrefix action later) := rfl

/-- The number of outgoing alternatives controls how many times the
distributed program executes the prefix. It is not the number of incoming prefixes. -/
theorem distributed_prefix_drain (action : World → World) (values : List Value) (world : World) :
    (distributedPrefix action values world).drain =
      (values, repeatAction action values.length world) := by
  induction values generalizing world with
  | nil => rfl
  | cons first later ih =>
      rw [distributed_cons, Trace.drain_append]
      simpa only [Trace.drain_answer, Trace.drain_done, List.singleton_append,
        List.length_cons, repeatAction] using congrArg
          (fun result : List Value × World => (first :: result.1, result.2)) (ih (action world))

theorem shared_prefix_empty (action : World → World) (world : World) :
    (sharedPrefix action ([] : List Value) world).drain = ([], action world) := rfl

theorem distributed_prefix_empty (action : World → World) (world : World) :
    (distributedPrefix action ([] : List Value) world).drain = ([], world) := rfl

/-- The retained residual contains only the remaining alternatives. Resuming
it in an externally changed world does not re-enter the already run action. -/
theorem shared_prefix_residual (action : World → World) (first : Value) (later : List Value)
    (world : World) : sharedPrefix action (first :: later) world =
      .answer first (action world) (Search.superpose later) := rfl

theorem bind_identity (source : Trace World Value) :
    source.bind (fun value world => .answer value world .done) = source := by
  induction source with
  | done world => rfl
  | answer value world residual ih =>
      simp only [Trace.bind, Trace.append]
      congr 1
      funext next
      exact ih next

/-- The existing packet construction preserves the actual producer, so
capturing its outgoing results does not redistribute its common effect. -/
theorem capture_shared_prefix (action : World → World) (values : List Value) (world : World)
    (first : Nat) :
    (LetChoicePackets.fire (LetChoicePackets.capture id first (sharedPrefix action values world))
      (fun value world => .answer value world .done)).drain = (values, action world) := by
  rw [LetChoicePackets.fire_capture, bind_identity]
  exact shared_prefix_drain action values world

def acquire : Search Bool Unit := fun available =>
  if available then .answer () false .done else .done available

def takeValue (value : Value) : Search Bool Value := fun available =>
  if available then .answer value false .done else .done available

def perResultTake (values : List Value) : Search Bool Value :=
  (Search.superpose values).bind takeValue

/-- This groups the alternatives after one successful acquisition. It does
not acquire the same linear occurrence separately for every output. -/
def groupedTake (values : List Value) : Search Bool Value :=
  acquire.bind (fun _ => Search.superpose values)

theorem per_result_cons (first : Value) (later : List Value) (world : Bool) :
    perResultTake (first :: later) world =
      (takeValue first world).append (perResultTake later) := rfl

theorem per_result_unavailable (values : List Value) :
    (perResultTake values false).drain = ([], false) := by
  induction values with
  | nil => rfl
  | cons first later ih =>
      simpa only [per_result_cons, takeValue, Bool.false_eq_true, ↓reduceIte,
        Trace.append] using ih

theorem per_result_one_token (first : Value) (later : List Value) :
    (perResultTake (first :: later) true).drain = ([first], false) := by
  rw [per_result_cons]
  simp only [takeValue, ↓reduceIte, Trace.append, Trace.drain_answer]
  rw [per_result_unavailable]

theorem grouped_one_token (values : List Value) :
    (groupedTake values true).drain = (values, false) := by
  simp [groupedTake, acquire, Search.bind, Trace.bind, Trace.drain_append,
    Search.drain_superpose]

theorem grouped_unavailable (values : List Value) :
    (groupedTake values false).drain = ([], false) := rfl

def sharedBody (action : World → World) (values : List Value) : ScopedCommit.Body Value World :=
  .effect (fun binding world => (binding, action world))
    (.choose (fun _ _ => values) .done)

def distributedBody (action : World → World) (values : List Value) : ScopedCommit.Body Value World :=
  .choose (fun _ _ => values) (.effect (fun binding world => (binding, action world)) .done)

example : ScopedCommit.run (sharedBody (· + 1) [10, 20]) 0 0 = ([10, 20], 1) := by decide
example : ScopedCommit.run (distributedBody (· + 1) [10, 20]) 0 0 = ([10, 20], 2) := by decide

def paused := ScopedCommit.selectFrom 1 (ScopedCommit.stream (sharedBody (· + 1) [10, 20]) 0) 0

example : paused.1 = [10] ∧ paused.2.1 = 1 ∧
    ScopedCommit.resume paused.2.2 paused.2.1 = ([20], 1) := by decide

example : ScopedCommit.resume paused.2.2 99 = ([20], 99) := by decide

/-- Restarting differs from resuming: it reruns the shared prefix and offers
the first value again, so retaining only output values is insufficient. -/
example : ScopedCommit.run (sharedBody (· + 1) [10, 20]) 0 paused.2.1 = ([10, 20], 2) := by decide

example : (sharedPrefix (· + 1) ([] : List Nat) 0).drain = ([], 1) ∧
    (distributedPrefix (· + 1) ([] : List Nat) 0).drain = ([], 0) := by decide

example : (perResultTake [10, 20] true).drain = ([10], false) ∧
    (groupedTake [10, 20] true).drain = ([10, 20], false) := by decide

/-- An answerless grouped firing can still consume its resource. An empty
list of per-result branches contains no acquisition at all. -/
example : (perResultTake ([] : List Nat) true).drain = ([], true) ∧
    (groupedTake ([] : List Nat) true).drain = ([], false) := by decide

open LetEffectProfiles

def prefixWorld : LetEffectProfiles.World Unit Unit Nat := ⟨fun _ => (), []⟩
def prefixCode : Code Unit Unit Nat Unit String :=
  .read (.perform (.record 42)) fun _ => .pure (.answer ())
def prefixPacket := prepared .overlay prefixCode prefixWorld

abbrev Published := LetEffectProfiles.World Unit Unit Nat × List (Receipt Unit Unit Nat Unit)

/-- One previously computed prefix payload is published again by every call.
Retaining that payload is not, by itself, a one-time ownership protocol. -/
def publishCopiedPrefix (state : Published) : Published :=
  let publication := publish true true state.1 prefixPacket
  (publication.world, state.2 ++ publication.receipt.toList)

example :
    let result := (sharedPrefix publishCopiedPrefix [10, 20] (prefixWorld, [])).drain
    result.1 = [10, 20] ∧ result.2.1.events = [42] ∧ result.2.2.length = 1 := by decide

example :
    let result := (distributedPrefix publishCopiedPrefix [10, 20] (prefixWorld, [])).drain
    result.1 = [10, 20] ∧ result.2.1.events = [42, 42] ∧ result.2.2.length = 2 := by decide

end Mettapedia.Machines.Cursor.LetChoiceEffects
