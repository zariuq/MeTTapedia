import Mettapedia.Machines.Cursor.QueryCore
import Mettapedia.Machines.ImmediateStorePrefixes

/-!
# Replacing an execution provider at an arbitrary retained prefix

A provider replacement transports the reached world, reply-indexed residual,
ordered replies and paid account. The local law preserves responses and
successor states, including error and pending responses when those are part of
the service. Such responses must not be collapsed to an empty answer.

The examples include allocation of fresh identities and output without a store
write: observable progress is wider than a mutation flag. They contrast exact
continuation transfer with restarting the original program in the reached
world. The model does not choose an error-catching policy or prove native
error-payload ownership.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RuntimePlumbing.ProgressTransfer

open ReadOnlyQuery (Program Reads)
open Cursor.ReadOnlyQuery (client)
open Cursor.ReadOnlyQuery

variable {Source Target Key Reply Answer : Type}

/-- The adapter is local: one request, its complete reply and the reached world. -/
def adapter (source : Source → Key → Reply × Source)
    (target : Target → Key → Reply × Target) (move : Source → Target)
    (commutes : ∀ state key,
      target (move state) key = ((source state key).1, move (source state key).2)) :
    Cursor.Hom (Sampled.provider source) (Sampled.provider target) where
  map saved := (move saved.1, saved.2)
  step saved key := by
    rcases saved with ⟨state, reads⟩
    simp only [Sampled.provider]
    rw [commutes state key]

/-- No root replay occurs even when effects preceded the provider switch. -/
theorem transfer_resume (source : Source → Key → Reply × Source)
    (target : Target → Key → Reply × Target) (move : Source → Target)
    (commutes : ∀ state key,
      target (move state) key = ((source state key).1, move (source state key).2))
    (price : Key → Nat) (fuel : Nat)
    (previous : Nat × Cursor.Outcome (Sampled.provider source)
      (client (Answer := Answer)) PUnit.unit) :
    let bridge := adapter source target move commutes
    let continued := Sampled.resume source price fuel previous
    (continued.1, bridge.outcome client continued.2) =
      Sampled.resume target price fuel (previous.1, bridge.outcome client previous.2) :=
  (adapter source target move commutes).resume_account client
    (Sampled.charge source price) (Sampled.charge target price) (fun _ _ => rfl) fuel previous

theorem transfer_keeps_reached_world (source : Source → Key → Reply × Source)
    (target : Target → Key → Reply × Target) (move : Source → Target)
    (commutes : ∀ state key,
      target (move state) key = ((source state key).1, move (source state key).2))
    (previous : Cursor.Outcome (Sampled.provider source)
      (client (Answer := Answer)) PUnit.unit) :
    (Sampled.savedState target ((adapter source target move commutes).outcome client previous)).1 =
      move (Sampled.savedState source previous).1 := by
  cases previous with
  | paused packet => rcases packet with ⟨⟨⟩, program, state, reads⟩; rfl
  | done finished => rcases finished with ⟨⟨⟩, answer, state, reads⟩; rfl

theorem transfer_keeps_history (source : Source → Key → Reply × Source)
    (target : Target → Key → Reply × Target) (move : Source → Target)
    (commutes : ∀ state key,
      target (move state) key = ((source state key).1, move (source state key).2))
    (previous : Cursor.Outcome (Sampled.provider source)
      (client (Answer := Answer)) PUnit.unit) :
    Sampled.recorded target ((adapter source target move commutes).outcome client previous) =
      Sampled.recorded source previous := by
  cases previous with
  | paused packet => rcases packet with ⟨⟨⟩, program, state, reads⟩; rfl
  | done finished => rcases finished with ⟨⟨⟩, answer, state, reads⟩; rfl

namespace Controls

inductive Command where
  | fresh
  | print (value : Nat)
  | put (value : Nat)
  | ask
  deriving DecidableEq, Repr

structure World where
  next : Nat
  printed : List Nat
  stored : List Nat
  deriving DecidableEq, Repr

def sample (world : World) : Command → Nat × World
  | .fresh => (world.next, { world with next := world.next + 1 })
  | .print value => (value, { world with printed := world.printed ++ [value] })
  | .put value => (value, { world with stored := world.stored ++ [value] })
  | .ask => (world.next, world)

def start : World := ⟨10, [], []⟩

def producer : Program Command Nat Nat :=
  .read .fresh fun chosen =>
    .read (.print chosen) fun _ => .read (.put chosen) fun _ => .pure chosen

def cut := Sampled.advance sample (fun _ => 1) 2 producer start []
def resumed := Sampled.resume sample (fun _ => 1) 3 cut
def restarted := Sampled.advance sample (fun _ => 1) 4 producer
  (Sampled.savedState sample cut.2).1 []

theorem output_and_freshness_are_progress_without_a_store_write :
    (Sampled.savedState sample cut.2).1 = ⟨11, [10], []⟩ ∧
      cut.1 = 2 ∧ Sampled.completed? sample cut.2 = none := by decide

theorem resumption_keeps_the_chosen_identity_and_effect_prefix :
    (Sampled.completed? sample resumed.2).map (·.answer) = some 10 ∧
      (Sampled.savedState sample resumed.2).1 = ⟨11, [10], [10]⟩ ∧
      resumed.1 = 3 := by decide

theorem root_replay_duplicates_output_and_changes_the_answer :
    (Sampled.completed? sample restarted.2).map (·.answer) = some 11 ∧
      (Sampled.savedState sample restarted.2).1 = ⟨12, [10, 11], [11]⟩ := by decide

/-- Private provider metadata may be discarded while progress is retained. -/
structure Packed where
  world : World
  inspected : Nat

def packedSample (saved : Packed) (command : Command) : Nat × Packed :=
  let reply := sample saved.world command
  (reply.1, ⟨reply.2, saved.inspected + 1⟩)

theorem packed_local (saved : Packed) (command : Command) :
    sample saved.world command =
      ((packedSample saved command).1, (packedSample saved command).2.world) := by
  rfl

def packedCut := Sampled.advance packedSample (fun _ => 1) 2 producer ⟨start, 0⟩ []

def bridge := adapter packedSample sample Packed.world packed_local
def switched := Sampled.resume sample (fun _ => 1) 3
  (packedCut.1, bridge.outcome client packedCut.2)

theorem replacing_the_provider_preserves_prior_output_and_paid_work :
    (Sampled.completed? sample switched.2).map (·.answer) = some 10 ∧
      (Sampled.savedState sample switched.2).1 = ⟨11, [10], [10]⟩ ∧
      switched.1 = 3 := by decide

end Controls

end Mettapedia.Machines.RuntimePlumbing.ProgressTransfer
