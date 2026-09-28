import Mettapedia.GSLT.LanguageDef.NativeControlEffectCursor

/-!
# Bounded answer observation through the common cursor protocol

This is a client of `Machines.Cursor`, using the world-preserving provider of
`NativeControlEffectCursor`. The answer allowance and scheduler inspection
budget are independent. Suspensions spend a poll but no answer allowance.
Reaching the allowance retains the live provider residual; discovering
exhaustion retains the world of that terminal poll. Neither event closes or
cancels a provider.

`readout_exact` compares every bounded execution with an independent recursive
collector, including the partial prefix, remaining allowance, actual residual,
world, and poll receipt. A readout can recognize a ready client return even
when the scheduler has paused immediately before publishing it. The completed
comparison allows one additional inspection only after such a ready return;
that inspection never polls the provider.

An allowance of one supplies the observation needed by `once`. Abandoning its
residual must additionally respect the host's local cut scope and resource
ownership. That connection is separate from this observation theorem.

The model takes already visible occurrences as its answers. Dialect filtering,
resolved answer export, and surface result packaging are outside this client.
In particular, CeTTa's current extended `select 1` emits a bare value whereas
larger bounds package a collection, and PeTTa's unary `once` has its own
scoped control semantics. No new language operation is specified here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeControlBoundedCursor

open Mettapedia.Machines.Cursor
open HostCalls (Pull)
open NativeControlCursor (protocol)
open NativeControlEffectCursor (provider)
open CategoryTheory

variable {HState World Answer : Type}

inductive Finish where
  | limit
  | exhausted
  deriving DecidableEq, Repr

inductive Stop where
  | budget
  | limit
  | exhausted
  deriving DecidableEq, Repr

def Finish.stop : Finish → Stop
  | .limit => .limit
  | .exhausted => .exhausted

structure Selection (Answer : Type) where
  remaining : Nat
  reason : Finish
  answers : List Answer
  deriving DecidableEq, Repr

/-- Local control for one client, not a second interaction calculus. -/
inductive Control (Answer : Type) where
  | pulling (remaining : Nat) (reversed : List Answer)
  | exhausted (remaining : Nat) (answers : List Answer)

def client (Answer : Type) :
    Client (P := protocol Answer) (Return := fun _ _ => Selection Answer) where
  V _ _ := Control Answer
  str := fun _ _ => ↾(fun control => match control with
    | .pulling 0 reversed =>
        ⟨.inl ⟨0, .limit, reversed.reverse⟩, fun impossible => nomatch impossible⟩
    | .exhausted remaining answers =>
        ⟨.inl ⟨remaining, .exhausted, answers⟩, fun impossible => nomatch impossible⟩
    | .pulling (remaining + 1) reversed =>
        ⟨.inr (), fun reply => match reply with
          | .done => .exhausted (remaining + 1) reversed.reverse
          | .yield answer _ => .pulling remaining (answer :: reversed)
          | .suspend _ => .pulling (remaining + 1) reversed⟩)

def packet (pull : HState → World → World × Pull HState Answer)
    (allowance : Nat) (cursor : HState) (world : World) (reversed : List Answer) :
    Packet (provider pull) (client Answer) () :=
  ⟨(), .pulling allowance reversed, (cursor, world)⟩

/-- A pure reading of retained state. `limit` is not a claim of exhaustion,
and `budget` is not an empty answer. No operation is performed by reading. -/
structure Snapshot (HState World Answer : Type) where
  cursor : HState
  world : World
  answers : List Answer
  remaining : Nat
  stop : Stop
  deriving DecidableEq, Repr

def Snapshot.prefix (answers : List Answer) (snapshot : Snapshot HState World Answer) :
    Snapshot HState World Answer :=
  { snapshot with answers := answers ++ snapshot.answers }

def readout (pull : HState → World → World × Pull HState Answer) :
    Outcome (provider pull) (client Answer) () → Snapshot HState World Answer
  | .paused ⟨_, .pulling 0 reversed, (cursor, world)⟩ =>
      ⟨cursor, world, reversed.reverse, 0, .limit⟩
  | .paused ⟨_, .pulling (remaining + 1) reversed, (cursor, world)⟩ =>
      ⟨cursor, world, reversed.reverse, remaining + 1, .budget⟩
  | .paused ⟨_, .exhausted remaining answers, (cursor, world)⟩ =>
      ⟨cursor, world, answers, remaining, .exhausted⟩
  | .done ⟨_, selection, (cursor, world)⟩ =>
      ⟨cursor, world, selection.answers, selection.remaining, selection.reason.stop⟩

/-- Independent forward-list collector with a poll budget and an answer
allowance. A zero allowance takes priority over polling or reporting a pause. -/
def collectBounded (pull : HState → World → World × Pull HState Answer) :
    Nat → Nat → HState → World → Nat × Snapshot HState World Answer
  | _, 0, cursor, world => (0, ⟨cursor, world, [], 0, .limit⟩)
  | 0, remaining + 1, cursor, world =>
      (0, ⟨cursor, world, [], remaining + 1, .budget⟩)
  | fuel + 1, remaining + 1, cursor, world =>
      let pulled := pull cursor world
      match pulled.2 with
      | .done => (1, ⟨cursor, pulled.1, [], remaining + 1, .exhausted⟩)
      | .yield answer residual =>
          let result := collectBounded pull fuel remaining residual pulled.1
          (1 + result.1, result.2.prefix [answer])
      | .suspend residual =>
          let result := collectBounded pull fuel (remaining + 1) residual pulled.1
          (1 + result.1, result.2)

/-- Any inspection of a satisfied allowance returns immediately, without
pulling or altering the world. At zero scheduler budget publication waits. -/
theorem zero_allowance_no_poll (pull : HState → World → World × Pull HState Answer)
    (fuel : Nat) (cursor : HState) (world : World) (reversed : List Answer) :
    advance (provider pull) (client Answer) (fun _ _ => 1) (fuel + 1)
      (packet pull 0 cursor world reversed) =
    (0, .done ⟨(), ⟨0, .limit, reversed.reverse⟩, (cursor, world)⟩) := rfl

theorem advance_poll (pull : HState → World → World × Pull HState Answer)
    (fuel remaining : Nat) (cursor : HState) (world : World) (reversed : List Answer) :
    advance (provider pull) (client Answer) (fun _ _ => 1) (fuel + 1)
      (packet pull (remaining + 1) cursor world reversed) =
      let pulled := pull cursor world
      let next : Packet (provider pull) (client Answer) () := match pulled.2 with
        | .done => ⟨(), .exhausted (remaining + 1) reversed.reverse, (cursor, pulled.1)⟩
        | .yield answer residual => packet pull remaining residual pulled.1 (answer :: reversed)
        | .suspend residual => packet pull (remaining + 1) residual pulled.1 reversed
      let result := advance (provider pull) (client Answer) (fun _ _ => 1) fuel next
      (1 + result.1, result.2) := by
  cases h : pull cursor world with
  | mk nextWorld reply =>
      cases reply <;>
        simp only [advance, packet, client, provider, protocol] <;>
        dsimp <;> rw [h] <;> rfl

/-- Arbitrary budget partitioning retains the actual provider residual,
world, local answer allowance, pending answers, and exact poll receipt. -/
theorem chunk_exact (pull : HState → World → World × Pull HState Answer)
    (first second allowance : Nat) (cursor : HState) (world : World)
    (reversed : List Answer) :
    advance (provider pull) (client Answer) (fun _ _ => 1) (first + second)
      (packet pull allowance cursor world reversed) =
    resume (provider pull) (client Answer) (fun _ _ => 1) second
      (advance (provider pull) (client Answer) (fun _ _ => 1) first
        (packet pull allowance cursor world reversed)) :=
  advance_add _ _ _ first second _

theorem exhausted_readout (pull : HState → World → World × Pull HState Answer)
    (fuel remaining : Nat) (cursor : HState) (world : World) (answers : List Answer) :
    let result := advance (provider pull) (client Answer) (fun _ _ => 1) fuel
      ⟨(), .exhausted remaining answers, (cursor, world)⟩
    (result.1, readout pull result.2) =
      (0, ⟨cursor, world, answers, remaining, .exhausted⟩) := by
  cases fuel <;> rfl

/-- Exact prefix observation at the same budget, without an extra poll on
unfinished executions. The two collectors build their lists independently. -/
theorem readout_exact (pull : HState → World → World × Pull HState Answer) :
    ∀ (fuel allowance : Nat) (cursor : HState) (world : World) (reversed : List Answer),
      let actual := advance (provider pull) (client Answer) (fun _ _ => 1) fuel
        (packet pull allowance cursor world reversed)
      let expected := collectBounded pull fuel allowance cursor world
      (actual.1, readout pull actual.2) =
        (expected.1, expected.2.prefix reversed.reverse)
  | 0, 0, _, _, _ => by simp [advance, packet, readout, collectBounded, Snapshot.prefix]
  | 0, _ + 1, _, _, _ => by simp [advance, packet, readout, collectBounded, Snapshot.prefix]
  | fuel + 1, 0, cursor, world, reversed => by
      simp [zero_allowance_no_poll, collectBounded, readout, Finish.stop, Snapshot.prefix]
  | fuel + 1, remaining + 1, cursor, world, reversed => by
      rw [advance_poll]
      dsimp only
      cases pulled : pull cursor world with
      | mk nextWorld reply =>
          cases reply with
          | done =>
              simp only [collectBounded, pulled]
              have terminal := exhausted_readout pull fuel (remaining + 1)
                cursor nextWorld reversed.reverse
              simpa only [Snapshot.prefix, List.append_nil] using
                congrArg (fun p : Nat × Snapshot HState World Answer => (1 + p.1, p.2)) terminal
          | suspend residual =>
              simpa only [collectBounded, pulled] using
                congrArg (fun p : Nat × Snapshot HState World Answer => (1 + p.1, p.2))
                  (readout_exact pull fuel (remaining + 1) residual nextWorld reversed)
          | yield answer residual =>
              simpa only [collectBounded, pulled, Snapshot.prefix, List.reverse_cons,
                List.append_assoc, List.singleton_append] using
                congrArg (fun p : Nat × Snapshot HState World Answer => (1 + p.1, p.2))
                  (readout_exact pull fuel remaining residual nextWorld (answer :: reversed))

/-- Reading a ready result permits a return inspection, never another poll.
The result's provider state is still retained; publication does not close it. -/
theorem publish_ready (pull : HState → World → World × Pull HState Answer)
    (previous : Nat × Outcome (provider pull) (client Answer) ()) (reason : Finish)
    (ready : (readout pull previous.2).stop = reason.stop) :
    let snapshot := readout pull previous.2
    resume (provider pull) (client Answer) (fun _ _ => 1) 1 previous =
      (previous.1, .done ⟨(), ⟨snapshot.remaining, reason, snapshot.answers⟩,
        (snapshot.cursor, snapshot.world)⟩) := by
  rcases previous with ⟨spent, outcome⟩
  cases outcome with
  | paused live =>
      rcases live with ⟨⟨⟩, control, cursor, world⟩
      cases control with
      | pulling remaining reversed =>
          cases remaining with
          | zero =>
              cases reason with
              | limit =>
                  change ((spent + 0, .done ⟨(),
                    ⟨0, .limit, reversed.reverse⟩, (cursor, world)⟩) :
                    Nat × Outcome (provider pull) (client Answer) ()) = _
                  simp only [Nat.add_zero]
                  rfl
              | exhausted => cases ready
          | succ remaining =>
              cases reason <;> simp_all [readout, Finish.stop]
      | exhausted remaining answers =>
          cases reason with
          | limit => cases ready
          | exhausted =>
              change ((spent + 0, .done ⟨(),
                ⟨remaining, .exhausted, answers⟩, (cursor, world)⟩) :
                Nat × Outcome (provider pull) (client Answer) ()) = _
              simp only [Nat.add_zero]
              rfl
  | done result =>
      rcases result with ⟨⟨⟩, ⟨remaining, previousReason, answers⟩, cursor, world⟩
      cases previousReason <;> cases reason <;>
        simp_all [readout, Finish.stop, resume]

/-- Both limit completion and exhausted completion publish with the same
receipt, world, residual and answers as the independent bounded collector. -/
theorem completed_exact (pull : HState → World → World × Pull HState Answer)
    (fuel allowance : Nat) (cursor : HState) (world : World) (reversed : List Answer)
    (spent remaining : Nat) (finalCursor : HState) (finalWorld : World)
    (answers : List Answer) (reason : Finish)
    (completed : collectBounded pull fuel allowance cursor world =
      (spent, ⟨finalCursor, finalWorld, answers, remaining, reason.stop⟩)) :
    advance (provider pull) (client Answer) (fun _ _ => 1) (fuel + 1)
      (packet pull allowance cursor world reversed) =
    (spent, .done ⟨(), ⟨remaining, reason, reversed.reverse ++ answers⟩,
      (finalCursor, finalWorld)⟩) := by
  have exactPrefix := readout_exact pull fuel allowance cursor world reversed
  rw [completed] at exactPrefix
  have receipt := congrArg Prod.fst exactPrefix
  have observation := congrArg Prod.snd exactPrefix
  dsimp only at receipt observation
  rw [chunk_exact]
  have ready := publish_ready pull
    (advance (provider pull) (client Answer) (fun _ _ => 1) fuel
      (packet pull allowance cursor world reversed)) reason
    (by rw [observation]; rfl)
  simpa only [observation, receipt, Snapshot.prefix] using ready

/-- Conversely, a published result has exactly the source collector's
receipt, residual, world, stop reason and occurrence list at that budget. -/
theorem finished_reflect (pull : HState → World → World × Pull HState Answer)
    (fuel allowance : Nat) (cursor : HState) (world : World)
    (spent : Nat) (selection : Selection Answer) (finalCursor : HState) (finalWorld : World)
    (finished : advance (provider pull) (client Answer) (fun _ _ => 1) fuel
      (packet pull allowance cursor world []) =
      (spent, .done ⟨(), selection, (finalCursor, finalWorld)⟩)) :
    collectBounded pull fuel allowance cursor world =
      (spent, ⟨finalCursor, finalWorld, selection.answers, selection.remaining,
        selection.reason.stop⟩) := by
  have exactPrefix := readout_exact pull fuel allowance cursor world []
  rw [finished] at exactPrefix
  simpa only [readout, List.reverse_nil, Snapshot.prefix, List.nil_append] using
    exactPrefix.symm

/-- If the unbounded collector completes, bounded observation delivers
exactly its requested prefix. No equality of worlds is asserted after an
early limit: the complete collector may have executed further effects. -/
theorem prefix_of_complete_collection
    (pull : HState → World → World × Pull HState Answer) :
    ∀ (fuel allowance : Nat) (cursor : HState) (world : World)
      (spent : Nat) (finalWorld : World) (answers : List Answer),
      NativeControlEffectCursor.collectCounted pull fuel cursor world =
        (spent, finalWorld, some answers) →
      (collectBounded pull fuel allowance cursor world).2.answers = answers.take allowance
  | 0, _, _, _, _, _, _, completed => by
      simp [NativeControlEffectCursor.collectCounted] at completed
  | _ + 1, 0, _, _, _, _, _, _ => by
      simp [collectBounded]
  | fuel + 1, remaining + 1, cursor, world, spent, finalWorld, answers, completed => by
      cases pulled : pull cursor world with
      | mk nextWorld reply =>
          cases reply with
          | done =>
              simp only [NativeControlEffectCursor.collectCounted, pulled, Prod.mk.injEq,
                Option.some.injEq] at completed
              rcases completed with ⟨rfl, rfl, rfl⟩
              simp [collectBounded, pulled]
          | suspend residual =>
              cases rest : NativeControlEffectCursor.collectCounted pull fuel residual nextWorld with
              | mk used result =>
                  rcases result with ⟨lastWorld, observation⟩
                  cases observation with
                  | none => simp [NativeControlEffectCursor.collectCounted, pulled, rest] at completed
                  | some values =>
                      simp only [NativeControlEffectCursor.collectCounted, pulled, rest,
                        Prod.mk.injEq, Option.some.injEq] at completed
                      rcases completed with ⟨rfl, rfl, rfl⟩
                      simpa only [collectBounded, pulled] using
                        prefix_of_complete_collection pull fuel (remaining + 1) residual
                          nextWorld used lastWorld values rest
          | yield answer residual =>
              cases rest : NativeControlEffectCursor.collectCounted pull fuel residual nextWorld with
              | mk used result =>
                  rcases result with ⟨lastWorld, observation⟩
                  cases observation with
                  | none => simp [NativeControlEffectCursor.collectCounted, pulled, rest] at completed
                  | some values =>
                      simp only [NativeControlEffectCursor.collectCounted, pulled, rest,
                        Option.map_some, Prod.mk.injEq, Option.some.injEq] at completed
                      rcases completed with ⟨rfl, rfl, rfl⟩
                      simpa only [collectBounded, pulled, Snapshot.prefix, List.singleton_append,
                        List.take_succ_cons] using
                        congrArg (answer :: ·) (prefix_of_complete_collection pull fuel remaining
                          residual nextWorld used lastWorld values rest)

/-- An allowance strictly larger than a completed collection reaches its
actual terminal poll. The final world and receipt then agree as well. An
allowance exactly equal to the answer count stops before this terminal poll. -/
theorem complete_collection_agreement
    (pull : HState → World → World × Pull HState Answer) :
    ∀ (fuel allowance : Nat) (cursor : HState) (world : World)
      (spent : Nat) (finalWorld : World) (answers : List Answer),
      NativeControlEffectCursor.collectCounted pull fuel cursor world =
        (spent, finalWorld, some answers) →
      answers.length < allowance →
      ∃ finalCursor, collectBounded pull fuel allowance cursor world =
        (spent, ⟨finalCursor, finalWorld, answers, allowance - answers.length, .exhausted⟩)
  | 0, _, _, _, _, _, _, completed, _ => by
      simp [NativeControlEffectCursor.collectCounted] at completed
  | _ + 1, 0, _, _, _, _, _, _, room => by omega
  | fuel + 1, remaining + 1, cursor, world, spent, finalWorld, answers, completed, room => by
      cases pulled : pull cursor world with
      | mk nextWorld reply =>
          cases reply with
          | done =>
              simp only [NativeControlEffectCursor.collectCounted, pulled, Prod.mk.injEq,
                Option.some.injEq] at completed
              rcases completed with ⟨rfl, rfl, rfl⟩
              exact ⟨cursor, by simp [collectBounded, pulled]⟩
          | suspend residual =>
              cases rest : NativeControlEffectCursor.collectCounted pull fuel residual nextWorld with
              | mk used result =>
                  rcases result with ⟨lastWorld, observation⟩
                  cases observation with
                  | none => simp [NativeControlEffectCursor.collectCounted, pulled, rest] at completed
                  | some values =>
                      simp only [NativeControlEffectCursor.collectCounted, pulled, rest,
                        Prod.mk.injEq, Option.some.injEq] at completed
                      rcases completed with ⟨rfl, rfl, rfl⟩
                      obtain ⟨finalCursor, exactRest⟩ := complete_collection_agreement pull fuel
                        (remaining + 1) residual nextWorld used lastWorld values rest room
                      exact ⟨finalCursor, by simp only [collectBounded, pulled, exactRest]⟩
          | yield answer residual =>
              cases rest : NativeControlEffectCursor.collectCounted pull fuel residual nextWorld with
              | mk used result =>
                  rcases result with ⟨lastWorld, observation⟩
                  cases observation with
                  | none => simp [NativeControlEffectCursor.collectCounted, pulled, rest] at completed
                  | some values =>
                      simp only [NativeControlEffectCursor.collectCounted, pulled, rest,
                        Option.map_some, Prod.mk.injEq, Option.some.injEq] at completed
                      rcases completed with ⟨rfl, rfl, rfl⟩
                      have roomRest : values.length < remaining := by simpa using room
                      obtain ⟨finalCursor, exactRest⟩ := complete_collection_agreement pull fuel
                        remaining residual nextWorld used lastWorld values rest roomRest
                      refine ⟨finalCursor, ?_⟩
                      simp only [collectBounded, pulled, exactRest, Snapshot.prefix,
                        List.singleton_append, List.length_cons, Nat.add_sub_add_right]

theorem receipt_le_budget (pull : HState → World → World × Pull HState Answer) :
    ∀ (fuel allowance : Nat) (cursor : HState) (world : World),
      (collectBounded pull fuel allowance cursor world).1 ≤ fuel
  | _, 0, _, _ => by simp [collectBounded]
  | 0, _ + 1, _, _ => Nat.le_refl _
  | fuel + 1, remaining + 1, cursor, world => by
      cases pulled : pull cursor world with
      | mk nextWorld reply =>
          cases reply with
          | done => simp [collectBounded, pulled]
          | suspend residual =>
              have := receipt_le_budget pull fuel (remaining + 1) residual nextWorld
              simp only [collectBounded, pulled]
              omega
          | yield answer residual =>
              have := receipt_le_budget pull fuel remaining residual nextWorld
              simp only [collectBounded, pulled]
              omega

/-- Every successful occurrence, including duplicates, consumes exactly one
answer allowance. Suspension and exhaustion consume none. -/
theorem answer_accounting (pull : HState → World → World × Pull HState Answer) :
    ∀ (fuel allowance : Nat) (cursor : HState) (world : World),
      let result := (collectBounded pull fuel allowance cursor world).2
      result.answers.length + result.remaining = allowance
  | _, 0, _, _ => by simp [collectBounded]
  | 0, _ + 1, _, _ => by simp [collectBounded]
  | fuel + 1, remaining + 1, cursor, world => by
      cases pulled : pull cursor world with
      | mk nextWorld reply =>
          cases reply with
          | done => simp [collectBounded, pulled]
          | suspend residual =>
              simpa only [collectBounded, pulled] using
                answer_accounting pull fuel (remaining + 1) residual nextWorld
          | yield answer residual =>
              have := answer_accounting pull fuel remaining residual nextWorld
              simp only [collectBounded, pulled, Snapshot.prefix, List.singleton_append,
                List.length_cons]
              omega

/-- A yield at allowance one makes the client ready immediately. Its residual
is retained for a separate scoped abandonment/ownership operation. -/
theorem once_yield_stops (pull : HState → World → World × Pull HState Answer)
    (cursor residual : HState) (world nextWorld : World) (answer : Answer)
    (yielded : pull cursor world = (nextWorld, .yield answer residual)) :
    advance (provider pull) (client Answer) (fun _ _ => 1) 2
      (packet pull 1 cursor world []) =
      (1, .done ⟨(), ⟨0, .limit, [answer]⟩, (residual, nextWorld)⟩) := by
  rw [advance_poll]
  simp only [yielded]
  rfl

theorem suspend_keeps_allowance (pull : HState → World → World × Pull HState Answer)
    (remaining : Nat) (cursor residual : HState) (world nextWorld : World)
    (reversed : List Answer)
    (suspended : pull cursor world = (nextWorld, .suspend residual)) :
    advance (provider pull) (client Answer) (fun _ _ => 1) 1
      (packet pull (remaining + 1) cursor world reversed) =
      (1, .paused (packet pull (remaining + 1) residual nextWorld reversed)) := by
  rw [advance_poll]
  simp only [suspended]
  rfl

namespace Controls

/-- Suspension, two duplicate values, then an effectful exhaustion step. -/
def delayed (cursor world : Nat) : Nat × Pull Nat Nat :=
  match cursor with
  | 0 => (world + 1, .suspend 1)
  | 1 => (world + 10, .yield 7 2)
  | 2 => (world + 100, .yield 7 3)
  | _ => (world + 1000, .done)

theorem zero_bound_avoids_effect :
    collectBounded delayed 100 0 0 0 =
      (0, ⟨0, 0, [], 0, .limit⟩) := rfl

theorem pause_is_not_exhaustion :
    collectBounded delayed 1 2 0 0 =
      (1, ⟨1, 1, [], 2, .budget⟩) := rfl

theorem duplicates_consume_two_answers :
    collectBounded delayed 3 2 0 0 =
      (3, ⟨3, 111, [7, 7], 0, .limit⟩) := rfl

theorem exact_bound_does_not_discover_exhaustion :
    collectBounded delayed 50 2 0 0 =
      (3, ⟨3, 111, [7, 7], 0, .limit⟩) := rfl

theorem spare_allowance_retains_terminal_effect :
    collectBounded delayed 50 3 0 0 =
      (4, ⟨3, 1111, [7, 7], 1, .exhausted⟩) := rfl

theorem pause_and_resume_without_replay :
    resume (provider delayed) (client Nat) (fun _ _ => 1) 3
      (advance (provider delayed) (client Nat) (fun _ _ => 1) 1
        (packet delayed 2 0 0 [])) =
      (3, .done ⟨(), ⟨0, .limit, [7, 7]⟩, (3, 111)⟩) := rfl

theorem once_does_not_poll_second_answer :
    advance (provider delayed) (client Nat) (fun _ _ => 1) 50
      (packet delayed 1 0 0 []) =
      (2, .done ⟨(), ⟨0, .limit, [7]⟩, (2, 11)⟩) := rfl

/-- Reusing the updated world but restarting the initial host state repeats
the suspension's effect. The residual is part of the continuation. -/
theorem silent_restart_is_wrong :
    (collectBounded delayed 2 1 0 1).2.world ≠
      (collectBounded delayed 2 1 1 1).2.world := by decide

/-- Polling merely to confirm a reached output bound executes an extra
terminal effect. Limit completion itself licenses no such poll. -/
theorem extra_poll_is_wrong :
    (delayed (collectBounded delayed 3 2 0 0).2.cursor
      (collectBounded delayed 3 2 0 0).2.world).1 ≠
      (collectBounded delayed 3 2 0 0).2.world := by decide

theorem answer_budget_is_not_poll_budget :
    (collectBounded delayed 2 2 0 0).2.answers = [7] ∧
      (collectBounded delayed 2 2 0 0).2.remaining = 1 ∧
      (collectBounded delayed 2 2 0 0).2.stop = .budget := by decide

end Controls

#print axioms zero_allowance_no_poll
#print axioms advance_poll
#print axioms chunk_exact
#print axioms exhausted_readout
#print axioms readout_exact
#print axioms publish_ready
#print axioms completed_exact
#print axioms finished_reflect
#print axioms prefix_of_complete_collection
#print axioms complete_collection_agreement
#print axioms receipt_le_budget
#print axioms answer_accounting
#print axioms once_yield_stops
#print axioms suspend_keeps_allowance
#print axioms Controls.zero_bound_avoids_effect
#print axioms Controls.pause_is_not_exhaustion
#print axioms Controls.duplicates_consume_two_answers
#print axioms Controls.exact_bound_does_not_discover_exhaustion
#print axioms Controls.spare_allowance_retains_terminal_effect
#print axioms Controls.pause_and_resume_without_replay
#print axioms Controls.once_does_not_poll_second_answer
#print axioms Controls.silent_restart_is_wrong
#print axioms Controls.extra_poll_is_wrong
#print axioms Controls.answer_budget_is_not_poll_budget

end Mettapedia.GSLT.LanguageDef.NativeControlBoundedCursor
