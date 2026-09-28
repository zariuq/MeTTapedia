import Mettapedia.GSLT.LanguageDef.NativeControlCursor
import Mettapedia.GSLT.LanguageDef.NativeControlCollection

/-!
# World-preserving host controls in the common cursor protocol

The provider retains the world returned by every host step, including the
exhaustion step. It uses the existing polling protocol and collection client;
there is no second stream surface or client calculus.

`chunk_exact` preserves the complete packet, world and pull receipt across
arbitrary scheduler cuts. `completed_exact` compares completed execution with
an independent recursive, counted collector; `collectCounted_effects` connects
that collector to `NativeControlCollection.Effects.collectWorld`.

The client needs a final inspection to publish its result. A shifted fuel
comparison is asserted only for completed source collections. At an unfinished
run that extra inspection may instead perform another host pull and change the
world; `unfinished_extra_poll_changes_world` exhibits that boundary.

The world and host residual are mathematical values. Concrete effect dispatch,
handle ownership, cancellation, faults and disposal remain implementation
obligations. Polling an exhausted provider manually is not prohibited by this
internal protocol; this collecting client stops polling on its first `done`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeControlEffectCursor

open Mettapedia.Machines.Cursor
open HostCalls (Pull)
open NativeControlCursor (protocol client)

section Generic

variable {HState World Answer : Type}

/-- Every reply retains the returned world, including exhaustion. The cursor
component at exhaustion names the final host state whose pull returned `done`. -/
def provider (pull : HState → World → World × Pull HState Answer) :
    Provider (protocol Answer) where
  State _ _ := HState × World
  step state _ :=
    let pulled := pull state.1 state.2
    match pulled.2 with
    | .done => ⟨.done, (state.1, pulled.1)⟩
    | .yield answer residual => ⟨.yield answer (), (residual, pulled.1)⟩
    | .suspend residual => ⟨.suspend (), (residual, pulled.1)⟩

def packet (pull : HState → World → World × Pull HState Answer)
    (cursor : HState) (world : World) (reversed : List Answer) :
    Packet (provider pull) (client Answer) () :=
  ⟨(), .pulling reversed, (cursor, world)⟩

def observed (pull : HState → World → World × Pull HState Answer) :
    Outcome (provider pull) (client Answer) () → World × Option (List Answer)
  | .paused live => (live.2.2.2, none)
  | .done result => (result.2.2.2, some result.2.1)

/-- One host poll has one receipt and transfers the actual residual and world.
Even the terminal reply stores `nextWorld` before the client finishes. -/
theorem advance_poll (pull : HState → World → World × Pull HState Answer)
    (fuel : Nat) (cursor : HState) (world : World) (reversed : List Answer) :
    advance (provider pull) (client Answer) (fun _ _ => 1) (fuel + 1)
      (packet pull cursor world reversed) =
      let pulled := pull cursor world
      let next : Packet (provider pull) (client Answer) () := match pulled.2 with
        | .done => ⟨(), .finished reversed.reverse, (cursor, pulled.1)⟩
        | .yield answer residual => packet pull residual pulled.1 (answer :: reversed)
        | .suspend residual => packet pull residual pulled.1 reversed
      let result := advance (provider pull) (client Answer) (fun _ _ => 1) fuel next
      (1 + result.1, result.2) := by
  cases h : pull cursor world with
  | mk nextWorld reply =>
      cases reply <;>
        simp only [advance, packet, client, provider, protocol] <;>
        dsimp <;> rw [h] <;> rfl

/-- Pausing/resuming preserves all retained state and the exact pull receipt,
not only the eventual answer list. -/
theorem chunk_exact (pull : HState → World → World × Pull HState Answer)
    (first second : Nat) (cursor : HState) (world : World) (reversed : List Answer) :
    advance (provider pull) (client Answer) (fun _ _ => 1) (first + second)
      (packet pull cursor world reversed) =
    resume (provider pull) (client Answer) (fun _ _ => 1) second
      (advance (provider pull) (client Answer) (fun _ _ => 1) first
        (packet pull cursor world reversed)) :=
  advance_add _ _ _ first second _

/-- A recursive source collector additionally counts the pulls it performed.
It retains the world even when the last operation suspends or exhausts. -/
def collectCounted (pull : HState → World → World × Pull HState Answer) :
    Nat → HState → World → Nat × World × Option (List Answer)
  | 0, _, world => (0, world, none)
  | fuel + 1, cursor, world =>
      let pulled := pull cursor world
      match pulled.2 with
      | .done => (1, pulled.1, some [])
      | .suspend residual =>
          let result := collectCounted pull fuel residual pulled.1
          (1 + result.1, result.2)
      | .yield answer residual =>
          let result := collectCounted pull fuel residual pulled.1
          (1 + result.1, result.2.1, result.2.2.map (answer :: ·))

theorem collectCounted_bound (pull : HState → World → World × Pull HState Answer) :
    ∀ (fuel : Nat) (cursor : HState) (world : World),
      (collectCounted pull fuel cursor world).1 ≤ fuel
  | 0, _, _ => Nat.zero_le _
  | fuel + 1, cursor, world => by
      cases pulled : pull cursor world with
      | mk nextWorld reply =>
          cases reply with
          | done => simp [collectCounted, pulled]
          | suspend residual =>
              have := collectCounted_bound pull fuel residual nextWorld
              simp only [collectCounted, pulled]
              omega
          | yield answer residual =>
              have := collectCounted_bound pull fuel residual nextWorld
              simp only [collectCounted, pulled]
              omega

/-- Forgetting the receipt gives exactly the existing world-aware source
collector at a fixed logical checkpoint. This permits answer-store pairs and
does not change which logical store is restored between pulls. -/
theorem collectCounted_effects {Store Value : Type}
    (pull : HState → Store → World → World × Pull HState (Value × Store))
    (checkpoint : Store) :
    ∀ (fuel : Nat) (cursor : HState) (world : World),
      (collectCounted (fun h w => pull h checkpoint w) fuel cursor world).2 =
        NativeControlCollection.Effects.collectWorld pull checkpoint fuel cursor world
  | 0, _, _ => rfl
  | fuel + 1, cursor, world => by
      cases pulled : pull cursor checkpoint world with
      | mk nextWorld reply =>
          cases reply with
          | done => simp [collectCounted, NativeControlCollection.Effects.collectWorld, pulled]
          | suspend residual =>
              simpa only [collectCounted, NativeControlCollection.Effects.collectWorld, pulled] using
                collectCounted_effects pull checkpoint fuel residual nextWorld
          | yield answer residual =>
              simp only [collectCounted, NativeControlCollection.Effects.collectWorld, pulled]
              rw [collectCounted_effects]

/-- A completed source run gives a completed cursor with exactly its pull
receipt, final world and ordered answers. The existential residual is the
actual host state retained when its final poll returned exhaustion. -/
theorem completed_exact (pull : HState → World → World × Pull HState Answer) :
    ∀ (fuel : Nat) (cursor : HState) (world : World) (reversed : List Answer)
      (spent : Nat) (finalWorld : World) (answers : List Answer),
      collectCounted pull fuel cursor world = (spent, finalWorld, some answers) →
      ∃ finalCursor,
        advance (provider pull) (client Answer) (fun _ _ => 1) (fuel + 1)
          (packet pull cursor world reversed) =
          (spent, .done ⟨(), reversed.reverse ++ answers, (finalCursor, finalWorld)⟩)
  | 0, _, _, _, _, _, _, completed => by
      simp [collectCounted] at completed
  | fuel + 1, cursor, world, reversed, spent, finalWorld, answers, completed => by
      cases pulled : pull cursor world with
      | mk nextWorld reply =>
          cases reply with
          | done =>
              simp only [collectCounted, pulled, Prod.mk.injEq, Option.some.injEq] at completed
              rcases completed with ⟨rfl, rfl, rfl⟩
              refine ⟨cursor, ?_⟩
              rw [advance_poll]
              dsimp only
              rw [pulled]
              simp only [List.append_nil]
              rfl
          | suspend residual =>
              cases h : collectCounted pull fuel residual nextWorld with
              | mk used result =>
                  rcases result with ⟨lastWorld, observation⟩
                  cases observation with
                  | none => simp [collectCounted, pulled, h] at completed
                  | some values =>
                      simp only [collectCounted, pulled, h, Prod.mk.injEq,
                        Option.some.injEq] at completed
                      rcases completed with ⟨rfl, rfl, rfl⟩
                      obtain ⟨finalCursor, exactRun⟩ :=
                        completed_exact pull fuel residual nextWorld reversed used lastWorld values h
                      refine ⟨finalCursor, ?_⟩
                      rw [advance_poll]
                      simp only [pulled, exactRun]
          | yield answer residual =>
              cases h : collectCounted pull fuel residual nextWorld with
              | mk used result =>
                  rcases result with ⟨lastWorld, observation⟩
                  cases observation with
                  | none => simp [collectCounted, pulled, h] at completed
                  | some values =>
                      simp only [collectCounted, pulled, h, Option.map_some, Prod.mk.injEq,
                        Option.some.injEq] at completed
                      rcases completed with ⟨rfl, rfl, rfl⟩
                      obtain ⟨finalCursor, exactRun⟩ :=
                        completed_exact pull fuel residual nextWorld (answer :: reversed)
                          used lastWorld values h
                      refine ⟨finalCursor, ?_⟩
                      rw [advance_poll]
                      simp only [pulled, exactRun, List.reverse_cons, List.append_assoc,
                        List.singleton_append]

/-- Complete-list observations also reflect from cursor to source. This
projection intentionally forgets an unfinished world's state: the extra
scheduler inspection may execute an additional pull while still unfinished. -/
theorem advance_published (pull : HState → World → World × Pull HState Answer) :
    ∀ (fuel : Nat) (cursor : HState) (world : World) (reversed : List Answer),
      (observed pull (advance (provider pull) (client Answer) (fun _ _ => 1)
        (fuel + 1) (packet pull cursor world reversed)).2).2 =
      (collectCounted pull fuel cursor world).2.2.map (reversed.reverse ++ ·)
  | 0, cursor, world, reversed => by
      rw [advance_poll]
      cases pulled : pull cursor world with
      | mk nextWorld reply => cases reply <;> rfl
  | fuel + 1, cursor, world, reversed => by
      rw [advance_poll]
      dsimp only
      cases pulled : pull cursor world with
      | mk nextWorld reply =>
          cases reply with
          | done =>
              simp only [collectCounted, pulled, Option.map_some, List.append_nil]
              rfl
          | suspend residual =>
              simpa only [collectCounted, pulled] using
                advance_published pull fuel residual nextWorld reversed
          | yield answer residual =>
              simpa only [collectCounted, pulled, List.reverse_cons, List.append_assoc,
                List.singleton_append, Option.map_map, Function.comp_def] using
                advance_published pull fuel residual nextWorld (answer :: reversed)

/-- Two-sided completed observation: the same receipt, final world and full
collection occur on exactly the same completed source/cursor runs. This makes
no equality assertion for the worlds of unfinished runs. -/
theorem completed_iff (pull : HState → World → World × Pull HState Answer)
    (fuel : Nat) (cursor : HState) (world : World)
    (spent : Nat) (finalWorld : World) (answers : List Answer) :
    (∃ finalCursor,
      advance (provider pull) (client Answer) (fun _ _ => 1) (fuel + 1)
        (packet pull cursor world []) =
        (spent, .done ⟨(), answers, (finalCursor, finalWorld)⟩)) ↔
      collectCounted pull fuel cursor world = (spent, finalWorld, some answers) := by
  constructor
  · rintro ⟨finalCursor, cursorDone⟩
    have publishes := advance_published pull fuel cursor world []
    rw [cursorDone] at publishes
    simp only [observed, List.reverse_nil, List.nil_append] at publishes
    cases counted : collectCounted pull fuel cursor world with
    | mk actualSpent result =>
        rcases result with ⟨actualWorld, observation⟩
        rw [counted] at publishes
        dsimp only at publishes
        have actualObservation : observation = some answers := by simpa using publishes.symm
        subst observation
        obtain ⟨actualCursor, exactRun⟩ :=
          completed_exact pull fuel cursor world [] actualSpent actualWorld answers counted
        have results := congrArg
          (fun result => (result.1, observed pull result.2)) (cursorDone.symm.trans exactRun)
        simp only [observed, List.reverse_nil, List.nil_append] at results
        exact results.symm
  · intro completed
    simpa only [List.reverse_nil, List.nil_append] using
      completed_exact pull fuel cursor world [] spent finalWorld answers completed

/-- Interoperability with the actual world-aware source collector. The cursor
publishes the same complete answer-store occurrences and final world, and its
receipt is bounded by the source's pull budget. -/
theorem completed_effects {Store Value : Type}
    (pull : HState → Store → World → World × Pull HState (Value × Store))
    (checkpoint : Store) (fuel : Nat) (cursor : HState) (world finalWorld : World)
    (reversed answers : List (Value × Store))
    (completed : NativeControlCollection.Effects.collectWorld pull checkpoint fuel cursor world =
      (finalWorld, some answers)) :
    ∃ spent finalCursor, spent ≤ fuel ∧
      advance (provider (fun h w => pull h checkpoint w)) (client (Value × Store))
        (fun _ _ => 1) (fuel + 1)
        (packet (fun h w => pull h checkpoint w) cursor world reversed) =
        (spent, .done ⟨(), reversed.reverse ++ answers, (finalCursor, finalWorld)⟩) := by
  have agrees := collectCounted_effects pull checkpoint fuel cursor world
  rw [completed] at agrees
  cases counted : collectCounted (fun h w => pull h checkpoint w) fuel cursor world with
  | mk spent result =>
      rcases result with ⟨lastWorld, observation⟩
      rw [counted] at agrees
      simp only [Prod.mk.injEq] at agrees
      rcases agrees with ⟨rfl, rfl⟩
      obtain ⟨finalCursor, exactRun⟩ :=
        completed_exact (fun h w => pull h checkpoint w) fuel cursor world reversed
          spent lastWorld answers counted
      have bound := collectCounted_bound (fun h w => pull h checkpoint w) fuel cursor world
      rw [counted] at bound
      exact ⟨spent, finalCursor, bound, exactRun⟩

/-- Completed observations include the terminal world's effects. No assertion
about a shifted-fuel unfinished world is needed. -/
theorem completed_effects_observed {Store Value : Type}
    (pull : HState → Store → World → World × Pull HState (Value × Store))
    (checkpoint : Store) (fuel : Nat) (cursor : HState) (world finalWorld : World)
    (answers : List (Value × Store))
    (completed : NativeControlCollection.Effects.collectWorld pull checkpoint fuel cursor world =
      (finalWorld, some answers)) :
    observed (fun h w => pull h checkpoint w)
      (advance (provider (fun h w => pull h checkpoint w)) (client (Value × Store))
        (fun _ _ => 1) (fuel + 1)
        (packet (fun h w => pull h checkpoint w) cursor world [])).2 =
      (finalWorld, some answers) := by
  obtain ⟨spent, finalCursor, _, exactRun⟩ :=
    completed_effects pull checkpoint fuel cursor world finalWorld [] answers completed
  rw [exactRun]
  rfl

end Generic

namespace Controls

def effects : Nat → List Nat → List Nat × Pull Nat Nat
  | 0, world => (world ++ [10], .suspend 1)
  | 1, world => (world ++ [20], .yield 7 2)
  | 2, world => (world ++ [30], .yield 7 3)
  | _, world => (world ++ [40], .done)

/-- An interruption retains the actual continuation and the effect already
performed before any answer was available. -/
theorem paused_state_and_world :
    advance (provider effects) (client Nat) (fun _ _ => 1) 1
      (packet effects 0 [] []) =
      (1, .paused (packet effects 1 [10] [])) := rfl

/-- Exhaustion contributes an effect too. Four pulls and a final client
inspection return both duplicate occurrences and the complete effect log. -/
theorem terminal_world_and_receipt :
    advance (provider effects) (client Nat) (fun _ _ => 1) 5
      (packet effects 0 [] []) =
      (4, .done ⟨(), [7, 7], (3, [10, 20, 30, 40])⟩) := rfl

/-- Resumption does not replay the first effect or reset the pull receipt. -/
theorem resumed_without_replay :
    resume (provider effects) (client Nat) (fun _ _ => 1) 4
      (advance (provider effects) (client Nat) (fun _ _ => 1) 1
        (packet effects 0 [] [])) =
      (4, .done ⟨(), [7, 7], (3, [10, 20, 30, 40])⟩) := rfl

def terminalOnly (_ : Unit) (world : Nat) : Nat × Pull Unit Nat := (world + 1, .done)

/-- The terminal world's update is already retained when the scheduler pauses
immediately after the terminal pull, before inspecting the client's return. -/
theorem terminal_world_retained_at_pause :
    advance (provider terminalOnly) (client Nat) (fun _ _ => 1) 1
      (packet terminalOnly () 7 []) =
      (1, .paused ⟨(), .finished [], ((), 8)⟩) := rfl

/-- A completed client is inert: resuming it neither repeats exhaustion nor
charges another host pull. -/
theorem completed_resume_is_inert :
    resume (provider terminalOnly) (client Nat) (fun _ _ => 1) 100
      (advance (provider terminalOnly) (client Nat) (fun _ _ => 1) 2
        (packet terminalOnly () 7 [])) =
      (1, .done ⟨(), [], ((), 8)⟩) := rfl

/-- An incorrect attempt to embed worlds in the old host state has nowhere to
return the terminal update when it converts exhaustion to bare `Pull.done`. -/
def discardTerminalWorld (state : Unit × Nat) : Pull (Unit × Nat) Nat :=
  match terminalOnly state.1 state.2 with
  | (_, .done) => .done
  | (world, .yield answer residual) => .yield answer (residual, world)
  | (world, .suspend residual) => .suspend (residual, world)

/-- Negative control: stripping the world's terminal reply loses a real
effect, even though both adapters return exactly the same empty collection. -/
theorem lost_terminal_world_is_wrong :
    advance (NativeControlCursor.provider discardTerminalWorld) (client Nat) (fun _ _ => 1) 2
      (NativeControlCursor.packet discardTerminalWorld ((), 7) []) =
      (1, .done ⟨(), [], ((), 7)⟩) ∧
    advance (provider terminalOnly) (client Nat) (fun _ _ => 1) 2
      (packet terminalOnly () 7 []) =
      (1, .done ⟨(), [], ((), 8)⟩) := ⟨rfl, rfl⟩

/-- A shifted-fuel equality for *unfinished worlds* would be false: the extra
client step can execute an effectful poll instead of inspecting a return. -/
theorem unfinished_extra_poll_changes_world :
    (collectCounted effects 0 0 []).2 = ([], none) ∧
    observed effects
      (advance (provider effects) (client Nat) (fun _ _ => 1) 1
        (packet effects 0 [] [])).2 = ([10], none) ∧
    (collectCounted effects 0 0 []).2 ≠
      observed effects
        (advance (provider effects) (client Nat) (fun _ _ => 1) 1
          (packet effects 0 [] [])).2 := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.NativeControlEffectCursor
