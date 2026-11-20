import Mettapedia.Machines.NetworkBackpressureModule

/-!
# Finite receiver traces through the authored transition boundary

Replay checks preparation and permission at every event. Successful replay
preserves the buffer account and supplies a path of actual module rewrites.
One concrete transport read can project to an adjacent read/credit pair.

A runtime observer can supply a trace and a separate observation receipt.
Replay checks the supplied data, not the observer, compiler, driver or kernel.
The consumer role at a TLS transport boundary is executed by the networking
service; the byte projection establishes no physical domain authority or
scheduling-justice premise.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NetworkBackpressure.Trace

open Mettapedia.Machines.NetworkServiceModule
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation

def replay (batch : Nat) : State → List Action → Option State
  | s, [] => some s
  | s, a :: rest => if Admitted batch s a then replay batch (apply a s) rest else none

theorem replay_append (batch : Nat) (first rest : List Action) (s : State) :
    replay batch s (first ++ rest) = (replay batch s first).bind (fun t => replay batch t rest) := by
  induction first generalizing s with
  | nil => rfl
  | cons a first ih =>
      simp only [List.cons_append, replay]
      split <;> simp_all

theorem replay_concat {batch : Nat} {first rest : List Action} {s middle t : State}
    (left : replay batch s first = some middle) (right : replay batch middle rest = some t) :
    replay batch s (first ++ rest) = some t := by
  rw [replay_append, left]
  exact right

theorem replay_valid {batch capacity : Nat} {s t : State} {events : List Action}
    (initial : Valid capacity s) (checked : replay batch s events = some t) : Valid capacity t := by
  induction events generalizing s with
  | nil =>
      simp only [replay, Option.some.injEq] at checked
      exact checked ▸ initial
  | cons a rest ih =>
      simp only [replay] at checked
      split at checked
      next ready => exact ih (apply_valid initial ready.1) checked
      next => contradiction

def AuthoredStep (batch : Nat) (s t : State) : Prop :=
  ∃ a, atState (encodeState t) ∈ rewriteStepWithPremisesUsing (queries batch).relations NetworkServiceModule.language
    (request (encodeState s) (encodeAction a))

theorem replay_authored {batch : Nat} {s t : State} {events : List Action}
    (checked : replay batch s events = some t) :
    Relation.ReflTransGen (AuthoredStep batch) s t := by
  induction events generalizing s with
  | nil =>
      simp only [replay, Option.some.injEq] at checked
      subst t
      exact .refl
  | cons a rest ih =>
      simp only [replay] at checked
      split at checked
      next ready =>
        exact Relation.ReflTransGen.head
          ⟨a, (emitted_iff batch s (apply a s) a).mpr ⟨ready, rfl⟩⟩ (ih checked)
      next => contradiction

theorem read_credit_pair {batch n : Nat} {s : State} (openGate : s.backlog < batch)
    (positive : 0 < n) (available : n ≤ s.queued) :
    replay batch s [.read n, .credit] = some (apply .credit (apply (.read n) s)) := by
  simp [replay, Admitted, Prepared, Permitted, Eligible, Action.actor, apply,
    openGate, positive, available]

theorem unprepared_read_refused :
    replay 64 ⟨0, 3, 0, 4093, 0, 0, 0⟩ [.read 4] = none := by decide

#print axioms replay_valid
#print axioms replay_authored
#print axioms read_credit_pair

end Mettapedia.Machines.NetworkBackpressure.Trace
