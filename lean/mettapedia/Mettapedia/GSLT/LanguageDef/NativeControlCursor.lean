import Mettapedia.GSLT.LanguageDef.HostGoalDelimiters
import Mettapedia.Machines.Cursor.Fold

/-!
# Host answer controls as providers of the common cursor protocol

This adapter connects `HostCalls.Pull` to `Machines.Cursor.Provider`. It
retains the real host residual after both a yield and a suspension. The
collector is a client of that existing protocol, so arbitrary chunking uses
the existing `Cursor.advance_add` law, with the same residual and receipts.

`advance_collect` identifies its completed observation with `HostCalls.collect`.
Its extra unit allows inspection of the client's return; on an unfinished run
it can instead perform one more poll. The comparison therefore does not equate
intermediate residuals or effects at that shifted fuel. `chunk_exact` preserves
the actual residual and receipt within this adapter. The receipt counts pulls,
not runtime instructions or wall time. This internal polling protocol does not
model handle allocation, affine ownership, disposal, faults, or exceptions.
Those are additional interface obligations, not implied by the adapter.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeControlCursor

open Mettapedia.TypeTheory
open Mettapedia.Machines.Cursor
open Mettapedia.GSLT.LanguageDef.HostCalls (Pull collect)
open CategoryTheory

variable {HState Answer : Type}

/-- A poll explicitly distinguishes suspension, exhaustion and an answer. -/
def protocol (Answer : Type) : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Unit
  Position _ := Pull Unit Answer
  next _ _ := ()

def provider (pull : HState → Pull HState Answer) : Provider (protocol Answer) where
  State _ _ := HState
  step h _ := match pull h with
    | .done => ⟨.done, h⟩
    | .yield a residual => ⟨.yield a (), residual⟩
    | .suspend residual => ⟨.suspend (), residual⟩

/-- The collector uses the common client type and existing fold-control states. -/
def client (Answer : Type) :
    Client (P := protocol Answer) (Return := fun _ _ => List Answer) where
  V _ _ := Fold.State (List Answer)
  str := fun _ _ => ↾(fun state => match state with
    | .finished values => ⟨.inl values, fun impossible => nomatch impossible⟩
    | .pulling reversed => ⟨.inr (), fun reply => match reply with
        | .done => .finished reversed.reverse
        | .yield value _ => .pulling (value :: reversed)
        | .suspend _ => .pulling reversed⟩)

def packet (pull : HState → Pull HState Answer) (cursor : HState) (reversed : List Answer) :
    Packet (provider pull) (client Answer) () := ⟨(), .pulling reversed, cursor⟩

/-- A paused client has no completed collection. -/
def published (pull : HState → Pull HState Answer) :
    Outcome (provider pull) (client Answer) () → Option (List Answer)
  | .paused _ => none
  | .done result => some result.2.1

theorem advance_poll (pull : HState → Pull HState Answer) (fuel : Nat)
    (cursor : HState) (reversed : List Answer) :
    advance (provider pull) (client Answer) (fun _ _ => 1) (fuel + 1)
        (packet pull cursor reversed) =
      let next : Packet (provider pull) (client Answer) () := match pull cursor with
        | .done => ⟨(), .finished reversed.reverse, cursor⟩
        | .yield a residual => packet pull residual (a :: reversed)
        | .suspend residual => packet pull residual reversed
      let result := advance (provider pull) (client Answer) (fun _ _ => 1) fuel next
      (1 + result.1, result.2) := by
  cases h : pull cursor <;>
    simp only [advance, packet, client, provider, protocol] <;>
    dsimp <;> rw [h] <;> rfl

/-- Equality of completed collection observations. The shifted client budget
may perform an extra poll when no collection is published, so this theorem
does not compare intermediate state or effects against the host collector. -/
theorem advance_collect (pull : HState → Pull HState Answer) :
    ∀ (fuel : Nat) (cursor : HState) (reversed : List Answer),
      published pull (advance (provider pull) (client Answer) (fun _ _ => 1)
        (fuel + 1) (packet pull cursor reversed)).2 =
      (collect pull fuel cursor).map (reversed.reverse ++ ·)
  | 0, cursor, reversed => by
      rw [advance_poll]
      cases pull cursor <;> rfl
  | fuel + 1, cursor, reversed => by
      rw [advance_poll]
      cases h : pull cursor with
      | done =>
          simp only [h, collect, Option.map_some, List.append_nil]
          rfl
      | yield value residual =>
          simp only [h, collect, Option.map_map, Function.comp_def]
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
            advance_collect pull fuel residual (value :: reversed)
      | suspend residual =>
          simpa only [h, collect] using advance_collect pull fuel residual reversed

/-- A host control may be run in any budget partition without changing its
actual residual, completed result or pull count. -/
theorem chunk_exact (pull : HState → Pull HState Answer) (first second : Nat)
    (cursor : HState) (reversed : List Answer) :
    advance (provider pull) (client Answer) (fun _ _ => 1) (first + second)
      (packet pull cursor reversed) =
    resume (provider pull) (client Answer) (fun _ _ => 1) second
      (advance (provider pull) (client Answer) (fun _ _ => 1) first
        (packet pull cursor reversed)) :=
  advance_add _ _ _ first second _

/-- A local conservation law for the unfinished answer sequence gives a
sound completed collection. Suspended work is included in `remaining`; it
cannot be replaced by just the rows already prepared for publication. -/
theorem collect_sound (pull : HState → Pull HState Answer)
    (remaining : HState → List Answer)
    (preserves : ∀ state, match pull state with
      | .done => remaining state = []
      | .suspend next => remaining state = remaining next
      | .yield answer next => remaining state = answer :: remaining next)
    (fuel : Nat) (state : HState) (answers : List Answer)
    (completed : collect pull fuel state = some answers) :
    answers = remaining state := by
  induction fuel generalizing state answers with
  | zero => simp [collect] at completed
  | succ fuel ih =>
      have conserved := preserves state
      cases moved : pull state with
      | done =>
          simp only [moved] at conserved
          simpa [collect, moved, conserved] using completed.symm
      | suspend next =>
          simp only [moved] at conserved
          simp only [collect, moved] at completed
          exact (ih next answers completed).trans conserved.symm
      | yield answer next =>
          simp only [moved] at conserved
          simp only [collect, moved] at completed
          cases found : collect pull fuel next with
          | none => simp [found] at completed
          | some tail =>
              simp only [found, Option.map_some, Option.some.injEq] at completed
              subst answers
              rw [ih next tail found, conserved]

/-- A decreasing finite work measure proves exhaustion of a conserving
provider. This bound counts provider polls, not the work inside a primitive
or the time taken by that primitive. The running cursor need not compute it. -/
theorem collect_complete (pull : HState → Pull HState Answer)
    (remaining : HState → List Answer)
    (preserves : ∀ state, match pull state with
      | .done => remaining state = []
      | .suspend next => remaining state = remaining next
      | .yield answer next => remaining state = answer :: remaining next)
    (rank : HState → Nat)
    (decreases : ∀ state, match pull state with
      | .done => rank state = 0
      | .suspend next => rank next < rank state
      | .yield _ next => rank next < rank state)
    (fuel : Nat) (state : HState) (enough : rank state < fuel) :
    collect pull fuel state = some (remaining state) := by
  induction fuel generalizing state with
  | zero => omega
  | succ fuel ih =>
      have conserved := preserves state
      have decrease := decreases state
      cases moved : pull state with
      | done =>
          simp only [moved] at conserved
          simp [collect, moved, conserved]
      | suspend next =>
          simp only [moved] at conserved decrease
          have small : rank next < fuel := by omega
          simp [collect, moved, ih next small, conserved]
      | yield answer next =>
          simp only [moved] at conserved decrease
          have small : rank next < fuel := by omega
          simp [collect, moved, ih next small, conserved]

namespace Controls

def delayed : Nat → Pull Nat Nat
  | 0 => .suspend 1
  | 1 => .yield 7 2
  | 2 => .yield 7 3
  | _ => .done

theorem pending_keeps_residual :
    advance (provider delayed) (client Nat) (fun _ _ => 1) 1
      (packet delayed 0 []) = (1, .paused (packet delayed 1 [])) := rfl

theorem duplicate_occurrences :
    published delayed (advance (provider delayed) (client Nat) (fun _ _ => 1) 5
      (packet delayed 0 [])).2 = some [7, 7] := rfl

theorem completion_needs_exhaustion :
    published delayed (advance (provider delayed) (client Nat) (fun _ _ => 1) 3
      (packet delayed 0 [])).2 = none := rfl

/-- Restarting at a pause loses the completed observation available by resuming. -/
theorem restart_is_wrong :
    published delayed (advance (provider delayed) (client Nat) (fun _ _ => 1) 3
      (packet delayed 0 [])).2 ≠
    published delayed (resume (provider delayed) (client Nat) (fun _ _ => 1) 3
      (advance (provider delayed) (client Nat) (fun _ _ => 1) 2
        (packet delayed 0 []))).2 := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.NativeControlCursor
