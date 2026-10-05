import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.Stack
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReductionPaths
import Mettapedia.Languages.TuringMachine.Configurations

/-!
# A selected table row performs its tape action through canonical rho

The row body pushes its written symbol onto one half-tape and pops the other.
Relays return a uniform four-port packet: state, left half-tape, scanned
symbol, right half-tape. Six canonical communications implement this action
for every finite tape, including movement beyond either represented end.

The transition table's selection of a row is not performed by this module.
`selected_row` makes that boundary explicit using the source row witness;
it does not claim an encoding of a complete machine or its halting behavior.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.TapeActions

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.TuringMachine
open Stack

abbrev statePort : Pattern := port 7
abbrev leftPort : Pattern := port 8
abbrev scannedPort : Pattern := port 9
abbrev rightPort : Pattern := port 10

/-- Forward a process value by a bound drop in the new output payload. -/
def relay (source destination : Nat) : Pattern :=
  receive (port source) (send (port destination) (drop 0))

theorem relay_result (destination : Nat) (payload : Pattern) :
    semanticCommSubst (send (port destination) (drop 0)) payload =
      send (port destination) (semanticNormalizeProc payload) := by
  simp [semanticCommSubst, send, drop, semanticSubstProc, semanticSubstName]

/-- A relay uses COMM, retaining all other live processes. -/
noncomputable def relay_step (source destination : Nat) (payload : Pattern)
    (rest : List Pattern) :
    Reduces (parallel ([send (port source) payload, relay source destination] ++ rest))
      (parallel ([send (port destination) (semanticNormalizeProc payload)] ++ rest)) := by
  change Reduces
    (parallel ([send (port source) payload,
      receive (port source) (send (port destination) (drop 0))] ++ rest)) _
  have step := Reduces.comm (n := port source) (q := payload)
    (p := send (port destination) (drop 0)) (rest := rest)
  simpa only [relay_result] using step

def pushTo (destination head : Nat) (tail : List Nat) : Pattern :=
  parallel [push head tail, relay 6 destination]

theorem pushTo_reduces (destination head : Nat) (tail : List Nat) :
    Nonempty (ReducesN 2 (pushTo destination head tail)
      (send (port destination) (encode (head :: tail)))) := by
  obtain ⟨pushed⟩ := push_reduces head tail
  have first : Reduces (pushTo destination head tail)
      (parallel [send resultPort (encode (head :: tail)), relay 6 destination]) :=
    .par pushed
  have second := relay_step 6 destination (encode (head :: tail)) []
  rw [normalize_encode] at second
  have finalStep : Reduces
      (parallel [send resultPort (encode (head :: tail)), relay 6 destination])
      (send (port destination) (encode (head :: tail))) :=
    .equiv (.refl _) second (StructuralCongruence.par_singleton _)
  exact ⟨.succ first (.succ finalStep (.zero _))⟩

def popTo (destination : Nat) (cells : List Nat) : Pattern :=
  parallel [relay 3 9, relay 4 destination, pop cells]

def popReply (destination : Nat) (cells : List Nat) : Pattern :=
  parallel [send scannedPort (symbolCode (cells.headD 0)), send (port destination) (encode cells.tail)]

theorem popTo_reduces (destination : Nat) (cells : List Nat) :
    Nonempty (ReducesN 4 (popTo destination cells) (popReply destination cells)) := by
  obtain ⟨popped⟩ := pop_reduces cells
  have first := ReducesN.par_any_pos
    (before := [relay 3 9, relay 4 destination]) (after := []) popped
  have flat : parallel [relay 3 9, relay 4 destination, reply (cells.headD 0) cells.tail] ≡
      parallel [send headPort (symbolCode (cells.headD 0)), relay 3 9,
        send tailPort (encode cells.tail), relay 4 destination] := by
    refine .trans _ _ _
      (StructuralCongruence.par_flatten [relay 3 9, relay 4 destination]
        [send headPort (symbolCode (cells.headD 0)), send tailPort (encode cells.tail)]) ?_
    apply StructuralCongruence.par_perm
    exact (List.perm_middle (l₁ := [relay 3 9, relay 4 destination])
      (l₂ := [send tailPort (encode cells.tail)])).trans
      (.cons _ (.cons _ (.swap _ _ [])))
  have next := relay_step 3 9 (symbolCode (cells.headD 0))
    [send tailPort (encode cells.tail), relay 4 destination]
  rw [normalize_symbolCode] at next
  have third : Reduces
      (parallel [relay 3 9, relay 4 destination, reply (cells.headD 0) cells.tail])
      (parallel [send scannedPort (symbolCode (cells.headD 0)),
        send tailPort (encode cells.tail), relay 4 destination]) :=
    .equiv flat next (.refl _)
  have last := relay_step 4 destination (encode cells.tail)
    [send scannedPort (symbolCode (cells.headD 0))]
  rw [normalize_encode] at last
  have fourth : Reduces
      (parallel [send scannedPort (symbolCode (cells.headD 0)),
        send tailPort (encode cells.tail), relay 4 destination])
      (popReply destination cells) := by
    refine .equiv ?_ last (StructuralCongruence.par_comm _ _)
    exact StructuralCongruence.par_perm _ _
      (List.perm_append_comm (l₁ := [send scannedPort (symbolCode (cells.headD 0))])
        (l₂ := [send tailPort (encode cells.tail), relay 4 destination]))
  exact ⟨reducesN_concat first (.succ third (.succ fourth (.zero _)))⟩

def action (next written pushDestination popDestination : Nat)
    (pushCells popCells : List Nat) : Pattern :=
  parallel [send statePort (symbolCode next),
    pushTo pushDestination written pushCells, popTo popDestination popCells]

def actionReply (next written pushDestination popDestination : Nat)
    (pushCells popCells : List Nat) : Pattern :=
  parallel [send statePort (symbolCode next),
    send (port pushDestination) (encode (written :: pushCells)),
    send scannedPort (symbolCode (popCells.headD 0)),
    send (port popDestination) (encode popCells.tail)]

theorem action_reduces (next written pushDestination popDestination : Nat)
    (pushCells popCells : List Nat) :
    Nonempty (ReducesN 6 (action next written pushDestination popDestination pushCells popCells)
      (actionReply next written pushDestination popDestination pushCells popCells)) := by
  obtain ⟨pushed⟩ := pushTo_reduces pushDestination written pushCells
  have first := ReducesN.par_any_pos
    (before := [send statePort (symbolCode next)]) (after := [popTo popDestination popCells]) pushed
  obtain ⟨popped⟩ := popTo_reduces popDestination popCells
  have second := ReducesN.par_any_pos
    (before := [send statePort (symbolCode next),
      send (port pushDestination) (encode (written :: pushCells))]) (after := []) popped
  have final : parallel [send statePort (symbolCode next),
      send (port pushDestination) (encode (written :: pushCells)), popReply popDestination popCells] ≡
      actionReply next written pushDestination popDestination pushCells popCells :=
    StructuralCongruence.par_flatten
      [send statePort (symbolCode next), send (port pushDestination) (encode (written :: pushCells))]
      [send scannedPort (symbolCode (popCells.headD 0)), send (port popDestination) (encode popCells.tail)]
  exact ⟨reducesN_concat first (second.transport (.refl _) final)⟩

def configurationReply (configuration : Configuration) : Pattern :=
  parallel [send statePort (symbolCode configuration.state), send leftPort (encode configuration.left),
    send scannedPort (symbolCode configuration.scanned), send rightPort (encode configuration.right)]

/-- The body of an already selected row; selection is a separate protocol. -/
def rowAction (entry : Transition) (configuration : Configuration) : Pattern :=
  match entry.move with
  | .right => action entry.next entry.write 8 10 configuration.left configuration.right
  | .left => action entry.next entry.write 10 8 configuration.right configuration.left

theorem rowAction_reduces (entry : Transition) (configuration : Configuration) :
    Nonempty (ReducesN 6 (rowAction entry configuration)
      (configurationReply (configuration.after entry))) := by
  cases moving : entry.move with
  | right =>
      simp only [rowAction, moving]
      obtain ⟨path⟩ := action_reduces entry.next entry.write 8 10 configuration.left configuration.right
      have same : actionReply entry.next entry.write 8 10 configuration.left configuration.right =
          configurationReply (configuration.after entry) := by
        cases cells : configuration.right <;>
          simp [Configuration.after, moving, cells, actionReply, configurationReply]
      exact ⟨path.transport (.refl _) (same ▸ StructuralCongruence.refl _)⟩
  | left =>
      simp only [rowAction, moving]
      obtain ⟨path⟩ := action_reduces entry.next entry.write 10 8 configuration.right configuration.left
      have swapped : actionReply entry.next entry.write 10 8 configuration.right configuration.left ≡
          configurationReply (configuration.after entry) := by
        cases cells : configuration.left <;>
          (simp only [Configuration.after, moving, cells, configurationReply, actionReply,
            List.headD, List.tail]
           apply StructuralCongruence.par_perm
           exact .cons _ ((List.perm_middle (l₁ := [_, _]) (l₂ := [])).trans
             (.cons _ (.swap _ _ []))))
      exact ⟨path.transport (.refl _) swapped⟩

/-- The source row witness and its concrete target action agree on every
part of the resulting configuration. This is the local tape obligation. -/
theorem selected_row {machine : Machine} (entry : Transition) (configuration : Configuration)
    (member : entry ∈ machine.transitions) (applies : entry.Applies configuration) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base (turingMachine machine)
        configuration.term (configuration.after entry).term ∧
      Nonempty (ReducesN 6 (rowAction entry configuration)
        (configurationReply (configuration.after entry))) :=
  ⟨step_term_iff.mpr ⟨entry, member, applies, rfl⟩, rowAction_reduces entry configuration⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.TapeActions
