import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.TapeActions

/-!
# Configuration-independent code for a table row

A compiled row receives its two half-tapes as process values. Its code depends
only on the finite table entry. The received values instantiate the tape
action through COMM, including dynamic construction of the pushed cell.
Eight communications return the complete updated configuration.

Selecting an entry and repeating the compiled rows are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.RowProgram

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.TuringMachine
open Stack TapeActions

def pushCode (destination head : Nat) (cells : Pattern) : Pattern :=
  parallel [parallel [send pushPort cells, receive pushPort (pushBody head)],
    relay 6 destination]

def popCode (destination : Nat) (cells : Pattern) : Pattern :=
  parallel [relay 3 9, relay 4 destination,
    parallel [send nilPort emptyCase, cells, send consPort zero]]

def actionCode (next written pushDestination popDestination : Nat)
    (pushCells popCells : Pattern) : Pattern :=
  parallel [send statePort (symbolCode next),
    pushCode pushDestination written pushCells, popCode popDestination popCells]

def rowCode (entry : Transition) (left right : Pattern) : Pattern :=
  match entry.move with
  | .right => actionCode entry.next entry.write 8 10 left right
  | .left => actionCode entry.next entry.write 10 8 right left

/-- The two tape arguments remain outside literal quotes. -/
def program (entry : Transition) : Pattern :=
  receive leftPort (receive rightPort (rowCode entry (drop 1) (drop 0)))

private theorem subst_pushBody (head k : Nat) (replacement : Pattern) :
    semanticSubstProc (k + 1) replacement (pushBody head) = pushBody head := by
  simp [pushBody, send, receive, consBody, parallel, drop,
    semanticSubstProc, semanticSubstProcList, semanticSubstName, subst_symbolCode]

private theorem subst_relay (source destination k : Nat) (replacement : Pattern) :
    semanticSubstProc k replacement (relay source destination) = relay source destination := by
  simp [relay, send, receive, drop, semanticSubstProc, semanticSubstName]

theorem subst_pushCode (destination head k : Nat) (replacement cells : Pattern) :
    semanticSubstProc k replacement (pushCode destination head cells) =
      pushCode destination head (semanticSubstProc k replacement cells) := by
  simp [pushCode, parallel, send, receive, semanticSubstProc,
    semanticSubstProcList, semanticSubstName, subst_pushBody, subst_relay]

theorem subst_popCode (destination k : Nat) (replacement cells : Pattern) :
    semanticSubstProc k replacement (popCode destination cells) =
      popCode destination (semanticSubstProc k replacement cells) := by
  simp [popCode, parallel, send, semanticSubstProc, semanticSubstProcList,
    semanticSubstName, subst_emptyCase, subst_relay, zero]

theorem subst_actionCode (next written pushDestination popDestination k : Nat)
    (replacement pushCells popCells : Pattern) :
    semanticSubstProc k replacement
        (actionCode next written pushDestination popDestination pushCells popCells) =
      actionCode next written pushDestination popDestination
        (semanticSubstProc k replacement pushCells) (semanticSubstProc k replacement popCells) := by
  simp [actionCode, parallel, send, semanticSubstProc, semanticSubstProcList,
    semanticSubstName, subst_symbolCode, subst_pushCode, subst_popCode]

theorem subst_rowCode (entry : Transition) (k : Nat) (replacement left right : Pattern) :
    semanticSubstProc k replacement (rowCode entry left right) =
      rowCode entry (semanticSubstProc k replacement left)
        (semanticSubstProc k replacement right) := by
  cases moving : entry.move <;> simp [rowCode, moving, subst_actionCode]

theorem subst_program (entry : Transition) (k : Nat) (replacement : Pattern) :
    semanticSubstProc k replacement (program entry) = program entry := by
  simp [program, receive, semanticSubstProc, semanticSubstName, subst_rowCode, drop]

theorem comm_program (entry : Transition) (payload : Pattern) :
    semanticCommSubst (program entry) payload = program entry :=
  subst_program entry 0 _

theorem normalize_program (entry : Transition) :
    semanticNormalizeProc (program entry) = program entry := by
  cases moving : entry.move <;>
    simp [program, rowCode, moving, actionCode, pushCode, popCode, relay, pushBody,
      emptyCase, reply, encode, consBody, parallel, send, receive, drop,
      semanticNormalizeProc, semanticNormalizeProcList, semanticNormalizeName,
      normalize_symbolCode]

theorem program_coreShape (entry : Transition) : rhoProcCoreShape (program entry) = true := by
  cases moving : entry.move <;>
    simp [program, rowCode, moving, actionCode, pushCode, popCode, relay, pushBody,
      emptyCase, reply, encode, consBody, parallel, send, receive, drop,
      rhoProcCoreShape, rhoProcCoreShapeList, rhoNameCoreShape, symbolCode_coreShape, zero]

theorem program_binderSafe (entry : Transition) (depth : Nat) :
    Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt "NQuote" depth (program entry) = true := by
  cases moving : entry.move <;>
    simp [program, rowCode, moving, actionCode, pushCode, popCode, relay, pushBody,
      emptyCase, reply, encode, consBody, parallel, send, receive, drop,
      Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt,
      Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeListAt, symbolCode_binderSafe, zero]

theorem left_received (entry : Transition) (left : List Nat) :
    semanticCommSubst (receive rightPort (rowCode entry (drop 1) (drop 0))) (encode left) =
      receive rightPort (rowCode entry (encode left) (drop 0)) := by
  simp [semanticCommSubst, receive, semanticSubstProc, semanticSubstName,
    normalize_encode, subst_rowCode, drop]

theorem right_received (entry : Transition) (left right : List Nat) :
    semanticCommSubst (rowCode entry (encode left) (drop 0)) (encode right) =
      rowCode entry (encode left) (encode right) := by
  simp [semanticCommSubst, normalize_encode, subst_rowCode, subst_encode, drop,
    semanticSubstProc]

theorem rowCode_encodes_action (entry : Transition) (configuration : Configuration) :
    rowCode entry (encode configuration.left) (encode configuration.right) =
      rowAction entry configuration := by
  cases entry.move <;> rfl

def invocation (entry : Transition) (left right : List Nat) : Pattern :=
  parallel [send leftPort (encode left), program entry, send rightPort (encode right)]

/-- The same finite row code works on every finite tape representation. -/
theorem invocation_reduces (entry : Transition) (configuration : Configuration) :
    Nonempty (ReducesN 8 (invocation entry configuration.left configuration.right)
      (configurationReply (configuration.after entry))) := by
  have first : Reduces (invocation entry configuration.left configuration.right)
      (parallel [receive rightPort (rowCode entry (encode configuration.left) (drop 0)),
        send rightPort (encode configuration.right)]) := by
    change Reduces (parallel ([send leftPort (encode configuration.left),
      receive leftPort (receive rightPort (rowCode entry (drop 1) (drop 0)))] ++
        [send rightPort (encode configuration.right)])) _
    simpa only [left_received, List.singleton_append] using
      (Reduces.comm (n := leftPort) (q := encode configuration.left)
        (p := receive rightPort (rowCode entry (drop 1) (drop 0)))
        (rest := [send rightPort (encode configuration.right)]))
  have rawSecond := Reduces.comm (n := rightPort) (q := encode configuration.right)
    (p := rowCode entry (encode configuration.left) (drop 0)) (rest := [])
  rw [right_received, rowCode_encodes_action] at rawSecond
  have second : Reduces
      (parallel [receive rightPort (rowCode entry (encode configuration.left) (drop 0)),
        send rightPort (encode configuration.right)]) (rowAction entry configuration) :=
    .equiv (StructuralCongruence.par_comm _ _) rawSecond (StructuralCongruence.par_singleton _)
  obtain ⟨actionPath⟩ := rowAction_reduces entry configuration
  exact ⟨.succ first (.succ second actionPath)⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.RowProgram
