import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.UniversalOutputs
import Mettapedia.Languages.TuringMachine.ClassicMachines

/-!
# Tape-protocol controls

Both represented tape ends supply a blank; nonempty movement retains its
neighbor and all other cells. Port names and tape symbols are separated by
structural observations. Quotation sealing distinguishes valid dynamic
cell construction from capturing an outer variable inside a literal quote.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.TuringMachine
open Stack TapeActions

theorem empty_pop_supplies_blank :
    Nonempty (ReducesN 2 (pop []) (reply 0 [])) := pop_reduces []

theorem nonempty_pop_retains_tail (head : Nat) (tail : List Nat) :
    Nonempty (ReducesN 2 (pop (head :: tail)) (reply head tail)) :=
  pop_reduces (head :: tail)

theorem pop_case_ports_distinct : ¬ StructuralCongruence nilPort consPort := by
  rw [port_sc_iff]
  decide

theorem head_and_tail_ports_distinct : ¬ StructuralCongruence headPort tailPort := by
  rw [port_sc_iff]
  decide

theorem blank_and_one_distinct : ¬ StructuralCongruence (symbolCode 0) (symbolCode 1) := by
  rw [symbolCode_sc_iff]
  decide

theorem different_states_have_different_keys :
    ¬ StructuralCongruence (LookupKey.key 0 1) (LookupKey.key 1 1) := by
  rw [LookupKey.key_sc_iff]
  decide

theorem different_symbols_have_different_keys :
    ¬ StructuralCongruence (LookupKey.key 1 0) (LookupKey.key 1 1) := by
  rw [LookupKey.key_sc_iff]
  decide

private theorem symbolCode_nameCount (names : List String) (index : Nat) :
    nameCount names (symbolCode index) = 0 := by
  induction index with
  | zero => simp [symbolCode, zero, nameCount]
  | succ index ih => simp [symbolCode, receive, symbolPort, zero, nameCount, ih]

theorem dispatcher_waits_for_request : NormalForm Persistent.dispatcher := by
  apply GuardedReplication.idle_normal _ _ _ []
  simp [Persistent.pulsePort, port, nameCount, symbolCode_nameCount]

theorem row_server_waits_for_request (index : Nat) (entry : Transition) :
    NormalForm (Persistent.rowServer index entry) := by
  apply GuardedReplication.idle_normal _ _ _ []
  simp [LookupKey.key, LookupKey.data, port, send, nameCount, symbolCode_nameCount]

theorem busyBeaver_run_retains_four_ones :
    Nonempty (ReducesStar (Persistent.encoding busyBeaver2 Configuration.blank)
      (Persistent.encoding busyBeaver2 busyBeaver2Final)) ∧ busyBeaver2Final.ones = 4 := by
  obtain ⟨final, same, run⟩ := Persistent.reaches_preserved busyBeaver2 busyBeaver2_run.1
  cases Configuration.term_injective same
  exact ⟨run, busyBeaver2_ones⟩

theorem repeated_runs_have_no_tape_bound (rounds : Nat) :
    Nonempty (ReducesStar (Persistent.encoding alternating Configuration.blank)
      (Persistent.encoding alternating ⟨0, alternatingTape rounds, 0, []⟩)) := by
  obtain ⟨final, same, run⟩ := Persistent.reaches_preserved alternating (alternating_reaches rounds)
  cases Configuration.term_injective same
  exact run

theorem busyBeaver_reaches_quiescent_result :
    Nonempty (ReducesStar (Persistent.encoding busyBeaver2 Configuration.blank)
      (Persistent.awaiting busyBeaver2 busyBeaver2Final)) ∧
      NormalForm (Persistent.awaiting busyBeaver2 busyBeaver2Final) ∧ busyBeaver2Final.ones = 4 := by
  obtain ⟨run⟩ := busyBeaver_run_retains_four_ones.1
  obtain ⟨⟨finish⟩, quiet⟩ := Halting.halted_dispatch busyBeaver2_run.2
  exact ⟨⟨run.trans (reducesN_to_star finish)⟩, quiet, busyBeaver2_ones⟩

theorem alternating_query_is_not_quiescent :
    ¬ NormalForm (Persistent.awaiting alternating Configuration.blank) := by
  apply Halting.awaiting_not_normal (entry := ⟨0, 0, 1, .right, 1⟩)
  · decide
  · decide

/-- A halted source still needs dispatch in the target; observing an
unprocessed packet is not the target halting test. -/
theorem halted_source_packet_still_dispatches :
    Halted busyBeaver2 busyBeaver2Final.term ∧
      ¬ NormalForm (Persistent.encoding busyBeaver2 busyBeaver2Final) :=
  ⟨busyBeaver2_run.2, Halting.encoding_not_normal _ _⟩

def rightRow : Transition := ⟨0, 2, 7, .right, 1⟩
def leftRow : Transition := ⟨0, 2, 7, .left, 1⟩

theorem right_edge_creates_blank (written : List Nat) :
    Nonempty (ReducesN 6 (rowAction rightRow ⟨0, written, 2, []⟩)
      (configurationReply ⟨1, 7 :: written, 0, []⟩)) :=
  rowAction_reduces rightRow ⟨0, written, 2, []⟩

theorem left_edge_creates_blank (written : List Nat) :
    Nonempty (ReducesN 6 (rowAction leftRow ⟨0, [], 2, written⟩)
      (configurationReply ⟨1, [], 0, 7 :: written⟩)) :=
  rowAction_reduces leftRow ⟨0, [], 2, written⟩

theorem right_neighbor_retained (left : List Nat) (neighbor : Nat) (right : List Nat) :
    Nonempty (ReducesN 6 (rowAction rightRow ⟨0, left, 2, neighbor :: right⟩)
      (configurationReply ⟨1, 7 :: left, neighbor, right⟩)) :=
  rowAction_reduces rightRow ⟨0, left, 2, neighbor :: right⟩

theorem left_neighbor_retained (left : List Nat) (neighbor : Nat) (right : List Nat) :
    Nonempty (ReducesN 6 (rowAction leftRow ⟨0, neighbor :: left, 2, right⟩)
      (configurationReply ⟨1, left, neighbor, 7 :: right⟩)) :=
  rowAction_reduces leftRow ⟨0, neighbor :: left, 2, right⟩

/-- A literal quote seals the intended outer tail variable. -/
def frozenPushBody (head : Nat) : Pattern :=
  send resultPort (.apply "PDrop" [.apply "NQuote"
    [receive nilPort (receive consPort (consBody head (drop 2)))]] )

theorem pushBody_binderSafe (head : Nat) : binderSafeAt "NQuote" 1 (pushBody head) = true := by
  simp [pushBody, send, receive, consBody, parallel, drop, binderSafeAt,
    binderSafeListAt, symbolCode_binderSafe]

theorem frozenPushBody_not_binderSafe (head : Nat) :
    binderSafeAt "NQuote" 1 (frozenPushBody head) = false := by
  simp [frozenPushBody, send, receive, consBody, parallel, drop, binderSafeAt,
    binderSafeListAt, symbolCode_binderSafe]

/-- Even structurally equal processes need a positive communication path
for endpoint transport; a zero-step path cannot rearrange their syntax. -/
theorem zero_path_does_not_transport :
    StructuralCongruence (parallel [zero]) zero ∧
      ¬ Nonempty (ReducesN 0 (parallel [zero]) zero) := by
  refine ⟨StructuralCongruence.par_singleton _, ?_⟩
  rw [ReducesN.zero_iff_eq]
  intro same
  cases same

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.Controls
