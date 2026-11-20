import Mettapedia.Machines.ScheduledRun.CertificateReuse
import Mettapedia.Machines.ScheduledRun.MonitorControls

/-!
# Lasso-certificate controls and transient-arity detection workloads

The initial fork contributes an irrelevant arity to the global prefix clock;
the subsequent two-state loop needs only its own local clock. Measurements of
first-report turns are logical detection delays, not native wall-clock timing.
The edge-only mutant demonstrates why a closed word alone is insufficient.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScheduledRun.Controls

open State

theorem local_cycle_accepted : checkLoop cycleNext .rotating 1 [wait, wake] = true := by decide
theorem wrong_phase_rejected : checkLoop cycleNext .rotating 0 [wait, wake] = false := by decide
theorem changed_footprint_rejected : checkLoop waitNext .rotating 1 [wait, wake] = false := by decide
theorem canonical_short_loop_accepted : checkLoop waitNext .canonical 0 [wait] = true := by decide
theorem stale_segment_rejected : checkLoop staleNext .rotating 1 [2, 3, 4] = false := by decide
theorem empty_loop_rejected : checkLoop noNext .canonical 1 [] = false := by decide

def swappedNext : State → List State
  | wait => [wake, wait]
  | wake => [wait]

theorem changing_only_successor_order_can_invalidate :
    (∀ state, (cycleNext state).toFinset = (swappedNext state).toFinset) ∧
      checkLoop swappedNext .rotating 1 [wait, wake] = false := by decide

def edgesOnlyCheck {S : Type*} [DecidableEq S] (next : S → List S)
    (mode : Mode) (start : Nat) (path : List S) : Bool :=
  if empty : path.length = 0 then false else
    (List.finRange path.length).all fun index =>
      decide (step next mode.schedule (start + index.val) (some (path.get index)) =
        some (cyclicAt path (Nat.pos_of_ne_zero empty) (index.val + 1)))

theorem edge_only_mutant_accepts_a_finite_run :
    edgesOnlyCheck waitNext .rotating 0 [wait] = true ∧
      checkLoop waitNext .rotating 0 [wait] = false ∧ EndsAt waitNext rotating wait 2 :=
  ⟨by decide, by decide, wake, by decide, rfl⟩

theorem checked_certificate_proves_actual_liveness :
    Nonterminating cycleNext rotating wait ∧ PeriodicFrom cycleNext rotating wait 1 2 :=
  checkLoop_sound_of_entry cycleNext .rotating wait 1 [wait, wake] local_cycle_accepted (by decide)

def forkNext (arity : Nat) : Nat → List Nat
  | 0 => 1 :: (List.range (arity - 1)).map (fun n => n + 3)
  | 1 => [1, 2]
  | 2 => [1]
  | _ => []

theorem fork_tail_agrees (first second : Nat) :
    ∀ state ∈ ([1, 2] : List Nat), forkNext first state = forkNext second state := by
  intro state member
  rcases List.mem_cons.mp member with rfl | later
  · rfl
  · have same := List.mem_singleton.mp later
    subst state
    rfl

theorem fork_local_certificate (arity : Nat) : checkLoop (forkNext arity) .rotating 1 [1, 2] = true := by
  have same := checkLoop_congr_next (forkNext 1) (forkNext arity) .rotating 1 [1, 2] (fork_tail_agrees 1 arity)
  rw [← same]
  decide

theorem fork_entry (arity : Nat) : run (forkNext arity) rotating 0 1 = some 1 := by
  simp [run, step, forkNext, rotating]

theorem fork_tail_infinite (arity : Nat) : Nonterminating (forkNext arity) rotating 0 ∧
    PeriodicFrom (forkNext arity) rotating 0 1 2 :=
  checkLoop_sound_of_entry (forkNext arity) .rotating 0 1 [1, 2] (fork_local_certificate arity) (fork_entry arity)

theorem valid_loop_still_needs_the_actual_entry :
    checkLoop (forkNext 7) .rotating 1 [1, 2] = true ∧ ¬ Nonterminating (forkNext 7) rotating 3 :=
  ⟨fork_local_certificate 7,
    ended_not_nonterminating (forkNext 7) rotating 3 (turn := 0) ⟨3, rfl, rfl⟩⟩

def firstGlobalClaim (arity horizon : Nat) : Option Nat :=
  (List.range horizon).find? (claimsAt (forkNext arity) .rotating (run (forkNext arity) rotating 0))

theorem firstGlobalClaim_sound (arity horizon turn : Nat)
    (reported : firstGlobalClaim arity horizon = some turn) : Nonterminating (forkNext arity) rotating 0 :=
  claimsAt_sound (forkNext arity) .rotating 0 turn (List.find?_some reported)

theorem transient_arity_delays_the_global_monitor :
    firstGlobalClaim 7 20 = some 16 ∧ checkLoop (forkNext 7) .rotating 1 [1, 2] = true ∧
      4 * 3 ≤ 16 := by decide

def delayRow (arity : Nat) : Nat × Option Nat × Bool :=
  (arity, firstGlobalClaim arity (2 * arity + 4), checkLoop (forkNext arity) .rotating 1 [1, 2])

end Mettapedia.Machines.ScheduledRun.Controls
