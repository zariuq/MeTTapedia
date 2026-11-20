import Mettapedia.Machines.ScheduledRun.LocalDetection
import Mettapedia.Machines.ScheduledRun.CertificateControls

/-!
# Automatic local certificates on transient-heavy scheduled runs

The certificate is extracted from the actual observed interval, not supplied
by an oracle. The control compares logical first-report turns and does not
assert native timing, allocation or candidate-search complexity.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScheduledRun.Controls

theorem automatic_local_fork_report :
    localClaimAt (forkNext 7) .rotating (run (forkNext 7) rotating 0) 3 = true := by decide

def firstLocalClaim (arity horizon : Nat) : Option Nat :=
  (List.range horizon).find? (localClaimAt (forkNext arity) .rotating (run (forkNext arity) rotating 0))

theorem automatic_local_first_report : firstLocalClaim 7 20 = some 3 := by decide

theorem detection_delay_fourfold_control :
    firstGlobalClaim 7 20 = some 16 ∧
      localClaimAt (forkNext 7) .rotating (run (forkNext 7) rotating 0) 3 = true ∧
      4 * 3 ≤ 16 :=
  ⟨transient_arity_delays_the_global_monitor.1, automatic_local_fork_report, by decide⟩

theorem local_rejects_the_stale_interval :
    checkInterval staleNext .rotating (run staleNext rotating 1) 1 4 = false := by decide

theorem local_rejects_a_finite_wait (turn : Nat) :
    localClaimAt waitNext .rotating (run waitNext rotating State.wait) turn = false := by
  cases result : localClaimAt waitNext .rotating (run waitNext rotating State.wait) turn with
  | false => rfl
  | true => exact False.elim (rotating_revisit_not_infinite.2.2
      (localClaimAt_sound waitNext .rotating State.wait turn result))

def autoDelayRow (arity : Nat) : Nat × Option Nat × Option Nat × Bool :=
  (arity, firstGlobalClaim arity (2 * arity + 4), firstLocalClaim arity 8,
    checkLoop (forkNext arity) .rotating 1 [1, 2])

def measuredDelays : List (Nat × Option Nat × Option Nat × Bool) :=
  [7, 15, 31, 63].map autoDelayRow

end Mettapedia.Machines.ScheduledRun.Controls
