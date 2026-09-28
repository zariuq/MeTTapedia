import Mettapedia.GSLT.Dynamics.GuardedWork
import Mettapedia.Machines.Cursor.Scheduling
import Mettapedia.Machines.Cursor.Fold

/-!
# Guarded dispatch of an existing cursor

This is the concrete connection between `where` and retained computation.
Only acceptance advances the cursor. Rejection and waiting return the entire
unchanged cursor, including its previous operation account. A caller can keep,
retire, or recheck that work according to its authored policy; rejection does
not secretly delete an agenda entry.

The returned receipt charges this guard check and newly performed provider
operations. The cursor's cumulative account continues to measure provider
operations alone. The accounting law relates the two without refunding earlier
work or counting it twice. Guard cost is not confused with the inspection
quantum, and may be greater than the cost of the admitted work.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.GuardedCursor

open Mettapedia.TypeTheory
open Mettapedia.Machines.Cursor
open GuardedWork

universe u v
variable {Base : Type u} {Index : Base → Type u}
variable {P : IndexedPolynomial.{u,u,u,u} Base Index}
variable {Return : (base : Base) → Index base → Type u}
variable (provider : Provider P) (client : Client (P := P) (Return := Return))
variable (charge : Charge provider)
variable {base : Base} {eligible : Prop} {Dependency : Type v}

/-- `Unit` is the guard action's acknowledgment; all actual results, effects,
and residuals remain inside the original cursor outcome. -/
def dispatch (probe : Nat × Decision eligible Dependency) (quantum : Nat)
    (previous : Scheduling.Cell provider client base) :
    Nat × (Result Unit Dependency × Scheduling.Cell provider client base) :=
  attempt probe (fun _ old =>
    let next := resume provider client charge quantum old
    (next.1 - old.1, ((), next))) previous

theorem accepted_resumes_exactly (guardCost : Nat) (proof : eligible)
    (quantum : Nat) (previous : Scheduling.Cell provider client base) :
    (dispatch provider client charge (Dependency := Dependency)
      (guardCost, .accept proof) quantum previous).2.2 =
      resume provider client charge quantum previous := rfl

/-- Waiting retains the live provider and pending client, not a replay recipe. -/
theorem waiting_retains_exactly (guardCost : Nat) (dependency : Dependency)
    (quantum : Nat) (previous : Scheduling.Cell provider client base) :
    dispatch provider client charge (eligible := eligible)
      (guardCost, .defer dependency) quantum previous =
      (guardCost, (.waiting dependency, previous)) := rfl

theorem rejected_retains_exactly (guardCost : Nat) (no : ¬ eligible)
    (quantum : Nat) (previous : Scheduling.Cell provider client base) :
    dispatch provider client charge (Dependency := Dependency)
      (guardCost, .reject no) quantum previous =
      (guardCost, (.rejected, previous)) := rfl

/-- Previous provider work plus this dispatch's receipt equals guard work plus
the resumed provider account. Truncated subtraction cannot hide a refund. -/
theorem accepted_total_accounting (guardCost : Nat) (proof : eligible)
    (quantum : Nat) (previous : Scheduling.Cell provider client base) :
    previous.1 +
      (dispatch provider client charge (Dependency := Dependency)
        (guardCost, .accept proof) quantum previous).1 =
      guardCost + (resume provider client charge quantum previous).1 := by
  have monotone := Scheduling.resume_charge_monotone provider client charge quantum previous
  change previous.1 + (guardCost +
    ((resume provider client charge quantum previous).1 - previous.1)) = _
  omega

/-- Deferring and later accepting costs both checks. Acceptance resumes from
the same retained cursor, without replaying its earlier provider work. -/
theorem defer_then_accept_accounting (waitCost acceptCost : Nat)
    (dependency : Dependency) (proof : eligible) (firstQuantum nextQuantum : Nat)
    (previous : Scheduling.Cell provider client base) :
    let waiting := dispatch provider client charge (eligible := eligible)
      (waitCost, .defer dependency) firstQuantum previous
    let accepted := dispatch provider client charge (Dependency := Dependency)
      (acceptCost, .accept proof) nextQuantum waiting.2.2
    previous.1 + waiting.1 + accepted.1 =
      waitCost + acceptCost + (resume provider client charge nextQuantum previous).1 := by
  dsimp only
  rw [waiting_retains_exactly]
  have accounting := accepted_total_accounting provider client charge
    (Dependency := Dependency) acceptCost proof nextQuantum previous
  dsimp only at *
  omega

namespace Controls

def delivered : Scheduling.Cell (Sequence.tails Nat) (Fold.client (· + ·)) () :=
  advance (Sequence.tails Nat) (Fold.client (· + ·)) (fun _ _ => 1) 2
    (Fold.start _ (· + ·) [3, 3, 5] 0)

theorem waiting_after_delivery_keeps_accumulator :
    dispatch (Sequence.tails Nat) (Fold.client (· + ·)) (fun _ _ => 1)
      (eligible := 1 < 2) (100, .defer "input-ready") 50 delivered =
      (100, (.waiting "input-ready",
        (2, .paused (Fold.start _ (· + ·) [5] 6)))) := rfl

theorem accepted_work_can_be_cheaper_than_its_guard :
    (dispatch (Sequence.tails Nat) (Fold.client (· + ·)) (fun _ _ => 1)
      (Dependency := String) (100, .accept (by decide : 1 < 2)) 3 delivered).1 = 102 := rfl

end Controls

#print axioms accepted_resumes_exactly
#print axioms accepted_total_accounting
#print axioms defer_then_accept_accounting

end Mettapedia.GSLT.Dynamics.GuardedCursor
