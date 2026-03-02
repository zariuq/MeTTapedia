import Mathlib.Data.Bool.Basic

/-!
# Trail-Free Protocol Dynamics Counterexample

This file gives a minimal Chapter-9-style counterexample for trail-free iteration:
an inference protocol can be perfectly deterministic and still fail to stabilize.

We model a protocol on a two-state TV space (`Bool`) by a single update step
that flips the state each iteration.
-/

namespace Mettapedia.Logic.PLNTrailFreeDynamicsCounterexample

abbrev TVState := Bool

/-- A concrete trail-free protocol step: toggle the current TV state. -/
def trailFreeStep : TVState → TVState
  | true => false
  | false => true

/-- Protocol orbit starting from `x0`. -/
def orbit (x0 : TVState) : Nat → TVState
  | 0 => x0
  | n + 1 => trailFreeStep (orbit x0 n)

/-- Positive example: two steps return to the same state. -/
theorem trailFreeStep_involutive (x : TVState) :
    trailFreeStep (trailFreeStep x) = x := by
  cases x <;> rfl

/-- Negative example: there is no fixed point for this update step. -/
theorem trailFreeStep_ne_self (x : TVState) :
    trailFreeStep x ≠ x := by
  cases x <;> decide

/-- Orbit has exact period 2. -/
theorem orbit_period_two (x0 : TVState) :
    ∀ n : Nat, orbit x0 (n + 2) = orbit x0 n
  | 0 => by
      simp [orbit, trailFreeStep_involutive]
  | n + 1 => by
      simpa [Nat.add_assoc, orbit] using congrArg trailFreeStep (orbit_period_two x0 n)

example : orbit true 0 = true := rfl
example : orbit true 1 = false := rfl
example : orbit true 2 = true := by simp [orbit, trailFreeStep]

/-- Eventual stabilization notion for protocol orbits. -/
def EventuallyConstant (x0 : TVState) : Prop :=
  ∃ N y, ∀ n, N ≤ n → orbit x0 n = y

/-- Counterexample: trail-free iteration need not stabilize. -/
theorem orbit_not_eventually_constant (x0 : TVState) :
    ¬ EventuallyConstant x0 := by
  rintro ⟨N, y, hConst⟩
  have hN : orbit x0 N = y := hConst N (Nat.le_refl N)
  have hN1 : orbit x0 (N + 1) = y := hConst (N + 1) (Nat.le_succ N)
  have hFix : trailFreeStep y = y := by
    calc
      trailFreeStep y = trailFreeStep (orbit x0 N) := by simp [hN]
      _ = orbit x0 (N + 1) := by simp [orbit]
      _ = y := hN1
  exact trailFreeStep_ne_self y hFix

end Mettapedia.Logic.PLNTrailFreeDynamicsCounterexample
