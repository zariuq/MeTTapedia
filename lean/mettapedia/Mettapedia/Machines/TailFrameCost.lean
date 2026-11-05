import Mathlib.Tactic

/-!
# Tail frames: work per step bounded once a tail step leaves nothing pending

Two findings of the adversarial audit had one cause.  A right-nested
generator, `(range a b) = (superpose (a (range (+ a 1) b)))`, handed each of
its `n` answers back through every alternative still pending above it:
32,000 answers took 1.81 s, exponent 2.11.  A recursive loop of `remove-atom`
calls kept each iteration's choice bindings, and every collection walked all
of them: 64k to 512k calls took 0.1 to 1.17 s.  In both, the work of step `i`
is the state pending at step `i`, and that state grew with `i`.  Once a step
in tail position leaves nothing pending (an answer goes to the enclosing
continuation; an iteration's bindings go with it), the pending state stays
within a constant and the total is linear.

The model: a run of `n` steps, each paying the state pending when it runs,
plus its own unit.  What the steps answer does not enter the model; the
scaling gate (`check_generator_loop_scaling.py`) checks that the generator
still answers 0 to N - 1, each once.  This file proves:
* `pending_total`: when each step leaves its frame pending, the run pays
  `n * (n + 1) / 2` in all (`n (n + 1) / 2` frames walked);
* `tail_total_le`: when no step leaves more than `c` pending, the run pays at
  most `(c + 1) * n`;
* `pending_exceeds_tail`: past `n = 2 c + 2`, the pending run pays more than
  any tail run with `c`, and the gap grows with `n`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TailFrameCost

/-- A run where step `i` finds `pending i` frames waiting and walks them, then
pays one for itself. -/
def cost (pending : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((List.range n).map (fun i => pending i + 1)).sum

/-- Each step leaves its frame: step `i` finds `i` waiting. -/
def leaves (i : ℕ) : ℕ := i

theorem cost_succ (pending : ℕ → ℕ) (n : ℕ) :
    cost pending (n + 1) = cost pending n + (pending n + 1) := by
  simp [cost, List.range_succ]

theorem pending_total (n : ℕ) : 2 * cost leaves n = n * (n + 1) := by
  induction n with
  | zero => simp [cost]
  | succ n ih =>
    rw [cost_succ, mul_add, ih]
    simp only [leaves]
    ring

/-- No step finds more than `c` waiting. -/
theorem tail_total_le (pending : ℕ → ℕ) (c n : ℕ) (h : ∀ i, pending i ≤ c) :
    cost pending n ≤ (c + 1) * n := by
  induction n with
  | zero => simp [cost]
  | succ n ih =>
    rw [cost_succ]
    have := h n
    nlinarith

theorem pending_exceeds_tail (pending : ℕ → ℕ) (c n : ℕ)
    (h : ∀ i, pending i ≤ c) (hn : 2 * c + 2 < n) :
    cost pending n < cost leaves n := by
  have hle := tail_total_le pending c n h
  have htot := pending_total n
  nlinarith

end Mettapedia.Machines.TailFrameCost
