import Mathlib.Tactic

/-!
# Deep stored terms: decoding by recursion, interning by structural comparison

A stored term is decoded into an atom by decoding its children first.
Decoding by recursion takes one machine frame per level of the term, so for
any fixed stack some depth overflows it.  Decoding children first from an
explicit stack in the heap takes one frame for any depth.

A hash-consing table compares a new expression with the entries its probe
meets.  Comparing two chains `s (s (… z))` structurally walks both down to
the shorter one's depth.  Interning a chain level by level, each level
compared with the one below, costs a quadratic number of steps.  Comparing
cached hashes first decides most of these comparisons in one step, and
interning then costs a linear number.

This file proves:
* `recFrames_chain`: decoding `chain n` by recursion takes `n + 1` frames;
* `recFrames_exceeds`: for every stack bound some chain overflows it;
* `loopDecode_eq_recDecode`: on chains, decoding by a loop with one frame
  gives the recursive decoder's result;
* `cmpSteps_chain`: comparing `chain i` with `chain j` takes `min i j + 1`
  steps;
* `internSteps_eq`, `hashedSteps_eq`: interning `chain 0, …, chain n`, each
  compared with the one below, takes `n * (n + 1) / 2` structural steps
  against `n` hash comparisons.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.DeepTermCost

/-- A term with a leaf and a unary constructor, enough for chains. -/
inductive Tm
  | z
  | s (t : Tm)
  deriving DecidableEq

/-- `chain n` is `s` applied `n` times to `z`. -/
def chain : Nat → Tm
  | 0 => .z
  | n + 1 => .s (chain n)

/-- The decoded form of a term: here, its number of `s` levels. -/
def recDecode : Tm → Nat
  | .z => 0
  | .s t => recDecode t + 1

/-- The machine frames a recursive decoder holds at its deepest point. -/
def recFrames : Tm → Nat
  | .z => 1
  | .s t => recFrames t + 1

theorem recFrames_chain (n : Nat) : recFrames (chain n) = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [chain, recFrames, ih]

/-- No fixed stack holds every chain's recursive decode. -/
theorem recFrames_exceeds (bound : Nat) : bound < recFrames (chain bound) := by
  rw [recFrames_chain]; omega

/-- Decoding by a loop: an accumulator and the remaining term, one frame. -/
def loopDecode : Tm → Nat → Nat
  | .z, acc => acc
  | .s t, acc => loopDecode t (acc + 1)

theorem loopDecode_acc (t : Tm) (acc : Nat) :
    loopDecode t acc = recDecode t + acc := by
  induction t generalizing acc with
  | z => simp [loopDecode, recDecode]
  | s t ih => simp only [loopDecode, recDecode, ih]; omega

/-- The loop gives the recursive decoder's result. -/
theorem loopDecode_eq_recDecode (t : Tm) : loopDecode t 0 = recDecode t := by
  simp [loopDecode_acc]

/-- The steps a structural comparison takes: one per level visited, until
the two terms differ or both end. -/
def cmpSteps : Tm → Tm → Nat
  | .s a, .s b => cmpSteps a b + 1
  | _, _ => 1

theorem cmpSteps_chain (i j : Nat) : cmpSteps (chain i) (chain j) = min i j + 1 := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => rfl
    | succ j => simp [chain, cmpSteps]
  | succ i ih =>
    cases j with
    | zero => simp [chain, cmpSteps]
    | succ j => simp [chain, cmpSteps, ih]

/-- Interning `chain 1, …, chain n`, each new level compared structurally
with the level below it, which its probe meets. -/
def internSteps (n : Nat) : Nat :=
  ∑ i ∈ Finset.range n, cmpSteps (chain (i + 1)) (chain i)

/-- Interning the same levels with the cached hashes compared first: the
hashes of different levels differ, so each comparison takes one step. -/
def hashedSteps (n : Nat) : Nat := ∑ _i ∈ Finset.range n, 1

theorem internSteps_eq (n : Nat) : 2 * internSteps n = n * (n + 1) := by
  induction n with
  | zero => simp [internSteps]
  | succ n ih =>
    simp only [internSteps, Finset.sum_range_succ] at ih ⊢
    rw [cmpSteps_chain, Nat.min_eq_right (Nat.le_succ n)]
    rw [Nat.mul_add, ih]
    ring

theorem hashedSteps_eq (n : Nat) : hashedSteps n = n := by
  simp [hashedSteps]

/-- The structural cost overtakes the hashed one by a factor that grows with
the depth: `(n + 1) / 2`. -/
theorem internSteps_vs_hashed (n : Nat) :
    2 * internSteps n = (n + 1) * hashedSteps n := by
  rw [internSteps_eq, hashedSteps_eq]; ring

end Mettapedia.Machines.DeepTermCost
