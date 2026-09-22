import Mathlib

/-!
# Prefix distribution blows up; reflection does not

Eliminating the input prefix without reflection forces the prefix to be pushed
through its body: the elimination splits at every parallel composition and
delays every atom behind its own synchroniser, so each prefix multiplies the
body.  Down a chain of nested inputs a constant-factor expansion composes
multiplicatively.

Reflection removes the multiplication.  A continuation can be quoted once and
released by a fixed-size gate, so each prefix contributes a constant.

On the family of nested inputs whose bound names do not occur, the two counts
are the functions below.  `distributedAtoms` satisfies the recurrence the
prefix-distribution rules give, with closed form `(3 ^ n + 1) / 2`, stated here
without division as `two_mul_distributedAtoms`.  `reflectiveAtoms` is linear.

`reflective_lt_distributed` is the separation past the crossover, and
`no_separation_below_crossover` records that the crossover is real: below it the
distributed count is the smaller one, so the result is asymptotic and is not a
claim about every depth.

## Scope

These are theorems about the two counting functions, not lower bounds over all
encodings.  They say what the stated rules give on the stated family; a claim
that no elimination without reflection can do better would be a different
statement and is not made here.

## References

- N. Yoshida, *Minimality and separation results on asynchronous mobile
  processes*, TCS 274(1–2):231–276, 2002, whose elimination rules give the
  recurrence.
- F1R3FLY.io research note, *Name-Free Combinators for the Rho Calculus*,
  draft 3, 2026.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

/-- Atoms produced by prefix distribution on the family of nested inputs whose
bound names do not occur, indexed so that `n` is one less than the nesting
depth.  Each prefix inserts a duplicator along a binary tree over the body and
replaces every atom by a synchroniser and a relabelled copy. -/
def distributedAtoms : ℕ → ℕ
  | 0 => 1
  | n + 1 => 3 * distributedAtoms n - 1

/-- Atoms produced by the reflective encoding on the same family: each prefix
contributes an empty distributor and one gate. -/
def reflectiveAtoms (n : ℕ) : ℕ := 3 * (n + 1) + 1

theorem distributedAtoms_pos (n : ℕ) : 0 < distributedAtoms n := by
  induction n with
  | zero => simp [distributedAtoms]
  | succ n ih => simp only [distributedAtoms]; omega

/-- Closed form for the distributed count, stated without division. -/
theorem two_mul_distributedAtoms (n : ℕ) :
    2 * distributedAtoms n = 3 ^ n + 1 := by
  induction n with
  | zero => simp [distributedAtoms]
  | succ n ih =>
      have pos := distributedAtoms_pos n
      simp only [distributedAtoms, pow_succ]
      omega

/-- The distributed count grows exponentially in the nesting depth. -/
theorem distributedAtoms_ge (n : ℕ) : 3 ^ n < 2 * distributedAtoms n := by
  rw [two_mul_distributedAtoms]; omega

/-- Exponential dominance past the crossover, as a standalone bound. -/
theorem linear_lt_pow (m : ℕ) : 6 * (m + 3) + 7 < 3 ^ (m + 3) := by
  induction m with
  | zero => norm_num
  | succ k ih =>
      have expand : (3 : ℕ) ^ (k + 3 + 1) = 3 * 3 ^ (k + 3) := by ring
      rw [expand]
      omega

/-- **The separation.**  Past the crossover the reflective encoding is
strictly smaller, and the gap is exponential: the distributed count is
`(3 ^ n + 1) / 2` while the reflective count is linear in `n`. -/
theorem reflective_lt_distributed {n : ℕ} (h : 3 ≤ n) :
    reflectiveAtoms n < distributedAtoms n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have closed := two_mul_distributedAtoms (m + 3)
  have bound := linear_lt_pow m
  simp only [reflectiveAtoms]
  omega

/-- Honest boundary: below the crossover the reflective encoding is not
smaller, so the separation is asymptotic and the threshold is real. -/
theorem no_separation_below_crossover :
    distributedAtoms 2 < reflectiveAtoms 2 := by
  simp [distributedAtoms, reflectiveAtoms]

end Mettapedia.Languages.ProcessCalculi.RhoCombinators

#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.two_mul_distributedAtoms
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.distributedAtoms_ge
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.reflective_lt_distributed
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.no_separation_below_crossover
