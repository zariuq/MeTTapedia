/-!
# Fuel readings of well-founded recursion

Lean defines `Nat.gcd` by well-founded recursion: its equation
`gcd m n = if m = 0 then n else gcd (n % m) m` has no constructor pattern to
recur on. The same function, given a fuel argument above its measure, is
structurally recursive on the fuel, and Lean proves the two equal. The
export reads `F.eq_fuel`, when it exists, as the definition of `F`: a
non-recursive equation into the fuelled function, proved here, so the
reading of `F` rests on Lean theorems only.
-/

/-- `Nat.gcd` with a fuel argument: structural on the fuel. Out of fuel, the
value is the second argument. -/
def Nat.gcdFuel : Nat → Nat → Nat → Nat
  | Nat.zero, _, n => n
  | Nat.succ k, m, n => if m = 0 then n else Nat.gcdFuel k (n % m) m

/-- Any fuel above the first argument computes `Nat.gcd`. -/
theorem Nat.gcdFuel_eq (k m n : Nat) (h : m < k) : Nat.gcd m n = Nat.gcdFuel k m n := by
  induction k generalizing m n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ k ih =>
    rw [Nat.gcdFuel]
    by_cases hm : m = 0
    · subst hm
      simp [Nat.gcd_zero_left]
    · rw [if_neg hm, Nat.gcd_rec m n]
      apply ih
      have := Nat.mod_lt n (Nat.pos_of_ne_zero hm)
      omega

theorem Nat.gcd.eq_fuel (m n : Nat) : Nat.gcd m n = Nat.gcdFuel (Nat.succ m) m n :=
  Nat.gcdFuel_eq (Nat.succ m) m n (Nat.lt_succ_self m)

/-! Positive and negative examples. -/

example : Nat.gcdFuel 1072 1071 462 = 21 := by decide

example : Nat.gcdFuel 1 1071 462 ≠ 21 := by decide
