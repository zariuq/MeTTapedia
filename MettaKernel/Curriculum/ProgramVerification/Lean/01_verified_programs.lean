/- ============================================================================
   Program Verification / Lean — verified programs: functions proven correct,
   type-enforced invariants, and proof-carrying values.
   (MeTTaKernel curriculum, 4th pillar; vanilla Lean 4, no Mathlib.)
   Style after "Functional Programming in Lean".  Check: `lean verified_programs.lean`.
   ========================================================================== -/
namespace PVLean

-- a verified recursive function: list reverse, proven involutive
def rev {α : Type} : List α → List α
  | []      => []
  | x :: xs => rev xs ++ [x]

theorem rev_append {α} (xs ys : List α) : rev (xs ++ ys) = rev ys ++ rev xs := by
  induction xs with
  | nil => simp [rev]
  | cons x xs ih => simp [rev, ih, List.append_assoc]

theorem rev_rev {α} (xs : List α) : rev (rev xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [rev, rev_append, ih]

-- a verified invariant: append adds lengths
theorem length_append {α} (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.succ_add]

-- proof-carrying program: returns a value TOGETHER WITH a proof about it
def doublePos (n : Nat) : { m : Nat // m = 2 * n } := ⟨2 * n, rfl⟩
#eval (doublePos 5).val   -- 10

-- type-ENFORCED invariant: length-indexed vectors; `map` preserves the length n
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : {n : Nat} → α → Vec α n → Vec α (n + 1)

def Vec.map {α β : Type} {n : Nat} (f : α → β) : Vec α n → Vec β n
  | .nil       => .nil
  | .cons a v  => .cons (f a) (v.map f)

def v3 : Vec Nat 3 := .cons 1 (.cons 2 (.cons 3 .nil))
-- the result is STILL `Vec _ 3` — the length invariant is checked by the kernel
def v3' : Vec Nat 3 := v3.map (· + 10)

end PVLean
