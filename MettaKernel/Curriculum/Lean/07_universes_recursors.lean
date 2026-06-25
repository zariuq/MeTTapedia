/- Lean 07 — universes, explicit recursors, definitional conversion, well-founded
   recursion.  (MeTTaKernel curriculum, DTT ladder; vanilla Lean 4, no Mathlib.) -/
namespace L07

-- universe polymorphism: identity at any level
universe u v
def myId {α : Type u} (a : α) : α := a
theorem myId_eq {α : Type u} (a : α) : myId a = a := rfl

structure Pair (α : Type u) (β : Type v) where
  fst : α
  snd : β

-- EXPLICIT recursor: addition via Nat.rec, agreeing with + by computation
def addRec (m : Nat) : Nat → Nat := fun n => Nat.rec m (fun _ ih => ih + 1) n
theorem addRec_zero (m : Nat) : addRec m 0 = m := rfl
theorem addRec_succ (m n : Nat) : addRec m (n + 1) = addRec m n + 1 := rfl

-- definitional conversion: equal BY COMPUTATION (no rewriting), since x + 0 ≡ x
theorem conv_add_zero : (fun x : Nat => x + 0) = (fun x : Nat => x) := rfl

-- well-founded / non-structural recursion: log2 by repeated halving
def log2 (n : Nat) : Nat :=
  if h : n ≤ 1 then 0 else log2 (n / 2) + 1
termination_by n
decreasing_by omega

#eval log2 8   -- 3  (well-founded recursion computes via the compiler)
theorem log2_one : log2 1 = 0 := by simp [log2]

end L07
