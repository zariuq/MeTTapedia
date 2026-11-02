import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Nonnegative division by doubling the positive divisor and recovering
one quotient bit on return. Correctness uses quotient/remainder uniqueness.
-/

set_option autoImplicit false

namespace Mettapedia.Data.Nat.DoublingDivision

def run (number divisor : Nat) : Nat × Nat :=
  if _positive : 0 < divisor then
    if _small : number < divisor then (0, number)
    else
      let result := run number (divisor + divisor)
      if result.2 < divisor then (result.1 + result.1, result.2)
      else (result.1 + result.1 + 1, result.2 - divisor)
  else (0, number)
termination_by number / divisor
decreasing_by
  have bounded : divisor ≤ number := Nat.le_of_not_gt _small
  rw [show divisor + divisor = divisor * 2 by omega, ← Nat.div_div_eq_div_mul]
  exact Nat.div_lt_self (Nat.div_pos bounded _positive) (by decide)

theorem invariant (number divisor : Nat) (positive : 0 < divisor) :
    number = divisor * (run number divisor).1 + (run number divisor).2 ∧ (run number divisor).2 < divisor := by
  by_cases small : number < divisor
  · have stopped : run number divisor = (0, number) := by
      rw [run.eq_def]
      simp only [positive, small, dite_true]
    rw [stopped]
    exact ⟨by simp, small⟩
  · have growing : run number divisor =
        (let result := run number (divisor + divisor)
         if result.2 < divisor then (result.1 + result.1, result.2)
         else (result.1 + result.1 + 1, result.2 - divisor)) := by
      rw [run.eq_def]
      simp only [positive, small, dite_true, dite_false]
    rw [growing]
    dsimp only
    have ih := invariant number (divisor + divisor) (by omega)
    split
    · rename_i remainderSmall
      dsimp only
      constructor
      · nlinarith [ih.1]
      · exact remainderSmall
    · rename_i remainderLarge
      dsimp only
      have lower : divisor ≤ (run number (divisor + divisor)).2 := by omega
      constructor
      · nlinarith [ih.1, Nat.sub_add_cancel lower]
      · omega
termination_by number / divisor
decreasing_by
  rw [show divisor + divisor = divisor * 2 by omega, ← Nat.div_div_eq_div_mul]
  exact Nat.div_lt_self (Nat.div_pos (by omega) positive) (by decide)

theorem exact_result (number divisor : Nat) (positive : 0 < divisor) :
    run number divisor = (number / divisor, number % divisor) := by
  obtain ⟨equation, bounded⟩ := invariant number divisor positive
  have div : number / divisor = (run number divisor).1 := by
    conv_lhs => rw [equation]
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt bounded, Nat.zero_add]
  have mod : number % divisor = (run number divisor).2 := by
    conv_lhs => rw [equation]
    rw [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt bounded, Nat.mod_eq_of_lt bounded]
  exact Prod.ext div.symm mod.symm

example : run 27 4 = (6, 3) := by decide +kernel
example : run 0 4 = (0, 0) := by decide +kernel
example : run 15 16 = (0, 15) := by decide +kernel

#print axioms invariant
#print axioms exact_result

end Mettapedia.Data.Nat.DoublingDivision
