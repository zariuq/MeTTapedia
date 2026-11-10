import Mettapedia.Languages.Lean.Recursion.AccessibleRecipe

/-!
# Structural fuel for exported measure recipes

The finite evaluator consumes the exported recipe, not the source function.
Its zero-fuel seed is arbitrary. A bound derived from the recipe's measure
proves that the seed is never observed, and identifies the result with the
accessible interpretation. Without that bound a fuel result is unqualified.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.Recursion.AccessibleRecipe

universe u v
variable {α : Sort u} {C : α → Sort v}

/-- A structurally recursive evaluation of the same decreasing-call recipe. -/
def fuel (measure : α → Nat)
    (recipe : ∀ x, (∀ y, measure y < measure x → C y) → C x)
    (seed : ∀ x, C x) : Nat → ∀ x, C x
  | 0, x => seed x
  | k + 1, x => recipe x (fun y _ => fuel measure recipe seed k y)

/-- Sufficient fuel computes the accessible interpretation for every input. -/
theorem fuel_eq_evaluate (measure : α → Nat)
    (recipe : ∀ x, (∀ y, measure y < measure x → C y) → C x)
    (seed : ∀ x, C x) (k : Nat) (x : α) (bound : measure x < k) :
    fuel measure recipe seed k x = evaluate measure recipe x := by
  induction k generalizing x with
  | zero => exact False.elim (Nat.not_lt_zero _ bound)
  | succ k ih =>
      rw [fuel, unfold]
      apply congrArg (recipe x)
      funext y decrease
      exact ih y (Nat.lt_of_lt_of_le decrease (Nat.le_of_lt_succ bound))

/-- Above the measure, neither extra fuel nor a different seed changes the answer. -/
theorem fuel_stable (measure : α → Nat)
    (recipe : ∀ x, (∀ y, measure y < measure x → C y) → C x)
    (firstSeed secondSeed : ∀ x, C x) (k l : Nat) (x : α)
    (firstBound : measure x < k) (secondBound : measure x < l) :
    fuel measure recipe firstSeed k x = fuel measure recipe secondSeed l x :=
  (fuel_eq_evaluate measure recipe firstSeed k x firstBound).trans
    (fuel_eq_evaluate measure recipe secondSeed l x secondBound).symm

/-- A source's checked unfolding equations connect its value to structural fuel. -/
theorem fuel_eq_of_equations (measure : α → Nat)
    (recipe : ∀ x, (∀ y, measure y < measure x → C y) → C x)
    (seed function : ∀ x, C x)
    (equations : ∀ x, function x = recipe x (fun y _ => function y))
    (k : Nat) (x : α) (bound : measure x < k) :
    fuel measure recipe seed k x = function x :=
  (fuel_eq_evaluate measure recipe seed k x bound).trans
    (equals_of_equations measure recipe function equations x)

namespace FuelControls

def countRecipe : ∀ n : Nat, (∀ m, m < n → Nat) → Nat
  | 0, _ => 0
  | n + 1, previous => previous n (Nat.lt_succ_self n) + 1

theorem countRecipe_unfold (n : Nat) :
    n = countRecipe n (fun m _ => m) := by
  cases n <;> rfl

theorem count_fuel (n k : Nat) (bound : n < k) :
    fuel id countRecipe (fun _ => 0) k n = n :=
  fuel_eq_of_equations id countRecipe (fun _ => 0) id countRecipe_unfold k n bound

example : fuel id countRecipe (fun _ => 0) 4 3 = 3 := by decide

/-- One step on input three observes the seed and does not compute the source. -/
example : fuel id countRecipe (fun _ => 0) 1 3 ≠ 3 := by decide

example : fuel id countRecipe (fun _ => 0) 4 3 =
    fuel id countRecipe (fun _ => 99) 8 3 :=
  fuel_stable id countRecipe (fun _ => 0) (fun _ => 99) 4 8 3 (by decide) (by decide)

end FuelControls
end Mettapedia.Languages.Lean.Recursion.AccessibleRecipe
