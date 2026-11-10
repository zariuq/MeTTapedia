import Mettapedia.Languages.Lean.Recursion.AccessibleRecipe

/-!
# Fuel for a recipe with a general well-founded relation

A natural rank need only decrease on the calls the recipe actually observes.
It need not rank every pair in the source relation (for example, a
lexicographic relation). Locality states exactly that observational condition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.Recursion.RelationFuel

universe u v
variable {α : Sort u} {C : α → Sort v}

def fuel (relation : α → α → Prop)
    (recipe : ∀ x, (∀ y, relation y x → C y) → C x)
    (seed : ∀ x, C x) : Nat → ∀ x, C x
  | 0, x => seed x
  | k + 1, x => recipe x (fun y _ => fuel relation recipe seed k y)

/-- Agreement at smaller ranks suffices for one execution of the recipe. -/
def Local (relation : α → α → Prop) (rank : α → Nat)
    (recipe : ∀ x, (∀ y, relation y x → C y) → C x) : Prop :=
  ∀ x (first second : ∀ y, C y),
    (∀ y, rank y < rank x → first y = second y) →
    recipe x (fun y _ => first y) = recipe x (fun y _ => second y)

theorem fuel_eq_of_equations (relation : α → α → Prop) (rank : α → Nat)
    (recipe : ∀ x, (∀ y, relation y x → C y) → C x)
    (locality : Local relation rank recipe) (seed function : ∀ x, C x)
    (equations : ∀ x, function x = recipe x (fun y _ => function y))
    (k : Nat) (x : α) (bound : rank x < k) :
    fuel relation recipe seed k x = function x := by
  induction k generalizing x with
  | zero => exact False.elim (Nat.not_lt_zero _ bound)
  | succ k ih =>
      rw [fuel, equations x]
      apply locality x
      intro y decrease
      exact ih y (Nat.lt_of_lt_of_le decrease (Nat.le_of_lt_succ bound))

theorem fuel_eq_evaluate (relation : α → α → Prop) (founded : WellFounded relation)
    (rank : α → Nat) (recipe : ∀ x, (∀ y, relation y x → C y) → C x)
    (locality : Local relation rank recipe) (seed : ∀ x, C x)
    (k : Nat) (x : α) (bound : rank x < k) :
    fuel relation recipe seed k x = AccessibleRecipe.evaluateRelation relation founded recipe x := by
  apply fuel_eq_of_equations relation rank recipe locality seed
    (AccessibleRecipe.evaluateRelation relation founded recipe)
  · intro y
    unfold AccessibleRecipe.evaluateRelation
    rw [Mettapedia.Algorithms.WellFoundedServices.InertRecursor.unfold]
  · exact bound

theorem fuel_stable (relation : α → α → Prop) (founded : WellFounded relation)
    (rank : α → Nat) (recipe : ∀ x, (∀ y, relation y x → C y) → C x)
    (locality : Local relation rank recipe) (firstSeed secondSeed : ∀ x, C x)
    (k l : Nat) (x : α) (firstBound : rank x < k) (secondBound : rank x < l) :
    fuel relation recipe firstSeed k x = fuel relation recipe secondSeed l x :=
  (fuel_eq_evaluate relation founded rank recipe locality firstSeed k x firstBound).trans
    (fuel_eq_evaluate relation founded rank recipe locality secondSeed l x secondBound).symm

end Mettapedia.Languages.Lean.Recursion.RelationFuel
