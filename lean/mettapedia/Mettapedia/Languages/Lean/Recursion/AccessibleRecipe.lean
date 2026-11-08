import Mettapedia.Algorithms.WellFoundedServices.InertRecursor

/-!
# Exported measure recipes through Flower's accessible recursor

The implementation is the existing accessibility-code recursor, realized by
`Acc.rec`. Lean's optimized `WellFounded.Nat.fix` is compared with it using
the two unfolding equations and accessibility induction. The exported
functional and measure are inputs; the source function is not used to define
the accessible interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.Recursion.AccessibleRecipe

open Mettapedia.Order Mettapedia.Algorithms.WellFoundedServices

universe u v
variable {α : Sort u} {C : α → Sort v}

noncomputable def evaluateRelation (relation : α → α → Prop) (founded : WellFounded relation)
    (recipe : ∀ x, (∀ y, relation y x → C y) → C x) (x : α) : C x :=
  (InertRecursor.ofAcc relation).recursor recipe x (accCode_of_wellFounded founded x)

theorem function_equals_fix (relation : α → α → Prop) (founded : WellFounded relation)
    (recipe : ∀ x, (∀ y, relation y x → C y) → C x) :
    evaluateRelation relation founded recipe = founded.fix recipe := by
  funext x
  exact (InertRecursor.ofAcc relation).rec_eq_of_fix recipe (founded.fix recipe)
    (fun x => founded.fix_eq recipe x) (accCode_of_wellFounded founded x)

theorem measure_wellFounded (measure : α → Nat) :
    WellFounded (fun y x => measure y < measure x) :=
  InvImage.wf measure Nat.lt_wfRel.wf

noncomputable def evaluate (measure : α → Nat)
    (recipe : ∀ x, (∀ y, measure y < measure x → C y) → C x) (x : α) : C x :=
  (InertRecursor.ofAcc (fun y x => measure y < measure x)).recursor
    recipe x (accCode_measure measure x)

theorem unfold (measure : α → Nat)
    (recipe : ∀ x, (∀ y, measure y < measure x → C y) → C x) (x : α) :
    evaluate measure recipe x = recipe x (fun y _ => evaluate measure recipe y) := by
  unfold evaluate
  rw [InertRecursor.unfold]

theorem equals_natFix (measure : α → Nat)
    (recipe : ∀ x, (∀ y, measure y < measure x → C y) → C x) (x : α) :
    evaluate measure recipe x = WellFounded.Nat.fix measure recipe x := by
  exact (InertRecursor.ofAcc (fun y x => measure y < measure x)).rec_eq_of_fix
    recipe (WellFounded.Nat.fix measure recipe)
    (fun x => WellFounded.Nat.fix_eq measure recipe x) (accCode_measure measure x)

theorem function_equals_natFix (measure : α → Nat)
    (recipe : ∀ x, (∀ y, measure y < measure x → C y) → C x) :
    evaluate measure recipe = WellFounded.Nat.fix measure recipe := by
  funext x
  exact equals_natFix measure recipe x

/-- Equations supplied by an actual source declaration determine the same
function. Applications must supply their own checked unfolding proof. -/
theorem equals_of_equations (measure : α → Nat)
    (recipe : ∀ x, (∀ y, measure y < measure x → C y) → C x)
    (function : ∀ x, C x)
    (equations : ∀ x, function x = recipe x (fun y _ => function y)) (x : α) :
    evaluate measure recipe x = function x :=
  (InertRecursor.ofAcc (fun y x => measure y < measure x)).rec_eq_of_fix
    recipe function equations (accCode_measure measure x)

end Mettapedia.Languages.Lean.Recursion.AccessibleRecipe
