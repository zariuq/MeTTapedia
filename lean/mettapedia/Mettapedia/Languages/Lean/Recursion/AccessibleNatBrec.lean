import Mettapedia.Languages.Lean.Recursion.AccessibleRecipe

/-!
# Natural-number course-of-values recursion through accessibility

The below table is reconstructed from the lower-value capability. This gives
an independent accessible interpretation of Lean's compiled `Nat.brecOn`,
including motives whose results accept invariant proofs. Equality is proved
by the source recursor's equation and accessibility uniqueness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.Recursion.AccessibleNatBrec

universe u
variable {C : Nat → Sort u}

def below (n : Nat) (previous : ∀ m, m < n → C m) : @Nat.below C n :=
  match n with
  | 0 => PUnit.unit
  | n + 1 => ⟨previous n (Nat.lt_succ_self n),
      below n (fun m h => previous m (Nat.lt_trans h (Nat.lt_succ_self n)))⟩

theorem below_brecOn (step : ∀ n, @Nat.below C n → C n) (n : Nat) :
    below n (fun m _ => Nat.brecOn m step) = (Nat.brecOn.go n step).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (⟨Nat.brecOn n step, below n (fun m _ => Nat.brecOn m step)⟩ : @Nat.below C (n + 1)) = _
      rw [ih]

def recipe (step : ∀ n, @Nat.below C n → C n) (n : Nat)
    (previous : ∀ m, m < n → C m) : C n := step n (below n previous)

theorem source_unfold (step : ∀ n, @Nat.below C n → C n) (n : Nat) :
    Nat.brecOn n step = recipe step n (fun m _ => Nat.brecOn m step) := by
  rw [Nat.brecOn.eq, recipe, below_brecOn]

noncomputable def evaluate (n : Nat) (step : ∀ n, @Nat.below C n → C n) : C n :=
  AccessibleRecipe.evaluate (fun n => n) (recipe step) n

theorem equals_brecOn (n : Nat) (step : ∀ n, @Nat.below C n → C n) :
    evaluate n step = Nat.brecOn n step := by
  change AccessibleRecipe.evaluate (fun n => n) (recipe step) n = Nat.brecOn n step
  exact AccessibleRecipe.equals_of_equations (C := C) (fun n => n) (recipe step)
    (fun m => Nat.brecOn (motive := C) m step) (fun m => source_unfold step m) n

end Mettapedia.Languages.Lean.Recursion.AccessibleNatBrec
