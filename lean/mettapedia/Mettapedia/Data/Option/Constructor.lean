import Mathlib.Data.Option.Basic

/-! # Presence of independently checked constructor arguments -/

set_option autoImplicit false

namespace Option

universe u

theorem assemble_two_isSome {A B C : Type u}
    (left : Option A) (right : Option B) (assemble : A → B → C) :
    (do let left ← left; let right ← right; pure (assemble left right)).isSome =
      (left.isSome && right.isSome) := by
  cases left <;> cases right <;> rfl

theorem assemble_three_isSome {A B C D : Type u}
    (first : Option A) (second : Option B) (third : Option C) (assemble : A → B → C → D) :
    (do let first ← first; let second ← second; let third ← third
        pure (assemble first second third)).isSome =
      (first.isSome && second.isSome && third.isSome) := by
  cases first <;> cases second <;> cases third <;> rfl

end Option
