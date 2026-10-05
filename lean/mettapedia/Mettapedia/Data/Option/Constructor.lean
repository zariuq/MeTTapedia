import Mathlib.Data.Option.Basic

/-! # Presence and relations of independently checked constructor arguments -/

set_option autoImplicit false

namespace Option

universe u v w x

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

/-- Relational construction preserves failure and compares each successful
    continuation at the related arguments it actually receives. -/
theorem Rel.bind {A : Type u} {B : Type v} {C : Type w} {D : Type x}
    {relation : A → B → Prop} {result : C → D → Prop}
    {left : Option A} {right : Option B} {nextLeft : A → Option C} {nextRight : B → Option D}
    (same : Rel relation left right)
    (next : ∀ a b, relation a b → Rel result (nextLeft a) (nextRight b)) :
    Rel result (left.bind nextLeft) (right.bind nextRight) := by
  cases same with
  | none => exact .none
  | some related => exact next _ _ related

/-- Mapping a checked value preserves its absence and the supplied
    successful-value relation. -/
theorem Rel.map {A : Type u} {B : Type v} {C : Type w} {D : Type x}
    {relation : A → B → Prop} {result : C → D → Prop}
    {left : Option A} {right : Option B} {mapLeft : A → C} {mapRight : B → D}
    (same : Rel relation left right)
    (mapped : ∀ a b, relation a b → result (mapLeft a) (mapRight b)) :
    Rel result (left.map mapLeft) (right.map mapRight) := by
  cases same with
  | none => exact .none
  | some related => exact .some (mapped _ _ related)

theorem Rel.isSome_eq {A : Type u} {B : Type v} {relation : A → B → Prop}
    {left : Option A} {right : Option B} (same : Rel relation left right) :
    left.isSome = right.isSome := by
  cases same <;> rfl

theorem Rel.eq {A : Type u} {left right : Option A} (same : Rel Eq left right) :
    left = right := by
  cases same with
  | none => rfl
  | some equal => cases equal; rfl

theorem Rel.of_eq {A : Type u} {left right : Option A} (equal : left = right) :
    Rel Eq left right := by
  cases equal
  cases left with
  | none => exact .none
  | some _ => exact .some rfl

end Option
