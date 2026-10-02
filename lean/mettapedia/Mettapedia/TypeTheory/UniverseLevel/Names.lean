import Mettapedia.TypeTheory.UniverseLevel.Algebra

/-!
# Level expressions spelled in names

A level expression is spelled after a name by numeric components, in postfix
order (`appendLevel`):

* `const n` as the components `n, 0`, and `param n` as `n, 1`;
* `succ e` as the spelling of `e` followed by `2`;
* `max a b` as the spelling of `a`, then that of `b`, followed by `3`.

The last component of a spelling tells its former, so a spelling is read back
from the end of a name (`readLevel`), and the spelling is injective in the level
and in the name it extends (`appendLevel_inj`). Every spelling ends in a numeric
component, so no spelling is a name ending in a string (`appendLevel_ne_str`).
The reading is by constructor matching and fuel bounded by the number of
components; injectivity is by injectivity of the constructors of names.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniverseLevel

/-- The spelling of a level expression after a name, in postfix order. -/
def appendLevel : Lean.Name → LevelExpr Nat → Lean.Name
  | p, .const n => .num (.num p n) 0
  | p, .param n => .num (.num p n) 1
  | p, .succ e => .num (appendLevel p e) 2
  | p, .max a b => .num (appendLevel (appendLevel p a) b) 3

/-- Every spelling ends in a numeric component. -/
theorem appendLevel_ne_str (p : Lean.Name) (e : LevelExpr Nat) (q : Lean.Name) (s : String) :
    appendLevel p e ≠ .str q s := by
  cases e <;> exact Lean.Name.noConfusion

theorem appendLevel_ne_anonymous (p : Lean.Name) (e : LevelExpr Nat) :
    appendLevel p e ≠ .anonymous := by
  cases e <;> exact Lean.Name.noConfusion

/-- **The spelling is injective**, in the level and in the name it extends. -/
theorem appendLevel_inj : ∀ {e e' : LevelExpr Nat} {p p' : Lean.Name},
    appendLevel p e = appendLevel p' e' → e = e' ∧ p = p'
  | .const n, .const n', p, p', h => by
      simp only [appendLevel, Lean.Name.num.injEq, and_true] at h
      exact ⟨congrArg _ h.2, h.1⟩
  | .param n, .param n', p, p', h => by
      simp only [appendLevel, Lean.Name.num.injEq, and_true] at h
      exact ⟨congrArg _ h.2, h.1⟩
  | .succ e, .succ e', p, p', h => by
      simp only [appendLevel, Lean.Name.num.injEq, and_true] at h
      obtain ⟨rfl, rfl⟩ := appendLevel_inj h
      exact ⟨rfl, rfl⟩
  | .max a b, .max a' b', p, p', h => by
      simp only [appendLevel, Lean.Name.num.injEq, and_true] at h
      obtain ⟨rfl, h'⟩ := appendLevel_inj h
      obtain ⟨rfl, rfl⟩ := appendLevel_inj h'
      exact ⟨rfl, rfl⟩
  | .const _, .param _, _, _, h => by simp [appendLevel] at h
  | .const _, .succ _, _, _, h => by simp [appendLevel] at h
  | .const _, .max _ _, _, _, h => by simp [appendLevel] at h
  | .param _, .const _, _, _, h => by simp [appendLevel] at h
  | .param _, .succ _, _, _, h => by simp [appendLevel] at h
  | .param _, .max _ _, _, _, h => by simp [appendLevel] at h
  | .succ _, .const _, _, _, h => by simp [appendLevel] at h
  | .succ _, .param _, _, _, h => by simp [appendLevel] at h
  | .succ _, .max _ _, _, _, h => by simp [appendLevel] at h
  | .max _ _, .const _, _, _, h => by simp [appendLevel] at h
  | .max _ _, .param _, _, _, h => by simp [appendLevel] at h
  | .max _ _, .succ _, _, _, h => by simp [appendLevel] at h

/-! ## Reading a spelling back -/

/-- The number of components of a name. -/
def componentCount : Lean.Name → Nat
  | .anonymous => 0
  | .str p _ => componentCount p + 1
  | .num p _ => componentCount p + 1

/-- The spelled level expression at the end of a name and the name before it, read
in at most `fuel` nested steps. -/
def readLevelAux : Nat → Lean.Name → Option (LevelExpr Nat × Lean.Name)
  | 0, _ => none
  | _ + 1, .num (.num p n) 0 => some (.const n, p)
  | _ + 1, .num (.num p n) 1 => some (.param n, p)
  | fuel + 1, .num p 2 =>
      match readLevelAux fuel p with
      | some (e, q) => some (.succ e, q)
      | none => none
  | fuel + 1, .num p 3 =>
      match readLevelAux fuel p with
      | some (b, q) =>
          match readLevelAux fuel q with
          | some (a, r) => some (.max a b, r)
          | none => none
      | none => none
  | _ + 1, _ => none

/-- **The spelled level expression at the end of a name**, and the name it extends. -/
def readLevel (name : Lean.Name) : Option (LevelExpr Nat × Lean.Name) :=
  readLevelAux (componentCount name) name

/-- The nesting depth of a level expression. -/
def LevelExpr.depth : LevelExpr Nat → Nat
  | .const _ => 1
  | .param _ => 1
  | .succ e => e.depth + 1
  | .max a b => Max.max a.depth b.depth + 1

theorem componentCount_appendLevel (p : Lean.Name) :
    ∀ e : LevelExpr Nat, componentCount p + e.depth ≤ componentCount (appendLevel p e)
  | .const _ => by simp only [appendLevel, componentCount, LevelExpr.depth]; omega
  | .param _ => by simp only [appendLevel, componentCount, LevelExpr.depth]; omega
  | .succ e => by
      have := componentCount_appendLevel p e
      simp only [appendLevel, componentCount, LevelExpr.depth]
      omega
  | .max a b => by
      have ha := componentCount_appendLevel p a
      have hb := componentCount_appendLevel (appendLevel p a) b
      simp only [appendLevel, componentCount, LevelExpr.depth]
      omega

/-- With enough fuel the reading recovers a spelling and the name it extends. -/
theorem readLevelAux_appendLevel :
    ∀ (e : LevelExpr Nat) (p : Lean.Name) (fuel : Nat), e.depth ≤ fuel →
      readLevelAux fuel (appendLevel p e) = some (e, p)
  | .const _, _, _ + 1, _ => rfl
  | .param _, _, _ + 1, _ => rfl
  | .succ e, p, fuel + 1, enough => by
      have inner := readLevelAux_appendLevel e p fuel (Nat.le_of_succ_le_succ enough)
      simp only [appendLevel, readLevelAux, inner]
  | .max a b, p, fuel + 1, enough => by
      have below : Max.max a.depth b.depth ≤ fuel := Nat.le_of_succ_le_succ enough
      have innerB := readLevelAux_appendLevel b (appendLevel p a) fuel
        (Nat.le_trans (Nat.le_max_right _ _) below)
      have innerA := readLevelAux_appendLevel a p fuel
        (Nat.le_trans (Nat.le_max_left _ _) below)
      simp only [appendLevel, readLevelAux, innerB, innerA]
  | .const _, _, 0, enough => absurd enough (Nat.not_succ_le_zero 0)
  | .param _, _, 0, enough => absurd enough (Nat.not_succ_le_zero 0)
  | .succ _, _, 0, enough => absurd enough (Nat.not_succ_le_zero _)
  | .max _ _, _, 0, enough => absurd enough (Nat.not_succ_le_zero _)

/-- **The reading recovers every spelling.** -/
theorem readLevel_appendLevel (p : Lean.Name) (e : LevelExpr Nat) :
    readLevel (appendLevel p e) = some (e, p) :=
  readLevelAux_appendLevel e p _
    (Nat.le_trans (Nat.le_add_left _ _) (componentCount_appendLevel p e))

/-- The reading returns only spellings. -/
theorem readLevelAux_sound :
    ∀ (fuel : Nat) (name : Lean.Name) {p : Lean.Name} {e : LevelExpr Nat},
      readLevelAux fuel name = some (e, p) → name = appendLevel p e
  | 0, _, _, _, found => by cases found
  | _ + 1, .anonymous, _, _, found => by cases found
  | _ + 1, .str _ _, _, _, found => by cases found
  | _ + 1, .num .anonymous 0, _, _, found => by cases found
  | _ + 1, .num (.str _ _) 0, _, _, found => by cases found
  | _ + 1, .num (.num q n) 0, p, e, found => by
      simp only [readLevelAux, Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl⟩ := found
      rfl
  | _ + 1, .num .anonymous 1, _, _, found => by cases found
  | _ + 1, .num (.str _ _) 1, _, _, found => by cases found
  | _ + 1, .num (.num q n) 1, p, e, found => by
      simp only [readLevelAux, Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl⟩ := found
      rfl
  | fuel + 1, .num q 2, p, e, found => by
      simp only [readLevelAux] at found
      cases inner : readLevelAux fuel q with
      | none => rw [inner] at found; cases found
      | some r =>
          obtain ⟨e', q'⟩ := r
          rw [inner] at found
          simp only [Option.some.injEq, Prod.mk.injEq] at found
          obtain ⟨rfl, rfl⟩ := found
          rw [readLevelAux_sound fuel q inner]
          rfl
  | fuel + 1, .num q 3, p, e, found => by
      simp only [readLevelAux] at found
      cases innerB : readLevelAux fuel q with
      | none => rw [innerB] at found; cases found
      | some rb =>
          obtain ⟨b, q'⟩ := rb
          rw [innerB] at found
          simp only at found
          cases innerA : readLevelAux fuel q' with
          | none => rw [innerA] at found; cases found
          | some ra =>
              obtain ⟨a, r⟩ := ra
              rw [innerA] at found
              simp only [Option.some.injEq, Prod.mk.injEq] at found
              obtain ⟨rfl, rfl⟩ := found
              rw [readLevelAux_sound fuel q innerB, readLevelAux_sound fuel q' innerA]
              rfl
  | _ + 1, .num _ (_ + 4), _, _, found => by simp [readLevelAux] at found

/-- **The reading returns only spellings.** -/
theorem readLevel_sound {name p : Lean.Name} {e : LevelExpr Nat}
    (found : readLevel name = some (e, p)) : name = appendLevel p e :=
  readLevelAux_sound _ _ found

/-- A name ending in a string spells no level. -/
theorem readLevel_str (q : Lean.Name) (s : String) : readLevel (.str q s) = none := rfl

theorem readLevel_anonymous : readLevel .anonymous = none := rfl

/-- The reading of a name, as a statement about spellings. -/
theorem readLevel_eq_some_iff {name p : Lean.Name} {e : LevelExpr Nat} :
    readLevel name = some (e, p) ↔ name = appendLevel p e :=
  ⟨readLevel_sound, fun h => h ▸ readLevel_appendLevel p e⟩

end Mettapedia.TypeTheory.UniverseLevel
