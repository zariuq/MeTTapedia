import Mettapedia.TypeTheory.UniverseLevel.Offsets

/-!
# A level order followed by the natural numbers

Over a level order `L`, the levels `Above L` are the levels of `L` and then one more level for
every natural number: `below l` for a level of `L`, and `above n` above all of those, ordered
by `n`. They are again a level order. As ordinals: when `L` has order type `α`, `Above L` has
order type `α + ω`.

The first new level, `above 0`, is a limit: it is not a successor, and every level of `L` is
below it. A tower of universes over `Above L` therefore has, above every universe at a level of
`L`, a universe that contains them all, then the universe of that one, and so on. That is how
the type of all sets and its sort are placed over a tower of type universes.

The levels of `L` are an initial segment (`belowEmbedding`, `belowEmbedding_initial`), so the
tower over `L` is the lower part of the tower over `Above L`.

Positive examples: every level of `L` is below `above 0` (`below_lt_above`); the successor of
`above n` is `above (n + 1)` (`succ_above`). Negative examples: `above 0` is the successor of
no level (`above_zero_isLimit`), and no new level is below a level of `L`
(`not_above_le_below`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniverseLevel

/-- **The levels of a level order followed by the natural numbers.** -/
inductive Above (L : Type) where
  | below : L → Above L
  | above : Nat → Above L

namespace Above

variable {L : Type} [LevelOrder L]

/-- The order: the levels of `L` as before, the new levels by their numbers, and every level
of `L` below every new level. -/
def le : Above L → Above L → Prop
  | below a, below b => a ≤ b
  | below _, above _ => True
  | above _, below _ => False
  | above m, above n => m ≤ n

theorem le_refl' : ∀ a : Above L, le a a
  | below a => _root_.le_refl a
  | above n => Nat.le_refl n

theorem le_trans' : ∀ {a b c : Above L}, le a b → le b c → le a c
  | below _, below _, below _, hab, hbc => _root_.le_trans hab hbc
  | below _, below _, above _, _, _ => trivial
  | below _, above _, below _, _, hbc => hbc.elim
  | below _, above _, above _, _, _ => trivial
  | above _, below _, _, hab, _ => hab.elim
  | above _, above _, below _, _, hbc => hbc.elim
  | above _, above _, above _, hab, hbc => Nat.le_trans hab hbc

theorem le_antisymm' : ∀ {a b : Above L}, le a b → le b a → a = b
  | below _, below _, hab, hba => congrArg below (_root_.le_antisymm hab hba)
  | below _, above _, _, hba => hba.elim
  | above _, below _, hab, _ => hab.elim
  | above _, above _, hab, hba => congrArg above (Nat.le_antisymm hab hba)

theorem le_total' : ∀ a b : Above L, le a b ∨ le b a
  | below a, below b => _root_.le_total a b
  | below _, above _ => .inl trivial
  | above _, below _ => .inr trivial
  | above m, above n => Nat.le_total m n

instance decidableLe : (a b : Above L) → Decidable (le a b)
  | below a, below b => inferInstanceAs (Decidable (a ≤ b))
  | below _, above _ => isTrue trivial
  | above _, below _ => isFalse fun h => h
  | above m, above n => inferInstanceAs (Decidable (m ≤ n))

instance : LinearOrder (Above L) where
  le := le
  le_refl := le_refl'
  le_trans := fun _ _ _ => le_trans'
  le_antisymm := fun _ _ => le_antisymm'
  le_total := le_total'
  toDecidableLE := decidableLe

theorem below_le_below {a b : L} : (below a : Above L) ≤ below b ↔ a ≤ b := Iff.rfl

theorem above_le_above {m n : Nat} : (above m : Above L) ≤ above n ↔ m ≤ n := Iff.rfl

/-- Every level of `L` is at most every new level. -/
theorem below_le_above (a : L) (n : Nat) : (below a : Above L) ≤ above n := trivial

/-- Negative example: no new level is at most a level of `L`. -/
theorem not_above_le_below (n : Nat) (a : L) : ¬ (above n : Above L) ≤ below a := fun h => h

theorem below_lt_below {a b : L} : (below a : Above L) < below b ↔ a < b := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge]
  exact Iff.rfl

theorem above_lt_above {m n : Nat} : (above m : Above L) < above n ↔ m < n := by
  rw [lt_iff_le_not_ge, Nat.lt_iff_le_and_not_ge]
  exact Iff.rfl

/-- **Every level of `L` is below every new level.** -/
theorem below_lt_above (a : L) (n : Nat) : (below a : Above L) < above n :=
  lt_of_le_not_ge trivial fun h => h

theorem not_above_lt_below (n : Nat) (a : L) : ¬ (above n : Above L) < below a := fun h =>
  not_above_le_below n a (le_of_lt h)

theorem acc_below (a : L) : Acc (fun x y : Above L => x < y) (below a) :=
  LevelOrder.wf.induction (C := fun a => Acc (fun x y : Above L => x < y) (below a)) a
    fun a earlier => Acc.intro _ fun y hy => by
      cases y with
      | below b => exact earlier b (below_lt_below.mp hy)
      | above n => exact absurd hy (not_above_lt_below n a)

theorem acc_above (n : Nat) : Acc (fun x y : Above L => x < y) (above n) :=
  Nat.strong_induction_on n fun n earlier => Acc.intro _ fun y hy => by
    cases y with
    | below b => exact acc_below b
    | above m => exact earlier m (above_lt_above.mp hy)

/-- The successor: of a level of `L` as before, of a new level the next one. -/
def succ : Above L → Above L
  | below a => below (LevelOrder.succ a)
  | above n => above (n + 1)

/-- **The levels of a level order followed by the natural numbers are a level order.** -/
instance : LevelOrder (Above L) where
  wf := ⟨fun x => by
    cases x with
    | below a => exact acc_below a
    | above n => exact acc_above n⟩
  bot := below LevelOrder.bot
  bot_le := fun l => by
    cases l with
    | below a => exact below_le_below.mpr (LevelOrder.bot_le a)
    | above n => exact below_le_above _ n
  succ := succ
  lt_succ := fun l => by
    cases l with
    | below a => exact below_lt_below.mpr (LevelOrder.lt_succ a)
    | above n => exact above_lt_above.mpr (Nat.lt_succ_self n)
  succ_le_of_lt := fun {a b} h => by
    cases a with
    | below a =>
      cases b with
      | below b => exact below_le_below.mpr (LevelOrder.succ_le_of_lt (below_lt_below.mp h))
      | above n => exact below_le_above _ n
    | above m =>
      cases b with
      | below b => exact absurd h (not_above_lt_below m b)
      | above n => exact above_le_above.mpr (Nat.succ_le_of_lt (above_lt_above.mp h))

theorem bot_eq : (LevelOrder.bot : Above L) = below LevelOrder.bot := rfl

theorem succ_below (a : L) : LevelOrder.succ (below a : Above L) = below (LevelOrder.succ a) := rfl

/-- Positive example: the successor of a new level is the next new level. -/
theorem succ_above (n : Nat) : LevelOrder.succ (above n : Above L) = above (n + 1) := rfl

/-- Negative example: **the first new level is a limit**: it lies above the least level and is
the successor of no level. -/
theorem above_zero_isLimit : LevelOrder.IsLimit (above 0 : Above L) :=
  ⟨below_lt_above _ 0, fun p h => by
    cases p with
    | below a => exact nomatch h
    | above n => exact absurd (above.inj h) (Nat.succ_ne_zero n)⟩

variable (L) in
/-- **The levels of `L` among the levels followed by the natural numbers.** -/
def belowEmbedding : LevelOrder.Embedding L (Above L) where
  toFun := below
  le_iff := Iff.rfl
  map_bot := rfl
  map_succ := fun _ => rfl

/-- The levels of `L` are an initial segment. -/
theorem belowEmbedding_initial : (belowEmbedding L).Initial := fun a b h => by
  cases b with
  | below b => exact ⟨b, rfl⟩
  | above n => exact absurd h (not_above_lt_below n a)

end Above

end Mettapedia.TypeTheory.UniverseLevel
