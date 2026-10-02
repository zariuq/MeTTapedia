import Mettapedia.TypeTheory.UniverseLevel.Order

/-!
# Finite offsets, limits, predecessors and embeddings of level orders

In a level order, the level `k` steps above `l` is the `k`-fold successor of `l`. It is
monotone and injective in both arguments and commutes with `max`. The finite levels are the
offsets of the least level.

A level is a limit when it is positive and is not a successor; a limit is closed under the
successor, so it lies above every finite level. A level order has *predecessors* when it
computes, for every level, whether it is a successor and of which level.

An embedding of level orders preserves and reflects the order and commutes with the least
level and the successor. It is *initial* when its image is closed downward; an initial
embedding sends limits to limits. The finite levels embed initially into every level order.

Positive examples: over the natural numbers the offset is addition and no level is a limit.
Negative examples: doubling is strictly increasing on the natural numbers but is not an
embedding, since it does not commute with the successor.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniverseLevel

namespace LevelOrder

variable {L : Type} [LevelOrder L]

/-! ## The successor -/

/-- A level below a successor is at most its predecessor. -/
theorem le_of_lt_succ {a b : L} (h : a < succ b) : a ≤ b :=
  le_of_not_gt fun hba => not_lt_of_lt_succ hba h

/-- `a < succ b` exactly when `a ≤ b`. -/
theorem lt_succ_iff {a b : L} : a < succ b ↔ a ≤ b :=
  ⟨le_of_lt_succ, fun h => lt_of_le_of_lt h (lt_succ b)⟩

/-- The successor reflects the order. -/
theorem le_of_succ_le_succ {a b : L} (h : succ a ≤ succ b) : a ≤ b :=
  le_of_lt_succ (lt_of_succ_le h)

/-- `succ a ≤ succ b` exactly when `a ≤ b`. -/
theorem succ_le_succ_iff {a b : L} : succ a ≤ succ b ↔ a ≤ b :=
  ⟨le_of_succ_le_succ, succ_le_succ⟩

/-- `succ a < succ b` exactly when `a < b`. -/
theorem succ_lt_succ_iff {a b : L} : succ a < succ b ↔ a < b :=
  ⟨fun h => lt_of_succ_le (le_of_lt_succ h), fun h => lt_succ_iff.mpr (succ_le_of_lt h)⟩

/-- The successor is injective. -/
theorem succ_injective : Function.Injective (succ : L → L) := fun _ _ h =>
  le_antisymm (le_of_succ_le_succ (le_of_eq h)) (le_of_succ_le_succ (le_of_eq h.symm))

/-- A successor is positive. -/
theorem bot_lt_succ (l : L) : bot < succ l := lt_of_le_of_lt (bot_le l) (lt_succ l)

/-- A successor is not the least level. -/
theorem succ_ne_bot (l : L) : succ l ≠ bot := fun h =>
  lt_irrefl (bot : L) (h ▸ bot_lt_succ l)

/-- A level other than the least one is positive. -/
theorem bot_lt_of_ne_bot {l : L} (h : l ≠ bot) : bot < l :=
  lt_of_le_of_ne (bot_le l) (Ne.symm h)

/-- A level below the least level is the least level. -/
theorem eq_bot_of_le_bot {l : L} (h : l ≤ bot) : l = bot := le_antisymm h (bot_le l)

/-- The larger of the least level and another level is that level. -/
theorem bot_max (l : L) : max bot l = l := max_eq_right (bot_le l)

/-- The larger of a level and the least level is that level. -/
theorem max_bot (l : L) : max l bot = l := max_eq_left (bot_le l)

/-- The successor commutes with `max`. -/
theorem max_succ_succ (a b : L) : max (succ a) (succ b) = succ (max a b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (succ_le_succ h)]
  · rw [max_eq_left h, max_eq_left (succ_le_succ h)]

/-- A level lies below a maximum exactly when it lies below one of the two. -/
theorem lt_max_iff' {a b c : L} : a < max b c ↔ a < b ∨ a < c := by
  rcases le_total b c with h | h
  · rw [max_eq_right h]
    exact ⟨Or.inr, fun h' => h'.elim (fun hab => lt_of_lt_of_le hab h) id⟩
  · rw [max_eq_left h]
    exact ⟨Or.inl, fun h' => h'.elim id (fun hac => lt_of_lt_of_le hac h)⟩

/-- A level is at most a maximum exactly when it is at most one of the two. -/
theorem le_max_iff' {a b c : L} : a ≤ max b c ↔ a ≤ b ∨ a ≤ c := by
  rcases le_total b c with h | h
  · rw [max_eq_right h]
    exact ⟨Or.inr, fun h' => h'.elim (fun hab => le_trans hab h) id⟩
  · rw [max_eq_left h]
    exact ⟨Or.inl, fun h' => h'.elim id (fun hac => le_trans hac h)⟩

/-! ## Finite offsets -/

/-- The level `k` steps above `l`. -/
def addNat (l : L) : Nat → L
  | 0 => l
  | k + 1 => succ (addNat l k)

@[simp] theorem addNat_zero (l : L) : addNat l 0 = l := rfl

@[simp] theorem addNat_succ (l : L) (k : Nat) : addNat l (k + 1) = succ (addNat l k) := rfl

/-- An offset of a successor is the successor of the offset. -/
theorem succ_addNat (l : L) : ∀ k : Nat, addNat (succ l) k = succ (addNat l k)
  | 0 => rfl
  | k + 1 => by rw [addNat_succ, addNat_succ, succ_addNat l k]

/-- Offsets compose by addition. -/
theorem addNat_add (l : L) (j : Nat) : ∀ k : Nat, addNat l (j + k) = addNat (addNat l j) k
  | 0 => rfl
  | k + 1 => by rw [← Nat.add_assoc, addNat_succ, addNat_succ, addNat_add l j k]

/-- A level lies at most its offsets. -/
theorem le_addNat (l : L) : ∀ k : Nat, l ≤ addNat l k
  | 0 => le_refl l
  | k + 1 => le_trans (le_addNat l k) (le_succ _)

/-- A level lies strictly below its positive offsets. -/
theorem lt_addNat_succ (l : L) (k : Nat) : l < addNat l (k + 1) :=
  lt_of_le_of_lt (le_addNat l k) (lt_succ _)

/-- Offsets are monotone in the level. -/
theorem addNat_le_addNat_left {a b : L} (h : a ≤ b) : ∀ k : Nat, addNat a k ≤ addNat b k
  | 0 => h
  | k + 1 => succ_le_succ (addNat_le_addNat_left h k)

/-- Offsets reflect the order of levels. -/
theorem addNat_le_addNat_iff_left {a b : L} : ∀ {k : Nat}, addNat a k ≤ addNat b k ↔ a ≤ b
  | 0 => Iff.rfl
  | k + 1 => by
    rw [addNat_succ, addNat_succ, succ_le_succ_iff]
    exact addNat_le_addNat_iff_left

/-- Offsets reflect the strict order of levels. -/
theorem addNat_lt_addNat_iff_left {a b : L} {k : Nat} : addNat a k < addNat b k ↔ a < b := by
  rw [← not_le, ← not_le, addNat_le_addNat_iff_left]

/-- Offsets are monotone in the number of steps. -/
theorem addNat_le_addNat_right (l : L) {j k : Nat} (h : j ≤ k) : addNat l j ≤ addNat l k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [addNat_add]
  exact le_addNat _ d

/-- Offsets are strictly monotone in the number of steps. -/
theorem addNat_lt_addNat_right (l : L) {j k : Nat} (h : j < k) : addNat l j < addNat l k :=
  lt_of_lt_of_le (lt_succ _) (addNat_le_addNat_right l (k := k) (j := j + 1) h)

/-- Offsets of one level compare as their numbers of steps. -/
theorem addNat_le_addNat_iff_right {l : L} {j k : Nat} : addNat l j ≤ addNat l k ↔ j ≤ k :=
  ⟨fun h => Nat.le_of_not_lt fun hkj => not_lt_of_ge h (addNat_lt_addNat_right l hkj),
    addNat_le_addNat_right l⟩

/-- Offsets of one level compare strictly as their numbers of steps. -/
theorem addNat_lt_addNat_iff_right {l : L} {j k : Nat} : addNat l j < addNat l k ↔ j < k :=
  ⟨fun h => Nat.lt_of_not_le fun hkj => not_lt_of_ge (addNat_le_addNat_right l hkj) h,
    addNat_lt_addNat_right l⟩

/-- The number of steps of an offset is determined. -/
theorem addNat_injective_right {l : L} {j k : Nat} (h : addNat l j = addNat l k) : j = k :=
  Nat.le_antisymm (addNat_le_addNat_iff_right.mp (le_of_eq h))
    (addNat_le_addNat_iff_right.mp (le_of_eq h.symm))

/-- Offsets are monotone in both arguments. -/
theorem addNat_le_addNat {a b : L} {j k : Nat} (h : a ≤ b) (hjk : j ≤ k) :
    addNat a j ≤ addNat b k :=
  le_trans (addNat_le_addNat_left h j) (addNat_le_addNat_right b hjk)

/-- Offsets commute with `max` of levels. -/
theorem addNat_max_left (a b : L) (k : Nat) :
    addNat (max a b) k = max (addNat a k) (addNat b k) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (addNat_le_addNat_left h k)]
  · rw [max_eq_left h, max_eq_left (addNat_le_addNat_left h k)]

/-- Offsets commute with `max` of the numbers of steps. -/
theorem addNat_max_right (l : L) (j k : Nat) :
    addNat l (max j k) = max (addNat l j) (addNat l k) := by
  rcases Nat.le_total j k with h | h
  · rw [Nat.max_eq_right h, max_eq_right (addNat_le_addNat_right l h)]
  · rw [Nat.max_eq_left h, max_eq_left (addNat_le_addNat_right l h)]

/-! ## Finite levels -/

/-- The finite level `k`: the level `k` steps above the least one. -/
def ofNat (k : Nat) : L := addNat bot k

@[simp] theorem ofNat_zero : (ofNat 0 : L) = bot := rfl

@[simp] theorem ofNat_succ (k : Nat) : (ofNat (k + 1) : L) = succ (ofNat k) := rfl

/-- A finite level lies at most the offset of any level by the same number of steps. -/
theorem ofNat_le_addNat (l : L) (k : Nat) : ofNat k ≤ addNat l k :=
  addNat_le_addNat_left (bot_le l) k

/-- Finite levels compare as their numbers. -/
theorem ofNat_le_ofNat_iff {j k : Nat} : (ofNat j : L) ≤ ofNat k ↔ j ≤ k :=
  addNat_le_addNat_iff_right

/-- Finite levels compare strictly as their numbers. -/
theorem ofNat_lt_ofNat_iff {j k : Nat} : (ofNat j : L) < ofNat k ↔ j < k :=
  addNat_lt_addNat_iff_right

/-- Distinct numbers give distinct finite levels. -/
theorem ofNat_injective : Function.Injective (ofNat : Nat → L) := fun _ _ h =>
  addNat_injective_right h

/-- Finite levels commute with `max`. -/
theorem ofNat_max (j k : Nat) : (ofNat (max j k) : L) = max (ofNat j) (ofNat k) :=
  addNat_max_right bot j k

/-- An offset of a finite level is a finite level. -/
theorem addNat_ofNat (j k : Nat) : addNat (ofNat j : L) k = ofNat (j + k) :=
  (addNat_add bot j k).symm

/-- A positive finite level is positive. -/
theorem bot_lt_ofNat_succ (k : Nat) : (bot : L) < ofNat (k + 1) := bot_lt_succ _

/-- A level below a finite level is a finite level. -/
theorem exists_ofNat_eq_of_lt : ∀ {k : Nat} {l : L}, l < ofNat k → ∃ j, j < k ∧ ofNat j = l
  | 0, l, h => absurd h (not_lt_of_ge (bot_le l))
  | k + 1, l, h =>
    if heq : l = ofNat k then ⟨k, Nat.lt_succ_self k, heq.symm⟩
    else
      let ⟨j, hj, hjl⟩ := exists_ofNat_eq_of_lt (lt_of_le_of_ne (le_of_lt_succ h) heq)
      ⟨j, Nat.lt_succ_of_lt hj, hjl⟩

/-! ## Limits -/

/-- A limit level: positive, and not a successor. -/
def IsLimit (l : L) : Prop := bot < l ∧ ∀ p : L, succ p ≠ l

/-- A limit is closed under the successor. -/
theorem IsLimit.succ_lt {l : L} (h : IsLimit l) {a : L} (ha : a < l) : succ a < l :=
  lt_of_le_of_ne (succ_le_of_lt ha) (h.2 a)

/-- A limit is closed under finite offsets. -/
theorem IsLimit.addNat_lt {l : L} (h : IsLimit l) {a : L} (ha : a < l) :
    ∀ k : Nat, addNat a k < l
  | 0 => ha
  | k + 1 => h.succ_lt (IsLimit.addNat_lt h ha k)

/-- A limit lies above every finite level. -/
theorem IsLimit.ofNat_lt {l : L} (h : IsLimit l) (k : Nat) : ofNat k < l :=
  h.addNat_lt h.1 k

/-- A successor is not a limit. -/
theorem not_isLimit_succ (l : L) : ¬ IsLimit (succ l) := fun h => h.2 l rfl

/-- The least level is not a limit. -/
theorem not_isLimit_bot : ¬ IsLimit (bot : L) := fun h => lt_irrefl _ h.1

/-- A finite level is not a limit. -/
theorem not_isLimit_ofNat : ∀ k : Nat, ¬ IsLimit (ofNat k : L)
  | 0 => not_isLimit_bot
  | _ + 1 => not_isLimit_succ _

end LevelOrder

/-! ## Predecessors -/

/-- A level order with predecessors: for every level it is computed whether the level is a
successor, and of which level. -/
class PredLevelOrder (L : Type) extends LevelOrder L where
  /-- The predecessor of a successor level; `none` at the least level and at limits. -/
  pred? : L → Option L
  pred?_eq_some : ∀ {l p : L}, pred? l = some p ↔ l = succ p

namespace PredLevelOrder

open LevelOrder

variable {L : Type} [PredLevelOrder L]

/-- The predecessor of a successor. -/
@[simp] theorem pred?_succ (p : L) : pred? (succ p) = some p := pred?_eq_some.mpr rfl

/-- A level has no predecessor exactly when it is not a successor. -/
theorem pred?_eq_none {l : L} : pred? l = none ↔ ∀ p : L, succ p ≠ l := by
  constructor
  · intro h p hp
    rw [← hp, pred?_succ] at h
    exact nomatch h
  · intro h
    cases hp : pred? l with
    | none => rfl
    | some p => exact absurd (pred?_eq_some.mp hp).symm (h p)

/-- The least level has no predecessor. -/
@[simp] theorem pred?_bot : pred? (bot : L) = none :=
  pred?_eq_none.mpr fun p => succ_ne_bot p

/-- A positive level without a predecessor is a limit. -/
theorem isLimit_of_pred?_eq_none {l : L} (pos : bot < l) (h : pred? l = none) : IsLimit l :=
  ⟨pos, pred?_eq_none.mp h⟩

/-- A limit has no predecessor. -/
theorem pred?_eq_none_of_isLimit {l : L} (h : IsLimit l) : pred? l = none :=
  pred?_eq_none.mpr h.2

/-- Whether a level is a limit is decided. -/
instance decidableIsLimit (l : L) : Decidable (IsLimit l) :=
  decidable_of_iff (bot < l ∧ pred? l = none)
    ⟨fun h => isLimit_of_pred?_eq_none h.1 h.2, fun h => ⟨h.1, pred?_eq_none_of_isLimit h⟩⟩

end PredLevelOrder

/-- The natural numbers have predecessors. -/
instance : PredLevelOrder Nat where
  pred?
    | 0 => none
    | n + 1 => some n
  pred?_eq_some := by
    intro l p
    cases l with
    | zero => exact ⟨nofun, fun h => absurd h.symm (Nat.succ_ne_zero p)⟩
    | succ n =>
      exact ⟨fun h => congrArg Nat.succ (Option.some.inj h),
        fun h => congrArg some (Nat.succ.inj h)⟩

/-- Over the natural numbers, the offset is addition. -/
@[simp] theorem nat_addNat (l : Nat) : ∀ k : Nat, LevelOrder.addNat l k = l + k
  | 0 => rfl
  | k + 1 => by
    rw [LevelOrder.addNat_succ, nat_addNat l k]
    rfl

/-- Over the natural numbers, the finite level `k` is `k`. -/
@[simp] theorem nat_ofNat (k : Nat) : (LevelOrder.ofNat k : Nat) = k := by
  rw [LevelOrder.ofNat, nat_addNat]
  exact Nat.zero_add k

/-- No natural number is a limit. -/
theorem nat_not_isLimit (n : Nat) : ¬ LevelOrder.IsLimit n := by
  rw [← nat_ofNat n]
  exact LevelOrder.not_isLimit_ofNat n

/-! ## Embeddings -/

namespace LevelOrder

/-- An embedding of level orders: it preserves and reflects the order and commutes with the
least level and the successor. -/
structure Embedding (L L' : Type) [LevelOrder L] [LevelOrder L'] where
  toFun : L → L'
  le_iff : ∀ {a b : L}, toFun a ≤ toFun b ↔ a ≤ b
  map_bot : toFun bot = bot
  map_succ : ∀ a : L, toFun (succ a) = succ (toFun a)

namespace Embedding

variable {L L' L'' : Type} [LevelOrder L] [LevelOrder L'] [LevelOrder L'']

instance : CoeFun (Embedding L L') (fun _ => L → L') := ⟨toFun⟩

/-- An embedding preserves and reflects the strict order. -/
theorem lt_iff (f : Embedding L L') {a b : L} : f a < f b ↔ a < b := by
  rw [← not_le, ← not_le, f.le_iff]

/-- An embedding is injective. -/
theorem injective (f : Embedding L L') : Function.Injective f := fun _ _ h =>
  le_antisymm (f.le_iff.mp (le_of_eq h)) (f.le_iff.mp (le_of_eq h.symm))

/-- An embedding commutes with `max`. -/
theorem map_max (f : Embedding L L') (a b : L) : f (max a b) = max (f a) (f b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (f.le_iff.mpr h)]
  · rw [max_eq_left h, max_eq_left (f.le_iff.mpr h)]

/-- An embedding commutes with finite offsets. -/
theorem map_addNat (f : Embedding L L') (l : L) : ∀ k : Nat, f (addNat l k) = addNat (f l) k
  | 0 => rfl
  | k + 1 => by rw [addNat_succ, f.map_succ, map_addNat f l k, addNat_succ]

/-- An embedding preserves the finite levels. -/
theorem map_ofNat (f : Embedding L L') (k : Nat) : f (ofNat k) = ofNat k := by
  rw [ofNat, map_addNat, f.map_bot, ofNat]

/-- The identity embedding. -/
def id (L : Type) [LevelOrder L] : Embedding L L where
  toFun := fun l => l
  le_iff := Iff.rfl
  map_bot := rfl
  map_succ := fun _ => rfl

/-- Embeddings compose. -/
def comp (g : Embedding L' L'') (f : Embedding L L') : Embedding L L'' where
  toFun := fun l => g (f l)
  le_iff := g.le_iff.trans f.le_iff
  map_bot := by rw [f.map_bot, g.map_bot]
  map_succ := fun a => by rw [f.map_succ, g.map_succ]

/-- An embedding is initial when its image is closed downward. -/
def Initial (f : Embedding L L') : Prop := ∀ (a : L) (b : L'), b < f a → ∃ a' : L, f a' = b

/-- An initial embedding reflects successors: a level whose image is a successor is the
successor of a level. -/
theorem Initial.eq_succ_of_map_eq_succ {f : Embedding L L'} (initial : f.Initial) {l : L}
    {q : L'} (h : f l = succ q) : ∃ p : L, l = succ p ∧ f p = q := by
  obtain ⟨p, hp⟩ := initial l q (h ▸ lt_succ q)
  refine ⟨p, f.injective ?_, hp⟩
  rw [h, f.map_succ, hp]

/-- An initial embedding sends limits to limits. -/
theorem Initial.map_isLimit {f : Embedding L L'} (initial : f.Initial) {l : L}
    (limit : IsLimit l) : IsLimit (f l) := by
  refine ⟨?_, fun q hq => ?_⟩
  · rw [← f.map_bot]
    exact f.lt_iff.mpr limit.1
  · obtain ⟨p, hp, _⟩ := initial.eq_succ_of_map_eq_succ hq.symm
    exact limit.2 p hp.symm

/-- The identity embedding is initial. -/
theorem id_initial (L : Type) [LevelOrder L] : (id L).Initial := fun _ b _ => ⟨b, rfl⟩

/-- The finite levels embed into every level order. -/
def ofNat (L : Type) [LevelOrder L] : Embedding Nat L where
  toFun := LevelOrder.ofNat
  le_iff := ofNat_le_ofNat_iff
  map_bot := rfl
  map_succ := fun _ => rfl

/-- The embedding of the finite levels is initial. -/
theorem ofNat_initial (L : Type) [LevelOrder L] : (ofNat L).Initial := fun _ _ h =>
  let ⟨j, _, hj⟩ := exists_ofNat_eq_of_lt h
  ⟨j, hj⟩

end Embedding

end LevelOrder

namespace PredLevelOrder

open LevelOrder

variable {L L' : Type} [PredLevelOrder L] [PredLevelOrder L']

/-- An initial embedding commutes with the predecessor. -/
theorem pred?_map {f : Embedding L L'} (initial : f.Initial) (l : L) :
    pred? (f l) = (pred? l).map f := by
  cases hp : pred? l with
  | some p =>
    rw [pred?_eq_some.mp hp, f.map_succ, pred?_succ]
    rfl
  | none =>
    refine pred?_eq_none.mpr fun q hq => ?_
    obtain ⟨p, hp', _⟩ := initial.eq_succ_of_map_eq_succ hq.symm
    exact pred?_eq_none.mp hp p hp'.symm

end PredLevelOrder

/-! ## Examples -/

section Examples

open LevelOrder

/-- Over the natural numbers, three steps above four is seven. -/
example : addNat (4 : Nat) 3 = 7 := by decide

/-- The predecessor of five is four, and zero has none. -/
example : PredLevelOrder.pred? (5 : Nat) = some 4 ∧ PredLevelOrder.pred? (0 : Nat) = none :=
  ⟨rfl, rfl⟩

/-- Doubling preserves and reflects the order of the natural numbers but does not commute
with the successor, so it is not an embedding of level orders. -/
theorem doubling_not_embedding :
    ¬ ∃ f : Embedding Nat Nat, ∀ n : Nat, f n = 2 * n := fun ⟨f, h⟩ =>
  absurd ((h 1).symm.trans ((f.map_succ 0).trans (congrArg succ (h 0)))) (by decide)

end Examples

end Mettapedia.TypeTheory.UniverseLevel
