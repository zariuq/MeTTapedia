import Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
import Mathlib.Tactic

/-!
# Shifts on binding trees

The terms of the guarded rewriting calculus are binding trees: `SignatureIndexedABT.Term Head`, whose leaves
are de Bruijn indices (`idx n`: the variable bound `n` binders out) and whose nodes carry, for each
field, the number of binders the field sits under. Bound names are not stored, so two terms that
differ only in the names of their bound variables are the same tree.

A **shift** `lift c a t` adds `a` to every index of `t` that points past the `c` innermost binders.
This module collects the facts about shifts that the shared representation (`Store`, `Build`,
`Operations`) relies on.

* `lift c 0` is the identity (`lift_zero`); two shifts at nested cutoffs add up (`lift_lift_le`);
  shifts at separated cutoffs commute (`lift_comm`); a shift loses nothing (`lift_injective`).
* `freeAt t i` says that index `i` of `t` points outside `t`. A shift moves free indices exactly as
  expected (`freeAt_lift`), and a tree is **supported** below `d` exactly when its free indices are
  below `d` (`supportedAt_iff`).
* `above c t` is the least free index of `t` at or past `c` (`above_none_iff`, `above_some_iff`).
* `lower c m` undoes `lift c m` (`lower_lift`), and is undone by it when no index in `[c, c + m)` is
  free (`lift_lower`).
* A tree is **tight** when it is closed or uses index `0`. Every tree is a shift of a tight tree:
  `t = lift 0 m (lower 0 m t)` with `m` its least free index (`tighten`).
* Opening a binder (`instantiateAt`) commutes with shifts (`instantiateAt_lift_le`,
  `instantiateAt_lift_gt`) and leaves a tree with no free index at or past the opened one alone
  (`instantiateAt_of_supported`).

Example: in `λx. λy. x`, written `lam (lam (idx 1))`, the body `idx 1` of the inner binder is
`lift 0 1 (idx 0)`: a variable that skips the innermost binder.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT

variable {Head : Type}

/-! ## Laws of `lift` -/

mutual

/-- Shifting by zero changes nothing. -/
theorem lift_zero (c : ℕ) (t : Term Head) : Term.lift c 0 t = t := by
  cases t with
  | idx n => by_cases h : n < c <;> simp [Term.lift, h]
  | node head fields => simp [Term.lift, fields_lift_zero c fields]

theorem fields_lift_zero (c : ℕ) (fields : Fields Head) : Term.Fields.lift c 0 fields = fields := by
  cases fields with
  | nil => rfl
  | cons d t rest => simp [Term.Fields.lift, lift_zero (c + d) t, fields_lift_zero c rest]

end

mutual

/-- **Shifts at nested cutoffs add up**: a shift past `c'`, applied after a shift by `b` past `c`
with `c ≤ c' ≤ c + b`, is one shift by `b + a` past `c`. -/
theorem lift_lift_le (a b : ℕ) {c c' : ℕ} (low : c ≤ c') (high : c' ≤ c + b) (t : Term Head) :
    Term.lift c' a (Term.lift c b t) = Term.lift c (b + a) t := by
  cases t with
  | idx n =>
      by_cases h : n < c
      · have h' : n < c' := lt_of_lt_of_le h low
        simp [Term.lift, h, h']
      · have h' : ¬ n + b < c' := by omega
        simp [Term.lift, h, h', Nat.add_assoc]
  | node head fields =>
      simp [Term.lift, fields_lift_lift_le a b low high fields]

theorem fields_lift_lift_le (a b : ℕ) {c c' : ℕ} (low : c ≤ c') (high : c' ≤ c + b)
    (fields : Fields Head) :
    Term.Fields.lift c' a (Term.Fields.lift c b fields) = Term.Fields.lift c (b + a) fields := by
  cases fields with
  | nil => rfl
  | cons d t rest =>
      simp only [Term.Fields.lift]
      rw [lift_lift_le a b (c := c + d) (c' := c' + d) (by omega) (by omega) t,
        fields_lift_lift_le a b low high rest]

end

/-- Two shifts past the root add up. -/
theorem lift_lift_zero (a b : ℕ) (t : Term Head) :
    Term.lift 0 a (Term.lift 0 b t) = Term.lift 0 (b + a) t :=
  lift_lift_le a b (le_refl 0) (Nat.zero_le _) t

mutual

/-- **Shifts at separated cutoffs commute**: shifting by `b` past `c` and then by `a` past
`c' + b` is shifting by `a` past `c'` first, when `c ≤ c'`. -/
theorem lift_comm (a b : ℕ) {c c' : ℕ} (le : c ≤ c') (t : Term Head) :
    Term.lift (c' + b) a (Term.lift c b t) = Term.lift c b (Term.lift c' a t) := by
  cases t with
  | idx n =>
      by_cases h : n < c
      · have h1 : n < c' + b := by omega
        have h2 : n < c' := by omega
        simp [Term.lift, h, h1, h2]
      · by_cases h' : n < c'
        · have h1 : n + b < c' + b := by omega
          simp [Term.lift, h, h', h1]
        · have h1 : ¬ n + b < c' + b := by omega
          have h2 : ¬ n + a < c := by omega
          simp [Term.lift, h, h', h1, h2]
          omega
  | node head fields =>
      simp [Term.lift, fields_lift_comm a b le fields]

theorem fields_lift_comm (a b : ℕ) {c c' : ℕ} (le : c ≤ c') (fields : Fields Head) :
    Term.Fields.lift (c' + b) a (Term.Fields.lift c b fields) =
      Term.Fields.lift c b (Term.Fields.lift c' a fields) := by
  cases fields with
  | nil => rfl
  | cons d t rest =>
      simp only [Term.Fields.lift]
      have := lift_comm a b (c := c + d) (c' := c' + d) (by omega) t
      rw [show c' + b + d = c' + d + b by omega, this, fields_lift_comm a b le rest]

end

mutual

/-- **A shift loses nothing.** -/
theorem lift_injective (c a : ℕ) : ∀ s t : Term Head, Term.lift c a s = Term.lift c a t → s = t
  | .idx m, .idx n, h => by
      by_cases hm : m < c <;> by_cases hn : n < c <;>
        simp [Term.lift, hm, hn] at h <;> first | (subst h; rfl) | omega
  | .idx m, .node _ _, h => by
      by_cases hm : m < c <;> simp [Term.lift, hm] at h
  | .node _ _, .idx n, h => by
      by_cases hn : n < c <;> simp [Term.lift, hn] at h
  | .node h₁ f₁, .node h₂ f₂, h => by
      simp only [Term.lift, Term.node.injEq] at h
      rw [h.1, fields_lift_injective c a f₁ f₂ h.2]

theorem fields_lift_injective (c a : ℕ) :
    ∀ f g : Fields Head, Term.Fields.lift c a f = Term.Fields.lift c a g → f = g
  | .nil, .nil, _ => rfl
  | .nil, .cons _ _ _, h => by simp [Term.Fields.lift] at h
  | .cons _ _ _, .nil, h => by simp [Term.Fields.lift] at h
  | .cons d₁ t₁ r₁, .cons d₂ t₂ r₂, h => by
      simp only [Term.Fields.lift, Fields.cons.injEq] at h
      obtain ⟨hd, ht, hr⟩ := h
      subst hd
      rw [lift_injective (c + d₁) a t₁ t₂ ht, fields_lift_injective c a r₁ r₂ hr]

end

/-! ## Free indices -/

mutual

/-- `freeAt t i`: index `i` of `t` points outside `t` (seen from the root of `t`). -/
def freeAt : Term Head → ℕ → Bool
  | .idx n, i => decide (n = i)
  | .node _ fields, i => fieldsFreeAt fields i

/-- A field under `d` binders sees the root's index `i` as its own index `i + d`. -/
def fieldsFreeAt : Fields Head → ℕ → Bool
  | .nil, _ => false
  | .cons d t rest, i => freeAt t (i + d) || fieldsFreeAt rest i

end

@[simp] theorem freeAt_idx (n i : ℕ) : freeAt (.idx n : Term Head) i = decide (n = i) := by
  simp [freeAt]

@[simp] theorem freeAt_node (head : Head) (fields : Fields Head) (i : ℕ) :
    freeAt (.node head fields) i = fieldsFreeAt fields i := by
  simp [freeAt]

@[simp] theorem fieldsFreeAt_nil (i : ℕ) : fieldsFreeAt (.nil : Fields Head) i = false := by
  simp [fieldsFreeAt]

@[simp] theorem fieldsFreeAt_cons (d : ℕ) (t : Term Head) (rest : Fields Head) (i : ℕ) :
    fieldsFreeAt (.cons d t rest) i = (freeAt t (i + d) || fieldsFreeAt rest i) := by
  simp [fieldsFreeAt]

mutual

/-- **A shift moves the free indices it passes and keeps the others.** -/
theorem freeAt_lift (c a : ℕ) (t : Term Head) (i : ℕ) :
    freeAt (Term.lift c a t) i = true ↔
      (i < c ∧ freeAt t i = true) ∨ (c + a ≤ i ∧ freeAt t (i - a) = true) := by
  cases t with
  | idx n =>
      by_cases h : n < c
      · simp only [Term.lift, h, if_true, freeAt_idx, decide_eq_true_eq]
        constructor
        · rintro rfl; exact Or.inl ⟨h, rfl⟩
        · rintro (⟨_, e⟩ | ⟨le, e⟩)
          · exact e
          · omega
      · simp only [Term.lift, h, if_false, freeAt_idx, decide_eq_true_eq]
        constructor
        · intro e; right; constructor <;> omega
        · rintro (⟨lt, e⟩ | ⟨le, e⟩)
          · omega
          · omega
  | node head fields =>
      simp only [Term.lift, freeAt_node]
      exact fields_freeAt_lift c a fields i

theorem fields_freeAt_lift (c a : ℕ) (fields : Fields Head) (i : ℕ) :
    fieldsFreeAt (Term.Fields.lift c a fields) i = true ↔
      (i < c ∧ fieldsFreeAt fields i = true) ∨ (c + a ≤ i ∧ fieldsFreeAt fields (i - a) = true) := by
  cases fields with
  | nil => simp [Term.Fields.lift]
  | cons d t rest =>
      simp only [Term.Fields.lift, fieldsFreeAt_cons, Bool.or_eq_true]
      rw [freeAt_lift (c + d) a t (i + d), fields_freeAt_lift c a rest i]
      constructor
      · rintro ((⟨lt, ft⟩ | ⟨le, ft⟩) | (⟨lt, fr⟩ | ⟨le, fr⟩))
        · exact Or.inl ⟨by omega, Or.inl ft⟩
        · refine Or.inr ⟨by omega, Or.inl ?_⟩
          rwa [show i - a + d = i + d - a by omega]
        · exact Or.inl ⟨lt, Or.inr fr⟩
        · exact Or.inr ⟨le, Or.inr fr⟩
      · rintro (⟨lt, ft | fr⟩ | ⟨le, ft | fr⟩)
        · exact Or.inl (Or.inl ⟨by omega, ft⟩)
        · exact Or.inr (Or.inl ⟨lt, fr⟩)
        · refine Or.inl (Or.inr ⟨by omega, ?_⟩)
          rwa [show i + d - a = i - a + d by omega]
        · exact Or.inr (Or.inr ⟨le, fr⟩)

end

/-- A shift past the root moves every free index by its amount. -/
theorem freeAt_lift_zero (a : ℕ) (t : Term Head) (i : ℕ) :
    freeAt (Term.lift 0 a t) i = true ↔ a ≤ i ∧ freeAt t (i - a) = true := by
  rw [freeAt_lift]
  constructor
  · rintro (⟨lt, _⟩ | ⟨le, f⟩)
    · omega
    · exact ⟨by omega, f⟩
  · rintro ⟨le, f⟩
    exact Or.inr ⟨by omega, f⟩

mutual

/-- **A tree is supported below `d` exactly when its free indices are below `d`.** -/
theorem supportedAt_iff (d : ℕ) (t : Term Head) :
    Term.supportedAt d t = true ↔ ∀ i, freeAt t i = true → i < d := by
  cases t with
  | idx n =>
      simp only [Term.supportedAt, decide_eq_true_eq, freeAt_idx]
      constructor
      · rintro h i rfl; exact h
      · intro h; exact h n rfl
  | node head fields =>
      simp only [Term.supportedAt, freeAt_node]
      exact fields_supportedAt_iff d fields

theorem fields_supportedAt_iff (d : ℕ) (fields : Fields Head) :
    Term.Fields.supportedAt d fields = true ↔ ∀ i, fieldsFreeAt fields i = true → i < d := by
  cases fields with
  | nil => simp [Term.Fields.supportedAt]
  | cons fd t rest =>
      simp only [Term.Fields.supportedAt, Bool.and_eq_true, fieldsFreeAt_cons, Bool.or_eq_true]
      rw [supportedAt_iff (d + fd) t, fields_supportedAt_iff d rest]
      constructor
      · rintro ⟨ht, hr⟩ i (fi | fi)
        · have := ht _ fi; omega
        · exact hr i fi
      · intro h
        refine ⟨fun i fi => ?_, fun i fi => h i (Or.inr fi)⟩
        by_cases small : i < fd
        · omega
        · have := h (i - fd) (Or.inl (by rwa [show i - fd + fd = i by omega]))
          omega

end

/-- A tree is **closed** when no index points outside it. -/
def Closed (t : Term Head) : Prop := ∀ i, freeAt t i = false

theorem closed_iff_supportedAt_zero (t : Term Head) : Closed t ↔ Term.supportedAt 0 t = true := by
  rw [supportedAt_iff]
  constructor
  · intro h i fi; rw [h i] at fi; cases fi
  · intro h i
    cases fi : freeAt t i
    · rfl
    · exact absurd (h i fi) (Nat.not_lt_zero _)

/-- A shift past the root leaves a tree closed exactly when it was closed. -/
theorem closed_lift_zero_iff (a : ℕ) (t : Term Head) : Closed (Term.lift 0 a t) ↔ Closed t := by
  constructor
  · intro h i
    cases fi : freeAt t i
    · rfl
    · have := (freeAt_lift_zero a t (i + a)).mpr ⟨by omega, by rwa [Nat.add_sub_cancel]⟩
      rw [h] at this; cases this
  · intro h i
    cases fi : freeAt (Term.lift 0 a t) i
    · rfl
    · obtain ⟨_, f⟩ := (freeAt_lift_zero a t i).mp fi
      rw [h] at f; cases f

/-- A closed tree is not changed by a shift. -/
theorem lift_of_closed {t : Term Head} (closed : Closed t) (c a : ℕ) : Term.lift c a t = t :=
  Term.lift_of_supported c a t
    (Term.supportedAt_mono 0 c (Nat.zero_le c) t ((closed_iff_supportedAt_zero t).mp closed))

/-! ## The least free index past a cutoff -/

/-- The smaller of two optional numbers; `none` is "no number". -/
def omin : Option ℕ → Option ℕ → Option ℕ
  | none, y => y
  | some a, none => some a
  | some a, some b => some (min a b)

/-- `IsLeast P x`: `x` is the least number with property `P`, or `none` when there is none. -/
def IsLeast (P : ℕ → Prop) : Option ℕ → Prop
  | none => ∀ j, ¬ P j
  | some j => P j ∧ ∀ j', P j' → j ≤ j'

theorem IsLeast.unique {P : ℕ → Prop} {x y : Option ℕ} (hx : IsLeast P x) (hy : IsLeast P y) :
    x = y := by
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some b => exact absurd hy.1 (hx b)
  | some a =>
      cases y with
      | none => exact absurd hx.1 (hy a)
      | some b => exact congrArg some (le_antisymm (hx.2 b hy.1) (hy.2 a hx.1))

theorem IsLeast.congr {P Q : ℕ → Prop} (same : ∀ j, P j ↔ Q j) {x : Option ℕ} (h : IsLeast P x) :
    IsLeast Q x := by
  cases x with
  | none => exact fun j q => h j ((same j).mpr q)
  | some j => exact ⟨(same j).mp h.1, fun j' q => h.2 j' ((same j').mpr q)⟩

theorem omin_isLeast {P Q : ℕ → Prop} {x y : Option ℕ} (hx : IsLeast P x) (hy : IsLeast Q y) :
    IsLeast (fun j => P j ∨ Q j) (omin x y) := by
  cases x with
  | none =>
      cases y with
      | none => rintro j (p | q); exacts [hx j p, hy j q]
      | some b =>
          refine ⟨Or.inr hy.1, ?_⟩
          rintro j' (p | q)
          · exact absurd p (hx j')
          · exact hy.2 j' q
  | some a =>
      cases y with
      | none =>
          refine ⟨Or.inl hx.1, ?_⟩
          rintro j' (p | q)
          · exact hx.2 j' p
          · exact absurd q (hy j')
      | some b =>
          refine ⟨?_, ?_⟩
          · rcases le_total a b with ab | ba
            · rw [min_eq_left ab]; exact Or.inl hx.1
            · rw [min_eq_right ba]; exact Or.inr hy.1
          · rintro j' (p | q)
            · exact (min_le_left a b).trans (hx.2 j' p)
            · exact (min_le_right a b).trans (hy.2 j' q)

mutual

/-- `above c t`: the least `j` such that index `c + j` is free in `t`. -/
def above : ℕ → Term Head → Option ℕ
  | c, .idx n => if c ≤ n then some (n - c) else none
  | c, .node _ fields => fieldsAbove c fields

def fieldsAbove : ℕ → Fields Head → Option ℕ
  | _, .nil => none
  | c, .cons d t rest => omin (above (c + d) t) (fieldsAbove c rest)

end

mutual

/-- **`above` is the least free index past the cutoff.** -/
theorem above_isLeast (c : ℕ) (t : Term Head) :
    IsLeast (fun j => freeAt t (c + j) = true) (above c t) := by
  cases t with
  | idx n =>
      by_cases h : c ≤ n
      · simp only [above, h, if_true, IsLeast, freeAt_idx, decide_eq_true_eq]
        exact ⟨by omega, fun j' e => by omega⟩
      · simp only [above, h, if_false, IsLeast, freeAt_idx, decide_eq_true_eq]
        intro j e; omega
  | node head fields =>
      simp only [above, freeAt_node]
      exact fields_above_isLeast c fields

theorem fields_above_isLeast (c : ℕ) (fields : Fields Head) :
    IsLeast (fun j => fieldsFreeAt fields (c + j) = true) (fieldsAbove c fields) := by
  cases fields with
  | nil => simp [fieldsAbove, IsLeast]
  | cons d t rest =>
      simp only [fieldsAbove]
      refine IsLeast.congr ?_ (omin_isLeast (above_isLeast (c + d) t) (fields_above_isLeast c rest))
      intro j
      simp only [fieldsFreeAt_cons, Bool.or_eq_true]
      rw [show c + d + j = c + j + d by omega]

end

theorem above_eq_none_iff (c : ℕ) (t : Term Head) :
    above c t = none ↔ ∀ j, freeAt t (c + j) = false := by
  constructor
  · intro h j
    have := above_isLeast c t
    rw [h] at this
    cases f : freeAt t (c + j)
    · rfl
    · exact absurd f (this j)
  · intro h
    exact (above_isLeast c t).unique (fun j (f : freeAt t (c + j) = true) => by rw [h j] at f; cases f)

theorem closed_iff_above_zero (t : Term Head) : Closed t ↔ above 0 t = none := by
  rw [above_eq_none_iff]
  simp [Closed]

/-! ## Lowering -/

mutual

/-- `lower c m t` moves every index at or past `c + m` down by `m`. It undoes `lift c m`. -/
def lower (c m : ℕ) : Term Head → Term Head
  | .idx n => if n < c then .idx n else .idx (n - m)
  | .node head fields => .node head (fieldsLower c m fields)

def fieldsLower (c m : ℕ) : Fields Head → Fields Head
  | .nil => .nil
  | .cons d t rest => .cons d (lower (c + d) m t) (fieldsLower c m rest)

end

mutual

/-- **Lowering undoes a shift.** -/
theorem lower_lift (c m : ℕ) (t : Term Head) : lower c m (Term.lift c m t) = t := by
  cases t with
  | idx n =>
      by_cases h : n < c
      · simp [Term.lift, lower, h]
      · have h' : ¬ n + m < c := by omega
        simp [Term.lift, lower, h, h']
  | node head fields => simp [Term.lift, lower, fields_lower_lift c m fields]

theorem fields_lower_lift (c m : ℕ) (fields : Fields Head) :
    fieldsLower c m (Term.Fields.lift c m fields) = fields := by
  cases fields with
  | nil => rfl
  | cons d t rest => simp [Term.Fields.lift, fieldsLower, lower_lift (c + d) m t,
      fields_lower_lift c m rest]

end

mutual

/-- **A shift undoes lowering** when no index in `[c, c + m)` is free. -/
theorem lift_lower (c m : ℕ) (t : Term Head) (gap : ∀ j < m, freeAt t (c + j) = false) :
    Term.lift c m (lower c m t) = t := by
  cases t with
  | idx n =>
      by_cases h : n < c
      · simp [Term.lift, lower, h]
      · have big : c + m ≤ n := by
          by_contra small
          have := gap (n - c) (by omega)
          simp only [freeAt_idx, decide_eq_false_iff_not] at this
          omega
        have h' : ¬ n - m < c := by omega
        simp only [lower, h, if_false, Term.lift, h', Term.idx.injEq]
        omega
  | node head fields =>
      simp only [lower, Term.lift]
      rw [fields_lift_lower c m fields (fun j lt => by simpa using gap j lt)]

theorem fields_lift_lower (c m : ℕ) (fields : Fields Head)
    (gap : ∀ j < m, fieldsFreeAt fields (c + j) = false) :
    Term.Fields.lift c m (fieldsLower c m fields) = fields := by
  cases fields with
  | nil => rfl
  | cons d t rest =>
      simp only [fieldsLower, Term.Fields.lift]
      have gapT : ∀ j < m, freeAt t (c + d + j) = false := by
        intro j lt
        have := gap j lt
        simp only [fieldsFreeAt_cons, Bool.or_eq_false_iff] at this
        rw [show c + d + j = c + j + d by omega]; exact this.1
      have gapR : ∀ j < m, fieldsFreeAt rest (c + j) = false := by
        intro j lt
        have := gap j lt
        simp only [fieldsFreeAt_cons, Bool.or_eq_false_iff] at this
        exact this.2
      rw [lift_lower (c + d) m t gapT, fields_lift_lower c m rest gapR]

end

/-- The free indices of a lowered tree, when the gap is empty. -/
theorem freeAt_lower {c m : ℕ} {t : Term Head} (gap : ∀ j < m, freeAt t (c + j) = false) (i : ℕ) :
    freeAt (lower c m t) i = true ↔ (i < c ∧ freeAt t i = true) ∨ (c ≤ i ∧ freeAt t (i + m) = true) := by
  have back := lift_lower c m t gap
  constructor
  · intro f
    by_cases small : i < c
    · left
      refine ⟨small, ?_⟩
      rw [← back]
      exact (freeAt_lift c m _ i).mpr (Or.inl ⟨small, f⟩)
    · right
      refine ⟨by omega, ?_⟩
      rw [← back]
      exact (freeAt_lift c m _ (i + m)).mpr (Or.inr ⟨by omega, by rwa [Nat.add_sub_cancel]⟩)
  · rintro (⟨small, f⟩ | ⟨le, f⟩)
    · rw [← back] at f
      rcases (freeAt_lift c m _ i).mp f with ⟨_, g⟩ | ⟨big, _⟩
      · exact g
      · omega
    · rw [← back] at f
      rcases (freeAt_lift c m _ (i + m)).mp f with ⟨lt, _⟩ | ⟨_, g⟩
      · omega
      · rwa [Nat.add_sub_cancel] at g

/-! ## Tight trees -/

/-- A tree is **tight** when it is closed or uses index `0`: no shift can be pulled out of it. -/
def Tight (t : Term Head) : Prop := Closed t ∨ freeAt t 0 = true

/-- **Every tree is a shift of a tight tree**: with `m` its least free index,
`t = lift 0 m (lower 0 m t)` and `lower 0 m t` uses index `0`. -/
theorem tighten {t : Term Head} {m : ℕ} (least : above 0 t = some m) :
    Term.lift 0 m (lower 0 m t) = t ∧ freeAt (lower 0 m t) 0 = true := by
  have spec := above_isLeast 0 t
  rw [least] at spec
  have gap : ∀ j < m, freeAt t (0 + j) = false := by
    intro j lt
    cases f : freeAt t (0 + j)
    · rfl
    · exact absurd (spec.2 j f) (by omega)
  refine ⟨lift_lower 0 m t gap, ?_⟩
  exact (freeAt_lower gap 0).mpr (Or.inr ⟨le_refl 0, by simpa using spec.1⟩)

/-- A tight tree that is not closed has least free index `0`. -/
theorem above_zero_of_tight {t : Term Head} (tight : Tight t) (open_ : ¬ Closed t) :
    above 0 t = some 0 := by
  rcases tight with closed | uses
  · exact absurd closed open_
  · exact (above_isLeast 0 t).unique ⟨by simpa using uses, fun _ _ => Nat.zero_le _⟩

/-- The least free index of a shift of a tight open tree is the shift. -/
theorem above_lift_tight {t : Term Head} (tight : Tight t) (open_ : ¬ Closed t) (k : ℕ) :
    above 0 (Term.lift 0 k t) = some k := by
  have uses : freeAt t 0 = true := tight.resolve_left open_
  refine (above_isLeast 0 _).unique ⟨?_, fun j f => ?_⟩
  · exact (freeAt_lift_zero k t (0 + k)).mpr ⟨by omega, by simpa using uses⟩
  · exact ((freeAt_lift_zero k t (0 + j)).mp f).1.trans (by omega)

/-! ## Shifts and lowering past each other -/

mutual

/-- Lowering past a shift that clears the gap: the shift shrinks. -/
theorem lower_lift_ge (e c k m : ℕ) (big : c + m ≤ k) (t : Term Head) :
    lower (e + c) m (Term.lift e k t) = Term.lift e (k - m) t := by
  cases t with
  | idx n =>
      by_cases h : n < e
      · have h' : n < e + c := by omega
        simp [Term.lift, lower, h, h']
      · have h' : ¬ n + k < e + c := by omega
        simp only [Term.lift, h, if_false, lower, h', Term.idx.injEq]
        omega
  | node head fields =>
      simp [Term.lift, lower, fields_lower_lift_ge e c k m big fields]

theorem fields_lower_lift_ge (e c k m : ℕ) (big : c + m ≤ k) (fields : Fields Head) :
    fieldsLower (e + c) m (Term.Fields.lift e k fields) = Term.Fields.lift e (k - m) fields := by
  cases fields with
  | nil => rfl
  | cons d t rest =>
      simp only [Term.Fields.lift, fieldsLower]
      rw [show e + c + d = (e + d) + c by omega, lower_lift_ge (e + d) c k m big t,
        fields_lower_lift_ge e c k m big rest]

end

mutual

/-- Lowering past a shift below the cutoff: lower inside, then shift. -/
theorem lower_lift_lt (e c k m : ℕ) (small : k ≤ c) (t : Term Head)
    (gap : ∀ j < m, freeAt t (e + (c - k) + j) = false) :
    lower (e + c) m (Term.lift e k t) = Term.lift e k (lower (e + (c - k)) m t) := by
  cases t with
  | idx n =>
      by_cases h : n < e
      · have h1 : n < e + c := by omega
        have h2 : n < e + (c - k) := by omega
        simp [Term.lift, lower, h, h1, h2]
      · by_cases h' : n < e + (c - k)
        · have h1 : n + k < e + c := by omega
          simp [Term.lift, lower, h, h', h1]
        · have big : e + (c - k) + m ≤ n := by
            by_contra less
            have := gap (n - (e + (c - k))) (by omega)
            simp only [freeAt_idx, decide_eq_false_iff_not] at this
            omega
          have h1 : ¬ n + k < e + c := by omega
          have h2 : ¬ n - m < e := by omega
          simp only [Term.lift, h, if_false, lower, h1, h', h2, Term.idx.injEq]
          omega
  | node head fields =>
      simp only [Term.lift, lower]
      rw [fields_lower_lift_lt e c k m small fields (fun j lt => by simpa using gap j lt)]

theorem fields_lower_lift_lt (e c k m : ℕ) (small : k ≤ c) (fields : Fields Head)
    (gap : ∀ j < m, fieldsFreeAt fields (e + (c - k) + j) = false) :
    fieldsLower (e + c) m (Term.Fields.lift e k fields) =
      Term.Fields.lift e k (fieldsLower (e + (c - k)) m fields) := by
  cases fields with
  | nil => rfl
  | cons d t rest =>
      simp only [Term.Fields.lift, fieldsLower]
      have gapT : ∀ j < m, freeAt t ((e + d) + (c - k) + j) = false := by
        intro j lt
        have := gap j lt
        simp only [fieldsFreeAt_cons, Bool.or_eq_false_iff] at this
        rw [show e + d + (c - k) + j = e + (c - k) + j + d by omega]; exact this.1
      have gapR : ∀ j < m, fieldsFreeAt rest (e + (c - k) + j) = false := by
        intro j lt
        have := gap j lt
        simp only [fieldsFreeAt_cons, Bool.or_eq_false_iff] at this
        exact this.2
      rw [show e + c + d = (e + d) + c by omega, lower_lift_lt (e + d) c k m small t gapT,
        show e + (c - k) + d = (e + d) + (c - k) by omega, fields_lower_lift_lt e c k m small rest gapR]

end

/-! ## Opening a binder past a shift -/

mutual

/-- Opening index `e + d` of a tree shifted by `k ≤ d` past `e`: open inside, then shift. -/
theorem instantiateAt_lift_le (r : Term Head) (e d k : ℕ) (le : k ≤ d) (t : Term Head) :
    Term.instantiateAt (e + d) r (Term.lift e k t) =
      Term.lift e k (Term.instantiateAt (e + (d - k)) r t) := by
  cases t with
  | idx n =>
      by_cases h : n < e
      · have h1 : n < e + d := by omega
        have h2 : n < e + (d - k) := by omega
        simp [Term.lift, Term.instantiateAt, h, h1, h2]
      · by_cases lt : n < e + (d - k)
        · have h1 : n + k < e + d := by omega
          simp [Term.lift, Term.instantiateAt, h, lt, h1]
        · by_cases eq : n = e + (d - k)
          · subst eq
            have h0 : ¬ e + (d - k) < e := by omega
            have h2 : e + (d - k) + k = e + d := by omega
            have lhs : Term.lift e k (.idx (e + (d - k)) : Term Head) = .idx (e + d) := by
              simp only [Term.lift, h0, if_false, h2]
            have l1 : Term.instantiateAt (e + d) r (.idx (e + d) : Term Head) =
                Term.lift 0 (e + d) r := by
              simp [Term.instantiateAt]
            have l2 : Term.instantiateAt (e + (d - k)) r (.idx (e + (d - k)) : Term Head) =
                Term.lift 0 (e + (d - k)) r := by
              simp [Term.instantiateAt]
            rw [lhs, l1, l2, lift_lift_le k (e + (d - k)) (Nat.zero_le e) (by omega) r, h2]
          · have h1 : ¬ n + k < e + d := by omega
            have h2 : ¬ n + k = e + d := by omega
            have h3 : ¬ n - 1 < e := by omega
            simp only [Term.lift, h, if_false, Term.instantiateAt, h1, h2, lt, eq, h3,
              Term.idx.injEq]
            omega
  | node head fields =>
      simp only [Term.lift, Term.instantiateAt]
      rw [fields_instantiateAt_lift_le r e d k le fields]

theorem fields_instantiateAt_lift_le (r : Term Head) (e d k : ℕ) (le : k ≤ d)
    (fields : Fields Head) :
    Term.Fields.instantiateAt (e + d) r (Term.Fields.lift e k fields) =
      Term.Fields.lift e k (Term.Fields.instantiateAt (e + (d - k)) r fields) := by
  cases fields with
  | nil => rfl
  | cons fd t rest =>
      simp only [Term.Fields.lift, Term.Fields.instantiateAt]
      rw [show e + d + fd = (e + fd) + d by omega, instantiateAt_lift_le r (e + fd) d k le t,
        show e + (d - k) + fd = (e + fd) + (d - k) by omega,
        fields_instantiateAt_lift_le r e d k le rest]

end

mutual

/-- Opening an index that a shift jumped over: the shift shrinks by one. -/
theorem instantiateAt_lift_gt (r : Term Head) (e d k : ℕ) (gt : d < k) (t : Term Head) :
    Term.instantiateAt (e + d) r (Term.lift e k t) = Term.lift e (k - 1) t := by
  cases t with
  | idx n =>
      by_cases h : n < e
      · have h1 : n < e + d := by omega
        simp [Term.lift, Term.instantiateAt, h, h1]
      · have h1 : ¬ n + k < e + d := by omega
        have h2 : ¬ n + k = e + d := by omega
        simp only [Term.lift, h, if_false, Term.instantiateAt, h1, h2, Term.idx.injEq]
        omega
  | node head fields =>
      simp only [Term.lift, Term.instantiateAt]
      rw [fields_instantiateAt_lift_gt r e d k gt fields]

theorem fields_instantiateAt_lift_gt (r : Term Head) (e d k : ℕ) (gt : d < k)
    (fields : Fields Head) :
    Term.Fields.instantiateAt (e + d) r (Term.Fields.lift e k fields) =
      Term.Fields.lift e (k - 1) fields := by
  cases fields with
  | nil => rfl
  | cons fd t rest =>
      simp only [Term.Fields.lift, Term.Fields.instantiateAt]
      rw [show e + d + fd = (e + fd) + d by omega, instantiateAt_lift_gt r (e + fd) d k gt t,
        fields_instantiateAt_lift_gt r e d k gt rest]

end

mutual

/-- Opening an index past every free index changes nothing. -/
theorem instantiateAt_of_supported (r : Term Head) (d : ℕ) (t : Term Head)
    (supported : Term.supportedAt d t = true) : Term.instantiateAt d r t = t := by
  cases t with
  | idx n =>
      simp only [Term.supportedAt, decide_eq_true_eq] at supported
      simp [Term.instantiateAt, supported]
  | node head fields =>
      simp only [Term.instantiateAt]
      rw [fields_instantiateAt_of_supported r d fields supported]

theorem fields_instantiateAt_of_supported (r : Term Head) (d : ℕ) (fields : Fields Head)
    (supported : Term.Fields.supportedAt d fields = true) :
    Term.Fields.instantiateAt d r fields = fields := by
  cases fields with
  | nil => rfl
  | cons fd t rest =>
      simp only [Term.Fields.supportedAt, Bool.and_eq_true] at supported
      simp only [Term.Fields.instantiateAt]
      rw [instantiateAt_of_supported r (d + fd) t supported.1,
        fields_instantiateAt_of_supported r d rest supported.2]

end

/-- Opening any index of a closed tree changes nothing. -/
theorem instantiateAt_of_closed {t : Term Head} (closed : Closed t) (d : ℕ) (r : Term Head) :
    Term.instantiateAt d r t = t :=
  instantiateAt_of_supported r d t
    (Term.supportedAt_mono 0 d (Nat.zero_le d) t ((closed_iff_supportedAt_zero t).mp closed))

/-! ## Controls -/

namespace Controls

/-- One binary head, standing for application. -/
abbrev T := Term Unit

/-- `app f x` with no binders over either field. -/
def app (f x : T) : T := .node () (.cons 0 f (.cons 0 x .nil))

/-- `lam b`: one binder over its single field. -/
def lam (b : T) : T := .node () (.cons 1 b .nil)

/-- Positive: `λ. (0 2)` is the shift by one of the tight `λ. (0 1)`. -/
theorem tighten_example : Term.lift 0 1 (lam (app (.idx 0) (.idx 1))) = lam (app (.idx 0) (.idx 2)) := by
  rfl

/-- Negative: a shift is not the identity on an open tree. -/
theorem shift_moves_open : Term.lift 0 1 (.idx 0 : T) ≠ .idx 0 := by
  intro h; cases h

/-- Positive: `λ. (0 1)` uses the root's index `0`, so it is tight. -/
theorem tight_example : freeAt (lam (app (.idx 0) (.idx 1))) 0 = true := by
  rfl

/-- Negative: `λ. (0 2)` does not use the root's index `0`; its least free index is `1`. -/
theorem untight_example : above 0 (lam (app (.idx 0) (.idx 2))) = some 1 := by
  rfl

end Controls

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms
