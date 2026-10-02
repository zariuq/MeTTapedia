import Mettapedia.TypeTheory.UniverseLevel.Offsets

/-!
# Ordinal notations below ε₀ as universe levels

Cantor normal forms `ω ^ e₁ * (n₁ + 1) + ⋯ + ω ^ eₖ * (nₖ + 1)`, with strictly
decreasing exponents that are themselves normal forms, are the standard notations for the
ordinals below ε₀. As a tree, `oadd e n a` stands for `ω ^ e * (n + 1) + a`. Trees are
compared lexicographically: exponent, then coefficient, then tail, with `zero` least. On
all trees this comparison is a strict total order; on normal forms it is the order of the
ordinals denoted, as `NotationComparison` checks against Mathlib's ordinal notations.

The normal forms are a level order, and everything here is constructive: the comparison,
the normal-form test and the order are decidable, and well-foundedness is proved by
building accessibility directly. If every normal form below `ω ^ e` is accessible, then
`ω ^ e * (n + 1) + a` is accessible for every accessible `a`, by induction on `n` and then
on `a`: an element below it either lies below `ω ^ e`, or shares the exponent and has a
smaller coefficient, or shares both and has a smaller tail. Induction along `e` then makes
every normal form below `ω ^ e` accessible whenever `e` is, and structural induction on
normal forms finishes.

The successor adds one at the end of a normal form; it is the least level strictly above.
The predecessor removes one from a finite last term, so it is computed whether a level is
a successor: the levels have predecessors, and `ω` is a limit.

Positive examples: finite levels lie below `ω`, `ω` below its successor, `max`
computes, and the table of interpretations reads finite levels below `ω`. Negative
examples: `1 + ω` written with increasing exponents is not a normal form, the comparison
places that tree strictly between `1` and `2` although no level lies there (it denotes
`ω`), and `ω` is the successor of no level.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniverseLevel

/-- Ordinal notation trees: `zero` is `0`, and `oadd e n a` is `ω ^ e * (n + 1) + a`. -/
inductive Cnf where
  | zero
  | oadd (e : Cnf) (n : Nat) (a : Cnf)
  deriving DecidableEq, Repr

namespace Cnf

/-! ## Lexicographic comparison -/

/-- Lexicographic comparison of trees: `zero` is least, and two sums compare by exponent,
then coefficient, then tail. -/
def cmp : Cnf → Cnf → Ordering
  | zero, zero => .eq
  | zero, oadd _ _ _ => .lt
  | oadd _ _ _, zero => .gt
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂ => (cmp e₁ e₂).then ((compare n₁ n₂).then (cmp a₁ a₂))

/-- The comparison of two sums. -/
theorem cmp_oadd (e₁ : Cnf) (n₁ : Nat) (a₁ e₂ : Cnf) (n₂ : Nat) (a₂ : Cnf) :
    cmp (oadd e₁ n₁ a₁) (oadd e₂ n₂ a₂) =
      (cmp e₁ e₂).then ((compare n₁ n₂).then (cmp a₁ a₂)) :=
  rfl

/-- Nothing compares below `zero`. -/
theorem cmp_zero_right (x : Cnf) : cmp x zero ≠ .lt := by
  cases x <;> exact nofun

/-- `zero` compares above nothing. -/
theorem cmp_zero_left (x : Cnf) : cmp zero x ≠ .gt := by
  cases x <;> exact nofun

/-- Swapping the arguments swaps the comparison. -/
theorem cmp_swap : ∀ x y : Cnf, (cmp x y).swap = cmp y x
  | zero, zero => rfl
  | zero, oadd _ _ _ => rfl
  | oadd _ _ _, zero => rfl
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂ => by
    rw [cmp_oadd, cmp_oadd, Ordering.swap_then, Ordering.swap_then, cmp_swap e₁ e₂,
      Nat.compare_swap, cmp_swap a₁ a₂]

/-- Every tree compares equal to itself. -/
theorem cmp_self : ∀ x : Cnf, cmp x x = .eq
  | zero => rfl
  | oadd e n a => by
    rw [cmp_oadd, cmp_self e, cmp_self a, Nat.compare_eq_eq.mpr rfl]
    rfl

/-- The comparison says `eq` only on equal trees. -/
theorem eq_of_cmp_eq : ∀ {x y : Cnf}, cmp x y = .eq → x = y
  | zero, zero, _ => rfl
  | zero, oadd _ _ _, h => nomatch h
  | oadd _ _ _, zero, h => nomatch h
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h => by
    obtain ⟨he, h⟩ := Ordering.then_eq_eq.mp h
    obtain ⟨hn, ha⟩ := Ordering.then_eq_eq.mp h
    rw [eq_of_cmp_eq he, Nat.compare_eq_eq.mp hn, eq_of_cmp_eq ha]

/-- The comparison says `eq` exactly on equal trees. -/
theorem cmp_eq_iff {x y : Cnf} : cmp x y = .eq ↔ x = y :=
  ⟨eq_of_cmp_eq, fun h => h ▸ cmp_self x⟩

/-- `x` compares above `y` exactly when `y` compares below `x`. -/
theorem cmp_eq_gt {x y : Cnf} : cmp x y = .gt ↔ cmp y x = .lt := by
  rw [← cmp_swap x y, Ordering.swap_eq_lt]

/-- Lexicographic refinement keeps the strict comparison transitive: if the first
components compare transitively and `eq` only on equals, and the second components compare
transitively, then so do the pairs. -/
theorem then_lt_trans {α : Sort _} {c : α → α → Ordering} (hc : ∀ {x y}, c x y = .eq → x = y)
    {x y z : α} (hxz : c x y = .lt → c y z = .lt → c x z = .lt) {p q r : Ordering}
    (hpr : p = .lt → q = .lt → r = .lt) (h₁ : (c x y).then p = .lt)
    (h₂ : (c y z).then q = .lt) : (c x z).then r = .lt := by
  rcases Ordering.then_eq_lt.mp h₁ with hxy | ⟨hxy, hp⟩
  · rcases Ordering.then_eq_lt.mp h₂ with hyz | ⟨hyz, _⟩
    · rw [hxz hxy hyz]
      rfl
    · rw [← hc hyz, hxy]
      rfl
  · rcases Ordering.then_eq_lt.mp h₂ with hyz | ⟨hyz, hq⟩
    · rw [hc hxy, hyz]
      rfl
    · rw [hc hxy, hyz]
      exact hpr hp hq

/-- Composing two comparisons that do not say `gt` gives one that does not say `gt`. -/
theorem then_ne_gt {o₁ o₂ : Ordering} (h₁ : o₁ ≠ .gt) (h₂ : o₂ ≠ .gt) : o₁.then o₂ ≠ .gt := by
  cases o₁ with
  | lt => exact nofun
  | eq => exact h₂
  | gt => exact absurd rfl h₁

/-- The strict comparison is transitive. -/
theorem cmp_lt_trans : ∀ {x y z : Cnf}, cmp x y = .lt → cmp y z = .lt → cmp x z = .lt
  | zero, zero, _, h, _ => nomatch h
  | zero, oadd _ _ _, zero, _, h => nomatch h
  | zero, oadd _ _ _, oadd _ _ _, _, _ => rfl
  | oadd _ _ _, zero, _, h, _ => nomatch h
  | oadd _ _ _, oadd _ _ _, zero, _, h => nomatch h
  | oadd e₁ _ a₁, oadd e₂ _ a₂, oadd e₃ _ a₃, h₁, h₂ =>
    then_lt_trans eq_of_cmp_eq (cmp_lt_trans (x := e₁) (y := e₂) (z := e₃))
      (then_lt_trans Nat.compare_eq_eq.mp
        (fun h h' => Nat.compare_eq_lt.mpr
          (Nat.lt_trans (Nat.compare_eq_lt.mp h) (Nat.compare_eq_lt.mp h')))
        (cmp_lt_trans (x := a₁) (y := a₂) (z := a₃))) h₁ h₂

/-! ## Normal forms -/

/-- The tree `ω ^ e`. -/
def omegaPow (e : Cnf) : Cnf := oadd e 0 zero

/-- Cantor normal form: `zero`, or `ω ^ e * (n + 1) + a` with `e` and `a` normal and the
tail `a` below `ω ^ e`. -/
inductive NF : Cnf → Prop where
  | zero : NF zero
  | oadd {e a : Cnf} (n : Nat) : NF e → NF a → cmp a (omegaPow e) = .lt → NF (oadd e n a)

/-- The exponent of a normal form is normal. -/
theorem NF.fst {e : Cnf} {n : Nat} {a : Cnf} : NF (Cnf.oadd e n a) → NF e
  | .oadd _ h _ _ => h

/-- The tail of a normal form is normal. -/
theorem NF.snd {e : Cnf} {n : Nat} {a : Cnf} : NF (Cnf.oadd e n a) → NF a
  | .oadd _ _ h _ => h

/-- The tail of a normal form lies below `ω ^ e`. -/
theorem NF.lt {e : Cnf} {n : Nat} {a : Cnf} :
    NF (Cnf.oadd e n a) → cmp a (omegaPow e) = .lt
  | .oadd _ _ _ h => h

/-- The conditions for a sum to be a normal form. -/
theorem nf_oadd_iff {e : Cnf} {n : Nat} {a : Cnf} :
    NF (oadd e n a) ↔ NF e ∧ NF a ∧ cmp a (omegaPow e) = .lt :=
  ⟨fun h => ⟨h.fst, h.snd, h.lt⟩, fun ⟨h₁, h₂, h₃⟩ => .oadd n h₁ h₂ h₃⟩

/-- Being a normal form is decidable, by structural recursion. -/
instance decidableNF : DecidablePred NF
  | zero => isTrue .zero
  | oadd e _ a =>
    have := decidableNF e
    have := decidableNF a
    decidable_of_iff _ nf_oadd_iff.symm

/-- A sum lies below `ω ^ e` exactly when its exponent lies below `e`. -/
theorem oadd_lt_omegaPow {e e' : Cnf} {n' : Nat} {a' : Cnf} :
    cmp (oadd e' n' a') (omegaPow e) = .lt ↔ cmp e' e = .lt := by
  refine ⟨fun h => ?_, fun h => by rw [omegaPow, cmp_oadd, h]; rfl⟩
  rcases Ordering.then_eq_lt.mp h with h | ⟨_, h⟩
  · exact h
  · rcases Ordering.then_eq_lt.mp h with h | ⟨_, h⟩
    · exact absurd (Nat.compare_eq_lt.mp h) (Nat.not_lt_zero n')
    · exact absurd h (cmp_zero_right a')

/-- Below `ω ^ 0 = 1` there is only `zero`. -/
theorem eq_zero_of_lt_omegaPow_zero {a : Cnf} (h : cmp a (omegaPow zero) = .lt) : a = zero := by
  cases a with
  | zero => rfl
  | oadd e _ _ => exact absurd (oadd_lt_omegaPow.mp h) (cmp_zero_right e)

/-! ## Numerals, `ω` and the successor -/

/-- The natural number `n`: `0` is `zero`, and `k + 1` is `ω ^ 0 * (k + 1)`. -/
def ofNat : Nat → Cnf
  | 0 => zero
  | k + 1 => oadd zero k zero

/-- The tree `ω = ω ^ 1`. -/
def omega : Cnf := oadd (oadd zero 0 zero) 0 zero

/-- Adding one at the end: the finite last term grows by one, or a last term `1` is added. -/
def succ : Cnf → Cnf
  | zero => oadd zero 0 zero
  | oadd zero n a => oadd zero (n + 1) a
  | oadd (oadd e' n' a') n a => oadd (oadd e' n' a') n (succ a)

/-- The successor of a numeral is the next numeral. -/
theorem succ_ofNat : ∀ n : Nat, succ (ofNat n) = ofNat (n + 1)
  | 0 => rfl
  | _ + 1 => rfl

/-- Numerals are normal forms. -/
theorem nf_ofNat : ∀ n : Nat, NF (ofNat n)
  | 0 => .zero
  | k + 1 => .oadd k .zero .zero rfl

/-- `ω` is a normal form. -/
theorem nf_omega : NF omega := .oadd 0 (.oadd 0 .zero .zero rfl) .zero rfl

/-- Below a positive power `ω ^ e`, the successor stays below `ω ^ e`: it keeps the
leading exponent of a sum. -/
theorem succ_lt_omegaPow {e' : Cnf} {n' : Nat} {a' a : Cnf}
    (h : cmp a (omegaPow (oadd e' n' a')) = .lt) :
    cmp (succ a) (omegaPow (oadd e' n' a')) = .lt := by
  cases a with
  | zero => rfl
  | oadd e _ _ => cases e <;> exact oadd_lt_omegaPow.mpr (oadd_lt_omegaPow.mp h)

/-- The successor of a normal form is a normal form. -/
theorem nf_succ : ∀ {x : Cnf}, NF x → NF (succ x)
  | zero, _ => .oadd 0 .zero .zero rfl
  | oadd zero n _, h => .oadd (n + 1) h.fst h.snd h.lt
  | oadd (oadd _ _ _) n _, h => .oadd n h.fst (nf_succ h.snd) (succ_lt_omegaPow h.lt)

/-- Every tree compares below its successor. -/
theorem cmp_succ : ∀ x : Cnf, cmp x (succ x) = .lt
  | zero => rfl
  | oadd zero n a => by
    rw [succ, cmp_oadd, Nat.compare_eq_lt.mpr (Nat.lt_succ_self n)]
    rfl
  | oadd (oadd e' n' a') n a => by
    rw [succ, cmp_oadd, cmp_self, Nat.compare_eq_eq.mpr rfl, cmp_succ a]
    rfl

/-- The successor is the least normal form strictly above: between a normal form and its
successor there is nothing. -/
theorem succ_le_of_lt : ∀ {x y : Cnf}, NF x → NF y → cmp x y = .lt → cmp (succ x) y ≠ .gt
  | zero, zero, _, _, h => nomatch h
  | zero, oadd e' n' a', _, _, _ => by
    rw [succ, cmp_oadd]
    exact then_ne_gt (cmp_zero_left e')
      (then_ne_gt (Nat.compare_ne_gt.mpr (Nat.zero_le n')) (cmp_zero_left a'))
  | oadd _ _ _, zero, _, _, h => nomatch h
  | oadd zero n a, oadd e' n' a', hx, hy, h => by
    cases e' with
    | oadd _ _ _ => rw [succ, cmp_oadd]; exact nofun
    | zero =>
      obtain rfl := eq_zero_of_lt_omegaPow_zero hx.lt
      obtain rfl := eq_zero_of_lt_omegaPow_zero hy.lt
      rcases Ordering.then_eq_lt.mp h with h | ⟨_, h⟩
      · exact nomatch h
      · rcases Ordering.then_eq_lt.mp h with h | ⟨_, h⟩
        · rw [succ, cmp_oadd]
          exact then_ne_gt nofun
            (then_ne_gt (Nat.compare_ne_gt.mpr (Nat.compare_eq_lt.mp h)) nofun)
        · exact nomatch h
  | oadd (oadd e₁ n₁ a₁) n a, oadd e' n' a', hx, hy, h => by
    rw [succ, cmp_oadd]
    rcases Ordering.then_eq_lt.mp h with he | ⟨he, h⟩
    · rw [he]; exact nofun
    · rw [he]
      rcases Ordering.then_eq_lt.mp h with hn | ⟨hn, ha⟩
      · rw [hn]; exact nofun
      · rw [hn]
        exact succ_le_of_lt hx.snd hy.snd ha

/-! ## The predecessor -/

/-- The predecessor of a successor tree: a finite last term shrinks by one, or disappears
when it is `1`. Trees whose last term is not finite have none. -/
def pred? : Cnf → Option Cnf
  | zero => none
  | oadd zero 0 a => some a
  | oadd zero (n + 1) a => some (oadd zero n a)
  | oadd (oadd e' n' a') n a => (pred? a).map (oadd (oadd e' n' a') n)

/-- The predecessor of a successor is the tree itself. -/
theorem pred?_succ : ∀ x : Cnf, pred? (succ x) = some x
  | zero => rfl
  | oadd zero _ _ => rfl
  | oadd (oadd e' n' a') n a => by
    show (pred? (succ a)).map (oadd (oadd e' n' a') n) = some (oadd (oadd e' n' a') n a)
    rw [pred?_succ a]
    rfl

/-- A normal form with a predecessor is the successor of it. -/
theorem eq_succ_of_pred?_eq_some : ∀ {x p : Cnf}, NF x → pred? x = some p → x = succ p
  | zero, _, _, h => nomatch h
  | oadd zero 0 a, p, hx, h => by
    obtain rfl : a = p := Option.some.inj h
    obtain rfl := eq_zero_of_lt_omegaPow_zero hx.lt
    rfl
  | oadd zero (n + 1) a, p, _, h => by
    obtain rfl : oadd zero n a = p := Option.some.inj h
    rfl
  | oadd (oadd e' n' a') n a, p, hx, h => by
    have h' : (pred? a).map (oadd (oadd e' n' a') n) = some p := h
    cases hq : pred? a with
    | none => rw [hq] at h'; exact nomatch h'
    | some q =>
      rw [hq] at h'
      obtain rfl : oadd (oadd e' n' a') n q = p := Option.some.inj h'
      rw [eq_succ_of_pred?_eq_some hx.snd hq]
      rfl

/-- The predecessor of a normal form is a normal form. -/
theorem nf_of_pred?_eq_some : ∀ {x p : Cnf}, NF x → pred? x = some p → NF p
  | zero, _, _, h => nomatch h
  | oadd zero 0 a, p, hx, h => by
    obtain rfl : a = p := Option.some.inj h
    exact hx.snd
  | oadd zero (n + 1) a, p, hx, h => by
    obtain rfl : oadd zero n a = p := Option.some.inj h
    exact .oadd n hx.fst hx.snd hx.lt
  | oadd (oadd e' n' a') n a, p, hx, h => by
    have h' : (pred? a).map (oadd (oadd e' n' a') n) = some p := h
    cases hq : pred? a with
    | none => rw [hq] at h'; exact nomatch h'
    | some q =>
      rw [hq] at h'
      obtain rfl : oadd (oadd e' n' a') n q = p := Option.some.inj h'
      have ha : a = succ q := eq_succ_of_pred?_eq_some hx.snd hq
      refine .oadd n hx.fst (nf_of_pred?_eq_some hx.snd hq) ?_
      exact cmp_lt_trans (by rw [ha]; exact cmp_succ q) hx.lt

/-! ## Well-foundedness -/

/-- `y` is a normal form below `x`. -/
def NFLt (y x : Cnf) : Prop := NF y ∧ cmp y x = .lt

/-- Nothing lies below `zero`. -/
theorem acc_zero : Acc NFLt zero :=
  .intro _ fun y h => absurd h.2 (cmp_zero_right y)

/-- If every normal form below `ω ^ e` is accessible, then `ω ^ e * (n + 1) + a` is
accessible for every accessible `a`. -/
theorem acc_oadd {e : Cnf} (H : ∀ y, NF y → cmp y (omegaPow e) = .lt → Acc NFLt y)
    (n : Nat) : ∀ {a : Cnf}, Acc NFLt a → Acc NFLt (oadd e n a) := by
  induction n using Nat.strongRecOn with
  | ind n ihn =>
    intro a ha
    induction ha with
    | intro a _ iha =>
      refine .intro _ fun z hz => ?_
      obtain ⟨hzn, hlt⟩ := hz
      cases z with
      | zero => exact acc_zero
      | oadd e₂ n₂ a₂ =>
        rcases Ordering.then_eq_lt.mp hlt with he | ⟨he, hlt'⟩
        · exact H _ hzn (oadd_lt_omegaPow.mpr he)
        · obtain rfl := eq_of_cmp_eq he
          rcases Ordering.then_eq_lt.mp hlt' with hn | ⟨hn, ha⟩
          · exact ihn n₂ (Nat.compare_eq_lt.mp hn) (H a₂ hzn.snd hzn.lt)
          · obtain rfl := Nat.compare_eq_eq.mp hn
            exact iha a₂ ⟨hzn.snd, ha⟩

/-- If `e` is accessible, then so is every normal form below `ω ^ e`. -/
theorem acc_of_lt_omegaPow {e : Cnf} (he : Acc NFLt e) :
    ∀ y, NF y → cmp y (omegaPow e) = .lt → Acc NFLt y := by
  induction he with
  | intro e _ ihe =>
    intro y hy hlt
    cases y with
    | zero => exact acc_zero
    | oadd e' n' a' =>
      have h : NFLt e' e := ⟨hy.fst, oadd_lt_omegaPow.mp hlt⟩
      exact acc_oadd (ihe e' h) n' (ihe e' h a' hy.snd hy.lt)

/-- Every normal form is accessible. -/
theorem acc_of_nf {x : Cnf} (h : NF x) : Acc NFLt x := by
  induction h with
  | zero => exact acc_zero
  | oadd n _ _ _ ihe iha => exact acc_oadd (acc_of_lt_omegaPow ihe) n iha

end Cnf

/-! ## Levels -/

/-- Universe levels below ε₀: the Cantor normal forms. -/
def Level : Type := {x : Cnf // x.NF}

namespace Level

open Cnf

/-- Equality of levels is decidable, as equality of trees. -/
instance : DecidableEq Level := inferInstanceAs (DecidableEq {x : Cnf // x.NF})

/-- A level is displayed as its normal form. -/
instance : Repr Level := ⟨fun x p => reprPrec x.1 p⟩

/-- Two levels are equal when their normal forms are. -/
theorem ext {x y : Level} (h : x.1 = y.1) : x = y := Subtype.ext h

/-- Levels are ordered by comparing their normal forms. -/
instance : LinearOrder Level where
  le x y := cmp x.1 y.1 ≠ .gt
  lt x y := cmp x.1 y.1 = .lt
  le_refl x := by
    show cmp x.1 x.1 ≠ .gt
    rw [cmp_self]
    exact nofun
  le_trans x y z hxy hyz := by
    show cmp x.1 z.1 ≠ .gt
    intro hxz
    cases hy : cmp x.1 y.1 with
    | lt =>
      cases hz : cmp y.1 z.1 with
      | lt => exact absurd (cmp_lt_trans hy hz) (by rw [hxz]; exact nofun)
      | eq =>
        rw [← eq_of_cmp_eq hz, hy] at hxz
        exact nomatch hxz
      | gt => exact hyz hz
    | eq => rw [eq_of_cmp_eq hy] at hxz; exact hyz hxz
    | gt => exact hxy hy
  lt_iff_le_not_ge x y := by
    show cmp x.1 y.1 = .lt ↔ cmp x.1 y.1 ≠ .gt ∧ ¬ cmp y.1 x.1 ≠ .gt
    refine ⟨fun h => ⟨by rw [h]; exact nofun, fun h' => h' (cmp_eq_gt.mpr h)⟩, ?_⟩
    rintro ⟨_, h⟩
    exact cmp_eq_gt.mp (Decidable.of_not_not h)
  le_antisymm x y hxy hyx := by
    apply ext
    apply eq_of_cmp_eq
    cases h : cmp x.1 y.1 with
    | lt => exact absurd (cmp_eq_gt.mpr h) hyx
    | eq => rfl
    | gt => exact absurd h hxy
  min x y := if cmp x.1 y.1 ≠ .gt then x else y
  max x y := if cmp x.1 y.1 ≠ .gt then y else x
  compare x y := cmp x.1 y.1
  le_total x y := by
    show cmp x.1 y.1 ≠ .gt ∨ cmp y.1 x.1 ≠ .gt
    cases h : cmp x.1 y.1 with
    | lt => exact .inl nofun
    | eq => exact .inl nofun
    | gt => exact .inr (by rw [cmp_eq_gt.mp h]; exact nofun)
  toDecidableLE x y := inferInstanceAs (Decidable (cmp x.1 y.1 ≠ .gt))
  toDecidableEq := inferInstance
  toDecidableLT x y := inferInstanceAs (Decidable (cmp x.1 y.1 = .lt))
  min_def _ _ := rfl
  max_def _ _ := rfl
  compare_eq_compareOfLessAndEq x y := by
    show cmp x.1 y.1 = if cmp x.1 y.1 = .lt then .lt else if x = y then .eq else .gt
    cases h : cmp x.1 y.1 with
    | lt => rfl
    | eq => rw [if_pos (ext (eq_of_cmp_eq h))]; rfl
    | gt =>
      have hne : x ≠ y := fun e => by
        subst e
        rw [cmp_self] at h
        exact nomatch h
      rw [if_neg hne]
      rfl

/-- The strict order of levels is the comparison of their normal forms. -/
theorem lt_def {x y : Level} : x < y ↔ cmp x.1 y.1 = .lt := Iff.rfl

/-- The order of levels is the comparison of their normal forms. -/
theorem le_def {x y : Level} : x ≤ y ↔ cmp x.1 y.1 ≠ .gt := Iff.rfl

/-- Levels are well-founded: every level is accessible. -/
theorem lt_wf : WellFounded (fun a b : Level => a < b) :=
  ⟨fun x => Subrelation.accessible (fun {a _} h => ⟨a.2, h⟩)
    (InvImage.accessible Subtype.val (acc_of_nf x.2))⟩

/-- The least level. -/
def zero : Level := ⟨.zero, .zero⟩

/-- The finite level `n`. -/
def ofNat (n : Nat) : Level := ⟨Cnf.ofNat n, nf_ofNat n⟩

/-- The first infinite level `ω`. -/
def omega : Level := ⟨Cnf.omega, nf_omega⟩

/-- The successor level. -/
def succ (x : Level) : Level := ⟨Cnf.succ x.1, nf_succ x.2⟩

/-- `zero` is the least level. -/
theorem zero_le (x : Level) : zero ≤ x := cmp_zero_left x.1

/-- A level lies below its successor. -/
theorem lt_succ (x : Level) : x < succ x := cmp_succ x.1

/-- The successor is the least level strictly above. -/
theorem succ_le_of_lt {x y : Level} (h : x < y) : succ x ≤ y :=
  Cnf.succ_le_of_lt x.2 y.2 h

/-- Levels below ε₀ form a level order. -/
instance : LevelOrder Level where
  toLinearOrder := inferInstance
  wf := lt_wf
  bot := zero
  bot_le := zero_le
  succ := succ
  lt_succ := lt_succ
  succ_le_of_lt := succ_le_of_lt

/-- The predecessor of a successor level; `none` at the least level and at limits. -/
def pred? (x : Level) : Option Level :=
  match h : Cnf.pred? x.1 with
  | some p => some ⟨p, nf_of_pred?_eq_some x.2 h⟩
  | none => none

/-- A level has the predecessor `p` exactly when it is the successor of `p`. -/
theorem pred?_eq_some {x p : Level} : pred? x = some p ↔ x = succ p := by
  unfold pred?
  split
  · rename_i q hq
    constructor
    · intro h
      obtain rfl : (⟨q, nf_of_pred?_eq_some x.2 hq⟩ : Level) = p := Option.some.inj h
      exact ext (eq_succ_of_pred?_eq_some x.2 hq)
    · intro h
      subst h
      have hqp : q = p.1 := Option.some.inj (hq.symm.trans (Cnf.pred?_succ p.1))
      exact congrArg some (ext hqp)
  · rename_i hnone
    constructor
    · intro h
      exact nomatch h
    · intro h
      subst h
      rw [show (succ p).1 = Cnf.succ p.1 from rfl, Cnf.pred?_succ] at hnone
      exact nomatch hnone

/-- Levels below ε₀ have predecessors. -/
instance : PredLevelOrder Level where
  pred? := pred?
  pred?_eq_some := pred?_eq_some

/-- The successor of a numeral is the next numeral. -/
theorem succ_ofNat (n : Nat) : succ (ofNat n) = ofNat (n + 1) :=
  ext (Cnf.succ_ofNat n)

/-- The finite levels of the level order are the numerals. -/
theorem levelOrder_ofNat : ∀ n : Nat, (LevelOrder.ofNat n : Level) = ofNat n
  | 0 => rfl
  | n + 1 => by
    rw [LevelOrder.ofNat_succ, levelOrder_ofNat n]
    exact succ_ofNat n

/-- Every finite level lies below `ω`. -/
theorem ofNat_lt_omega : ∀ n : Nat, ofNat n < omega
  | 0 => rfl
  | _ + 1 => rfl

/-- Every level below `ω` lies below a finite level. -/
theorem exists_lt_ofNat_of_lt_omega {β : Level} (hβ : β < omega) : ∃ n : Nat, β < ofNat n := by
  obtain ⟨x, hx⟩ := β
  cases x with
  | zero => exact ⟨1, rfl⟩
  | oadd e k a =>
    have he : cmp e (omegaPow Cnf.zero) = .lt := oadd_lt_omegaPow.mp (lt_def.mp hβ)
    obtain rfl := eq_zero_of_lt_omegaPow_zero he
    obtain rfl := eq_zero_of_lt_omegaPow_zero hx.lt
    refine ⟨k + 2, lt_def.mpr ?_⟩
    show cmp (Cnf.oadd Cnf.zero k Cnf.zero) (Cnf.oadd Cnf.zero (k + 1) Cnf.zero) = .lt
    rw [cmp_oadd, Nat.compare_eq_lt.mpr (Nat.lt_succ_self k)]
    rfl

/-- `ω` is the successor of no level: it is a limit. -/
theorem succ_ne_omega (x : Level) : succ x ≠ omega := by
  intro h
  have h' : Cnf.succ x.1 = Cnf.omega := congrArg Subtype.val h
  match x with
  | ⟨.zero, _⟩ => exact nomatch h'
  | ⟨.oadd .zero _ _, _⟩ => exact nomatch h'
  | ⟨.oadd (.oadd _ _ _) _ .zero, _⟩ => exact nomatch h'
  | ⟨.oadd (.oadd _ _ _) _ (.oadd .zero _ _), _⟩ => exact nomatch h'
  | ⟨.oadd (.oadd _ _ _) _ (.oadd (.oadd _ _ _) _ _), _⟩ => exact nomatch h'

/-- `ω` is a limit level. -/
theorem isLimit_omega : LevelOrder.IsLimit omega :=
  ⟨ofNat_lt_omega 0, fun p => succ_ne_omega p⟩

end Level

/-! ## Examples -/

section Examples

open Level

/-- A thousand lies below `ω`. -/
example : ofNat 1000 < omega := by decide

/-- `ω` lies below its successor. -/
example : omega < succ omega := by decide

/-- `ω` does not lie below `5`. -/
example : ¬ omega < ofNat 5 := by decide

/-- The successor of `3` is `4`. -/
example : LevelOrder.succ (ofNat 3) = ofNat 4 := by decide

/-- The larger of `3` and `ω` is `ω`. -/
example : max (ofNat 3) omega = omega := by decide

/-- The predecessor of `ω + 1` is `ω`, and of `4` is `3`. -/
example : PredLevelOrder.pred? (succ omega) = some omega ∧
    PredLevelOrder.pred? (ofNat 4) = some (ofNat 3) := by decide

/-- `ω` has no predecessor, and neither has `0`. -/
example : PredLevelOrder.pred? omega = none ∧ PredLevelOrder.pred? zero = none := by decide

/-- The table of interpretations over levels below ε₀ reads a finite level below `ω` by
its interpretation. -/
example : below (L := Level) (fun k _ => k) zero omega (ofNat 3) = ofNat 3 :=
  below_of_lt _ _ (ofNat_lt_omega 3)

/-- `1 + ω`, written with increasing exponents, is not a normal form. -/
theorem one_add_omega_not_nf : ¬ Cnf.NF (.oadd .zero 0 (.oadd (.oadd .zero 0 .zero) 0 .zero)) := by
  decide

/-- Off normal forms the comparison is not the order of what the trees denote: it places
the tree `ω ^ 0 * 1 + ω ^ 1 * 1`, which denotes `1 + ω = ω`, strictly between `1` and
`2`. -/
theorem cmp_one_add_omega :
    Cnf.cmp (Cnf.ofNat 1) (.oadd .zero 0 (.oadd (.oadd .zero 0 .zero) 0 .zero)) = .lt ∧
      Cnf.cmp (.oadd .zero 0 (.oadd (.oadd .zero 0 .zero) 0 .zero)) (Cnf.ofNat 2) = .lt := by
  decide

/-- No level lies strictly between `1` and `2`, so no level can stand for that tree. -/
theorem no_level_between_one_two : ¬ ∃ x : Level, ofNat 1 < x ∧ x < ofNat 2 :=
  fun ⟨_, h₁, h₂⟩ => LevelOrder.not_lt_of_lt_succ h₁ h₂

end Examples

end Mettapedia.TypeTheory.UniverseLevel
