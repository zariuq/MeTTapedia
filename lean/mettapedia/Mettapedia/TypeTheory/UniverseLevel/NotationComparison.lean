import Mettapedia.TypeTheory.UniverseLevel.Notation
import Mettapedia.TypeTheory.UniverseLevel.NotationArithmetic
import Mathlib.Algebra.Order.SuccPred
import Mathlib.SetTheory.Ordinal.Notation

/-!
# Levels below ε₀ against Mathlib's ordinal notations

An independent check of the level order of `Notation.lean` against Mathlib's `ONote` and
`NONote`. A tree translates to a Mathlib notation, its coefficient `n` becoming the
positive `n + 1`. The translation is a bijection, it turns the comparison into `ONote.cmp`
on all trees, and it turns normal forms into Mathlib's normal forms. Levels are therefore
order-isomorphic to `NONote`, and the ordinal a level denotes is read off through
`NONote.repr`: `ofNat n` denotes `n`, `omega` denotes `ω`, and the successor adds one.

Mathlib's ordinals are classical, and so is this file; `Notation.lean` is not.

The sum, product and power of `NotationArithmetic.lean` are the ordinal ones (`repr_add`,
`repr_mul`, `repr_pow`). Laws of ordinal arithmetic are therefore laws of levels: the exponent
laws for every base (`Level.pow_add`, `Level.pow_mul`), which the direct proofs on trees reach
only for the natural numbers and for `ω` as bases.

Positive examples: the order and the operations agree with the ordinals denoted. Negative
example: off normal forms the comparison disagrees with the ordinals denoted.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniverseLevel

open Ordinal

namespace Cnf

/-- A tree as a Mathlib ordinal notation: the coefficient `n` becomes the positive
`n + 1`. -/
def toONote : Cnf → ONote
  | zero => 0
  | oadd e n a => .oadd (toONote e) n.succPNat (toONote a)

/-- A Mathlib ordinal notation as a tree: the positive coefficient `n` becomes `n - 1`. -/
def ofONote : ONote → Cnf
  | .zero => zero
  | .oadd e n a => oadd (ofONote e) n.natPred (ofONote a)

/-- Translating to Mathlib and back is the identity. -/
theorem ofONote_toONote : ∀ x : Cnf, ofONote (toONote x) = x
  | zero => rfl
  | oadd e n a => by
    rw [toONote, ofONote, ofONote_toONote e, ofONote_toONote a, Nat.natPred_succPNat]

/-- Translating from Mathlib and back is the identity. -/
theorem toONote_ofONote : ∀ o : ONote, toONote (ofONote o) = o
  | .zero => rfl
  | .oadd e n a => by
    rw [ofONote, toONote, toONote_ofONote e, toONote_ofONote a, PNat.succPNat_natPred]

/-- Shifting two coefficients to positive ones keeps their comparison. -/
theorem compare_succPNat (m n : Nat) :
    compare (m.succPNat : Nat) (n.succPNat : Nat) = compare m n := by
  rw [Nat.succPNat_coe, Nat.succPNat_coe]
  rcases Nat.lt_trichotomy m n with h | rfl | h
  · rw [Nat.compare_eq_lt.2 h, Nat.compare_eq_lt.2 (Nat.succ_lt_succ h)]
  · rw [Nat.compare_eq_eq.2 rfl, Nat.compare_eq_eq.2 rfl]
  · rw [Nat.compare_eq_gt.2 h, Nat.compare_eq_gt.2 (Nat.succ_lt_succ h)]

/-- The comparison is Mathlib's comparison, on all trees. -/
theorem cmp_toONote : ∀ x y : Cnf, (toONote x).cmp (toONote y) = cmp x y
  | zero, zero => rfl
  | zero, oadd _ _ _ => rfl
  | oadd _ _ _, zero => rfl
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂ => by
    show ((toONote e₁).cmp (toONote e₂)).then
        ((_root_.cmp (n₁.succPNat : Nat) n₂.succPNat).then ((toONote a₁).cmp (toONote a₂))) = _
    rw [cmp_toONote e₁ e₂, cmp_toONote a₁ a₂, cmp_eq_compare, compare_succPNat, cmp_oadd]

/-- Normal forms are Mathlib's normal forms. -/
theorem nf_toONote_iff : ∀ {x : Cnf}, (toONote x).NF ↔ NF x
  | zero => ⟨fun _ => .zero, fun _ => ONote.NF.zero⟩
  | oadd e n a => by
    have ihe : (toONote e).NF ↔ NF e := nf_toONote_iff
    have iha : (toONote a).NF ↔ NF a := nf_toONote_iff
    constructor
    · intro h
      have he : (toONote e).NF := h.fst
      have htop := (ONote.nfBelow_iff_topBelow (b := toONote e)).1 h.snd'
      refine .oadd n (ihe.1 he) (iha.1 htop.1) ?_
      cases a with
      | zero => rfl
      | oadd e' _ _ =>
        rw [oadd_lt_omegaPow, ← cmp_toONote]
        exact htop.2
    · intro h
      have he : (toONote e).NF := ihe.2 h.fst
      refine ONote.NF.oadd he _ (ONote.nfBelow_iff_topBelow.2 ⟨iha.2 h.snd, ?_⟩)
      cases a with
      | zero => trivial
      | oadd e' _ _ =>
        show (toONote e').cmp (toONote e) = .lt
        rw [cmp_toONote]
        exact oadd_lt_omegaPow.1 h.lt

/-- Numerals are Mathlib's numerals. -/
theorem toONote_ofNat : ∀ n : Nat, toONote (ofNat n) = ONote.ofNat n
  | 0 => rfl
  | _ + 1 => rfl

/-- `omega` is Mathlib's `ω`. -/
theorem toONote_omega : toONote omega = ONote.omega := rfl

/-- Mathlib's addition of a leading term `ω ^ e * (n + 1)` to a tree below `ω ^ e` is
`oadd`. -/
theorem addAux_toONote {e : Cnf} {n : Nat} {y : Cnf} (h : cmp y (omegaPow e) = .lt) :
    ONote.addAux (toONote e) n.succPNat (toONote y) = toONote (oadd e n y) := by
  cases y with
  | zero => rfl
  | oadd e₁ n₁ a₁ =>
    have hgt : (toONote e).cmp (toONote e₁) = .gt := by
      rw [cmp_toONote, cmp_eq_gt]
      exact oadd_lt_omegaPow.1 h
    simp only [toONote, ONote.addAux, hgt]

/-- On normal forms the successor is Mathlib's addition of one. -/
theorem toONote_succ : ∀ {x : Cnf}, NF x → toONote (succ x) = toONote x + 1
  | zero, _ => rfl
  | oadd zero n a, h => by
    obtain rfl := eq_zero_of_lt_omegaPow_zero h.lt
    rfl
  | oadd (oadd e' n' a') n a, h => by
    show ONote.oadd _ n.succPNat (toONote (succ a)) = ONote.addAux _ n.succPNat (toONote a + 1)
    rw [← toONote_succ h.snd, addAux_toONote (succ_lt_omegaPow h.lt)]
    rfl

/-- The successor of a normal form denotes the ordinal successor. -/
theorem repr_succ : ∀ {x : Cnf}, NF x → (toONote (succ x)).repr = (toONote x).repr + 1
  | zero, _ => by simp [succ, toONote]
  | oadd zero n a, h => by
    obtain rfl := eq_zero_of_lt_omegaPow_zero h.lt
    simp [succ, toONote]
  | oadd (oadd e' n' a') n a, h => by
    rw [succ, toONote, ONote.repr, repr_succ h.snd, ← _root_.add_assoc]
    rfl

/-- `omega` denotes `ω`. -/
theorem repr_omega : (toONote omega).repr = ω := by
  simp [toONote, omega]

/-- A normal form with no predecessor denotes zero or a limit ordinal. The limit
predicate is `Order.IsSuccLimit`. -/
theorem repr_zero_or_isSuccLimit_of_pred?_eq_none :
    ∀ {x : Cnf}, NF x → pred? x = none →
      (toONote x).repr = 0 ∨ Order.IsSuccLimit (toONote x).repr
  | zero, _, _ => Or.inl rfl
  | oadd zero 0 _, _, h => nomatch h
  | oadd zero (_ + 1) _, _, h => nomatch h
  | oadd (oadd e' n' a') n a, hx, h => by
    have ha_none : pred? a = none := by
      cases hp : pred? a with
      | none => rfl
      | some _ =>
        unfold pred? at h
        rw [hp] at h
        exact nomatch h
    have ih := repr_zero_or_isSuccLimit_of_pred?_eq_none hx.snd ha_none
    have hexp : (toONote (oadd e' n' a')).repr ≠ 0 := by
      refine ne_of_gt (lt_of_lt_of_le ?_ (ONote.omega0_le_oadd (toONote e')
        n'.succPNat (toONote a')))
      exact Ordinal.opow_pos _ Ordinal.omega0_pos
    have hhead : Order.IsSuccLimit
        (ω ^ (toONote (oadd e' n' a')).repr * (n.succPNat : Ordinal)) :=
      Ordinal.isSuccLimit_mul_left
        (Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hexp)
        (Nat.cast_pos'.2 n.succPNat.2)
    have hrepr : (toONote (oadd (oadd e' n' a') n a)).repr =
        ω ^ (toONote (oadd e' n' a')).repr * (n.succPNat : Ordinal) +
          (toONote a).repr := by
      rw [toONote, ONote.repr]
    cases ih with
    | inl h0 =>
      rw [hrepr, h0, _root_.add_zero]
      exact Or.inr hhead
    | inr hlim =>
      rw [hrepr]
      exact Or.inr (Ordinal.isSuccLimit_add _ hlim)

/-- Off normal forms the comparison disagrees with the ordinals denoted: the tree
`ω ^ 0 * 1 + ω ^ 1 * 1` denotes `1 + ω = ω`, which lies above `2`, yet it compares below
`2`. -/
theorem cmp_disagrees_off_nf :
    cmp (oadd zero 0 omega) (ofNat 2) = .lt ∧
      (toONote (ofNat 2)).repr < (toONote (oadd zero 0 omega)).repr := by
  refine ⟨rfl, ?_⟩
  have h2 : (toONote (ofNat 2)).repr = 2 := ONote.repr_ofNat 2
  have hω : (toONote (oadd zero 0 omega)).repr = ω := by
    rw [toONote, ONote.repr, repr_omega]
    simp [toONote]
  rw [h2, hω]
  exact natCast_lt_omega0 2

/-- The merged coefficient `n + n' + 1` is the sum of the two positive coefficients. -/
theorem succPNat_add (n n' : Nat) :
    (n + n' + 1).succPNat = n.succPNat + n'.succPNat := by
  have hcoe : ((n + n' + 1).succPNat : Nat) =
      ((n.succPNat + n'.succPNat : ℕ+) : Nat) := by
    rw [Nat.succPNat_coe, PNat.add_coe, Nat.succPNat_coe, Nat.succPNat_coe]
    calc
      Nat.succ (n + n' + 1) = (n + n' + 1) + 1 := rfl
      _ = n + n' + (1 + 1) := by rw [Nat.add_assoc (n + n') 1 1]
      _ = n + (n' + (1 + 1)) := by rw [Nat.add_assoc n n' (1 + 1)]
      _ = n + ((n' + 1) + 1) := by rw [← Nat.add_assoc n' 1 1]
      _ = n + (1 + (n' + 1)) := by rw [Nat.add_comm (n' + 1) 1]
      _ = (n + 1) + (n' + 1) := by rw [← Nat.add_assoc n 1 (n' + 1)]
      _ = Nat.succ n + Nat.succ n' := rfl
  exact Subtype.ext hcoe

/-- The coefficient `n * n' + n + n'` is the product of the two positive coefficients. -/
theorem succPNat_mul (n n' : Nat) :
    (n * n' + n + n').succPNat = n.succPNat * n'.succPNat := by
  have hcoe : ((n * n' + n + n').succPNat : Nat) =
      ((n.succPNat * n'.succPNat : ℕ+) : Nat) := by
    rw [Nat.succPNat_coe, PNat.mul_coe, Nat.succPNat_coe, Nat.succPNat_coe]
    calc
      Nat.succ (n * n' + n + n') = n * n' + n + n' + 1 := rfl
      _ = n * n' + (n + n') + 1 := by rw [Nat.add_assoc (n * n') n n']
      _ = n * n' + (n' + n) + 1 := by rw [Nat.add_comm n n']
      _ = n * n' + n' + n + 1 := by rw [← Nat.add_assoc (n * n') n' n]
      _ = n * n' + n' + Nat.succ n := rfl
      _ = Nat.succ n * n' + Nat.succ n := by rw [← Nat.succ_mul]
      _ = Nat.succ n * Nat.succ n' := by rw [← Nat.mul_succ]
  exact Subtype.ext hcoe

/-- Attaching a leading term agrees with Mathlib, on every tree. -/
theorem toONote_addAux (e : Cnf) (n : Nat) (y : Cnf) :
    toONote (addAux e n y) = ONote.addAux (toONote e) n.succPNat (toONote y) := by
  cases y with
  | zero => rfl
  | oadd e' n' a' =>
    cases h : cmp e e' with
    | lt =>
      have h' : (toONote e).cmp (toONote e') = .lt := by
        rw [cmp_toONote, h]
      rw [addAux_lt h]
      simp only [toONote, ONote.addAux, h']
    | eq =>
      obtain rfl := eq_of_cmp_eq h
      have hc : (toONote e).cmp (toONote e) = .eq := by
        rw [cmp_toONote, cmp_self]
      rw [addAux_eq_exp]
      simp only [toONote, ONote.addAux, hc, succPNat_add]
    | gt =>
      have h' : (toONote e).cmp (toONote e') = .gt := by
        rw [cmp_toONote, h]
      rw [addAux_gt h]
      simp only [toONote, ONote.addAux, h']

/-- Sum agrees with Mathlib, on every tree. -/
theorem toONote_add : ∀ x y : Cnf, toONote (add x y) = toONote x + toONote y
  | .zero, y => by
    rw [zero_add]
    rfl
  | .oadd e n a, y => by
    rw [oadd_add, toONote_addAux, toONote_add a y, toONote, ONote.oadd_add]

/-- Product agrees with Mathlib, on every tree. -/
theorem toONote_mul : ∀ x y : Cnf, toONote (mul x y) = toONote x * toONote y
  | .zero, y => by
    rw [zero_mul]
    cases y <;> rfl
  | .oadd _ _ _, .zero => rfl
  | .oadd e₁ n₁ a₁, .oadd .zero n₂ a₂ => by
    rw [mul_oadd_zero, toONote, toONote, succPNat_mul]
    rfl
  | .oadd e₁ n₁ a₁, .oadd (.oadd e₂ n₂e a₂e) n₂ a₂ => by
    rw [mul_oadd_oadd, toONote, toONote, toONote_add e₁ (.oadd e₂ n₂e a₂e),
      toONote_mul (.oadd e₁ n₁ a₁) a₂]
    rfl

/-- Left subtraction of one agrees with Mathlib, on every tree. -/
theorem toONote_subOne : ∀ x : Cnf, toONote (subOne x) = toONote x - 1
  | .zero => rfl
  | .oadd .zero 0 a => by
    rw [subOne_finite_zero]
    change toONote a = ONote.sub (ONote.oadd 0 (Nat.succPNat 0) (toONote a))
      (ONote.oadd 0 (Nat.succPNat 0) 0)
    unfold ONote.sub
    rw [show ONote.cmp 0 0 = Ordering.eq from rfl]
    dsimp
    cases a with
    | zero =>
      unfold ONote.sub
      rfl
    | oadd _ _ _ =>
      unfold ONote.sub
      rfl
  | .oadd .zero (n + 1) a => by
    rw [subOne_finite_succ, toONote, toONote]
    rfl
  | .oadd (.oadd e n' a') n a => by
    rw [subOne_infinite, toONote]
    rfl

/-- Division by `ω` on the right agrees with Mathlib. -/
theorem toONote_split : ∀ o : Cnf,
    toONote (split o).1 = (ONote.split (toONote o)).1 ∧
      (split o).2 = (ONote.split (toONote o)).2
  | .zero => ⟨rfl, rfl⟩
  | .oadd .zero n _ => by
    rw [split, toONote]
    exact ⟨rfl, rfl⟩
  | .oadd (.oadd ei ni ai) n a => by
    have ih := toONote_split a
    cases hs : split a with
    | mk q m =>
      have hq : toONote q = (ONote.split (toONote a)).1 := by
        have t := ih.1
        rw [hs] at t
        exact t
      have hm : m = (ONote.split (toONote a)).2 := by
        have t := ih.2
        rw [hs] at t
        exact t
      unfold split
      rw [hs, toONote, hq, hm]
      exact ⟨rfl, rfl⟩

/-- Division by `ω` on the left agrees with Mathlib. -/
theorem toONote_split' : ∀ o : Cnf,
    toONote (split' o).1 = (ONote.split' (toONote o)).1 ∧
      (split' o).2 = (ONote.split' (toONote o)).2
  | .zero => ⟨rfl, rfl⟩
  | .oadd .zero n _ => by
    rw [split', toONote]
    exact ⟨rfl, rfl⟩
  | .oadd (.oadd ei ni ai) n a => by
    have ih := toONote_split' a
    cases hs : split' a with
    | mk q m =>
      have hq : toONote q = (ONote.split' (toONote a)).1 := by
        have t := ih.1
        rw [hs] at t
        exact t
      have hm : m = (ONote.split' (toONote a)).2 := by
        have t := ih.2
        rw [hs] at t
        exact t
      unfold split'
      rw [hs, toONote, toONote_subOne, hq, hm]
      exact ⟨rfl, rfl⟩

/-- Scaling by a power of `ω` agrees with Mathlib. -/
theorem toONote_scale : ∀ x y : Cnf,
    toONote (scale x y) = ONote.scale (toONote x) (toONote y)
  | _, .zero => rfl
  | x, .oadd e n a => by
    rw [scale_oadd, toONote, toONote_add, toONote_scale x a]
    rfl

/-- Multiplication by a natural number agrees with Mathlib. -/
theorem toONote_mulNat : ∀ (x : Cnf) (m : Nat),
    toONote (mulNat x m) = ONote.mulNat (toONote x) m
  | .zero, _ => rfl
  | .oadd _ _ _, 0 => by
    rw [mulNat_zero]
    rfl
  | .oadd e n a, m + 1 => by
    have hcoef : (n * (m + 1) + m).succPNat = n.succPNat * m.succPNat := by
      have hnm : n * (m + 1) + m = n * m + n + m := by
        rw [Nat.mul_succ, Nat.add_assoc]
      rw [hnm]
      exact succPNat_mul n m
    rw [show mulNat (.oadd e n a) (m + 1) = .oadd e (n * (m + 1) + m) a from rfl,
      toONote, hcoef]
    rfl

/-- A positive power `(t ^ k)` is the positive coefficient of index `t ^ k - 1`. -/
theorem succPNat_pow_sub {t k : Nat} (ht : 0 < t) :
    (t ^ k - 1).succPNat = (t - 1).succPNat ^ k := by
  have hcoe : ((t ^ k - 1).succPNat : Nat) =
      (((t - 1).succPNat ^ k : ℕ+) : Nat) := by
    rw [Nat.succPNat_coe, PNat.pow_coe, Nat.succPNat_coe,
      show Nat.succ (t - 1) = t from Nat.succ_pred_eq_of_pos ht]
    exact Nat.succ_pred_eq_of_pos (by
      cases t with
      | zero => exact absurd ht (Nat.not_lt_zero 0)
      | succ t => exact succ_pow_pos t k)
  exact Subtype.ext hcoe

/-- One step of a power of a positive multiple of `ω` agrees with Mathlib. -/
theorem toONote_opowAux (e a0 a : Cnf) : ∀ k m : Nat,
    toONote (opowAux e a0 a k m) =
      ONote.opowAux (toONote e) (toONote a0) (toONote a) k m
  | k, 0 => by
    rw [opowAux_zero]
    cases k with
    | zero =>
      unfold ONote.opowAux
      rfl
    | succ _ =>
      unfold ONote.opowAux
      rfl
  | 0, m + 1 => by
    unfold opowAux ONote.opowAux
    rfl
  | k + 1, m + 1 => by
    unfold opowAux ONote.opowAux
    rw [toONote_add, toONote_scale, toONote_add, toONote_mulNat,
      toONote_opowAux e a0 a k (m + 1)]

/-- The power, dispatched on the exponent and on `split` of the base, agrees with Mathlib. -/
theorem toONote_opowAux2 (exp : Cnf) : ∀ p : Cnf × Nat,
    toONote (opowAux2 exp p) = ONote.opowAux2 (toONote exp) (toONote p.1, p.2)
  | (.zero, 0) => by
    cases exp with
    | zero => rfl
    | oadd _ _ _ => rfl
  | (.zero, 1) => rfl
  | (.zero, m + 2) => by
    cases hs : split' exp with
    | mk b k =>
      have hsp : ONote.split' (toONote exp) = (toONote b, k) := by
        have ht := toONote_split' exp
        rw [hs] at ht
        exact Prod.ext ht.1.symm ht.2.symm
      have hl : opowAux2 exp (.zero, m + 2) =
          .oadd b ((m + 2) ^ k - 1) .zero := by
        unfold opowAux2
        rw [hs]
        rfl
      have hr : ONote.opowAux2 (toONote exp) (0, m + 2) =
          ONote.oadd (toONote b) ((Nat.succPNat (m + 1)) ^ k) 0 := by
        unfold ONote.opowAux2
        rw [hsp]
        dsimp
        rfl
      rw [hl]
      have hpair : ((zero, m + 2).1.toONote, (zero, m + 2).2) = (0, m + 2) := rfl
      rw [hpair, hr, toONote, succPNat_pow_sub (Nat.zero_lt_succ (m + 1))]
      rfl
  | (.oadd a0 n0 t0, m) => by
    cases hs : split exp with
    | mk b s =>
      have hsp : ONote.split (toONote exp) = (toONote b, s) := by
        have ht := toONote_split exp
        rw [hs] at ht
        exact Prod.ext ht.1.symm ht.2.symm
      cases s with
      | zero =>
        have hl : opowAux2 exp (.oadd a0 n0 t0, m) =
            .oadd (mul a0 b) 0 .zero := by
          unfold opowAux2
          rw [hs]
        have hr : ONote.opowAux2 (toONote exp) (toONote (.oadd a0 n0 t0), m) =
            ONote.oadd (toONote a0 * toONote b) (Nat.succPNat 0) 0 := by
          unfold ONote.opowAux2
          rw [hsp]
          dsimp
          rfl
        rw [hl, hr, toONote, toONote_mul]
        rfl
      | succ k =>
        have hl : opowAux2 exp (.oadd a0 n0 t0, m) =
            add (scale (add (mul a0 b) (mulNat a0 k)) (.oadd a0 n0 t0))
              (opowAux (mul a0 b) a0 (mulNat (.oadd a0 n0 t0) m) k m) := by
          unfold opowAux2
          rw [hs]
        have hr : ONote.opowAux2 (toONote exp) (toONote (.oadd a0 n0 t0), m) =
            ONote.scale (toONote a0 * toONote b + ONote.mulNat (toONote a0) k)
              (toONote (.oadd a0 n0 t0)) +
            ONote.opowAux (toONote a0 * toONote b) (toONote a0)
              (ONote.mulNat (toONote (.oadd a0 n0 t0)) m) k m := by
          unfold ONote.opowAux2
          rw [hsp]
          dsimp
          rfl
        rw [hl, hr, toONote_add, toONote_scale, toONote_add, toONote_mul, toONote_mulNat,
          toONote_opowAux, toONote_mul, toONote_mulNat, toONote]

/-- Power agrees with Mathlib, on every tree. -/
theorem toONote_pow (x y : Cnf) : toONote (pow x y) = toONote x ^ toONote y := by
  rw [ONote.opow_def]
  unfold pow
  have hs := toONote_split x
  cases h : split x with
  | mk q r =>
    have hq : toONote q = (ONote.split (toONote x)).1 := by
      have t := hs.1
      rw [h] at t
      exact t
    have hr : r = (ONote.split (toONote x)).2 := by
      have t := hs.2
      rw [h] at t
      exact t
    have hsp : ONote.split (toONote x) = (toONote q, r) := Prod.ext hq.symm hr.symm
    rw [toONote_opowAux2]
    have hpair : (toONote (q, r).1, (q, r).2) = (toONote q, r) := rfl
    rw [hpair, hsp]

/-- On normal forms the sum denotes the sum of the ordinals. -/
theorem repr_add {x y : Cnf} (hx : NF x) (hy : NF y) :
    (toONote (add x y)).repr = (toONote x).repr + (toONote y).repr := by
  rw [toONote_add]
  exact @ONote.repr_add (toONote x) (toONote y) (nf_toONote_iff.2 hx) (nf_toONote_iff.2 hy)

/-- On normal forms the product denotes the product of the ordinals. -/
theorem repr_mul {x y : Cnf} (hx : NF x) (hy : NF y) :
    (toONote (mul x y)).repr = (toONote x).repr * (toONote y).repr := by
  rw [toONote_mul]
  exact @ONote.repr_mul (toONote x) (toONote y) (nf_toONote_iff.2 hx) (nf_toONote_iff.2 hy)

/-- On normal forms the power denotes the power of the ordinals. -/
theorem repr_pow {x y : Cnf} (hx : NF x) (hy : NF y) :
    (toONote (pow x y)).repr = (toONote x).repr ^ (toONote y).repr := by
  rw [toONote_pow]
  exact @ONote.repr_opow (toONote x) (toONote y) (nf_toONote_iff.2 hx) (nf_toONote_iff.2 hy)

end Cnf

namespace Level

open Cnf

/-- A level as a Mathlib normal ordinal notation. -/
def toNONote (x : Level) : NONote := ⟨toONote x.1, nf_toONote_iff.2 x.2⟩

/-- A Mathlib normal ordinal notation as a level. -/
def ofNONote (o : NONote) : Level :=
  ⟨ofONote o.1, nf_toONote_iff.1 ((toONote_ofONote o.1).symm ▸ o.2)⟩

/-- The strict order of levels is the order of the ordinals they denote. -/
theorem lt_iff_toNONote_lt {x y : Level} : x < y ↔ toNONote x < toNONote y := by
  have : (toONote x.1).NF := nf_toONote_iff.2 x.2
  have : (toONote y.1).NF := nf_toONote_iff.2 y.2
  rw [lt_def, ← cmp_toONote]
  exact (ONote.cmp_compares _ _).eq_lt

/-- Levels below ε₀ are order-isomorphic to Mathlib's normal ordinal notations. -/
def orderIsoNONote : Level ≃o NONote where
  toFun := toNONote
  invFun := ofNONote
  left_inv x := ext (ofONote_toONote x.1)
  right_inv o := Subtype.ext (toONote_ofONote o.1)
  map_rel_iff' {x y} := by
    show toNONote x ≤ toNONote y ↔ x ≤ y
    rw [← not_lt, ← not_lt, lt_iff_toNONote_lt]

/-- `zero` denotes `0`. -/
theorem repr_zero : (toNONote zero).repr = 0 := rfl

/-- `ofNat n` denotes `n`. -/
theorem repr_ofNat (n : Nat) : (toNONote (ofNat n)).repr = n := by
  show (toONote (Cnf.ofNat n)).repr = n
  rw [toONote_ofNat]
  exact ONote.repr_ofNat n

/-- `omega` denotes `ω`. -/
theorem repr_omega : (toNONote omega).repr = ω := Cnf.repr_omega

/-- The successor denotes the ordinal successor. -/
theorem repr_succ (x : Level) : (toNONote (succ x)).repr = (toNONote x).repr + 1 :=
  Cnf.repr_succ x.2

/-- The level order is the order of the ordinals denoted. -/
theorem lt_iff_repr_lt {x y : Level} : x < y ↔ (toNONote x).repr < (toNONote y).repr :=
  lt_iff_toNONote_lt

/-- If a level has predecessor `p`, the ordinal it denotes is the successor of the
ordinal `p` denotes. -/
theorem repr_pred?_eq_some {x p : Level} (h : PredLevelOrder.pred? x = some p) :
    (toNONote x).repr = Order.succ (toNONote p).repr := by
  have hx : x = succ p := PredLevelOrder.pred?_eq_some.mp h
  rw [hx, repr_succ, ← Order.succ_eq_add_one]

/-- A level has no predecessor exactly when the ordinal it denotes is zero or a limit
ordinal. The limit predicate is `Order.IsSuccLimit`. -/
theorem pred?_eq_none_iff_repr_zero_or_isSuccLimit {x : Level} :
    PredLevelOrder.pred? x = none ↔
      (toNONote x).repr = 0 ∨ Order.IsSuccLimit (toNONote x).repr := by
  constructor
  · intro h
    have hc : Cnf.pred? x.1 = none := by
      cases hc : Cnf.pred? x.1 with
      | none => rfl
      | some q =>
        have hxsucc : x = succ ⟨q, Cnf.nf_of_pred?_eq_some x.2 hc⟩ :=
          ext (Cnf.eq_succ_of_pred?_eq_some x.2 hc)
        rw [PredLevelOrder.pred?_eq_some.mpr hxsucc] at h
        exact nomatch h
    exact Cnf.repr_zero_or_isSuccLimit_of_pred?_eq_none x.2 hc
  · intro hOr
    refine PredLevelOrder.pred?_eq_none.mpr fun p hp => ?_
    have hs : (toNONote x).repr = Order.succ (toNONote p).repr :=
      repr_pred?_eq_some (PredLevelOrder.pred?_eq_some.mpr hp.symm)
    cases hOr with
    | inl h0 =>
      have hsum : (toNONote p).repr + 1 = 0 := by
        rw [← Order.succ_eq_add_one, ← hs, h0]
      exact one_ne_zero (Ordinal.add_eq_zero_iff.mp hsum).2
    | inr hlim =>
      exact Order.not_isSuccLimit_succ (toNONote p).repr (hs.symm ▸ hlim)

/-- A level is a limit exactly when the ordinal it denotes is a limit ordinal.
The limit predicate is `Order.IsSuccLimit`. -/
theorem isLimit_iff_repr_isSuccLimit {x : Level} :
    LevelOrder.IsLimit x ↔ Order.IsSuccLimit (toNONote x).repr := by
  constructor
  · intro h
    cases (pred?_eq_none_iff_repr_zero_or_isSuccLimit.mp
        (PredLevelOrder.pred?_eq_none_of_isLimit h)) with
    | inl h0 =>
      have hlt : (toNONote zero).repr < (toNONote x).repr := lt_iff_repr_lt.mp h.1
      rw [repr_zero, h0] at hlt
      exact absurd hlt (lt_irrefl _)
    | inr hlim =>
      exact hlim
  · intro h
    refine ⟨lt_iff_repr_lt.mpr (repr_zero ▸ h.pos), fun p hp => ?_⟩
    exact Order.not_isSuccLimit_succ (toNONote p).repr
      ((repr_pred?_eq_some (PredLevelOrder.pred?_eq_some.mpr hp.symm)).symm ▸ h)

/-- The sum of two levels is the sum of the normal notations. -/
theorem toNONote_add (x y : Level) : toNONote (add x y) = toNONote x + toNONote y := by
  apply Subtype.ext
  exact Cnf.toONote_add x.1 y.1

/-- The product of two levels is the product of the normal notations. -/
theorem toNONote_mul (x y : Level) : toNONote (mul x y) = toNONote x * toNONote y := by
  apply Subtype.ext
  exact Cnf.toONote_mul x.1 y.1

/-- The power of two levels is the power of the normal notations. -/
theorem toNONote_pow (x y : Level) : toNONote (pow x y) = NONote.opow (toNONote x) (toNONote y) := by
  apply Subtype.ext
  exact Cnf.toONote_pow x.1 y.1

/-- A sum of levels denotes the sum of the ordinals. -/
theorem repr_add (x y : Level) :
    (toNONote (add x y)).repr = (toNONote x).repr + (toNONote y).repr := by
  rw [toNONote_add, NONote.repr_add]

/-- A product of levels denotes the product of the ordinals. -/
theorem repr_mul (x y : Level) :
    (toNONote (mul x y)).repr = (toNONote x).repr * (toNONote y).repr := by
  rw [toNONote_mul, NONote.repr_mul]

/-- A power of levels denotes the power of the ordinals. -/
theorem repr_pow (x y : Level) :
    (toNONote (pow x y)).repr = (toNONote x).repr ^ (toNONote y).repr := by
  rw [toNONote_pow, NONote.repr_opow]

/-- Levels that denote one ordinal are one level. -/
theorem eq_of_repr_eq {x y : Level} (h : (toNONote x).repr = (toNONote y).repr) : x = y := by
  have same : toNONote x = toNONote y := by
    rcases lt_trichotomy (toNONote x) (toNONote y) with lt | eq | gt
    · exact absurd h (ne_of_lt lt)
    · exact eq
    · exact absurd h.symm (ne_of_lt gt)
  exact orderIsoNONote.injective same

/-- **The exponent law for every base**: a power at a sum of exponents is the product of the
powers. The three operations are the ordinal ones (`repr_add`, `repr_mul`, `repr_pow`), and
the law holds for ordinals. -/
theorem pow_add (x y z : Level) : pow x (add y z) = mul (pow x y) (pow x z) :=
  eq_of_repr_eq (by
    rw [repr_pow, repr_add, repr_mul, repr_pow, repr_pow, Ordinal.opow_add])

/-- A power at a product of exponents is the iterated power. -/
theorem pow_mul (x y z : Level) : pow x (mul y z) = pow (pow x y) z :=
  eq_of_repr_eq (by
    rw [repr_pow, repr_mul, repr_pow, repr_pow, Ordinal.opow_mul])

end Level

end Mettapedia.TypeTheory.UniverseLevel
