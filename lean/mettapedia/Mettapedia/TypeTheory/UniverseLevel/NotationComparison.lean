import Mettapedia.TypeTheory.UniverseLevel.Notation
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
    simp [succ, toONote, add_assoc, one_add_one_eq_two]
  | oadd (oadd e' n' a') n a, h => by
    rw [succ, toONote, ONote.repr, repr_succ h.snd, ← add_assoc]
    rfl

/-- `omega` denotes `ω`. -/
theorem repr_omega : (toONote omega).repr = ω := by
  simp [toONote, omega]

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

end Level

end Mettapedia.TypeTheory.UniverseLevel
