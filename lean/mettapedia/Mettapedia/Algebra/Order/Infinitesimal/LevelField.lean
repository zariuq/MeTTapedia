import Mathlib.RingTheory.HahnSeries.Lex
import Mathlib.RingTheory.HahnSeries.Summable
import Mettapedia.Algebra.Order.Infinitesimal.NilpotentNotOrdered

/-!
# A field of levels: rationals with one infinite and one infinitesimal generator

The carrier is `Lex (HahnSeries ℤ ℚ)` — formal series with rational
coefficients indexed by integer *levels*, compared lexicographically from the
lowest level present.  Everything algebraic is upstream: it is a field, a
linear order, and a strict ordered ring, none of which is rebuilt here.

The convention is that a lower level is a larger magnitude, so that

    Ω := single (-1) 1     is above every rational,
    Ω⁻¹ := single 1 1      is below every positive rational,

and `Ω * Ω⁻¹ = 1`.  Two facts make this the *other* kind of infinitesimal from
the dual numbers of `NilpotentNotOrdered.lean`:

* `Om_mul_omInv` — the infinitesimal is invertible;
* `omInv_mul_omInv_ne_zero` — it is not nilpotent, which is forced, since the
  carrier is an ordered ring and `sq_ne_zero_of_ne_zero` applies.

`not_archimedean` records that the order is genuinely non-Archimedean, so no
finite multiple of `1` reaches `Ω`. The levels are not a fiction of the
representation: upstream's `archimedeanClassOrderIsoWithTop` identifies the
Archimedean classes of this carrier with `WithTop ℤ`, i.e. with the levels
themselves plus a class for zero.

This is the *mathematical* layer and it is noncomputable: `HahnSeries` stores a
coefficient function. The executable counterpart is a finite list of
level/coefficient pairs, related to this layer by a proved homomorphism.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Order.Infinitesimal

open HahnSeries

/-- Rationals with integer levels, ordered from the lowest level present. -/
abbrev LevelField : Type := Lex (HahnSeries ℤ ℚ)

/-- A rational as a level-zero series. -/
noncomputable def ofRat (q : ℚ) : LevelField := toLex (C q)

/-- The infinite generator: one unit at level `-1`. -/
noncomputable def Om : LevelField := toLex (single (-1 : ℤ) (1 : ℚ))

/-- Its inverse: one unit at level `1`. -/
noncomputable def omInv : LevelField := toLex (single (1 : ℤ) (1 : ℚ))

@[simp] theorem ofLex_ofRat (q : ℚ) : ofLex (ofRat q) = single 0 q := rfl
@[simp] theorem ofLex_Om : ofLex Om = single (-1 : ℤ) (1 : ℚ) := rfl
@[simp] theorem ofLex_omInv : ofLex omInv = single (1 : ℤ) (1 : ℚ) := rfl

/-! ## The generators are inverse to one another -/

/-- **The infinitesimal is invertible.**  This is the law the dual-number
infinitesimal cannot satisfy. -/
theorem Om_mul_omInv : Om * omInv = 1 := by
  show single (-1 : ℤ) (1 : ℚ) * single (1 : ℤ) (1 : ℚ) = 1
  rw [single_mul_single]
  norm_num

theorem omInv_mul_Om : omInv * Om = 1 := by
  rw [mul_comm]; exact Om_mul_omInv

/-! ## Order facts -/

/-- Every rational is below `Ω`. -/
theorem ofRat_lt_Om (q : ℚ) : ofRat q < Om := by
  rw [lt_iff]
  refine ⟨(-1 : ℤ), ?_, ?_⟩
  · intro j hj
    rw [ofLex_ofRat, ofLex_Om, coeff_single_of_ne (by omega), coeff_single_of_ne (by omega)]
  · rw [ofLex_ofRat, ofLex_Om, coeff_single_of_ne (by omega), coeff_single_same]
    norm_num

theorem Om_pos : 0 < Om := by
  have h := ofRat_lt_Om 0
  rwa [show ofRat 0 = 0 from by rw [ofRat, map_zero]; rfl] at h

/-- Every positive rational is above `Ω⁻¹`: it is a genuine infinitesimal. -/
theorem omInv_lt_ofRat {q : ℚ} (hq : 0 < q) : omInv < ofRat q := by
  rw [lt_iff]
  refine ⟨(0 : ℤ), ?_, ?_⟩
  · intro j hj
    rw [ofLex_omInv, ofLex_ofRat, coeff_single_of_ne (by omega), coeff_single_of_ne (by omega)]
  · rw [ofLex_omInv, ofLex_ofRat, coeff_single_of_ne (by omega), coeff_single_same]
    exact hq

theorem omInv_pos : 0 < omInv := by
  rw [lt_iff]
  refine ⟨(1 : ℤ), ?_, ?_⟩
  · intro j hj
    rw [ofLex_omInv, coeff_single_of_ne (by omega)]
    rfl
  · rw [ofLex_omInv, coeff_single_same]
    show (0 : ℚ) < 1
    norm_num

theorem omInv_ne_zero : omInv ≠ 0 := ne_of_gt omInv_pos

/-- **The infinitesimal is not nilpotent**, which in an ordered ring it could
not be: `sq_ne_zero_of_ne_zero` already forbids it.  Here it is also visible
directly — the square sits at level `2`. -/
theorem omInv_mul_omInv_ne_zero : omInv * omInv ≠ 0 :=
  sq_ne_zero_of_ne_zero omInv_ne_zero

theorem omInv_mul_omInv : omInv * omInv = toLex (single (2 : ℤ) (1 : ℚ)) := by
  show single (1 : ℤ) (1 : ℚ) * single (1 : ℤ) (1 : ℚ) = single (2 : ℤ) (1 : ℚ)
  rw [single_mul_single]
  norm_num

/-! ## The rationals sit inside, order and all -/

theorem ofRat_zero : ofRat 0 = 0 := by rw [ofRat, map_zero]; rfl

/-- **The embedding of the rationals is strictly monotone**: at level `0` the
comparison is the rationals' own. -/
theorem ofRat_lt_ofRat {a b : ℚ} (h : a < b) : ofRat a < ofRat b := by
  rw [lt_iff]
  refine ⟨(0 : ℤ), ?_, ?_⟩
  · intro j hj
    rw [ofLex_ofRat, ofLex_ofRat, coeff_single_of_ne (by omega),
      coeff_single_of_ne (by omega)]
  · rw [ofLex_ofRat, ofLex_ofRat, coeff_single_same, coeff_single_same]
    exact h

theorem ofRat_le_ofRat {a b : ℚ} (h : a ≤ b) : ofRat a ≤ ofRat b := by
  rcases lt_or_eq_of_le h with hlt | rfl
  · exact le_of_lt (ofRat_lt_ofRat hlt)
  · exact le_refl _

theorem ofRat_nonneg {q : ℚ} (hq : 0 ≤ q) : 0 ≤ ofRat q :=
  ofRat_zero ▸ ofRat_le_ofRat hq

/-! ## Non-Archimedean -/

theorem ofRat_natCast (n : ℕ) : ofRat (n : ℚ) = (n : LevelField) := by
  rw [ofRat, map_natCast]
  rfl

/-- No finite multiple of `1` reaches `Ω`. -/
theorem natCast_lt_Om (n : ℕ) : (n : LevelField) < Om := by
  rw [← ofRat_natCast]
  exact ofRat_lt_Om _

/-- **The order is not Archimedean.** -/
theorem not_archimedean : ¬ Archimedean LevelField := by
  intro h
  obtain ⟨n, hn⟩ := h.arch Om (y := (1 : LevelField)) one_pos
  rw [nsmul_eq_mul, mul_one] at hn
  exact absurd hn (not_le_of_gt (natCast_lt_Om n))

/-! ## The levels are the Archimedean classes

Upstream identifies the Archimedean classes of this carrier with the levels,
so "order of magnitude" is not an artefact of the chosen representation. -/

/-- The Archimedean classes of the carrier are the levels, plus one class for
zero. -/
noncomputable def levelClasses : ArchimedeanClass LevelField ≃o WithTop ℤ :=
  archimedeanClassOrderIsoWithTop ℤ ℚ

@[simp] theorem levelClasses_apply (x : LevelField) :
    levelClasses (ArchimedeanClass.mk x) = (ofLex x).orderTop :=
  archimedeanClassOrderIsoWithTop_apply x

/-- `Ω` and `Ω⁻¹` sit in different Archimedean classes: they are genuinely
different orders of magnitude, not merely different numbers. -/
theorem Om_omInv_different_classes :
    ArchimedeanClass.mk Om ≠ ArchimedeanClass.mk omInv := by
  intro h
  have := congrArg levelClasses h
  rw [levelClasses_apply, levelClasses_apply, ofLex_Om, ofLex_omInv,
    orderTop_single (by norm_num), orderTop_single (by norm_num)] at this
  exact absurd this (by decide)

end Mettapedia.Algebra.Order.Infinitesimal

#print axioms Mettapedia.Algebra.Order.Infinitesimal.Om_mul_omInv
#print axioms Mettapedia.Algebra.Order.Infinitesimal.ofRat_lt_Om
#print axioms Mettapedia.Algebra.Order.Infinitesimal.omInv_lt_ofRat
#print axioms Mettapedia.Algebra.Order.Infinitesimal.omInv_mul_omInv_ne_zero
#print axioms Mettapedia.Algebra.Order.Infinitesimal.not_archimedean
#print axioms Mettapedia.Algebra.Order.Infinitesimal.Om_omInv_different_classes
