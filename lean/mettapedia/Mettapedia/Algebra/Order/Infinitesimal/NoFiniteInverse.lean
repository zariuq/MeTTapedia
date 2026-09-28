import Mettapedia.Algebra.Order.Infinitesimal.LevelSeries

/-!
# The finite representation is a ring, not a field

`LevelField` is a field: every nonzero element has an inverse.  The executable
representation is a *finite* list of terms, and this file proves that the
finiteness is a real restriction rather than an accident of the encoding:

`Om - 1` is nonzero, so it is invertible in the field, but **no level series
denotes its inverse**.  The inverse is `Ω⁻¹ + Ω⁻² + Ω⁻³ + ⋯`, and no finite
list has that value.

The argument is elementary and needs neither the order nor infinite sums.  Put
a series in canonical form and look at its two extreme levels.  Multiplying by
`Ω - 1` moves each term to two places, one level lower and the same level
negated.  At the *highest* level nothing arrives from above, so the product's
coefficient there is minus the original's: nonzero.  At one below the *lowest*
level nothing arrives from below, so the product's coefficient there is the
original's: also nonzero.  A product equal to `1` has a nonzero coefficient
only at level `0`, so the highest level must be `0` and the lowest must be `1`
— and the lowest cannot exceed the highest.

This is the fact behind treating the fragment as an exact *numeric family*
rather than as a numeric foundation: division by a single term is exact and
stays inside the representation (`divideByTerm`), while general inversion
leaves it.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Order.Infinitesimal

open HahnSeries LevelSeries

/-- `Ω - 1`, as data. -/
def omegaSubOne : LevelSeries := [(-1, 1), (0, -1)]

@[simp] theorem toHahn_omegaSubOne :
    toHahn omegaSubOne = single (-1 : ℤ) (1 : ℚ) + single (0 : ℤ) (-1 : ℚ) := by
  simp [omegaSubOne, toHahn]

theorem toLevelField_omegaSubOne : toLevelField omegaSubOne = Om - 1 := by
  show toLex (toHahn omegaSubOne) = Om - 1
  rw [toHahn_omegaSubOne,
    show (single (0 : ℤ) (-1 : ℚ)) = -(1 : HahnSeries ℤ ℚ) by
      rw [← single_zero_one, ← single_neg],
    ← sub_eq_add_neg]
  rfl

/-! ## The two extreme levels of a canonical series -/

/-- **A canonical nonempty series has a top level, and does not vanish there.**
Proved by induction: the head sits strictly below every later level, so it
contributes nothing at the top. -/
theorem exists_top_level : ∀ {l : LevelSeries}, l ≠ [] → Sorted l → NoZero l →
    ∃ m : ℤ, (∀ t ∈ l, t.1 ≤ m) ∧ (toHahn l).coeff m ≠ 0
  | [], h, _, _ => absurd rfl h
  | [(i, a)], _, hs, hz => by
      refine ⟨i, ?_, ?_⟩
      · intro t ht
        rcases List.mem_singleton.mp ht with rfl
        exact le_rfl
      · rw [coeff_toHahn_head hs]
        exact hz (i, a) List.mem_cons_self
  | (i, a) :: u :: rest, _, hs, hz => by
      obtain ⟨m, hbound, hne⟩ :=
        exists_top_level (l := u :: rest) (by simp) hs.2
          (fun t ht => hz t (List.mem_cons_of_mem _ ht))
      have hiu : i < u.1 := hs.1 u List.mem_cons_self
      have him : i < m := lt_of_lt_of_le hiu (hbound u List.mem_cons_self)
      refine ⟨m, ?_, ?_⟩
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact le_of_lt him
        · exact hbound t ht'
      · simp only [toHahn_cons, coeff_add]
        rw [coeff_single_of_ne (show m ≠ i by omega), zero_add]
        exact hne

/-- **And a bottom level, where it also does not vanish** — namely the head. -/
theorem exists_bottom_level : ∀ {l : LevelSeries}, l ≠ [] → Sorted l → NoZero l →
    ∃ n : ℤ, (∀ t ∈ l, n ≤ t.1) ∧ (toHahn l).coeff n ≠ 0
  | [], h, _, _ => absurd rfl h
  | (i, a) :: rest, _, hs, hz => by
      refine ⟨i, ?_, ?_⟩
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact le_rfl
        · exact le_of_lt (hs.1 t ht')
      · rw [coeff_toHahn_head hs]
        exact hz (i, a) List.mem_cons_self

/-! ## What multiplying by `Ω - 1` does at the extremes -/

/-- At a level at or above every level of `q`, nothing arrives from above, so
the product's coefficient is exactly minus `q`'s. -/
theorem coeff_mul_omegaSubOne_at_upper {m : ℤ} :
    ∀ {q : LevelSeries}, (∀ t ∈ q, t.1 ≤ m) →
      (toHahn (mul q omegaSubOne)).coeff m = - (toHahn q).coeff m
  | [], _ => by simp [mul]
  | (i, c) :: rest, h => by
      have hrec := coeff_mul_omegaSubOne_at_upper (q := rest)
        (fun t ht => h t (List.mem_cons_of_mem _ ht))
      have him : i ≤ m := h (i, c) List.mem_cons_self
      have hstep : mul ((i, c) :: rest) omegaSubOne
          = (i + (-1 : ℤ), c * 1) :: (i + (0 : ℤ), c * (-1)) :: mul rest omegaSubOne := by
        simp [mul, omegaSubOne, scaleTerm]
      simp only [hstep, toHahn_cons, coeff_add, hrec, add_zero, mul_one, mul_neg_one]
      rw [coeff_single_of_ne (show m ≠ i + (-1 : ℤ) by omega)]
      by_cases hc : m = i
      · subst hc
        rw [coeff_single_same, coeff_single_same]
        ring
      · rw [coeff_single_of_ne hc, coeff_single_of_ne hc]
        ring

/-- At one level below every level of `q`, nothing arrives from below, so the
product's coefficient there is exactly `q`'s coefficient at the bottom. -/
theorem coeff_mul_omegaSubOne_at_lower {n : ℤ} :
    ∀ {q : LevelSeries}, (∀ t ∈ q, n ≤ t.1) →
      (toHahn (mul q omegaSubOne)).coeff (n - 1) = (toHahn q).coeff n
  | [], _ => by simp [mul]
  | (i, c) :: rest, h => by
      have hrec := coeff_mul_omegaSubOne_at_lower (q := rest)
        (fun t ht => h t (List.mem_cons_of_mem _ ht))
      have hni : n ≤ i := h (i, c) List.mem_cons_self
      have hstep : mul ((i, c) :: rest) omegaSubOne
          = (i + (-1 : ℤ), c * 1) :: (i + (0 : ℤ), c * (-1)) :: mul rest omegaSubOne := by
        simp [mul, omegaSubOne, scaleTerm]
      simp only [hstep, toHahn_cons, coeff_add, add_zero, mul_one, mul_neg_one]
      rw [hrec, coeff_single_of_ne (show n - 1 ≠ i by omega)]
      by_cases hc : n = i
      · subst hc
        rw [show n - 1 = n + (-1 : ℤ) by ring, coeff_single_same, coeff_single_same]
        ring
      · rw [coeff_single_of_ne (show n - 1 ≠ i + (-1 : ℤ) by omega),
          coeff_single_of_ne hc]
        ring

/-! ## `Ω - 1` has no inverse in the representation -/

/-- A series whose product with `Ω - 1` is `1` would have to have its top level
at `0` and its bottom level at `1`. -/
theorem toHahn_mul_omegaSubOne_ne_one (q : LevelSeries) :
    toHahn (mul q omegaSubOne) ≠ 1 := by
  intro hq
  -- Canonicalise: the denotation, hence the product, is unchanged.
  have hnorm : toHahn (mul (norm q) omegaSubOne) = 1 := by
    rw [toHahn_mul, toHahn_norm, ← toHahn_mul]; exact hq
  obtain ⟨hs, hz⟩ := normalized_norm q
  rcases eq_or_ne (norm q) [] with hnil | hnil
  · rw [hnil] at hnorm
    simp [mul] at hnorm
  obtain ⟨m, hmb, hmne⟩ := exists_top_level hnil hs hz
  obtain ⟨n, hnb, hnne⟩ := exists_bottom_level hnil hs hz
  -- The bottom is at or below the top, because the list is nonempty.
  have hnm : n ≤ m := by
    obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ hnil
    exact le_trans (hnb t ht) (hmb t ht)
  -- Top: the product does not vanish at `m`, so `m = 0`.
  have htop : (1 : HahnSeries ℤ ℚ).coeff m ≠ 0 := by
    rw [← hnorm, coeff_mul_omegaSubOne_at_upper hmb]
    simpa using hmne
  have hm0 : m = 0 := by
    by_contra h
    exact htop (by simp [h])
  -- Bottom: the product does not vanish at `n - 1`, so `n = 1`.
  have hbot : (1 : HahnSeries ℤ ℚ).coeff (n - 1) ≠ 0 := by
    rw [← hnorm, coeff_mul_omegaSubOne_at_lower hnb]
    exact hnne
  have hn1 : n = 1 := by
    by_contra h
    exact hbot (by simp [show n - 1 ≠ 0 by omega])
  omega

/-- **The representation is not closed under inversion.**  `Ω - 1` is nonzero,
hence invertible in `LevelField`, but no level series denotes its inverse. -/
theorem no_levelSeries_inverts_omegaSubOne (q : LevelSeries) :
    toLevelField (mul q omegaSubOne) ≠ 1 := by
  intro h
  refine toHahn_mul_omegaSubOne_ne_one q ?_
  have : (toLex (toHahn (mul q omegaSubOne)) : LevelField) = toLex (1 : HahnSeries ℤ ℚ) := h
  exact toLex.injective this

/-- The same, stated against the field element rather than the list: no finite
representation has `(Ω - 1)⁻¹` as its value. -/
theorem toLevelField_ne_inv_omegaSubOne (q : LevelSeries) :
    toLevelField q ≠ (Om - 1)⁻¹ := by
  intro h
  refine no_levelSeries_inverts_omegaSubOne q ?_
  have hone : (1 : LevelField) < Om := by
    have hr := ofRat_lt_Om 1
    rwa [show ofRat 1 = 1 from by rw [ofRat, map_one]; rfl] at hr
  have hne : (Om - 1 : LevelField) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hone)
  calc toLevelField (mul q omegaSubOne)
      = toLevelField q * toLevelField omegaSubOne := by
        show toLex (toHahn (mul q omegaSubOne)) = _
        rw [toHahn_mul]; rfl
    _ = (Om - 1)⁻¹ * (Om - 1) := by rw [h, toLevelField_omegaSubOne]
    _ = 1 := inv_mul_cancel₀ hne

/-! ## The positive side: division by a single term stays inside

The restriction is exactly to inversion of a *sum*.  A single term inverts
exactly, which is why moving between scales never leaves the representation. -/

theorem omega_inverts : toLevelField (mul omega omegaInv) = 1 :=
  toLevelField_mul_omega_omegaInv

end Mettapedia.Algebra.Order.Infinitesimal

#print axioms Mettapedia.Algebra.Order.Infinitesimal.toHahn_mul_omegaSubOne_ne_one
#print axioms Mettapedia.Algebra.Order.Infinitesimal.no_levelSeries_inverts_omegaSubOne
#print axioms Mettapedia.Algebra.Order.Infinitesimal.toLevelField_ne_inv_omegaSubOne
