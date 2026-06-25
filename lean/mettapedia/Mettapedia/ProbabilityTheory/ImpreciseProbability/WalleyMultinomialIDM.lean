import Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet
import Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles

/-!
# Walley's Multinomial IDM as a Finite Credal Set

This module lifts the binary IDM credal-set semantics to a categorical
`k`-outcome carrier.

For observed counts `nᵢ` and IDM strength `s > 0`, the predictive credal set is
the family

`P(i) = (nᵢ + s tᵢ) / (n + s)`

where `t` ranges over the probability simplex.  The upper endpoint for a
category is always attained by putting all prior mass on that category.  The
lower endpoint is attained only when there is another category to receive the
prior mass; this is why the lower theorem carries an explicit `j ≠ i`
hypothesis.
-/

open scoped BigOperators

namespace Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDM

open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet
open Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles

/-! ## Simplex-indexed predictive distributions -/

/-- Indicator gamble for one categorical outcome. -/
noncomputable def categoryGamble {k : ℕ} (i : Fin k) : Gamble (Fin k) :=
  fun j => if j = i then 1 else 0

/-- The expectation of a category indicator is exactly that category's mass. -/
theorem expectedValue_categoryGamble {k : ℕ} (P : ProbDist (Fin k)) (i : Fin k) :
    expectedValue P (categoryGamble i) = P.prob i := by
  unfold expectedValue categoryGamble
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- A multinomial IDM predictive distribution for one simplex point `t`. -/
noncomputable def predictiveDist {k : ℕ}
    (e : MultiEvidence k) (s : ℝ) (hs : 0 < s)
    (t : Fin k → ℝ) (ht_nonneg : ∀ i, 0 ≤ t i)
    (ht_sum : ∑ i : Fin k, t i = 1) : ProbDist (Fin k) :=
  let denom : ℝ := (e.total : ℝ) + s
  have hden_pos : 0 < denom := by
    have hTotal : 0 ≤ (e.total : ℝ) := by exact_mod_cast (Nat.zero_le e.total)
    linarith
  {
    prob := fun i => ((e.counts i : ℝ) + s * t i) / denom
    non_neg := by
      intro i
      exact div_nonneg
        (by
          have hCount : 0 ≤ (e.counts i : ℝ) := Nat.cast_nonneg _
          nlinarith [hCount, hs.le, ht_nonneg i])
        (le_of_lt hden_pos)
    sum_one := by
      change (∑ i : Fin k, (((e.counts i : ℝ) + s * t i) / denom)) = 1
      calc
        (∑ i : Fin k, (((e.counts i : ℝ) + s * t i) / denom))
            = (∑ i : Fin k, ((e.counts i : ℝ) + s * t i)) / denom := by
                simp [div_eq_mul_inv, Finset.sum_mul]
        _ = ((∑ i : Fin k, (e.counts i : ℝ)) + s * (∑ i : Fin k, t i)) / denom := by
                rw [Finset.sum_add_distrib]
                simp [Finset.mul_sum]
        _ = ((e.total : ℝ) + s) / denom := by
                simp [MultiEvidence.total, Nat.cast_sum, ht_sum]
        _ = 1 := by
                change ((e.total : ℝ) + s) / ((e.total : ℝ) + s) = 1
                field_simp [hden_pos.ne']
  }

@[simp] theorem predictiveDist_prob {k : ℕ}
    (e : MultiEvidence k) (s : ℝ) (hs : 0 < s)
    (t : Fin k → ℝ) (ht_nonneg : ∀ i, 0 ≤ t i)
    (ht_sum : ∑ i : Fin k, t i = 1) (i : Fin k) :
    (predictiveDist e s hs t ht_nonneg ht_sum).prob i =
      ((e.counts i : ℝ) + s * t i) / ((e.total : ℝ) + s) := by
  simp [predictiveDist]

theorem predictiveDist_expected_categoryGamble {k : ℕ}
    (e : MultiEvidence k) (s : ℝ) (hs : 0 < s)
    (t : Fin k → ℝ) (ht_nonneg : ∀ i, 0 ≤ t i)
    (ht_sum : ∑ i : Fin k, t i = 1) (i : Fin k) :
    expectedValue (predictiveDist e s hs t ht_nonneg ht_sum) (categoryGamble i) =
      ((e.counts i : ℝ) + s * t i) / ((e.total : ℝ) + s) := by
  rw [expectedValue_categoryGamble]
  simp

/-- The multinomial IDM predictive credal set over `Fin k`. -/
noncomputable def credalSet {k : ℕ}
    (e : MultiEvidence k) (s : ℝ) (hs : 0 < s) : CredalSetFinite (Fin k) :=
  {P | ∃ t : Fin k → ℝ,
      ∃ ht_nonneg : ∀ i, 0 ≤ t i,
        ∃ ht_sum : ∑ i : Fin k, t i = 1,
          P = predictiveDist e s hs t ht_nonneg ht_sum}

/-! ## Category endpoints -/

noncomputable def lowerEndpoint {k : ℕ}
    (e : MultiEvidence k) (s : ℝ) (i : Fin k) : ℝ :=
  (e.counts i : ℝ) / ((e.total : ℝ) + s)

noncomputable def upperEndpoint {k : ℕ}
    (e : MultiEvidence k) (s : ℝ) (i : Fin k) : ℝ :=
  ((e.counts i : ℝ) + s) / ((e.total : ℝ) + s)

/-- Every distribution in the multinomial IDM credal set lies above the category
lower endpoint. -/
theorem lower_bound_each {k : ℕ}
    (e : MultiEvidence k) (s : ℝ) (hs : 0 < s) (i : Fin k)
    {P : ProbDist (Fin k)} (hP : P ∈ credalSet e s hs) :
    lowerEndpoint e s i ≤ expectedValue P (categoryGamble i) := by
  rcases hP with ⟨t, ht_nonneg, ht_sum, rfl⟩
  rw [predictiveDist_expected_categoryGamble]
  unfold lowerEndpoint
  have hden : 0 ≤ (e.total : ℝ) + s := by
    have hTotal : 0 ≤ (e.total : ℝ) := by exact_mod_cast (Nat.zero_le e.total)
    linarith
  apply div_le_div_of_nonneg_right ?_ hden
  nlinarith [hs.le, ht_nonneg i]

/-- Every distribution in the multinomial IDM credal set lies below the category
upper endpoint. -/
theorem upper_bound_each {k : ℕ}
    (e : MultiEvidence k) (s : ℝ) (hs : 0 < s) (i : Fin k)
    {P : ProbDist (Fin k)} (hP : P ∈ credalSet e s hs) :
    expectedValue P (categoryGamble i) ≤ upperEndpoint e s i := by
  rcases hP with ⟨t, ht_nonneg, ht_sum, rfl⟩
  rw [predictiveDist_expected_categoryGamble]
  unfold upperEndpoint
  have hden : 0 ≤ (e.total : ℝ) + s := by
    have hTotal : 0 ≤ (e.total : ℝ) := by exact_mod_cast (Nat.zero_le e.total)
    linarith
  have hti_le_one : t i ≤ 1 := by
    rw [← ht_sum]
    exact Finset.single_le_sum (fun j _ => ht_nonneg j) (Finset.mem_univ i)
  apply div_le_div_of_nonneg_right ?_ hden
  nlinarith [hs.le, hti_le_one]

/-! ## Extreme simplex points -/

/-- Put all prior mass on one category. -/
noncomputable def pointMassT {k : ℕ} (i : Fin k) : Fin k → ℝ :=
  fun j => if j = i then 1 else 0

theorem pointMassT_nonneg {k : ℕ} (i : Fin k) :
    ∀ j, 0 ≤ pointMassT i j := by
  intro j
  by_cases h : j = i <;> simp [pointMassT, h]

theorem pointMassT_sum {k : ℕ} (i : Fin k) :
    ∑ j : Fin k, pointMassT i j = 1 := by
  unfold pointMassT
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The upper endpoint is attained by putting all prior mass on the queried
category. -/
theorem upperEndpoint_mem_values {k : ℕ}
    (e : MultiEvidence k) (s : ℝ) (hs : 0 < s) (i : Fin k) :
    upperEndpoint e s i ∈
      Set.image (fun P => expectedValue P (categoryGamble i))
        (credalSet e s hs) := by
  refine ⟨
    predictiveDist e s hs (pointMassT i) (pointMassT_nonneg i) (pointMassT_sum i),
    ?_, ?_⟩
  · exact ⟨pointMassT i, pointMassT_nonneg i, pointMassT_sum i, rfl⟩
  · change expectedValue
      (predictiveDist e s hs (pointMassT i) (pointMassT_nonneg i) (pointMassT_sum i))
        (categoryGamble i) = upperEndpoint e s i
    rw [predictiveDist_expected_categoryGamble]
    simp [upperEndpoint, pointMassT]

/-- The lower endpoint is attained by putting all prior mass on some other
category.  This explicit hypothesis is essential for excluding the degenerate
one-category case. -/
theorem lowerEndpoint_mem_values_of_other {k : ℕ}
    (e : MultiEvidence k) (s : ℝ) (hs : 0 < s) (i j : Fin k) (hji : j ≠ i) :
    lowerEndpoint e s i ∈
      Set.image (fun P => expectedValue P (categoryGamble i))
        (credalSet e s hs) := by
  refine ⟨
    predictiveDist e s hs (pointMassT j) (pointMassT_nonneg j) (pointMassT_sum j),
    ?_, ?_⟩
  · exact ⟨pointMassT j, pointMassT_nonneg j, pointMassT_sum j, rfl⟩
  · change expectedValue
      (predictiveDist e s hs (pointMassT j) (pointMassT_nonneg j) (pointMassT_sum j))
        (categoryGamble i) = lowerEndpoint e s i
    rw [predictiveDist_expected_categoryGamble]
    have hij : i ≠ j := fun h => hji h.symm
    simp [lowerEndpoint, pointMassT, hij]

/-! ## Credal lower/upper expectations -/

/-- The credal-set lower expectation derives Walley's multinomial IDM lower
endpoint for a category, provided another category exists to receive all prior
mass. -/
theorem lowerProb_categoryGamble_eq_of_other {k : ℕ}
    (e : MultiEvidence k) (s : ℝ) (hs : 0 < s) (i j : Fin k) (hji : j ≠ i) :
    lowerProb (credalSet e s hs) (categoryGamble i) = lowerEndpoint e s i := by
  unfold lowerProb
  let values := Set.image (fun P => expectedValue P (categoryGamble i)) (credalSet e s hs)
  have hmem : lowerEndpoint e s i ∈ values :=
    lowerEndpoint_mem_values_of_other e s hs i j hji
  have hbdd : BddBelow values := by
    refine ⟨lowerEndpoint e s i, ?_⟩
    intro y hy
    rcases hy with ⟨P, hP, rfl⟩
    exact lower_bound_each e s hs i hP
  have hnonempty : values.Nonempty := ⟨lowerEndpoint e s i, hmem⟩
  apply le_antisymm
  · exact csInf_le hbdd hmem
  · apply le_csInf hnonempty
    intro y hy
    rcases hy with ⟨P, hP, rfl⟩
    exact lower_bound_each e s hs i hP

/-- The credal-set upper expectation derives Walley's multinomial IDM upper
endpoint for a category. -/
theorem upperProb_categoryGamble_eq {k : ℕ}
    (e : MultiEvidence k) (s : ℝ) (hs : 0 < s) (i : Fin k) :
    upperProb (credalSet e s hs) (categoryGamble i) = upperEndpoint e s i := by
  unfold upperProb
  let values := Set.image (fun P => expectedValue P (categoryGamble i)) (credalSet e s hs)
  have hmem : upperEndpoint e s i ∈ values :=
    upperEndpoint_mem_values e s hs i
  have hbdd : BddAbove values := by
    refine ⟨upperEndpoint e s i, ?_⟩
    intro y hy
    rcases hy with ⟨P, hP, rfl⟩
    exact upper_bound_each e s hs i hP
  have hnonempty : values.Nonempty := ⟨upperEndpoint e s i, hmem⟩
  apply le_antisymm
  · apply csSup_le hnonempty
    intro y hy
    rcases hy with ⟨P, hP, rfl⟩
    exact upper_bound_each e s hs i hP
  · exact le_csSup hbdd hmem

/-- Width of the category envelope in the nondegenerate multinomial case. -/
theorem category_width_eq_idmWidth_of_other {k : ℕ}
    (e : MultiEvidence k) (s : ℝ) (hs : 0 < s) (i j : Fin k) (hji : j ≠ i) :
    upperProb (credalSet e s hs) (categoryGamble i) -
        lowerProb (credalSet e s hs) (categoryGamble i) =
      s / ((e.total : ℝ) + s) := by
  rw [upperProb_categoryGamble_eq, lowerProb_categoryGamble_eq_of_other e s hs i j hji]
  unfold upperEndpoint lowerEndpoint
  have hden : ((e.total : ℝ) + s) ≠ 0 := by
    have hTotal : 0 ≤ (e.total : ℝ) := by exact_mod_cast (Nat.zero_le e.total)
    linarith
  field_simp [hden]
  ring

/-! ## Bridge to the existing `EvidenceDirichlet` IDM formulas -/

/-- The credal-set lower endpoint is the existing `EvidenceDirichlet.idmLower`
formula. -/
theorem lowerEndpoint_eq_idmLower {k : ℕ}
    (ctx : IDMPredictiveContext) (e : MultiEvidence k) (i : Fin k) :
    lowerEndpoint e ctx.s i = idmLower ctx e i := by
  rfl

/-- The credal-set upper endpoint is the existing `EvidenceDirichlet.idmUpper`
formula. -/
theorem upperEndpoint_eq_idmUpper {k : ℕ}
    (ctx : IDMPredictiveContext) (e : MultiEvidence k) (i : Fin k) :
    upperEndpoint e ctx.s i = idmUpper ctx e i := by
  rfl

/-- The credal-set category lower expectation derives the existing
`EvidenceDirichlet.idmLower` formula in the nondegenerate categorical case. -/
theorem lowerProb_categoryGamble_eq_idmLower_of_other {k : ℕ}
    (ctx : IDMPredictiveContext) (e : MultiEvidence k)
    (i j : Fin k) (hji : j ≠ i) :
    lowerProb (credalSet e ctx.s ctx.s_pos) (categoryGamble i) =
      idmLower ctx e i := by
  rw [lowerProb_categoryGamble_eq_of_other e ctx.s ctx.s_pos i j hji]
  rfl

/-- The credal-set category upper expectation derives the existing
`EvidenceDirichlet.idmUpper` formula. -/
theorem upperProb_categoryGamble_eq_idmUpper {k : ℕ}
    (ctx : IDMPredictiveContext) (e : MultiEvidence k) (i : Fin k) :
    upperProb (credalSet e ctx.s ctx.s_pos) (categoryGamble i) =
      idmUpper ctx e i := by
  rw [upperProb_categoryGamble_eq]
  rfl

/-- The nondegenerate category-envelope width is the existing
`EvidenceDirichlet.idmWidth` formula. -/
theorem category_width_eq_EvidenceDirichlet_idmWidth_of_other {k : ℕ}
    (ctx : IDMPredictiveContext) (e : MultiEvidence k)
    (i j : Fin k) (hji : j ≠ i) :
    upperProb (credalSet e ctx.s ctx.s_pos) (categoryGamble i) -
        lowerProb (credalSet e ctx.s ctx.s_pos) (categoryGamble i) =
      idmWidth ctx e := by
  rw [category_width_eq_idmWidth_of_other e ctx.s ctx.s_pos i j hji]

end Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDM
