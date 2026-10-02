import Mettapedia.InformationTheory.ConditionalMutualInformation
import Mettapedia.UniversalAI.UniversalPrediction.Entropy

/-!
# Finite Pinsker inequality

For finite distributions in the natural-log convention,

`(∑ |p - q|) ^ 2 ≤ 2 * klSum p q`,

whenever `p` is absolutely continuous with respect to `q`. The constant is the
binary one. The positive set of `p - q` pushes both distributions forward to a
pair of Bernoulli masses, data processing does not increase divergence, and the
Bernoulli estimate is the closed-interval form of the binary lemma already
proved for Hutter's squared-distance bound. The total variation identity
`∑ |p - q| = 2 * ∑_{q ≤ p} (p - q)` turns that gap into the full `L1` distance.

`Real.log 0 = 0`, so the same real-valued sum is not a divergence once absolute
continuity fails. The two-point counterexample below has `L1` distance `2` and
real-valued divergence `0`.

The split into `{q ≤ p}` uses `Decidable (· ≤ ·)` on `ℝ`. That decidability is
the one already constructed for `LinearOrder ℝ` under `open scoped Classical`
in the real-number library. This file adds no axiom.
-/

namespace Mettapedia.InformationTheory

open Real Finset
open scoped BigOperators
open FiniteRV
open Mettapedia.UniversalAI.UniversalPrediction.Entropy

/-! ## Bernoulli divergence -/

/-- `x log(x/b) + (1-x) log((1-x)/(1-b))`, with the real-log convention. -/
noncomputable def binaryDivergence (b x : ℝ) : ℝ :=
  x * log (x / b) + (1 - x) * log ((1 - x) / (1 - b))

/-- On a reference in `(0, 1)`, the real-log formula agrees with the Bregman form
`klBinary`, including the endpoints `x = 0` and `x = 1`. -/
theorem binaryDivergence_eq_klBinary {b x : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    binaryDivergence b x = klBinary x b := by
  have hbne : b ≠ 0 := hb0.ne'
  have hb1ne : 1 - b ≠ 0 := (sub_pos.mpr hb1).ne'
  unfold binaryDivergence klBinary phi phiDeriv
  by_cases hx0 : x = 0
  · subst hx0
    simp [zero_div, log_zero, log_one, sub_zero]
    ring
  · by_cases hx1 : x = 1
    · subst hx1
      simp [sub_self, zero_div, log_zero, log_one]
      ring
    · have h1x : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
      rw [log_div hx0 hbne, log_div h1x hb1ne]
      ring

theorem two_sq_le_binaryDivergence {b x : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hac : 0 < x → 0 < b) (hac' : 0 < 1 - x → 0 < 1 - b) :
    2 * (x - b) ^ 2 ≤ binaryDivergence b x := by
  by_cases hxb : x = b
  · subst hxb
    have hvanish (y : ℝ) : y * log (y / y) = 0 := by
      by_cases hy : y = 0
      · simp [hy]
      · rw [div_self hy, log_one, mul_zero]
    unfold binaryDivergence
    rw [hvanish x, hvanish (1 - x)]
    simp
  · have hbpos : 0 < b := by
      by_contra hnb
      have hb : b = 0 := le_antisymm (le_of_not_gt hnb) hb0
      have hx : x = 0 := le_antisymm (le_of_not_gt fun hx => (hac hx).ne' hb) hx0
      exact hxb (by simp [hx, hb])
    have hblt : b < 1 := by
      by_contra hnb
      have hb : b = 1 := le_antisymm hb1 (le_of_not_gt hnb)
      have hxlt : ¬ x < 1 := by
        intro hlt
        have : 0 < 1 - b := hac' (sub_pos.mpr hlt)
        simp [hb] at this
      exact hxb (by simp [le_antisymm hx1 (le_of_not_gt hxlt), hb])
    have hle := sqDistBinary_le_klBinary_Icc_left (y := x) (z := b) ⟨hx0, hx1⟩ ⟨hbpos, hblt⟩
    rw [sqDistBinary_eq_two_mul] at hle
    rw [binaryDivergence_eq_klBinary hbpos hblt]
    exact hle

/-! ## From Bernoulli to an arbitrary finite type -/

theorem sum_abs_eq_two_positivePart {S : Type*} [Fintype S] (p q : S → ℝ)
    (hsum : ∑ s, p s = ∑ s, q s) :
    ∑ s, |p s - q s| =
      2 * ∑ s ∈ univ.filter (fun s => q s ≤ p s), (p s - q s) := by
  classical
  set A := univ.filter (fun s => q s ≤ p s)
  set B := univ.filter (fun s => ¬ q s ≤ p s)
  have hsplit := sum_filter_add_sum_filter_not univ (fun s => q s ≤ p s)
    (fun s => |p s - q s|)
  have hsplitSub := sum_filter_add_sum_filter_not univ (fun s => q s ≤ p s)
    (fun s => p s - q s)
  have hsum0 : ∑ s, (p s - q s) = 0 := by
    rw [sum_sub_distrib, hsum, sub_self]
  rw [← hsplitSub] at hsum0
  have hA : ∑ s ∈ A, |p s - q s| = ∑ s ∈ A, (p s - q s) := by
    refine sum_congr rfl fun s hs => ?_
    exact abs_of_nonneg (sub_nonneg.mpr (mem_filter.mp hs).2)
  have hB : ∑ s ∈ B, |p s - q s| = ∑ s ∈ B, (q s - p s) := by
    refine sum_congr rfl fun s hs => ?_
    have hneg : p s - q s < 0 := sub_neg.mpr (lt_of_not_ge (mem_filter.mp hs).2)
    rw [abs_of_neg hneg]
    ring
  have hB' : ∑ s ∈ B, (q s - p s) = ∑ s ∈ A, (p s - q s) := by
    have hneg : ∑ s ∈ B, (p s - q s) = -∑ s ∈ A, (p s - q s) := by
      have : ∑ s ∈ A, (p s - q s) + ∑ s ∈ B, (p s - q s) = 0 := by
        simpa [A, B] using hsum0
      linarith
    have hflip : ∑ s ∈ B, (q s - p s) = -∑ s ∈ B, (p s - q s) := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun s _ => ?_
      ring
    rw [hflip, hneg, neg_neg]
  calc
    ∑ s, |p s - q s| = ∑ s ∈ A, |p s - q s| + ∑ s ∈ B, |p s - q s| := by
      simpa [A, B] using hsplit.symm
    _ = ∑ s ∈ A, (p s - q s) + ∑ s ∈ A, (p s - q s) := by rw [hA, hB, hB']
    _ = 2 * ∑ s ∈ A, (p s - q s) := by ring

theorem klSum_prob_nonneg {S : Type*} [Fintype S] (p q : Prob S)
    (hac : ∀ s, 0 < p.1 s → 0 < q.1 s) : 0 ≤ klSum p.1 q.1 := by
  simpa [klSum] using klSumOn_nonneg univ p.1 q.1 (fun s _ => p.2.1 s) (fun s _ => q.2.1 s)
    (fun s _ hs => hac s hs) (le_of_eq (by rw [p.2.2, q.2.2]))

/-- Finite Pinsker, natural log: the squared `L1` distance is at most twice the divergence. -/
theorem l1_sq_le_two_klSum {S : Type*} [Fintype S] (p q : Prob S)
    (hac : ∀ s, 0 < p.1 s → 0 < q.1 s) :
    (∑ s, |p.1 s - q.1 s|) ^ 2 ≤ 2 * klSum p.1 q.1 := by
  classical
  -- Push both laws onto `{q ≤ p}` versus its complement. The image is a pair of
  -- Bernoulli masses, and data processing does not increase divergence.
  let φ : S → Fin 2 := fun s => if q.1 s ≤ p.1 s then 0 else 1
  set α : ℝ := pushforward p.1 φ 0
  set β : ℝ := pushforward q.1 φ 0
  have hp_sum : ∑ s, p.1 s = 1 := p.2.2
  have hq_sum : ∑ s, q.1 s = 1 := q.2.2
  have hpush_p : ∑ i, pushforward p.1 φ i = 1 := by rw [sum_pushforward, hp_sum]
  have hpush_q : ∑ i, pushforward q.1 φ i = 1 := by rw [sum_pushforward, hq_sum]
  have hα1 : pushforward p.1 φ 1 = 1 - α := by
    have htwo : pushforward p.1 φ 0 + pushforward p.1 φ 1 = 1 := by
      rw [Fin.sum_univ_two] at hpush_p
      exact hpush_p
    have : pushforward p.1 φ 0 = α := rfl
    rw [this] at htwo
    linarith
  have hβ1 : pushforward q.1 φ 1 = 1 - β := by
    have htwo : pushforward q.1 φ 0 + pushforward q.1 φ 1 = 1 := by
      rw [Fin.sum_univ_two] at hpush_q
      exact hpush_q
    have : pushforward q.1 φ 0 = β := rfl
    rw [this] at htwo
    linarith
  have hα0 : 0 ≤ α := pushforward_nonneg p.1 (fun s => p.2.1 s) φ 0
  have hβ0 : 0 ≤ β := pushforward_nonneg q.1 (fun s => q.2.1 s) φ 0
  have hα1le : α ≤ 1 := by
    have : 0 ≤ pushforward p.1 φ 1 := pushforward_nonneg p.1 (fun s => p.2.1 s) φ 1
    linarith [hα1]
  have hβ1le : β ≤ 1 := by
    have : 0 ≤ pushforward q.1 φ 1 := pushforward_nonneg q.1 (fun s => q.2.1 s) φ 1
    linarith [hβ1]
  have hfilter : ∀ s, φ s = 0 ↔ q.1 s ≤ p.1 s := by
    intro s
    by_cases hs : q.1 s ≤ p.1 s
    · simp [φ, if_pos hs, hs]
    · simp [φ, if_neg hs, hs]
  have hset : univ.filter (fun s => φ s = 0) = univ.filter (fun s => q.1 s ≤ p.1 s) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hfilter s
  have hgap : α - β = ∑ s ∈ univ.filter (fun s => q.1 s ≤ p.1 s), (p.1 s - q.1 s) := by
    unfold α β pushforward
    rw [← sum_sub_distrib, hset]
  have hl1 : ∑ s, |p.1 s - q.1 s| = 2 * (α - β) := by
    rw [sum_abs_eq_two_positivePart p.1 q.1 (by rw [hp_sum, hq_sum]), ← hgap]
  have hacβ : 0 < α → 0 < β := by
    intro hα
    have hpos : ∃ s ∈ univ.filter (fun s => φ s = 0), 0 < p.1 s := by
      by_contra hnone
      push Not at hnone
      have hall : ∀ s ∈ univ.filter (fun s => φ s = 0), p.1 s = 0 := by
        intro s hs
        exact le_antisymm (hnone s hs) (p.2.1 s)
      have : α = 0 := by
        unfold α pushforward
        exact sum_eq_zero hall
      exact hα.ne' this
    obtain ⟨s, hs, hps⟩ := hpos
    have hqs : 0 < q.1 s := hac s hps
    have hqle : q.1 s ≤ β := by
      unfold β pushforward
      exact single_le_sum (fun t _ => q.2.1 t) hs
    exact lt_of_lt_of_le hqs hqle
  have hacβ' : 0 < 1 - α → 0 < 1 - β := by
    intro hα
    have hpos : ∃ s ∈ univ.filter (fun s => φ s = 1), 0 < p.1 s := by
      by_contra hnone
      push Not at hnone
      have hall : ∀ s ∈ univ.filter (fun s => φ s = 1), p.1 s = 0 := by
        intro s hs
        exact le_antisymm (hnone s hs) (p.2.1 s)
      have : pushforward p.1 φ 1 = 0 := by
        unfold pushforward
        exact sum_eq_zero hall
      rw [hα1] at this
      linarith
    obtain ⟨s, hs, hps⟩ := hpos
    have hqs : 0 < q.1 s := hac s hps
    have hqle : q.1 s ≤ pushforward q.1 φ 1 := by
      unfold pushforward
      exact single_le_sum (fun t _ => q.2.1 t) hs
    rw [hβ1] at hqle
    exact lt_of_lt_of_le hqs hqle
  have hbin : 2 * (α - β) ^ 2 ≤ binaryDivergence β α :=
    two_sq_le_binaryDivergence hβ0 hβ1le hα0 hα1le hacβ hacβ'
  have hklbin : klSum (pushforward p.1 φ) (pushforward q.1 φ) = binaryDivergence β α := by
    rw [klSum_eq_sum, Fin.sum_univ_two, hα1, hβ1]
    rfl
  have hdp : klSum (pushforward p.1 φ) (pushforward q.1 φ) ≤ klSum p.1 q.1 :=
    klSum_pushforward_le p.1 q.1 φ (fun s => p.2.1 s) (fun s => q.2.1 s) hac
  have hsq : (∑ s, |p.1 s - q.1 s|) ^ 2 = 4 * (α - β) ^ 2 := by
    rw [hl1]
    ring
  have hfour : 4 * (α - β) ^ 2 = 2 * (2 * (α - β) ^ 2) := by ring
  rw [hsq, hfour]
  calc
    2 * (2 * (α - β) ^ 2) ≤ 2 * binaryDivergence β α :=
      mul_le_mul_of_nonneg_left hbin (by norm_num)
    _ = 2 * klSum (pushforward p.1 φ) (pushforward q.1 φ) := by rw [hklbin]
    _ ≤ 2 * klSum p.1 q.1 := mul_le_mul_of_nonneg_left hdp (by norm_num)

/-- A score in `[A, B]` changes its expectation by at most half its range times the `L1` distance. -/
theorem abs_expectation_sub_le_of_bounds {S : Type*} [Fintype S] (p q : Prob S)
    (score : S → ℝ) {A B : ℝ} (hA : ∀ s, A ≤ score s) (hB : ∀ s, score s ≤ B) :
    |∑ s, p.1 s * score s - ∑ s, q.1 s * score s| ≤
      ((B - A) / 2) * ∑ s, |p.1 s - q.1 s| := by
  let c := (A + B) / 2
  let centered : S → ℝ := fun s => score s - c
  have hbound : ∀ s, |centered s| ≤ (B - A) / 2 := by
    intro s
    have hlo : -((B - A) / 2) ≤ centered s := by
      unfold centered c
      linarith [hA s, hB s]
    have hhi : centered s ≤ (B - A) / 2 := by
      unfold centered c
      linarith [hA s, hB s]
    exact abs_le.mpr ⟨hlo, hhi⟩
  have hcenter : ∑ s, (p.1 s - q.1 s) * score s = ∑ s, (p.1 s - q.1 s) * centered s := by
    have hconst : ∑ s, (p.1 s - q.1 s) * c = 0 := by
      rw [← sum_mul]
      have : ∑ s, (p.1 s - q.1 s) = 0 := by
        rw [sum_sub_distrib, p.2.2, q.2.2, sub_self]
      rw [this, zero_mul]
    calc
      ∑ s, (p.1 s - q.1 s) * score s
          = ∑ s, (p.1 s - q.1 s) * (centered s + c) := by
            refine sum_congr rfl fun s _ => ?_
            unfold centered
            ring
      _ = ∑ s, (p.1 s - q.1 s) * centered s + ∑ s, (p.1 s - q.1 s) * c := by
            simp_rw [mul_add, sum_add_distrib]
      _ = ∑ s, (p.1 s - q.1 s) * centered s := by rw [hconst, add_zero]
  have habs : |∑ s, (p.1 s - q.1 s) * centered s| ≤
      ∑ s, |p.1 s - q.1 s| * |centered s| := by
    calc
      |∑ s, (p.1 s - q.1 s) * centered s| ≤ ∑ s, |(p.1 s - q.1 s) * centered s| :=
        abs_sum_le_sum_abs _ _
      _ = ∑ s, |p.1 s - q.1 s| * |centered s| := by
        refine sum_congr rfl fun s _ => ?_
        rw [abs_mul]
  have hscale : ∑ s, |p.1 s - q.1 s| * |centered s| ≤
      ((B - A) / 2) * ∑ s, |p.1 s - q.1 s| := by
    calc
      ∑ s, |p.1 s - q.1 s| * |centered s| ≤ ∑ s, |p.1 s - q.1 s| * ((B - A) / 2) := by
        refine sum_le_sum fun s _ => ?_
        exact mul_le_mul_of_nonneg_left (hbound s) (abs_nonneg _)
      _ = ((B - A) / 2) * ∑ s, |p.1 s - q.1 s| := by
        rw [← sum_mul]
        ring
  have hdiff : ∑ s, p.1 s * score s - ∑ s, q.1 s * score s =
      ∑ s, (p.1 s - q.1 s) * score s := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun s _ => ?_
    ring
  rw [hdiff, hcenter]
  exact habs.trans hscale

/-- `|E_p[f] - E_q[f]| ≤ M √(2 KL(p‖q))` when `|f| ≤ M`. -/
theorem abs_expectation_sub_le {S : Type*} [Fintype S] (p q : Prob S) (score : S → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ s, |score s| ≤ M)
    (hac : ∀ s, 0 < p.1 s → 0 < q.1 s) :
    |∑ s, p.1 s * score s - ∑ s, q.1 s * score s| ≤
      M * sqrt (2 * klSum p.1 q.1) := by
  have hrange := abs_expectation_sub_le_of_bounds p q score (A := -M) (B := M)
    (fun s => neg_le_of_abs_le (hf s)) (fun s => le_of_abs_le (hf s))
  have hspan : ((M - -M) / 2) = M := by ring
  rw [hspan] at hrange
  have hl1 : ∑ s, |p.1 s - q.1 s| ≤ sqrt (2 * klSum p.1 q.1) := by
    have hsq := l1_sq_le_two_klSum p q hac
    have hnn : 0 ≤ ∑ s, |p.1 s - q.1 s| := sum_nonneg fun s _ => abs_nonneg _
    have hkl : 0 ≤ 2 * klSum p.1 q.1 := by
      have := klSum_prob_nonneg p q hac
      positivity
    rw [← sqrt_sq hnn]
    exact sqrt_le_sqrt hsq
  exact hrange.trans (mul_le_mul_of_nonneg_left hl1 hM)

/-! ## Controls -/

theorem pinsker_self {S : Type*} [Fintype S] (p : Prob S) :
    (∑ s, |p.1 s - p.1 s|) ^ 2 ≤ 2 * klSum p.1 p.1 := by
  simpa using l1_sq_le_two_klSum p p fun _ h => h

theorem twoState_reference_pos (i : Fin 2) :
    0 < (binaryDist (1 / 4) (by norm_num) (by norm_num)).1 i := by
  fin_cases i <;> simp [binaryDist, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num

theorem twoState_consumer_pos :
    0 < |∑ i, (binaryDist (3 / 4) (by norm_num) (by norm_num)).1 i *
            (if i = (0 : Fin 2) then (1 : ℝ) else 0) -
          ∑ i, (binaryDist (1 / 4) (by norm_num) (by norm_num)).1 i *
            (if i = (0 : Fin 2) then (1 : ℝ) else 0)| := by
  simp [binaryDist, Matrix.cons_val_zero]
  norm_num

theorem twoState_pinsker :
    (∑ i, |(binaryDist (3 / 4) (by norm_num) (by norm_num)).1 i -
        (binaryDist (1 / 4) (by norm_num) (by norm_num)).1 i|) ^ 2 ≤
      2 * klSum (binaryDist (3 / 4) (by norm_num) (by norm_num)).1
        (binaryDist (1 / 4) (by norm_num) (by norm_num)).1 := by
  exact l1_sq_le_two_klSum _ _ fun _ _ => twoState_reference_pos _

/-- Dropping absolute continuity: `Real.log 0 = 0` makes this unsupported pair
look divergence-free, while the `L1` distance is `2`. The extended divergence is infinite. -/
theorem unsupported_real_divergence_fails_pinsker :
    ¬ (∑ i, |(binaryDist 1 (by norm_num) (by norm_num)).1 i -
          (binaryDist 0 (by norm_num) (by norm_num)).1 i|) ^ 2 ≤
        2 * klSum (binaryDist 1 (by norm_num) (by norm_num)).1
          (binaryDist 0 (by norm_num) (by norm_num)).1 := by
  simp [binaryDist, klSum_eq_sum, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.log_zero]

end Mettapedia.InformationTheory
