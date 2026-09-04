import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mettapedia.InformationTheory.Basic

/-!
# Conditional mutual information and the Markov coarsening identity (finite case)

Random variables are maps `f : Ω → α` out of a finite outcome type `Ω` that carries a weight
function `p : Ω → ℝ` (a probability distribution once `0 ≤ p` and `∑ p = 1`).  The law of a
random variable is the pushforward `pushforward p f`.

This file proves, for finite distributions:

* Gibbs' inequality for divergence sums (`klSumOn_nonneg`) and its equality case
  (`klSumOn_eq_zero_imp`), the log-sum inequality (`sum_mul_log_le_klSumOn`), and finite
  data processing: pushing two distributions forward through the same map cannot increase
  divergence (`klSum_pushforward_le`).
* The Markov coarsening identity.  Given three random variables `A = f`, `B = g`, `C = h`,
  the distribution `markovProjection p f g h` keeps the `(A,B)` and `(B,C)` laws of `p` and
  imposes `A ⊥ C | B`.  Its divergence from the true joint law is exactly the conditional
  mutual information `I(A;C|B)` (`klSum_law3_markovProjection_eq_condMutualInfo`), which is
  nonnegative (`condMutualInfo_nonneg`) and vanishes iff `A ⊥ C | B` holds in `p`
  (`condMutualInfo_eq_zero_iff`).  The end-to-end loss on the `(A,C)` law is bounded by the
  same quantity (`klSum_law2_markovProjectionAC_le_condMutualInfo`).

Positive canary: a joint law that is already Markov has zero conditional mutual information.
Negative canary (in `Mettapedia.PLN.Comparisons.ChainLoss`): two independent fair coins and
their disjunction, for which chaining through the disjunction is strictly worse than using the
prior.
-/

namespace Mettapedia.InformationTheory.FiniteRV

open Real Finset BigOperators

/-! ## Divergence sums -/

section DivergenceSums

variable {Ω : Type*}

/-- Divergence sum of `p` against `q` over the finset `s`.  Terms with `p ω = 0` vanish. -/
noncomputable def klSumOn (s : Finset Ω) (p q : Ω → ℝ) : ℝ :=
  ∑ ω ∈ s, p ω * Real.log (p ω / q ω)

/-- Pointwise Gibbs inequality: `a - b ≤ a * log (a / b)` for nonnegative `a, b` with
`b > 0` whenever `a > 0`. -/
theorem sub_le_mul_log_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a → 0 < b) :
    a - b ≤ a * Real.log (a / b) := by
  rcases ha.lt_or_eq with ha' | ha'
  · have hb' := hab ha'
    have hlog : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb' ha')
    have hneg : Real.log (a / b) = -Real.log (b / a) := by
      rw [← Real.log_inv, inv_div]
    have h2 : a * Real.log (b / a) ≤ b - a := by
      calc a * Real.log (b / a) ≤ a * (b / a - 1) := by
            exact mul_le_mul_of_nonneg_left hlog ha
        _ = b - a := by field_simp
    rw [hneg]
    linarith
  · subst ha'
    simp
    linarith

/-- Strict pointwise Gibbs inequality away from `a = b`. -/
theorem sub_lt_mul_log_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b) :
    a - b < a * Real.log (a / b) := by
  have hratio : b / a ≠ 1 := by
    intro h
    apply hne
    field_simp at h
    linarith
  have hlog : Real.log (b / a) < b / a - 1 := Real.log_lt_sub_one_of_pos (div_pos hb ha) hratio
  have hneg : Real.log (a / b) = -Real.log (b / a) := by
    rw [← Real.log_inv, inv_div]
  have h2 : a * Real.log (b / a) < b - a := by
    calc a * Real.log (b / a) < a * (b / a - 1) := by
          exact mul_lt_mul_of_pos_left hlog ha
      _ = b - a := by field_simp
  rw [hneg]
  linarith

theorem sum_sub_le_klSumOn (s : Finset Ω) (p q : Ω → ℝ)
    (hp : ∀ ω ∈ s, 0 ≤ p ω) (hq : ∀ ω ∈ s, 0 ≤ q ω)
    (hac : ∀ ω ∈ s, 0 < p ω → 0 < q ω) :
    ∑ ω ∈ s, (p ω - q ω) ≤ klSumOn s p q := by
  unfold klSumOn
  exact Finset.sum_le_sum fun ω hω => sub_le_mul_log_div (hp ω hω) (hq ω hω) (hac ω hω)

/-- Gibbs' inequality: if `q` has no more total mass than `p` on `s`, the divergence sum is
nonnegative. -/
theorem klSumOn_nonneg (s : Finset Ω) (p q : Ω → ℝ)
    (hp : ∀ ω ∈ s, 0 ≤ p ω) (hq : ∀ ω ∈ s, 0 ≤ q ω)
    (hac : ∀ ω ∈ s, 0 < p ω → 0 < q ω)
    (hsum : ∑ ω ∈ s, q ω ≤ ∑ ω ∈ s, p ω) :
    0 ≤ klSumOn s p q := by
  have h := sum_sub_le_klSumOn s p q hp hq hac
  rw [Finset.sum_sub_distrib] at h
  linarith

/-- Equality case of Gibbs' inequality: with equal total masses, a vanishing divergence sum
forces `p = q` on `s`. -/
theorem klSumOn_eq_zero_imp (s : Finset Ω) (p q : Ω → ℝ)
    (hp : ∀ ω ∈ s, 0 ≤ p ω) (hq : ∀ ω ∈ s, 0 ≤ q ω)
    (hac : ∀ ω ∈ s, 0 < p ω → 0 < q ω)
    (hsum : ∑ ω ∈ s, q ω = ∑ ω ∈ s, p ω)
    (hzero : klSumOn s p q = 0) :
    ∀ ω ∈ s, p ω = q ω := by
  -- each defect `p log(p/q) - (p - q)` is nonnegative and they sum to zero
  have hdef : ∑ ω ∈ s, (p ω * Real.log (p ω / q ω) - (p ω - q ω)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum]
    have : ∑ ω ∈ s, p ω * Real.log (p ω / q ω) = 0 := hzero
    rw [this]
    ring
  have hnn : ∀ ω ∈ s, 0 ≤ p ω * Real.log (p ω / q ω) - (p ω - q ω) := fun ω hω => by
    have := sub_le_mul_log_div (hp ω hω) (hq ω hω) (hac ω hω)
    linarith
  have heach := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hdef
  intro ω hω
  have h := heach ω hω
  rcases (hp ω hω).lt_or_eq with hpos | hzero'
  · have hqpos := hac ω hω hpos
    by_contra hne
    have := sub_lt_mul_log_div hpos hqpos hne
    linarith
  · rw [← hzero'] at h ⊢
    simp at h
    linarith

/-- Log-sum inequality: the divergence of the aggregated masses is at most the summed
divergence. -/
theorem sum_mul_log_le_klSumOn (s : Finset Ω) (p q : Ω → ℝ)
    (hp : ∀ ω ∈ s, 0 ≤ p ω) (hq : ∀ ω ∈ s, 0 ≤ q ω)
    (hac : ∀ ω ∈ s, 0 < p ω → 0 < q ω) :
    (∑ ω ∈ s, p ω) * Real.log ((∑ ω ∈ s, p ω) / (∑ ω ∈ s, q ω)) ≤ klSumOn s p q := by
  set P := ∑ ω ∈ s, p ω with hP
  set Q := ∑ ω ∈ s, q ω with hQ
  have hP0 : 0 ≤ P := Finset.sum_nonneg hp
  rcases hP0.lt_or_eq with hPpos | hPzero
  · -- some `p ω > 0`, hence `Q > 0`
    have hQpos : 0 < Q := by
      obtain ⟨ω, hω, hpω⟩ : ∃ ω ∈ s, 0 < p ω := by
        by_contra hcon
        have hall : ∀ ω ∈ s, p ω = 0 := fun ω hω =>
          le_antisymm (not_lt.1 fun h => hcon ⟨ω, hω, h⟩) (hp ω hω)
        have : P = 0 := Finset.sum_eq_zero hall
        linarith
      exact lt_of_lt_of_le (hac ω hω hpω)
        (Finset.single_le_sum (f := q) hq hω)
    -- rescale `q` so that it has total mass `P`
    set q' : Ω → ℝ := fun ω => q ω * (P / Q) with hq'
    have hq'nn : ∀ ω ∈ s, 0 ≤ q' ω := fun ω hω =>
      mul_nonneg (hq ω hω) (div_nonneg hP0 hQpos.le)
    have hac' : ∀ ω ∈ s, 0 < p ω → 0 < q' ω := fun ω hω h =>
      mul_pos (hac ω hω h) (div_pos hPpos hQpos)
    have hsum' : ∑ ω ∈ s, q' ω ≤ ∑ ω ∈ s, p ω := by
      simp only [hq']
      rw [← Finset.sum_mul, ← hQ, ← hP]
      rw [mul_div_assoc']
      rw [mul_comm, mul_div_assoc, div_self hQpos.ne', mul_one]
    have hnn := klSumOn_nonneg s p q' hp hq'nn hac' hsum'
    -- rewrite the rescaled divergence termwise
    have hterm : ∀ ω ∈ s, p ω * Real.log (p ω / q' ω) =
        p ω * Real.log (p ω / q ω) - p ω * Real.log (P / Q) := by
      intro ω hω
      rcases (hp ω hω).lt_or_eq with hpos | hzero
      · have hqpos := hac ω hω hpos
        simp only [hq']
        rw [← mul_sub, div_mul_eq_div_div, Real.log_div (div_pos hpos hqpos).ne'
          (div_pos hPpos hQpos).ne']
      · rw [← hzero]; simp
    unfold klSumOn at hnn ⊢
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_mul] at hnn
    linarith
  · -- `P = 0`: every `p ω = 0`
    have hall : ∀ ω ∈ s, p ω = 0 := fun ω hω =>
      le_antisymm (by
        have := Finset.single_le_sum (f := p) hp hω
        linarith) (hp ω hω)
    have : klSumOn s p q = 0 := by
      unfold klSumOn
      exact Finset.sum_eq_zero fun ω hω => by rw [hall ω hω]; simp
    rw [this, ← hPzero]
    simp

end DivergenceSums

section Pushforward

variable {Ω : Type*} [Fintype Ω]

/-- Divergence sum of `p` against `q` over the whole finite type. -/
noncomputable def klSum (p q : Ω → ℝ) : ℝ := klSumOn Finset.univ p q

theorem klSum_eq_klSumOn_univ (p q : Ω → ℝ) : klSum p q = klSumOn Finset.univ p q := rfl

theorem klSum_eq_sum (p q : Ω → ℝ) : klSum p q = ∑ ω, p ω * Real.log (p ω / q ω) := rfl

theorem klSum_self_eq_zero (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) : klSum p p = 0 := by
  unfold klSum klSumOn
  refine Finset.sum_eq_zero fun ω _ => ?_
  rcases (hp ω).lt_or_eq with hpos | hzero
  · rw [div_self hpos.ne', Real.log_one, mul_zero]
  · rw [← hzero]; simp

/-! ## Pushforward (law of a random variable) -/

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- The law of the random variable `φ` under the weights `p`. -/
noncomputable def pushforward (p : Ω → ℝ) (φ : Ω → α) (a : α) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω => φ ω = a), p ω

theorem pushforward_eq_sum_ite (p : Ω → ℝ) (φ : Ω → α) (a : α) :
    pushforward p φ a = ∑ ω, if φ ω = a then p ω else 0 := by
  unfold pushforward
  rw [Finset.sum_filter]

theorem pushforward_nonneg (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (φ : Ω → α) (a : α) :
    0 ≤ pushforward p φ a :=
  Finset.sum_nonneg fun ω _ => hp ω

theorem sum_pushforward [Fintype α] (p : Ω → ℝ) (φ : Ω → α) :
    ∑ a, pushforward p φ a = ∑ ω, p ω := by
  unfold pushforward
  exact Finset.sum_fiberwise Finset.univ φ p

/-- Expectation of a function of `φ` may be computed on `Ω` or on the law of `φ`. -/
theorem sum_pushforward_mul [Fintype α] (p : Ω → ℝ) (φ : Ω → α) (L : α → ℝ) :
    ∑ a, pushforward p φ a * L a = ∑ ω, p ω * L (φ ω) := by
  unfold pushforward
  simp only [Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ φ (fun ω => p ω * L (φ ω))]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun ω hω => ?_
  rw [Finset.mem_filter] at hω
  rw [hω.2]

theorem le_pushforward (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (φ : Ω → α) (ω : Ω) :
    p ω ≤ pushforward p φ (φ ω) := by
  unfold pushforward
  exact Finset.single_le_sum (f := p) (fun ω' _ => hp ω') (by simp)

theorem pushforward_pos_of_pos (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (φ : Ω → α) {ω : Ω}
    (h : 0 < p ω) : 0 < pushforward p φ (φ ω) :=
  lt_of_lt_of_le h (le_pushforward p hp φ ω)

/-- Two maps with the same fibre at `ω` give the same law value there. -/
theorem pushforward_congr_fiber (p : Ω → ℝ) (φ : Ω → α) (ψ : Ω → β) (ω : Ω)
    (h : ∀ ω', φ ω' = φ ω ↔ ψ ω' = ψ ω) :
    pushforward p φ (φ ω) = pushforward p ψ (ψ ω) := by
  unfold pushforward
  congr 1
  ext ω'
  simp [h ω']

theorem pushforward_of_injective (p : Ω → ℝ) (φ : Ω → α) (hφ : Function.Injective φ) (ω : Ω) :
    pushforward p φ (φ ω) = p ω := by
  unfold pushforward
  rw [Finset.sum_eq_single ω]
  · intro ω' hω' hne
    exact (hne (hφ (Finset.mem_filter.1 hω').2)).elim
  · intro h
    exact (h (by simp)).elim

theorem pushforward_pushforward [Fintype α] (p : Ω → ℝ) (φ : Ω → α) (ψ : α → β) (b : β) :
    pushforward (pushforward p φ) ψ b = pushforward p (ψ ∘ φ) b := by
  rw [pushforward_eq_sum_ite (pushforward p φ) ψ b]
  have : ∀ a, (if ψ a = b then pushforward p φ a else 0) =
      pushforward p φ a * (if ψ a = b then 1 else 0) := by
    intro a; split_ifs <;> simp
  rw [Finset.sum_congr rfl fun a _ => this a,
    sum_pushforward_mul p φ (fun a => if ψ a = b then 1 else 0)]
  rw [pushforward_eq_sum_ite]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [Function.comp]
  split_ifs <;> simp

/-- Finite data processing: divergence does not increase under a common pushforward. -/
theorem klSum_pushforward_le [Fintype α] (p q : Ω → ℝ) (φ : Ω → α)
    (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω) (hac : ∀ ω, 0 < p ω → 0 < q ω) :
    klSum (pushforward p φ) (pushforward q φ) ≤ klSum p q := by
  unfold klSum klSumOn
  rw [← Finset.sum_fiberwise Finset.univ φ (fun ω => p ω * Real.log (p ω / q ω))]
  refine Finset.sum_le_sum fun a _ => ?_
  have := sum_mul_log_le_klSumOn (Finset.univ.filter (fun ω => φ ω = a)) p q
    (fun ω _ => hp ω) (fun ω _ => hq ω) (fun ω _ => hac ω)
  unfold klSumOn at this
  exact this

/-! ## Laws of pairs and triples -/

/-- Joint law of `(f, g)`. -/
noncomputable def law2 (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) : α × β → ℝ :=
  pushforward p (fun ω => (f ω, g ω))

/-- Joint law of `(f, g, h)`. -/
noncomputable def law3 (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) : α × β × γ → ℝ :=
  pushforward p (fun ω => (f ω, g ω, h ω))

theorem sum_law2_right [Fintype β] (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (a : α) :
    ∑ b, law2 p f g (a, b) = pushforward p f a := by
  unfold law2 pushforward
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hf : f ω = a
  · subst hf; simp
  · simp [hf]

theorem sum_law2_left [Fintype α] (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (b : β) :
    ∑ a, law2 p f g (a, b) = pushforward p g b := by
  unfold law2 pushforward
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hg : g ω = b
  · subst hg; simp
  · simp [hg]

theorem sum_law3_right [Fintype γ] (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ)
    (a : α) (b : β) :
    ∑ c, law3 p f g h (a, b, c) = law2 p f g (a, b) := by
  unfold law3 law2 pushforward
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hf : f ω = a
  · by_cases hg : g ω = b
    · subst hf hg; simp
    · simp [hg]
  · simp [hf]

theorem sum_law3_left [Fintype α] (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ)
    (b : β) (c : γ) :
    ∑ a, law3 p f g h (a, b, c) = law2 p g h (b, c) := by
  unfold law3 law2 pushforward
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hg : g ω = b
  · by_cases hh : h ω = c
    · subst hg hh; simp
    · simp [hh]
  · simp [hg]

theorem law3_le_law2_fg [Fintype γ] (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) (x : α × β × γ) : law3 p f g h x ≤ law2 p f g (x.1, x.2.1) := by
  rw [← sum_law3_right p f g h x.1 x.2.1]
  exact Finset.single_le_sum (f := fun c => law3 p f g h (x.1, x.2.1, c))
    (fun c _ => pushforward_nonneg p hp _ _) (Finset.mem_univ x.2.2)

theorem law3_le_law2_gh [Fintype α] (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) (x : α × β × γ) : law3 p f g h x ≤ law2 p g h (x.2.1, x.2.2) := by
  rw [← sum_law3_left p f g h x.2.1 x.2.2]
  exact Finset.single_le_sum (f := fun a => law3 p f g h (a, x.2.1, x.2.2))
    (fun a _ => pushforward_nonneg p hp _ _) (Finset.mem_univ x.1)

theorem law2_le_pushforward_snd [Fintype α] (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α)
    (g : Ω → β) (x : α × β) : law2 p f g x ≤ pushforward p g x.2 := by
  rw [← sum_law2_left p f g x.2]
  exact Finset.single_le_sum (f := fun a => law2 p f g (a, x.2))
    (fun a _ => pushforward_nonneg p hp _ _) (Finset.mem_univ x.1)

theorem law2_le_pushforward_fst [Fintype β] (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α)
    (g : Ω → β) (x : α × β) : law2 p f g x ≤ pushforward p f x.1 := by
  rw [← sum_law2_right p f g x.1]
  exact Finset.single_le_sum (f := fun b => law2 p f g (x.1, b))
    (fun b _ => pushforward_nonneg p hp _ _) (Finset.mem_univ x.2)

/-! ## The Markov projection and conditional mutual information -/

/-- The distribution on `(A, B, C)` that keeps the `(A,B)` and `(B,C)` laws of `p` and imposes
`A ⊥ C | B`: `P_R(a,b,c) = P(a,b) · P(b,c) / P(b)`. -/
noncomputable def markovProjection (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    α × β × γ → ℝ := fun x =>
  if pushforward p g x.2.1 = 0 then 0
  else law2 p f g (x.1, x.2.1) * law2 p g h (x.2.1, x.2.2) / pushforward p g x.2.1

/-- `A ⊥ C | B` under `p`, stated multiplicatively so that it needs no division. -/
def CondIndep (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) : Prop :=
  ∀ x : α × β × γ, law3 p f g h x * pushforward p g x.2.1 =
    law2 p f g (x.1, x.2.1) * law2 p g h (x.2.1, x.2.2)

theorem markovProjection_nonneg (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) (x : α × β × γ) : 0 ≤ markovProjection p f g h x := by
  unfold markovProjection
  split_ifs with hz
  · exact le_rfl
  · have hpos : 0 < pushforward p g x.2.1 :=
      lt_of_le_of_ne (pushforward_nonneg p hp g _) (Ne.symm hz)
    exact div_nonneg (mul_nonneg (pushforward_nonneg p hp _ _) (pushforward_nonneg p hp _ _))
      hpos.le

variable [Fintype α] [Fintype β] [Fintype γ]

/-- Conditional mutual information `I(f ; h | g)` under the weights `p`, as a sum over the
joint law of the triple. -/
noncomputable def condMutualInfo (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) : ℝ :=
  ∑ x : α × β × γ, law3 p f g h x *
    Real.log (law3 p f g h x * pushforward p g x.2.1 /
      (law2 p f g (x.1, x.2.1) * law2 p g h (x.2.1, x.2.2)))

omit [Fintype β] in
theorem markovProjection_pos_of_law3_pos (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α)
    (g : Ω → β) (h : Ω → γ) {x : α × β × γ} (hx : 0 < law3 p f g h x) :
    0 < markovProjection p f g h x := by
  have h1 : 0 < law2 p f g (x.1, x.2.1) := lt_of_lt_of_le hx (law3_le_law2_fg p hp f g h x)
  have h2 : 0 < law2 p g h (x.2.1, x.2.2) := lt_of_lt_of_le hx (law3_le_law2_gh p hp f g h x)
  have h3 : 0 < pushforward p g x.2.1 :=
    lt_of_lt_of_le h1 (law2_le_pushforward_snd p hp f g (x.1, x.2.1))
  unfold markovProjection
  rw [if_neg h3.ne']
  exact div_pos (mul_pos h1 h2) h3

omit [Fintype β] in
/-- The Markov projection keeps the `(A,B)` law. -/
theorem sum_markovProjection_right (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) (a : α) (b : β) :
    ∑ c, markovProjection p f g h (a, b, c) = law2 p f g (a, b) := by
  unfold markovProjection
  by_cases hz : pushforward p g b = 0
  · simp only [hz, if_true, Finset.sum_const_zero]
    have h1 : law2 p f g (a, b) ≤ pushforward p g b := law2_le_pushforward_snd p hp f g (a, b)
    have h2 : 0 ≤ law2 p f g (a, b) := pushforward_nonneg p hp _ _
    rw [hz] at h1
    linarith
  · simp only [hz, if_false, div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_law2_right p g h b]
    field_simp

omit [Fintype β] in
/-- The Markov projection keeps the `(B,C)` law. -/
theorem sum_markovProjection_left (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) (b : β) (c : γ) :
    ∑ a, markovProjection p f g h (a, b, c) = law2 p g h (b, c) := by
  unfold markovProjection
  by_cases hz : pushforward p g b = 0
  · simp only [hz, if_true, Finset.sum_const_zero]
    have h1 : law2 p g h (b, c) ≤ pushforward p g b := law2_le_pushforward_fst p hp g h (b, c)
    have h2 : 0 ≤ law2 p g h (b, c) := pushforward_nonneg p hp _ _
    rw [hz] at h1
    linarith
  · simp only [hz, if_false, div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.sum_mul, sum_law2_left p f g b]
    field_simp

/-- The Markov projection is a probability distribution whenever `p` is. -/
theorem sum_markovProjection (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) : ∑ x, markovProjection p f g h x = ∑ ω, p ω := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  calc ∑ a, ∑ b, ∑ c, markovProjection p f g h (a, b, c)
      = ∑ a, ∑ b, law2 p f g (a, b) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        exact sum_markovProjection_right p hp f g h a b
    _ = ∑ a, pushforward p f a := by
        refine Finset.sum_congr rfl fun a _ => sum_law2_right p f g a
    _ = ∑ ω, p ω := sum_pushforward p f

theorem sum_law3 (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    ∑ x, law3 p f g h x = ∑ ω, p ω := by
  unfold law3
  exact sum_pushforward p _

/-- The Markov coarsening identity: `KL(P ∥ P_R) = I(A ; C | B)`. -/
theorem klSum_law3_markovProjection_eq_condMutualInfo (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    klSum (law3 p f g h) (markovProjection p f g h) = condMutualInfo p f g h := by
  unfold klSum klSumOn condMutualInfo
  refine Finset.sum_congr rfl fun x _ => ?_
  rcases (pushforward_nonneg p hp _ x : 0 ≤ law3 p f g h x).lt_or_eq with hpos | hzero
  · have h1 : 0 < law2 p f g (x.1, x.2.1) := lt_of_lt_of_le hpos (law3_le_law2_fg p hp f g h x)
    have h2 : 0 < law2 p g h (x.2.1, x.2.2) := lt_of_lt_of_le hpos (law3_le_law2_gh p hp f g h x)
    have h3 : 0 < pushforward p g x.2.1 :=
      lt_of_lt_of_le h1 (law2_le_pushforward_snd p hp f g (x.1, x.2.1))
    unfold markovProjection
    rw [if_neg h3.ne']
    congr 2
    field_simp
  · have hz : law3 p f g h x = 0 := hzero.symm
    rw [hz]
    simp

theorem condMutualInfo_nonneg (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) : 0 ≤ condMutualInfo p f g h := by
  rw [← klSum_law3_markovProjection_eq_condMutualInfo p hp f g h]
  unfold klSum
  refine klSumOn_nonneg _ _ _ (fun x _ => pushforward_nonneg p hp _ x)
    (fun x _ => markovProjection_nonneg p hp f g h x)
    (fun x _ hx => markovProjection_pos_of_law3_pos p hp f g h hx) ?_
  rw [sum_markovProjection p hp f g h, sum_law3]

omit [Fintype β] in
theorem condIndep_iff_law3_eq_markovProjection (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α)
    (g : Ω → β) (h : Ω → γ) :
    CondIndep p f g h ↔ ∀ x, law3 p f g h x = markovProjection p f g h x := by
  constructor
  · intro hci x
    have hx := hci x
    unfold markovProjection
    by_cases hz : pushforward p g x.2.1 = 0
    · rw [if_pos hz]
      have h1 : law3 p f g h x ≤ law2 p f g (x.1, x.2.1) := law3_le_law2_fg p hp f g h x
      have h2 : law2 p f g (x.1, x.2.1) ≤ pushforward p g x.2.1 :=
        law2_le_pushforward_snd p hp f g (x.1, x.2.1)
      have h3 : 0 ≤ law3 p f g h x := pushforward_nonneg p hp _ x
      rw [hz] at h2
      linarith
    · rw [if_neg hz]
      rw [eq_div_iff hz]
      exact hx
  · intro heq x
    have hx := heq x
    unfold markovProjection at hx
    by_cases hz : pushforward p g x.2.1 = 0
    · rw [if_pos hz] at hx
      show law3 p f g h x * pushforward p g x.2.1 = _
      rw [hx, hz]
      have h1 : law2 p f g (x.1, x.2.1) ≤ pushforward p g x.2.1 :=
        law2_le_pushforward_snd p hp f g (x.1, x.2.1)
      have h2 : 0 ≤ law2 p f g (x.1, x.2.1) := pushforward_nonneg p hp _ _
      rw [hz] at h1
      have : law2 p f g (x.1, x.2.1) = 0 := le_antisymm h1 h2
      rw [this]
      ring
    · rw [if_neg hz] at hx
      show law3 p f g h x * pushforward p g x.2.1 = _
      rw [hx]
      field_simp

/-- `I(A;C|B) = 0` exactly when `A ⊥ C | B` holds under `p`. -/
theorem condMutualInfo_eq_zero_iff (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) : condMutualInfo p f g h = 0 ↔ CondIndep p f g h := by
  rw [condIndep_iff_law3_eq_markovProjection p hp f g h,
    ← klSum_law3_markovProjection_eq_condMutualInfo p hp f g h]
  constructor
  · intro hzero
    exact fun x => klSumOn_eq_zero_imp Finset.univ _ _ (fun x _ => pushforward_nonneg p hp _ x)
      (fun x _ => markovProjection_nonneg p hp f g h x)
      (fun x _ hx => markovProjection_pos_of_law3_pos p hp f g h hx)
      (by rw [sum_markovProjection p hp f g h]; exact (sum_pushforward p _).symm) hzero x
      (Finset.mem_univ x)
  · intro heq
    unfold klSum klSumOn
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [← heq x]
    have hnn : 0 ≤ law3 p f g h x := pushforward_nonneg p hp _ x
    rcases hnn.lt_or_eq with hpos | hzero
    · rw [div_self hpos.ne', Real.log_one, mul_zero]
    · have hz : law3 p f g h x = 0 := hzero.symm
      rw [hz]; simp

/-- The `(A,C)` law of the Markov projection. -/
noncomputable def markovProjectionAC (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    α × γ → ℝ :=
  pushforward (markovProjection p f g h) (fun x => (x.1, x.2.2))

theorem law2_fh_eq_pushforward_law3 (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    law2 p f h = pushforward (law3 p f g h) (fun x => (x.1, x.2.2)) := by
  funext ac
  unfold law3 law2
  rw [pushforward_pushforward]
  rfl

/-- Prop 4.7 (ii): the end-to-end loss on the `(A, C)` law is at most `I(A;C|B)`. -/
theorem klSum_law2_markovProjectionAC_le_condMutualInfo (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    klSum (law2 p f h) (markovProjectionAC p f g h) ≤ condMutualInfo p f g h := by
  rw [← klSum_law3_markovProjection_eq_condMutualInfo p hp f g h,
    law2_fh_eq_pushforward_law3 p f g h]
  unfold markovProjectionAC
  exact klSum_pushforward_le _ _ _ (fun x => pushforward_nonneg p hp _ x)
    (fun x => markovProjection_nonneg p hp f g h x)
    (fun x hx => markovProjection_pos_of_law3_pos p hp f g h hx)

/-- Under `A ⊥ C | B` the Markov projection reproduces the `(A, C)` law exactly. -/
theorem markovProjectionAC_eq_law2_of_condIndep (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α)
    (g : Ω → β) (h : Ω → γ) (hci : CondIndep p f g h) :
    markovProjectionAC p f g h = law2 p f h := by
  have heq := (condIndep_iff_law3_eq_markovProjection p hp f g h).1 hci
  unfold markovProjectionAC
  rw [law2_fh_eq_pushforward_law3 p f g h]
  congr 1
  funext x
  exact (heq x).symm

omit [Fintype β] in
/-- Mutual information `I(f ; h)`: divergence of the joint law from the product of the
marginals.  Equivalently, the expected divergence of `P(C | A)` from the prior `P(C)`. -/
noncomputable def mutualInfo (p : Ω → ℝ) (f : Ω → α) (h : Ω → γ) : ℝ :=
  klSum (law2 p f h) (fun x => pushforward p f x.1 * pushforward p h x.2)

omit [Fintype β] in
theorem mutualInfo_nonneg (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1) (f : Ω → α)
    (h : Ω → γ) : 0 ≤ mutualInfo p f h := by
  unfold mutualInfo klSum
  refine klSumOn_nonneg _ _ _ (fun x _ => pushforward_nonneg p hp _ x)
    (fun x _ => mul_nonneg (pushforward_nonneg p hp f x.1) (pushforward_nonneg p hp h x.2))
    (fun x _ hx => mul_pos (lt_of_lt_of_le hx (law2_le_pushforward_fst p hp f h x))
      (lt_of_lt_of_le hx (law2_le_pushforward_snd p hp f h x))) ?_
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_pushforward, sum_pushforward, hsum, one_mul]
  unfold law2
  rw [sum_pushforward, hsum]

/-- The conditional mutual information as an expectation over outcomes. -/
theorem condMutualInfo_eq_sum_omega (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    condMutualInfo p f g h = ∑ ω, p ω *
      Real.log (law3 p f g h (f ω, g ω, h ω) * pushforward p g (g ω) /
        (law2 p f g (f ω, g ω) * law2 p g h (g ω, h ω))) := by
  unfold condMutualInfo
  have := sum_pushforward_mul p (fun ω => (f ω, g ω, h ω))
    (fun x => Real.log (law3 p f g h x * pushforward p g x.2.1 /
      (law2 p f g (x.1, x.2.1) * law2 p g h (x.2.1, x.2.2))))
  unfold law3 at this ⊢
  exact this

end Pushforward

/-! ## Hop additivity along a path

A path is a map `Fin (n+1) → X`.  Hop `i` compares the joint law of the prefix `X_{<i}`, the
current state `X_i` and the next state `X_{i+1}`; its conditional mutual information
`I(X_{i+1} ; X_{<i} | X_i)` is what the Markov assumption at that hop ignores.  Summing over
all hops gives exactly the divergence from the joint law to the Markov chain with the same
one-step transition laws (`sum_hopCondMutualInfo_eq_klSum_pathMarkov`).  Since every summand is
nonnegative, the losses of the hops add and never cancel.
-/

section Paths

variable {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}

/-- Restriction of a path to the indices `≤ j`. -/
def prefixLE (j : Fin (n + 1)) (x : Fin (n + 1) → X) : {k : Fin (n + 1) // k ≤ j} → X :=
  fun k => x k.1

/-- Restriction of a path to the indices `< j`. -/
def prefixLT (j : Fin (n + 1)) (x : Fin (n + 1) → X) : {k : Fin (n + 1) // k < j} → X :=
  fun k => x k.1

omit [Fintype X] [DecidableEq X] in
theorem prefixLE_eq_iff (j : Fin (n + 1)) (x y : Fin (n + 1) → X) :
    prefixLE j y = prefixLE j x ↔ ∀ k, k ≤ j → y k = x k := by
  constructor
  · intro h k hk
    exact congrFun h ⟨k, hk⟩
  · intro h
    funext k
    exact h k.1 k.2

omit [Fintype X] [DecidableEq X] in
theorem prefixLT_eq_iff (j : Fin (n + 1)) (x y : Fin (n + 1) → X) :
    prefixLT j y = prefixLT j x ↔ ∀ k, k < j → y k = x k := by
  constructor
  · intro h k hk
    exact congrFun h ⟨k, hk⟩
  · intro h
    funext k
    exact h k.1 k.2

omit [Fintype X] [DecidableEq X] in
theorem prefixLE_last_injective :
    Function.Injective (prefixLE (Fin.last n) : (Fin (n + 1) → X) → _) := by
  intro x y h
  funext k
  exact (prefixLE_eq_iff (Fin.last n) y x).1 h k (Fin.le_last k)

omit [Fintype X] [DecidableEq X] in
theorem prefixLE_zero_eq_iff (x y : Fin (n + 1) → X) :
    prefixLE 0 y = prefixLE 0 x ↔ y 0 = x 0 := by
  rw [prefixLE_eq_iff]
  constructor
  · intro h
    exact h 0 le_rfl
  · intro h k hk
    have : k = 0 := Fin.le_zero_iff.1 hk
    rw [this]
    exact h

omit [Fintype X] [DecidableEq X] in
/-- Fibre identity behind hop `i`: knowing `X_{<i}`, `X_i`, `X_{i+1}` is knowing `X_{≤ i+1}`. -/
theorem hop_law3_fiber_iff (i : Fin n) (x y : Fin (n + 1) → X) :
    (prefixLT i.castSucc y, y i.castSucc, y i.succ) =
      (prefixLT i.castSucc x, x i.castSucc, x i.succ) ↔
    prefixLE i.succ y = prefixLE i.succ x := by
  rw [Prod.mk.injEq, Prod.mk.injEq, prefixLT_eq_iff, prefixLE_eq_iff]
  constructor
  · rintro ⟨hlt, hi, hi1⟩ k hk
    have hk' : (k : ℕ) ≤ (i : ℕ) + 1 := by
      have := hk
      rw [Fin.le_def, Fin.val_succ] at this
      exact this
    rcases Nat.lt_or_ge (k : ℕ) (i : ℕ) with hlt' | hge
    · exact hlt k (by rw [Fin.lt_def, Fin.val_castSucc]; exact hlt')
    · rcases Nat.eq_or_lt_of_le hge with heq | hlt''
      · have : k = i.castSucc := Fin.ext (by rw [Fin.val_castSucc]; exact heq.symm)
        rw [this]; exact hi
      · have : k = i.succ := Fin.ext (by rw [Fin.val_succ]; omega)
        rw [this]; exact hi1
  · intro h
    refine ⟨fun k hk => h k ?_, h i.castSucc ?_, h i.succ le_rfl⟩
    · rw [Fin.le_def, Fin.val_succ]
      rw [Fin.lt_def, Fin.val_castSucc] at hk
      omega
    · rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
      omega

omit [Fintype X] [DecidableEq X] in
/-- Fibre identity: knowing `X_{<i}` and `X_i` is knowing `X_{≤ i}`. -/
theorem hop_law2_fiber_iff (i : Fin n) (x y : Fin (n + 1) → X) :
    (prefixLT i.castSucc y, y i.castSucc) = (prefixLT i.castSucc x, x i.castSucc) ↔
    prefixLE i.castSucc y = prefixLE i.castSucc x := by
  rw [Prod.mk.injEq, prefixLT_eq_iff, prefixLE_eq_iff]
  constructor
  · rintro ⟨hlt, hi⟩ k hk
    rcases lt_or_eq_of_le hk with hlt' | heq
    · exact hlt k hlt'
    · rw [heq]; exact hi
  · intro h
    exact ⟨fun k hk => h k hk.le, h i.castSucc le_rfl⟩

omit [Fintype X] [DecidableEq X] in
/-- Telescoping sum over `Fin n`. -/
theorem fin_sum_succ_sub_castSucc (F : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (F i.succ - F i.castSucc) = F (Fin.last n) - F 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have h1 : ∀ i : Fin n, F i.castSucc.succ = F i.succ.castSucc := fun i =>
      congrArg F (Fin.ext (by simp))
    have h2 : (Fin.last n).succ = Fin.last (n + 1) := Fin.ext (by simp)
    have h3 : ((0 : Fin (n + 1)).castSucc : Fin (n + 2)) = 0 := Fin.ext (by simp)
    have hih : ∑ i : Fin n, (F i.succ.castSucc - F i.castSucc.castSucc) =
        F (Fin.last n).castSucc - F (0 : Fin (n + 1)).castSucc := ih (fun j => F j.castSucc)
    have hsum : ∑ i : Fin n, (F i.castSucc.succ - F i.castSucc.castSucc) =
        ∑ i : Fin n, (F i.succ.castSucc - F i.castSucc.castSucc) :=
      Finset.sum_congr rfl fun i _ => by rw [h1 i]
    rw [hsum, hih, h2, h3]
    ring

/-- Conditional mutual information ignored by the Markov assumption at hop `i`:
`I(X_{i+1} ; X_{<i} | X_i)`. -/
noncomputable def hopCondMutualInfo (p : (Fin (n + 1) → X) → ℝ) (i : Fin n) : ℝ :=
  condMutualInfo p (prefixLT i.castSucc) (fun x => x i.castSucc) (fun x => x i.succ)

/-- The Markov chain with the initial law and the one-step transition laws of `p`. -/
noncomputable def pathMarkov (p : (Fin (n + 1) → X) → ℝ) (x : Fin (n + 1) → X) : ℝ :=
  pushforward p (fun y => y 0) (x 0) *
    ∏ i : Fin n, (if pushforward p (fun y => y i.castSucc) (x i.castSucc) = 0 then 0
      else law2 p (fun y => y i.castSucc) (fun y => y i.succ) (x i.castSucc, x i.succ) /
        pushforward p (fun y => y i.castSucc) (x i.castSucc))

/-- Hop additivity: `∑ᵢ I(X_{i+1}; X_{<i} | X_i) = KL(P ∥ P_Markov)`. -/
theorem sum_hopCondMutualInfo_eq_klSum_pathMarkov (p : (Fin (n + 1) → X) → ℝ)
    (hp : ∀ x, 0 ≤ p x) :
    ∑ i : Fin n, hopCondMutualInfo p i = klSum p (pathMarkov p) := by
  unfold hopCondMutualInfo
  simp only [condMutualInfo_eq_sum_omega]
  rw [Finset.sum_comm]
  unfold klSum klSumOn
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_sum]
  rcases (hp x).lt_or_eq with hpos | hzero
  · congr 1
    -- positivity of every law evaluated on the realised path
    have hm : ∀ j : Fin (n + 1), 0 < pushforward p (prefixLE j) (prefixLE j x) :=
      fun j => pushforward_pos_of_pos p hp _ hpos
    have hP : ∀ j : Fin (n + 1), 0 < pushforward p (fun y => y j) (x j) :=
      fun j => pushforward_pos_of_pos p hp (fun y => y j) hpos
    have hL : ∀ i : Fin n,
        0 < law2 p (fun y => y i.castSucc) (fun y => y i.succ) (x i.castSucc, x i.succ) :=
      fun i => pushforward_pos_of_pos p hp (fun y => (y i.castSucc, y i.succ)) hpos
    -- the prefix laws appearing in the hop terms
    have hL3 : ∀ i : Fin n, law3 p (prefixLT i.castSucc) (fun y => y i.castSucc)
        (fun y => y i.succ) (prefixLT i.castSucc x, x i.castSucc, x i.succ) =
        pushforward p (prefixLE i.succ) (prefixLE i.succ x) :=
      fun i => pushforward_congr_fiber p _ _ x (fun y => hop_law3_fiber_iff i x y)
    have hL2A : ∀ i : Fin n, law2 p (prefixLT i.castSucc) (fun y => y i.castSucc)
        (prefixLT i.castSucc x, x i.castSucc) =
        pushforward p (prefixLE i.castSucc) (prefixLE i.castSucc x) :=
      fun i => pushforward_congr_fiber p _ _ x (fun y => hop_law2_fiber_iff i x y)
    have hterm : ∀ i : Fin n,
        Real.log (law3 p (prefixLT i.castSucc) (fun y => y i.castSucc) (fun y => y i.succ)
            (prefixLT i.castSucc x, x i.castSucc, x i.succ) *
          pushforward p (fun y => y i.castSucc) (x i.castSucc) /
          (law2 p (prefixLT i.castSucc) (fun y => y i.castSucc)
              (prefixLT i.castSucc x, x i.castSucc) *
            law2 p (fun y => y i.castSucc) (fun y => y i.succ) (x i.castSucc, x i.succ))) =
        (Real.log (pushforward p (prefixLE i.succ) (prefixLE i.succ x)) -
          Real.log (pushforward p (prefixLE i.castSucc) (prefixLE i.castSucc x))) +
        (Real.log (pushforward p (fun y => y i.castSucc) (x i.castSucc)) -
          Real.log (law2 p (fun y => y i.castSucc) (fun y => y i.succ)
            (x i.castSucc, x i.succ))) := by
      intro i
      rw [hL3 i, hL2A i]
      rw [Real.log_div (mul_pos (hm _) (hP _)).ne' (mul_pos (hm _) (hL i)).ne',
        Real.log_mul (hm _).ne' (hP _).ne', Real.log_mul (hm _).ne' (hL i).ne']
      ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
      fin_sum_succ_sub_castSucc (fun j => Real.log (pushforward p (prefixLE j) (prefixLE j x)))]
    have hlast : pushforward p (prefixLE (Fin.last n)) (prefixLE (Fin.last n) x) = p x :=
      pushforward_of_injective p _ prefixLE_last_injective x
    have hzero' : pushforward p (prefixLE 0) (prefixLE 0 x) =
        pushforward p (fun y => y 0) (x 0) :=
      pushforward_congr_fiber p _ _ x (fun y => prefixLE_zero_eq_iff x y)
    rw [hlast, hzero']
    -- expand the logarithm of the Markov chain
    unfold pathMarkov
    have hfac : ∀ i : Fin n,
        (if pushforward p (fun y => y i.castSucc) (x i.castSucc) = 0 then 0
          else law2 p (fun y => y i.castSucc) (fun y => y i.succ) (x i.castSucc, x i.succ) /
            pushforward p (fun y => y i.castSucc) (x i.castSucc)) =
        law2 p (fun y => y i.castSucc) (fun y => y i.succ) (x i.castSucc, x i.succ) /
          pushforward p (fun y => y i.castSucc) (x i.castSucc) :=
      fun i => if_neg (hP i.castSucc).ne'
    rw [Finset.prod_congr rfl (fun i _ => hfac i)]
    have hprod : 0 < ∏ i : Fin n,
        law2 p (fun y => y i.castSucc) (fun y => y i.succ) (x i.castSucc, x i.succ) /
          pushforward p (fun y => y i.castSucc) (x i.castSucc) :=
      Finset.prod_pos fun i _ => div_pos (hL i) (hP _)
    rw [Real.log_div hpos.ne' (mul_pos (hP 0) hprod).ne', Real.log_mul (hP 0).ne' hprod.ne',
      Real.log_prod (fun i _ => (div_pos (hL i) (hP _)).ne')]
    rw [Finset.sum_congr rfl (fun i _ => Real.log_div (hL i).ne' (hP i.castSucc).ne'),
      Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    ring
  · rw [← hzero]
    simp

theorem hopCondMutualInfo_nonneg (p : (Fin (n + 1) → X) → ℝ) (hp : ∀ x, 0 ≤ p x) (i : Fin n) :
    0 ≤ hopCondMutualInfo p i :=
  condMutualInfo_nonneg p hp _ _ _

/-- The divergence to the Markov chain is nonnegative and dominates every single hop's
conditional mutual information: no hop's loss is cancelled by another. -/
theorem hopCondMutualInfo_le_klSum_pathMarkov (p : (Fin (n + 1) → X) → ℝ) (hp : ∀ x, 0 ≤ p x)
    (i : Fin n) : hopCondMutualInfo p i ≤ klSum p (pathMarkov p) := by
  rw [← sum_hopCondMutualInfo_eq_klSum_pathMarkov p hp]
  exact Finset.single_le_sum (f := fun i => hopCondMutualInfo p i)
    (fun j _ => hopCondMutualInfo_nonneg p hp j) (Finset.mem_univ i)

end Paths

/-! ## Factorization through the middle coordinate

The discrete Bayesian-network reading of the positive canary: when the joint weight on
`α × β × γ` factorizes through the middle coordinate, `p (a,b,c) = φ a b * ψ b c`, the outer
coordinates are conditionally independent given the middle one, so the Markov projection is
exact and every chain loss vanishes.  This is the factorization form used by the discrete local
Markov development in `Mettapedia.ProbabilityTheory.BayesianNetworks`. -/

section Factorization

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] in
/-- The coordinate maps of a triple recover the triple. -/
theorem coordinates_injective :
    Function.Injective (fun x : α × β × γ => (x.1, x.2.1, x.2.2)) := by
  intro x y h
  exact h

/-- Factorization through the middle coordinate gives `A ⊥ C | B`. -/
theorem condIndep_of_factorization (φ : α → β → ℝ) (ψ : β → γ → ℝ) :
    CondIndep (fun x : α × β × γ => φ x.1 x.2.1 * ψ x.2.1 x.2.2)
      (fun x => x.1) (fun x => x.2.1) (fun x => x.2.2) := by
  set p : α × β × γ → ℝ := fun x => φ x.1 x.2.1 * ψ x.2.1 x.2.2 with hpdef
  have h3 : ∀ x, law3 p (fun x => x.1) (fun x => x.2.1) (fun x => x.2.2) x = p x := fun x =>
    pushforward_of_injective p _ coordinates_injective x
  have hfg : ∀ a b, law2 p (fun x => x.1) (fun x => x.2.1) (a, b) = φ a b * ∑ c, ψ b c := by
    intro a b
    rw [← sum_law3_right p (fun x => x.1) (fun x => x.2.1) (fun x => x.2.2) a b, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => h3 (a, b, c)
  have hgh : ∀ b c, law2 p (fun x => x.2.1) (fun x => x.2.2) (b, c) = (∑ a, φ a b) * ψ b c := by
    intro b c
    rw [← sum_law3_left p (fun x => x.1) (fun x => x.2.1) (fun x => x.2.2) b c, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => h3 (a, b, c)
  have hg : ∀ b, pushforward p (fun x => x.2.1) b = (∑ a, φ a b) * ∑ c, ψ b c := by
    intro b
    rw [← sum_law2_left p (fun x => x.1) (fun x => x.2.1) b, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => hfg a b
  intro x
  rw [h3 x, hg x.2.1, hfg x.1 x.2.1, hgh x.2.1 x.2.2]
  simp only [hpdef]
  ring

end Factorization

end Mettapedia.InformationTheory.FiniteRV
