import Mettapedia.InformationTheory.KnowledgeQuantification.Entropic
import Mettapedia.InformationTheory.MutualInformation

/-!
# Knowledge about hypotheses: two corrections

D. Fanelli, *A theory and methodology to quantify knowledge*, R. Soc. open sci. 6: 181055
(2019), §3.5, values null and negative results through the information an experiment
carries about the hypothesis variable `T`.  `Entropic.eliminationGain` gives its eq. 3.23,
and `logRatioInformationGainBits_ruleOut` reads it as Bayesian conditioning: a test that
conclusively rules out one of `n` equally likely hypotheses moves each survivor from prior
`1/n` to posterior `1/(n − 1)` (`posterior_ruleOut`), a log-ratio gain of
`log₂ (n / (n − 1))` bits.  Two of the paper's supporting claims need correction.

* **Appendix H.**  Ruling out one hypothesis usually lowers the entropy of the rest, but not
  always: `entropy_can_rise_after_elimination` rules out the most probable of three
  hypotheses, `7/8, 1/16, 1/16`, and leaves a fair choice of entropy `log 2`, more than
  before.  The appendix notes this case; here it is a theorem.
* **Eq. 3.24, appendix G.**  The paper states `K(Y; X, T) = K(T; Y, X)` "because of the
  symmetry of mutual information".  Both sides carry the same factor, so the claim is
  `I(Y; X, T) = I(T; Y, X)`.  Appendix G derives it using `H(Y, X, T) − H(Y) − H(X) =
  H(T | Y, X)`, which needs `H(Y, X) = H(Y) + H(X)`: an input independent of the
  explanandum.  `mutualInfo_not_symmetric_in_hypothesis` is the counterexample: with the
  input an exact copy of a fair-bit explanandum and an independent fair-bit hypothesis,
  `I(Y; X, T) = log 2` while `I(T; Y, X) = 0`.  What holds is the exchange identity
  `I(Y; X, T) = I(T; Y, X) + I(Y; X) − I(T; X)` (`mutualInfo_exchange`, from the chain rule
  `mutualInfo_pair_eq` and the symmetry `condMutualInfo_comm`), so the claimed symmetry holds
  exactly when `I(Y; X) = I(T; X)` (`mutualInfo_symmetric_iff`).

Selecting a theory fixes the theory variable (eqs. 2.10–2.11): the conditional mutual
information then reduces to the mutual information (`condMutualInfo_of_const`), so the
numerator of `K` is `n_Y I(Y; X | T = τ)` in the tree's terms
(`FiniteSystem.budget_explained_eq_condMutualInfo`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.InformationTheory.KnowledgeQuantification

open Real
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV

/-! ## Ruling out the most probable hypothesis -/

/-- Three hypotheses with masses `7/8, 1/16, 1/16`. -/
def skewedThree : ProbVec 3 :=
  ⟨![7 / 8, 1 / 16, 1 / 16], by
    constructor
    · intro i
      fin_cases i <;> norm_num
    · rw [Fin.sum_univ_three]
      show (7 / 8 : ℝ) + 1 / 16 + 1 / 16 = 1
      norm_num⟩

/-- Ruling out the first hypothesis and renormalizing leaves a fair choice. -/
theorem skewedThree_rest :
    (fun i : Fin 2 => skewedThree.1 i.succ / (1 - skewedThree.1 0)) = binaryUniform.1 := by
  funext i
  fin_cases i
  · show (1 / 16 : ℝ) / (1 - 7 / 8) = binaryUniform.1 0
    rw [binaryUniform_apply_zero]
    norm_num
  · show (1 / 16 : ℝ) / (1 - 7 / 8) = binaryUniform.1 1
    rw [binaryUniform_apply_one]
    norm_num

theorem shannonEntropy_skewedThree :
    shannonEntropy skewedThree =
      negMulLog (7 / 8) + negMulLog (1 / 16) + negMulLog (1 / 16) := by
  unfold shannonEntropy skewedThree
  rw [Fin.sum_univ_three]
  rfl

/-- **Ruling out the most probable hypothesis can raise the entropy** (appendix H). -/
theorem entropy_can_rise_after_elimination :
    shannonEntropy skewedThree < shannonEntropy binaryUniform := by
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have key : 17 * Real.log 2 < 7 * Real.log 7 := by
    have h1 : Real.log ((2 : ℝ) ^ 17) = 17 * Real.log 2 := by
      rw [Real.log_pow]
      norm_num
    have h2 : Real.log ((7 : ℝ) ^ 7) = 7 * Real.log 7 := by
      rw [Real.log_pow]
      norm_num
    rw [← h1, ← h2]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  rw [shannonEntropy_skewedThree, shannonEntropy_binaryUniform]
  simp only [Real.negMulLog]
  rw [Real.log_div (by norm_num : (7 : ℝ) ≠ 0) (by norm_num : (8 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (16 : ℝ) ≠ 0), Real.log_one, h8,
    h16]
  linarith

/-! ## A conclusive negative result, as conditioning -/

section RuleOut

open Mettapedia.ProbabilityTheory.BayesianInference

/-- The likelihood of a test that conclusively rules out hypothesis `i`. -/
def ruleOut {n : ℕ} (i : Fin n) : Fin n → ℝ := fun k => if k = i then 0 else 1

theorem ruleOut_nonneg {n : ℕ} (i : Fin n) (k : Fin n) : 0 ≤ ruleOut i k := by
  unfold ruleOut
  split_ifs <;> norm_num

theorem evidence_ruleOut {n : ℕ} (hn : 0 < n) (i : Fin n) :
    evidence (uniformDist n hn) (ruleOut i) = ((n : ℝ) - 1) / n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hterm : ∀ k : Fin n, (uniformDist n hn).1 k * ruleOut i k =
      1 / (n : ℝ) - (if k = i then 1 / (n : ℝ) else 0) := by
    intro k
    rw [uniformDist_apply]
    unfold ruleOut
    split_ifs <;> ring
  unfold evidence
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem evidence_ruleOut_pos {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    0 < evidence (uniformDist n (by omega)) (ruleOut i) := by
  rw [evidence_ruleOut]
  have h1 : (1 : ℝ) < n := by exact_mod_cast hn
  exact div_pos (by linarith) (by linarith)

/-- Ruling out one of `n` equally likely hypotheses leaves every survivor with posterior
`1 / (n − 1)` (the tree's Bayesian `posterior`). -/
theorem posterior_ruleOut {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) (hj : j ≠ i) :
    (posterior (uniformDist n (by omega)) (ruleOut i) (ruleOut_nonneg i)
      (evidence_ruleOut_pos hn i)).1 j = 1 / ((n : ℝ) - 1) := by
  have h1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  rw [posterior_apply, evidence_ruleOut, uniformDist_apply]
  unfold ruleOut
  rw [if_neg hj]
  field_simp

/-- **A conclusive negative result, pointwise** (eq. 3.23).  Each surviving hypothesis gains
`eliminationGain n / log 2` bits: the tree's log-ratio information gain of its posterior
over its prior. -/
theorem logRatioInformationGainBits_ruleOut {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) (hj : j ≠ i) :
    logRatioInformationGainBits
        ((posterior (uniformDist n (by omega)) (ruleOut i) (ruleOut_nonneg i)
          (evidence_ruleOut_pos hn i)).1 j)
        ((uniformDist n (by omega)).1 j) =
      eliminationGain n / Real.log 2 := by
  have h1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  rw [posterior_ruleOut hn i j hj, uniformDist_apply,
    logRatioInformationGainBits_eq_log2_ratio (div_pos one_pos (by linarith))
      (div_pos one_pos (by linarith)),
    eliminationGain_eq_log_div hn]
  congr 2
  field_simp

end RuleOut

/-! ## The symmetry claimed in eq. 3.24 -/

/-- Two independent fair bits: the first is the explanandum and its copy the input; the
second is the hypothesis. -/
def fairPair : Fin 2 × Fin 2 → ℝ := fun _ => 1 / 4

theorem fairPair_nonneg (ω : Fin 2 × Fin 2) : 0 ≤ fairPair ω := by
  norm_num [fairPair]

theorem pushforward_fairPair_fst (a : Fin 2) : pushforward fairPair Prod.fst a = 1 / 2 := by
  rw [pushforward_fst, Fin.sum_univ_two]
  norm_num [fairPair]

theorem pushforward_fairPair_snd (c : Fin 2) : pushforward fairPair Prod.snd c = 1 / 2 := by
  rw [pushforward_snd, Fin.sum_univ_two]
  norm_num [fairPair]

theorem pushforward_fairPair_id (x : Fin 2 × Fin 2) :
    pushforward fairPair (fun ω => (ω.1, ω.2)) x = 1 / 4 := by
  rw [pushforward_of_injective fairPair (fun ω => (ω.1, ω.2)) (fun _ _ h => h) x]
  rfl

theorem pushforward_fairPair_diag (x : Fin 2 × Fin 2) :
    pushforward fairPair (fun ω => (ω.1, ω.1)) x = if x.1 = x.2 then 1 / 2 else 0 := by
  obtain ⟨a, b⟩ := x
  rw [pushforward_eq_sum_ite, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two,
    Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;> norm_num [fairPair]

theorem law2_fairPair_copy (x : Fin 2 × Fin 2 × Fin 2) :
    law2 fairPair Prod.fst (fun ω => (ω.1, ω.2)) x = if x.1 = x.2.1 then 1 / 4 else 0 := by
  obtain ⟨a, b, c⟩ := x
  rw [law2, pushforward_eq_sum_ite, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two,
    Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> norm_num [fairPair]

theorem law2_fairPair_hypothesis (x : Fin 2 × Fin 2 × Fin 2) :
    law2 fairPair Prod.snd (fun ω => (ω.1, ω.1)) x =
      pushforward fairPair Prod.snd x.1 * pushforward fairPair (fun ω => (ω.1, ω.1)) x.2 := by
  rw [pushforward_fairPair_snd, pushforward_fairPair_diag]
  obtain ⟨c, a, b⟩ := x
  rw [law2, pushforward_eq_sum_ite, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two,
    Fin.sum_univ_two]
  fin_cases c <;> fin_cases a <;> fin_cases b <;> norm_num [fairPair]

/-- With the input an exact copy of a fair-bit explanandum, input and hypothesis together carry
`log 2` about the explanandum. -/
theorem mutualInfo_explanandum_input_hypothesis :
    mutualInfo fairPair Prod.fst (fun ω => (ω.1, ω.2)) = Real.log 2 := by
  rw [mutualInfo, klSum_eq_sum]
  simp only [law2_fairPair_copy, pushforward_fairPair_fst, pushforward_fairPair_id]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  have h : Real.log ((1 / 4 : ℝ) / (1 / 2 * (1 / 4))) = Real.log 2 := by norm_num
  norm_num [h]
  ring

/-- An independent hypothesis carries nothing about explanandum and input. -/
theorem mutualInfo_hypothesis_explanandum_input :
    mutualInfo fairPair Prod.snd (fun ω => (ω.1, ω.1)) = 0 := by
  rw [mutualInfo]
  have hlaw : law2 fairPair Prod.snd (fun ω => (ω.1, ω.1)) =
      fun x => pushforward fairPair Prod.snd x.1 *
        pushforward fairPair (fun ω => (ω.1, ω.1)) x.2 :=
    funext law2_fairPair_hypothesis
  rw [hlaw]
  exact klSum_self_eq_zero _ fun x => mul_nonneg (pushforward_nonneg _ fairPair_nonneg _ _)
    (pushforward_nonneg _ fairPair_nonneg _ _)

/-- **Eq. 3.24 fails when the input is informative.**  `I(Y; X, T) = log 2` but
`I(T; Y, X) = 0`, so `K(Y; X, T)` and `K(T; Y, X)`, which share their positive factor, differ. -/
theorem mutualInfo_not_symmetric_in_hypothesis :
    mutualInfo fairPair Prod.fst (fun ω => (ω.1, ω.2)) ≠
      mutualInfo fairPair Prod.snd (fun ω => (ω.1, ω.1)) := by
  rw [mutualInfo_explanandum_input_hypothesis, mutualInfo_hypothesis_explanandum_input]
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

/-! ## What holds instead -/

section Exchange

open Mettapedia.ProbabilityTheory.BayesianInference

variable {Ω α β γ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Conditional mutual information is symmetric in its outer variables. -/
theorem condMutualInfo_comm (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    condMutualInfo p f g h = condMutualInfo p h g f := by
  rw [condMutualInfo_eq_sum_omega, condMutualInfo_eq_sum_omega]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have h3 : law3 p h g f (h ω, g ω, f ω) = law3 p f g h (f ω, g ω, h ω) :=
    pushforward_congr_fiber p (fun ω => (h ω, g ω, f ω)) (fun ω => (f ω, g ω, h ω)) ω
      (fun ω' => by simp only [Prod.mk.injEq]; tauto)
  have h2a : law2 p h g (h ω, g ω) = law2 p g h (g ω, h ω) :=
    pushforward_congr_fiber p (fun ω => (h ω, g ω)) (fun ω => (g ω, h ω)) ω
      (fun ω' => by simp only [Prod.mk.injEq]; tauto)
  have h2b : law2 p g f (g ω, f ω) = law2 p f g (f ω, g ω) :=
    pushforward_congr_fiber p (fun ω => (g ω, f ω)) (fun ω => (f ω, g ω)) ω
      (fun ω' => by simp only [Prod.mk.injEq]; tauto)
  rw [h3, h2a, h2b, mul_comm (law2 p g h (g ω, h ω))]

/-- Swapping the components of the second variable does not change mutual information. -/
theorem mutualInfo_pair_swap (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → γ) (g : Ω → α)
    (h : Ω → β) :
    mutualInfo p f (fun ω => (g ω, h ω)) = mutualInfo p f (fun ω => (h ω, g ω)) := by
  apply le_antisymm
  · have := mutualInfo_map_right_le p hp f (fun ω => (h ω, g ω)) Prod.swap
    exact this
  · have := mutualInfo_map_right_le p hp f (fun ω => (g ω, h ω)) Prod.swap
    exact this

/-- **The exchange identity behind eq. 3.24.**  `I(Y; X, T) = I(T; Y, X) + I(Y; X) − I(T; X)`:
the information input and hypothesis carry about the explanandum exceeds the information the
data carry about the hypothesis by what the input alone says about the explanandum, less what
it says about the hypothesis. -/
theorem mutualInfo_exchange (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (Y : Ω → α) (X : Ω → β)
    (T : Ω → γ) :
    mutualInfo p Y (fun ω => (X ω, T ω)) =
      mutualInfo p T (fun ω => (Y ω, X ω)) + mutualInfo p Y X - mutualInfo p T X := by
  rw [mutualInfo_pair_swap p hp T Y X, mutualInfo_pair_eq p hp Y X T,
    mutualInfo_pair_eq p hp T X Y, condMutualInfo_comm p Y X T]
  ring

/-- **Selecting a theory** (eqs. 2.10–2.11).  Once the theory variable is fixed at `τ`, the
conditional mutual information `I(f; h | T)` is the mutual information `I(f; h)`. -/
theorem condMutualInfo_of_const (p : Ω → ℝ) (hp1 : ∑ ω, p ω = 1) (f : Ω → α) (τ : β)
    (h : Ω → γ) :
    condMutualInfo p f (fun _ => τ) h = mutualInfo p f h := by
  rw [condMutualInfo_eq_sum_omega, mutualInfo, klSum_eq_sum]
  rw [show (∑ x : α × γ, law2 p f h x *
      Real.log (law2 p f h x / (pushforward p f x.1 * pushforward p h x.2))) =
      ∑ ω, p ω * Real.log (law2 p f h (f ω, h ω) /
        (pushforward p f (f ω) * pushforward p h (h ω))) from
    sum_pushforward_mul p (fun ω => (f ω, h ω))
      (fun x => Real.log (law2 p f h x / (pushforward p f x.1 * pushforward p h x.2)))]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have h3 : law3 p f (fun _ => τ) h (f ω, τ, h ω) = law2 p f h (f ω, h ω) :=
    pushforward_congr_fiber p (fun ω => (f ω, τ, h ω)) (fun ω => (f ω, h ω)) ω
      (fun ω' => by simp only [Prod.mk.injEq, true_and])
  have hT : pushforward p (fun _ => τ) τ = 1 := by
    rw [pushforward_eq_sum_ite]
    simp [hp1]
  have h2a : law2 p f (fun _ => τ) (f ω, τ) = pushforward p f (f ω) :=
    pushforward_congr_fiber p (fun ω => (f ω, τ)) f ω
      (fun ω' => by simp only [Prod.mk.injEq, and_true])
  have h2b : law2 p (fun _ => τ) h (τ, h ω) = pushforward p h (h ω) :=
    pushforward_congr_fiber p (fun ω => (τ, h ω)) h ω
      (fun ω' => by simp only [Prod.mk.injEq, true_and])
  rw [h3, hT, h2a, h2b, mul_one]

/-- **The numerator of `K` is `n_Y I(Y; X | T = τ)`**, the tree's conditional mutual
information of explanandum and input given the selected theory. -/
theorem FiniteSystem.budget_explained_eq_condMutualInfo {X' Y' Θ : Type*} [Fintype X']
    [Fintype Y'] [Fintype Θ] [DecidableEq X'] [DecidableEq Y'] [DecidableEq Θ]
    (s : FiniteSystem X' Y') (τ : Θ) :
    s.budget.explained =
      s.explananda * condMutualInfo (joint s.inputLaw s.kernel).1 Prod.snd (fun _ => τ)
        Prod.fst := by
  rw [condMutualInfo_comm, condMutualInfo_of_const _ (joint s.inputLaw s.kernel).2.2,
    s.budget_explained_eq_mutualInfo]

/-- The symmetry of eq. 3.24 holds exactly when the input says as much about the explanandum
as about the hypothesis; for an input independent of the hypothesis, exactly when the input
alone says nothing about the explanandum. -/
theorem mutualInfo_symmetric_iff (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (Y : Ω → α) (X : Ω → β)
    (T : Ω → γ) :
    mutualInfo p Y (fun ω => (X ω, T ω)) = mutualInfo p T (fun ω => (Y ω, X ω)) ↔
      mutualInfo p Y X = mutualInfo p T X := by
  rw [mutualInfo_exchange p hp Y X T]
  constructor <;> intro h <;> linarith

end Exchange

end Mettapedia.InformationTheory.KnowledgeQuantification
