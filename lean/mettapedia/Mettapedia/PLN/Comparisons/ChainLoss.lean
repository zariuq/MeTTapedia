import Mettapedia.InformationTheory.ConditionalMutualInformation
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation

/-!
# Chain loss: what pairwise, local chaining costs, and when relative order survives

PLN deduction replaces the true joint law of `A, B, C` by the law that keeps the `(A,B)` and
`(B,C)` marginals and imposes `A ⊥ C | B`.  The information-theoretic core is in
`Mettapedia.InformationTheory.ConditionalMutualInformation`; this file states the PLN-facing
consequences.

* **The deduction formula is the Markov projection** (`markovProjectionAC_cond_eq_plnDeductionStrength`):
  for binary `A, B, C`, `P_R(C = 1 | A = 1)` computed from the Markov projection is exactly
  `plnDeductionStrength s_AB s_BC s_B s_C`.
* **Hop criterion** (`chainLoss_le_mutualInfo_of_interaction_nonneg`): routing `A → C` through
  `B` costs at most `I(A;C|B)` and the bare prior costs `I(A;C)`.  When the interaction
  information `I(A;C) - I(A;C|B)` is nonnegative the hop cannot lose to the prior; when `B` is a
  common effect the hop can be strictly worse than ignorance.
* **Negative canary** (`orCollider_*`): two independent fair coins `A, C` and their disjunction
  `B`.  The prior is exact (`I(A;C) = 0`), yet deduction through `B` reports
  `P(C | A) = 2/3` against the truth `1/2`, and the chain loss is strictly positive.
* **Positive canary** (`chainLoss_eq_zero_of_condIndep`): under `A ⊥ C | B` the chain is exact.
* **Dobrushin contraction of a deduction step** (`abs_deductionStep_sub`): a binary deduction step
  is affine in the upstream strength with slope `P(C|B) - P(C|¬B)`, so a chain of steps
  transmits differences in the upstream estimate by the product of these slopes
  (`abs_deductionChain_sub`).  Moderate links forget their input; deterministic links pass it
  through unchanged.
* **Depth accumulation** (`error_accumulation`, `error_saturates`): with per-step error `δᵢ` and
  step Lipschitz constants `Lᵢ`, the accumulated error after `T` steps is at most
  `∑ᵢ δᵢ ∏_{j>i} Lⱼ`; under a uniform contraction `κ < 1` it saturates at `δ / (1 - κ)`,
  independent of depth.
* **Relative order** (`sibling_order_invariant_of_equal_links`,
  `sibling_order_preserved_of_margin`): two conclusions computed from the same upstream
  estimate keep their order for every value of that estimate when their links have equal
  strength; with unequal links the order survives an upstream error smaller than the gap divided
  by the difference of link strengths.  This is the precise sense in which relative values are
  more robust than absolute ones.

Double counting of shared evidence is a separate failure mode; its finite-source canary is
`Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision.revisionMany_duplicate_positiveUnitEvidence_ne_singleton`.
-/

namespace Mettapedia.PLN.Comparisons.ChainLoss

open Real Finset BigOperators
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation

/-! ## The deduction formula as a Markov projection -/

section DeductionFormula

variable {Ω : Type*} [Fintype Ω]

/-- Prop 4.7 (iii): for binary `A, B, C`, the conditional `P_R(C = 1 | A = 1)` of the Markov
projection is the PLN deduction formula evaluated on the strengths read off `p`. -/
theorem markovProjectionAC_cond_eq_plnDeductionStrength (p : Ω → ℝ)
    (hsum : ∑ ω, p ω = 1) (f g h : Ω → Bool)
    (hA : 0 < pushforward p f true) (hB : 0 < pushforward p g true)
    (hnB : 0 < pushforward p g false) :
    markovProjectionAC p f g h (true, true) / pushforward p f true =
      plnDeductionStrength
        (law2 p f g (true, true) / pushforward p f true)
        (law2 p g h (true, true) / pushforward p g true)
        (pushforward p g true) (pushforward p h true) := by
  -- marginal bookkeeping over `Bool`
  have hAB : law2 p f g (true, true) + law2 p f g (true, false) = pushforward p f true := by
    have := sum_law2_right p f g true
    rw [Fintype.sum_bool] at this
    exact this
  have hBC : law2 p g h (true, true) + law2 p g h (false, true) = pushforward p h true := by
    have := sum_law2_left p g h true
    rw [Fintype.sum_bool] at this
    exact this
  have hBtot : pushforward p g true + pushforward p g false = 1 := by
    have := sum_pushforward p g
    rw [Fintype.sum_bool, hsum] at this
    exact this
  have hAC : markovProjectionAC p f g h (true, true) =
      law2 p f g (true, true) * law2 p g h (true, true) / pushforward p g true +
      law2 p f g (true, false) * law2 p g h (false, true) / pushforward p g false := by
    unfold markovProjectionAC
    rw [pushforward_eq_sum_ite]
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Prod.mk.injEq, if_true, if_false,
      true_and, false_and, add_zero, Bool.false_eq_true]
    unfold markovProjection
    simp only [if_neg hB.ne', if_neg hnB.ne']
  rw [hAC]
  unfold plnDeductionStrength
  have h1 : 1 - law2 p f g (true, true) / pushforward p f true =
      law2 p f g (true, false) / pushforward p f true := by
    field_simp
    linarith
  have h2 : pushforward p h true - pushforward p g true *
      (law2 p g h (true, true) / pushforward p g true) = law2 p g h (false, true) := by
    field_simp
    linarith
  have h3 : 1 - pushforward p g true = pushforward p g false := by linarith
  rw [h1, h2, h3]
  field_simp

end DeductionFormula

/-! ## Hop criterion: information gained versus independence assumed -/

section HopCriterion

variable {Ω : Type*} [Fintype Ω] {α β γ : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

/-- The end-to-end loss of routing `A → C` through `B`: divergence of the true `(A, C)` law from
the `(A, C)` law of the Markov projection. -/
noncomputable def chainLoss (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) : ℝ :=
  klSum (law2 p f h) (markovProjectionAC p f g h)

/-- Interaction information `I(A;C) - I(A;C|B)`: information gained by the hop minus the
independence it assumes. -/
noncomputable def interactionInfo (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) : ℝ :=
  mutualInfo p f h - condMutualInfo p f g h

theorem chainLoss_le_condMutualInfo (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) : chainLoss p f g h ≤ condMutualInfo p f g h :=
  klSum_law2_markovProjectionAC_le_condMutualInfo p hp f g h

/-- Hop criterion: when the interaction information is nonnegative, chaining through `B` costs
no more than answering from the prior. -/
theorem chainLoss_le_mutualInfo_of_interaction_nonneg (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (f : Ω → α) (g : Ω → β) (h : Ω → γ) (hI : 0 ≤ interactionInfo p f g h) :
    chainLoss p f g h ≤ mutualInfo p f h := by
  unfold interactionInfo at hI
  have := chainLoss_le_condMutualInfo p hp f g h
  linarith

/-- Positive canary: under `A ⊥ C | B` the chain reproduces the `(A, C)` law and loses
nothing. -/
theorem chainLoss_eq_zero_of_condIndep (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α)
    (g : Ω → β) (h : Ω → γ) (hci : CondIndep p f g h) : chainLoss p f g h = 0 := by
  unfold chainLoss
  rw [markovProjectionAC_eq_law2_of_condIndep p hp f g h hci]
  exact klSum_self_eq_zero _ fun x => pushforward_nonneg p hp _ x

theorem markovProjectionAC_nonneg (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) (x : α × γ) : 0 ≤ markovProjectionAC p f g h x :=
  pushforward_nonneg _ (fun y => markovProjection_nonneg p hp f g h y) _ x

theorem sum_markovProjectionAC (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) : ∑ x, markovProjectionAC p f g h x = ∑ ω, p ω := by
  unfold markovProjectionAC
  rw [sum_pushforward, sum_markovProjection p hp f g h]

/-- Wherever the true `(A, C)` law is positive, so is the projected one. -/
theorem markovProjectionAC_pos_of_law2_pos (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α)
    (g : Ω → β) (h : Ω → γ) {x : α × γ} (hx : 0 < law2 p f h x) :
    0 < markovProjectionAC p f g h x := by
  rw [law2_fh_eq_pushforward_law3 p f g h] at hx
  unfold markovProjectionAC
  -- some triple with positive `law3` lies over `x`; the Markov projection is positive there
  unfold pushforward at hx ⊢
  obtain ⟨y, hy, hpos⟩ : ∃ y ∈ Finset.univ.filter (fun y : α × β × γ => (y.1, y.2.2) = x),
      0 < law3 p f g h y := by
    by_contra hcon
    have hall : ∀ y ∈ Finset.univ.filter (fun y : α × β × γ => (y.1, y.2.2) = x),
        law3 p f g h y = 0 := fun y hy =>
      le_antisymm (not_lt.1 fun hlt => hcon ⟨y, hy, hlt⟩) (pushforward_nonneg p hp _ y)
    rw [Finset.sum_eq_zero hall] at hx
    exact lt_irrefl _ hx
  exact lt_of_lt_of_le (markovProjection_pos_of_law3_pos p hp f g h hpos)
    (Finset.single_le_sum (f := markovProjection p f g h)
      (fun y _ => markovProjection_nonneg p hp f g h y) hy)

theorem chainLoss_nonneg (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    0 ≤ chainLoss p f g h := by
  unfold chainLoss klSum
  refine klSumOn_nonneg _ (law2 p f h) (markovProjectionAC p f g h)
    (fun x _ => pushforward_nonneg p hp _ x)
    (fun x _ => markovProjectionAC_nonneg p hp f g h x)
    (fun x _ hx => markovProjectionAC_pos_of_law2_pos p hp f g h hx) ?_
  rw [sum_markovProjectionAC p hp f g h]
  unfold law2
  rw [sum_pushforward]

end HopCriterion

/-! ## Negative canary: two independent coins and their disjunction -/

section OrCollider

/-- Uniform weights on two fair independent coins. -/
noncomputable def coinPair : Bool × Bool → ℝ := fun _ => (1 : ℝ) / 4

theorem coinPair_nonneg : ∀ ω, 0 ≤ coinPair ω := fun _ => by unfold coinPair; norm_num

theorem coinPair_sum : ∑ ω, coinPair ω = 1 := by
  unfold coinPair
  rw [Fintype.sum_prod_type]
  simp
  norm_num

/-- `A`: the first coin. -/
def coinA : Bool × Bool → Bool := Prod.fst
/-- `C`: the second coin. -/
def coinC : Bool × Bool → Bool := Prod.snd
/-- `B`: the disjunction of the two coins, a common effect of `A` and `C`. -/
def coinOr : Bool × Bool → Bool := fun ω => ω.1 || ω.2

theorem orCollider_law3_ttt : law3 coinPair coinA coinOr coinC (true, true, true) = 1 / 4 := by
  unfold law3 coinPair coinA coinOr coinC
  rw [pushforward_eq_sum_ite, Fintype.sum_prod_type]
  simp

theorem orCollider_pushforward_or_true : pushforward coinPair coinOr true = 3 / 4 := by
  unfold coinPair coinOr
  rw [pushforward_eq_sum_ite, Fintype.sum_prod_type]
  simp
  norm_num

theorem orCollider_pushforward_or_false : pushforward coinPair coinOr false = 1 / 4 := by
  unfold coinPair coinOr
  rw [pushforward_eq_sum_ite, Fintype.sum_prod_type]
  simp

theorem orCollider_law2_AB_tt : law2 coinPair coinA coinOr (true, true) = 1 / 2 := by
  unfold law2 coinPair coinA coinOr
  rw [pushforward_eq_sum_ite, Fintype.sum_prod_type]
  simp
  norm_num

theorem orCollider_law2_AB_tf : law2 coinPair coinA coinOr (true, false) = 0 := by
  unfold law2 coinPair coinA coinOr
  rw [pushforward_eq_sum_ite, Fintype.sum_prod_type]
  simp

theorem orCollider_law2_BC_tt : law2 coinPair coinOr coinC (true, true) = 1 / 2 := by
  unfold law2 coinPair coinOr coinC
  rw [pushforward_eq_sum_ite, Fintype.sum_prod_type]
  simp
  norm_num

theorem orCollider_law2_BC_ft : law2 coinPair coinOr coinC (false, true) = 0 := by
  unfold law2 coinPair coinOr coinC
  rw [pushforward_eq_sum_ite, Fintype.sum_prod_type]
  simp

theorem orCollider_pushforward_A_true : pushforward coinPair coinA true = 1 / 2 := by
  unfold coinPair coinA
  rw [pushforward_eq_sum_ite, Fintype.sum_prod_type]
  simp
  norm_num

theorem orCollider_law2_AC (a c : Bool) : law2 coinPair coinA coinC (a, c) = 1 / 4 := by
  unfold law2 coinPair coinA coinC
  rw [pushforward_eq_sum_ite, Fintype.sum_prod_type]
  cases a <;> cases c <;> simp

theorem orCollider_pushforward_A (a : Bool) : pushforward coinPair coinA a = 1 / 2 := by
  unfold coinPair coinA
  rw [pushforward_eq_sum_ite, Fintype.sum_prod_type]
  cases a <;> simp <;> norm_num

theorem orCollider_pushforward_C (c : Bool) : pushforward coinPair coinC c = 1 / 2 := by
  unfold coinPair coinC
  rw [pushforward_eq_sum_ite, Fintype.sum_prod_type]
  cases c <;> simp <;> norm_num

/-- `A` and `C` are not conditionally independent given their disjunction. -/
theorem orCollider_not_condIndep : ¬ CondIndep coinPair coinA coinOr coinC := by
  intro hci
  have := hci (true, true, true)
  simp only at this
  rw [orCollider_law3_ttt, orCollider_pushforward_or_true, orCollider_law2_AB_tt,
    orCollider_law2_BC_tt] at this
  norm_num at this

theorem orCollider_condMutualInfo_pos : 0 < condMutualInfo coinPair coinA coinOr coinC := by
  rcases (condMutualInfo_nonneg coinPair coinPair_nonneg coinA coinOr coinC).lt_or_eq
    with hpos | hzero
  · exact hpos
  · exact absurd ((condMutualInfo_eq_zero_iff coinPair coinPair_nonneg coinA coinOr coinC).1
      hzero.symm) orCollider_not_condIndep

/-- `A` and `C` are independent: the prior is already exact. -/
theorem orCollider_mutualInfo_eq_zero : mutualInfo coinPair coinA coinC = 0 := by
  unfold mutualInfo
  have hprod : (fun x : Bool × Bool => pushforward coinPair coinA x.1 *
      pushforward coinPair coinC x.2) = law2 coinPair coinA coinC := by
    funext x
    rw [orCollider_pushforward_A, orCollider_pushforward_C, orCollider_law2_AC]
    norm_num
  rw [hprod]
  exact klSum_self_eq_zero _ fun x => pushforward_nonneg coinPair coinPair_nonneg _ x

/-- Negative interaction information: the hop through the disjunction assumes more independence
than it gains information. -/
theorem orCollider_interactionInfo_neg : interactionInfo coinPair coinA coinOr coinC < 0 := by
  unfold interactionInfo
  rw [orCollider_mutualInfo_eq_zero]
  linarith [orCollider_condMutualInfo_pos]

theorem orCollider_markovProjectionAC_tt :
    markovProjectionAC coinPair coinA coinOr coinC (true, true) = 1 / 3 := by
  unfold markovProjectionAC
  rw [pushforward_eq_sum_ite, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Prod.mk.injEq, if_true, if_false,
    true_and, false_and, add_zero, Bool.false_eq_true]
  unfold markovProjection
  simp only
  rw [orCollider_pushforward_or_true, orCollider_pushforward_or_false, orCollider_law2_AB_tt,
    orCollider_law2_BC_tt, orCollider_law2_AB_tf, orCollider_law2_BC_ft]
  norm_num

/-- Deduction through the disjunction reports `P(C | A) = 2/3`. -/
theorem orCollider_chain_estimate :
    markovProjectionAC coinPair coinA coinOr coinC (true, true) /
      pushforward coinPair coinA true = 2 / 3 := by
  rw [orCollider_markovProjectionAC_tt, orCollider_pushforward_A_true]
  norm_num

/-- The truth is `P(C | A) = 1/2`. -/
theorem orCollider_true_conditional :
    law2 coinPair coinA coinC (true, true) / pushforward coinPair coinA true = 1 / 2 := by
  rw [orCollider_law2_AC, orCollider_pushforward_A_true]
  norm_num

/-- The chain loss is strictly positive while the prior loss is zero: routing through a common
effect is strictly worse than ignorance. -/
theorem orCollider_chainLoss_pos : 0 < chainLoss coinPair coinA coinOr coinC := by
  rcases (chainLoss_nonneg coinPair coinPair_nonneg coinA coinOr coinC).lt_or_eq
    with hpos | hzero
  · exact hpos
  · exfalso
    have hsum : ∑ x, markovProjectionAC coinPair coinA coinOr coinC x =
        ∑ x, law2 coinPair coinA coinC x := by
      rw [sum_markovProjectionAC coinPair coinPair_nonneg coinA coinOr coinC]
      unfold law2
      rw [sum_pushforward]
    have heq := klSumOn_eq_zero_imp Finset.univ (law2 coinPair coinA coinC)
      (markovProjectionAC coinPair coinA coinOr coinC)
      (fun x _ => pushforward_nonneg coinPair coinPair_nonneg _ x)
      (fun x _ => markovProjectionAC_nonneg coinPair coinPair_nonneg coinA coinOr coinC x)
      (fun x _ hx =>
        markovProjectionAC_pos_of_law2_pos coinPair coinPair_nonneg coinA coinOr coinC hx)
      hsum hzero.symm (true, true) (Finset.mem_univ _)
    rw [orCollider_law2_AC, orCollider_markovProjectionAC_tt] at heq
    norm_num at heq

end OrCollider

/-! ## Dobrushin contraction of a deduction step and chains of steps -/

section Contraction

/-- One binary deduction step in kernel form: upstream strength `m = P(B|A)`, link
`pC = P(C|B)`, `qC = P(C|¬B)`; output `P(C|A) = m·pC + (1-m)·qC`. -/
def deductionStep (pC qC m : ℝ) : ℝ := m * pC + (1 - m) * qC

theorem deductionStep_sub (pC qC m m' : ℝ) :
    deductionStep pC qC m - deductionStep pC qC m' = (pC - qC) * (m - m') := by
  unfold deductionStep
  ring

/-- Lemma 6.4 (Dobrushin coefficient of a binary kernel): a deduction step scales differences
in the upstream strength by exactly `|P(C|B) - P(C|¬B)|`. -/
theorem abs_deductionStep_sub (pC qC m m' : ℝ) :
    |deductionStep pC qC m - deductionStep pC qC m'| = |pC - qC| * |m - m'| := by
  rw [deductionStep_sub, abs_mul]

/-- A chain of deduction steps, applied in list order. -/
def deductionChain : List (ℝ × ℝ) → ℝ → ℝ
  | [], m => m
  | l :: L, m => deductionChain L (deductionStep l.1 l.2 m)

/-- Contraction coefficient of a chain: the product of the step coefficients. -/
def chainCoefficient (L : List (ℝ × ℝ)) : ℝ := (L.map fun l => |l.1 - l.2|).prod

/-- A chain transmits differences in its input scaled by exactly the product of the step
coefficients: inherited error and inherited information pass through the same factor. -/
theorem abs_deductionChain_sub (L : List (ℝ × ℝ)) (m m' : ℝ) :
    |deductionChain L m - deductionChain L m'| = chainCoefficient L * |m - m'| := by
  induction L generalizing m m' with
  | nil => simp [deductionChain, chainCoefficient]
  | cons l L ih =>
    simp only [deductionChain, chainCoefficient, List.map_cons, List.prod_cons]
    rw [ih, abs_deductionStep_sub]
    unfold chainCoefficient
    ring

theorem chainCoefficient_nonneg (L : List (ℝ × ℝ)) : 0 ≤ chainCoefficient L := by
  unfold chainCoefficient
  exact List.prod_nonneg fun x hx => by
    obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx
    exact abs_nonneg _

/-- Under a uniform bound `κ` on the step coefficients the chain contracts by `κ ^ length`. -/
theorem chainCoefficient_le_pow (L : List (ℝ × ℝ)) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hκ : ∀ l ∈ L, |l.1 - l.2| ≤ κ) : chainCoefficient L ≤ κ ^ L.length := by
  induction L with
  | nil => simp [chainCoefficient]
  | cons l L ih =>
    simp only [chainCoefficient, List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    have h1 := hκ l (List.mem_cons_self ..)
    have h2 := ih fun l' hl' => hκ l' (List.mem_cons_of_mem _ hl')
    unfold chainCoefficient at h2
    calc |l.1 - l.2| * (List.map (fun l => |l.1 - l.2|) L).prod
        ≤ κ * κ ^ L.length := by
          exact mul_le_mul h1 h2 (List.prod_nonneg fun x hx => by
            obtain ⟨l', _, rfl⟩ := List.mem_map.1 hx
            exact abs_nonneg _) hκ0
      _ = κ ^ L.length * κ := by ring

theorem abs_deductionChain_sub_le_pow (L : List (ℝ × ℝ)) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hκ : ∀ l ∈ L, |l.1 - l.2| ≤ κ) (m m' : ℝ) :
    |deductionChain L m - deductionChain L m'| ≤ κ ^ L.length * |m - m'| := by
  rw [abs_deductionChain_sub]
  exact mul_le_mul_of_nonneg_right (chainCoefficient_le_pow L κ hκ0 hκ) (abs_nonneg _)

/-- Inertness of long moderate chains: whatever the upstream strength in `[0,1]`, two runs of
the chain differ by at most `κ ^ length`.  With `κ < 1` the conclusion forgets its input as depth
grows. -/
theorem abs_deductionChain_sub_le_pow_of_mem_Icc (L : List (ℝ × ℝ)) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hκ : ∀ l ∈ L, |l.1 - l.2| ≤ κ) {m m' : ℝ} (hm : m ∈ Set.Icc (0 : ℝ) 1)
    (hm' : m' ∈ Set.Icc (0 : ℝ) 1) :
    |deductionChain L m - deductionChain L m'| ≤ κ ^ L.length := by
  have h := abs_deductionChain_sub_le_pow L κ hκ0 hκ m m'
  have hdiff : |m - m'| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hm.1, hm.2, hm'.1, hm'.2]
  calc |deductionChain L m - deductionChain L m'| ≤ κ ^ L.length * |m - m'| := h
    _ ≤ κ ^ L.length * 1 := mul_le_mul_of_nonneg_left hdiff (pow_nonneg hκ0 _)
    _ = κ ^ L.length := mul_one _

/-- Deterministic links pass upstream differences through unchanged: depth does not damp
anything when every link is certain. -/
theorem abs_deductionChain_sub_of_deterministic (L : List (ℝ × ℝ))
    (hL : ∀ l ∈ L, |l.1 - l.2| = 1) (m m' : ℝ) :
    |deductionChain L m - deductionChain L m'| = |m - m'| := by
  rw [abs_deductionChain_sub]
  have : chainCoefficient L = 1 := by
    unfold chainCoefficient
    rw [List.prod_eq_one]
    intro x hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact hL l hl
  rw [this, one_mul]

end Contraction

/-! ## Depth accumulation of implemented-versus-exact errors -/

section Accumulation

/-- Theorem 5.4 (depth accumulation) in the real-valued form: if the error after step `i+1`
is at most the step's own error `δ i` plus `L i` times the error before it, then after `T`
steps it is at most `∑ᵢ δᵢ ∏_{j > i} Lⱼ`. -/
theorem error_accumulation (δ L E : ℕ → ℝ) (hE0 : E 0 = 0) (hL : ∀ i, 0 ≤ L i)
    (hrec : ∀ i, E (i + 1) ≤ δ i + L i * E i) :
    ∀ T, E T ≤ ∑ i ∈ Finset.range T, δ i * ∏ j ∈ Finset.Ico (i + 1) T, L j := by
  intro T
  induction T with
  | zero => simp [hE0]
  | succ T ih =>
    have hstep := hrec T
    have hmul : L T * E T ≤ L T * ∑ i ∈ Finset.range T, δ i * ∏ j ∈ Finset.Ico (i + 1) T, L j :=
      mul_le_mul_of_nonneg_left ih (hL T)
    rw [Finset.sum_range_succ, Finset.mul_sum] at *
    have hprod : ∀ i ∈ Finset.range T,
        L T * (δ i * ∏ j ∈ Finset.Ico (i + 1) T, L j) =
        δ i * ∏ j ∈ Finset.Ico (i + 1) (T + 1), L j := by
      intro i hi
      have hi' : i + 1 ≤ T := Finset.mem_range.1 hi
      rw [Finset.prod_Ico_succ_top hi']
      ring
    rw [Finset.sum_congr rfl hprod] at hmul
    have hlast : δ T * ∏ j ∈ Finset.Ico (T + 1) (T + 1), L j = δ T := by
      rw [Finset.Ico_self, Finset.prod_empty, mul_one]
    rw [hlast]
    linarith

/-- Nonexpansive exact transports: errors add linearly in the depth. -/
theorem error_accumulation_of_nonexpansive (δ L E : ℕ → ℝ) (hE0 : E 0 = 0) (hδ : ∀ i, 0 ≤ δ i)
    (hL0 : ∀ i, 0 ≤ L i) (hL1 : ∀ i, L i ≤ 1)
    (hrec : ∀ i, E (i + 1) ≤ δ i + L i * E i) :
    ∀ T, E T ≤ ∑ i ∈ Finset.range T, δ i := by
  intro T
  refine le_trans (error_accumulation δ L E hE0 hL0 hrec T) (Finset.sum_le_sum fun i _ => ?_)
  have hprod : ∏ j ∈ Finset.Ico (i + 1) T, L j ≤ 1 :=
    Finset.prod_le_one (fun j _ => hL0 j) (fun j _ => hL1 j)
  calc δ i * ∏ j ∈ Finset.Ico (i + 1) T, L j ≤ δ i * 1 :=
        mul_le_mul_of_nonneg_left hprod (hδ i)
    _ = δ i := mul_one _

/-- Uniform contraction: the accumulated error saturates at `δ / (1 - κ)`, independent of the
depth. -/
theorem error_saturates (δ κ : ℝ) (E : ℕ → ℝ) (hE0 : E 0 = 0) (hδ : 0 ≤ δ) (hκ0 : 0 ≤ κ)
    (hκ1 : κ < 1) (hrec : ∀ i, E (i + 1) ≤ δ + κ * E i) :
    ∀ T, E T ≤ δ / (1 - κ) := by
  intro T
  induction T with
  | zero =>
    rw [hE0]
    exact div_nonneg hδ (by linarith)
  | succ T ih =>
    have h1 : 0 < 1 - κ := by linarith
    calc E (T + 1) ≤ δ + κ * E T := hrec T
      _ ≤ δ + κ * (δ / (1 - κ)) := by
          have := mul_le_mul_of_nonneg_left ih hκ0
          linarith
      _ = δ / (1 - κ) := by
          field_simp
          ring

end Accumulation

/-! ## Relative order of sibling conclusions -/

section Siblings

/-- Two conclusions computed from the same upstream strength `m` by links of equal strength
`pC - qC = pC' - qC'` keep their order for every value of `m`: a shared upstream error, however
large, cannot swap them. -/
theorem sibling_order_invariant_of_equal_links (pC qC pC' qC' m m' : ℝ)
    (h : pC - qC = pC' - qC') :
    deductionStep pC qC m < deductionStep pC' qC' m ↔
      deductionStep pC qC m' < deductionStep pC' qC' m' := by
  have hgap : ∀ t, deductionStep pC' qC' t - deductionStep pC qC t = qC' - qC := by
    intro t
    unfold deductionStep
    have : pC = pC' - qC' + qC := by linarith
    rw [this]
    ring
  constructor <;> intro hlt
  · have := hgap m
    have := hgap m'
    linarith
  · have := hgap m
    have := hgap m'
    linarith

/-- With links of unequal strength the order of two siblings survives an upstream error smaller
than their gap at the true strength divided by the difference of the link strengths. -/
theorem sibling_order_preserved_of_margin (pC qC pC' qC' m m' : ℝ)
    (hmargin : |m' - m| * |(pC' - qC') - (pC - qC)| <
      deductionStep pC' qC' m - deductionStep pC qC m) :
    deductionStep pC qC m' < deductionStep pC' qC' m' := by
  have hid : deductionStep pC' qC' m' - deductionStep pC qC m' =
      (deductionStep pC' qC' m - deductionStep pC qC m) +
        (m' - m) * ((pC' - qC') - (pC - qC)) := by
    unfold deductionStep
    ring
  have habs : -(|m' - m| * |(pC' - qC') - (pC - qC)|) ≤ (m' - m) * ((pC' - qC') - (pC - qC)) := by
    rw [← abs_mul]
    exact neg_abs_le _
  linarith

end Siblings

end Mettapedia.PLN.Comparisons.ChainLoss
