import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Premise-Selection Coverage Objective

This file formalizes a minimal set-function objective for premise selection:
dependency coverage of a selected premise set `S` against a ground-truth dependency
set `D`.

The main results are:

1. Monotonicity of coverage.
2. Diminishing returns (submodularity in marginal-gain form).
3. Tight cardinality bound `|S ∩ D| ≤ min(k, |D|)` for `|S| ≤ k`.
4. Existence of a set attaining this bound (hence exact cardinality-optimality for
   this surrogate objective).

This is the formal backbone for treating premise selection as a monotone submodular
coverage problem under a cardinality budget.
-/

namespace Mettapedia.Logic.PremiseSelection

open scoped Classical

variable {Fact : Type*} [DecidableEq Fact]

/-- Dependency coverage surrogate: number of selected premises that are true dependencies. -/
def dependencyCoverage (D S : Finset Fact) : Nat :=
  (S ∩ D).card

/-- Dependency recall surrogate. We define recall of the empty dependency set as `1`. -/
noncomputable def dependencyRecall (D S : Finset Fact) : ℝ :=
  if D.card = 0 then 1 else (dependencyCoverage D S : ℝ) / (D.card : ℝ)

/-- Marginal gain of adding one premise under the coverage objective. -/
def dependencyGain (D S : Finset Fact) (a : Fact) : Nat :=
  if a ∈ D ∧ a ∉ S then 1 else 0

/-- One-step greedy condition: pick a new item with maximal marginal gain. -/
def IsGreedyStep (D S : Finset Fact) (a : Fact) : Prop :=
  a ∉ S ∧ ∀ b, b ∉ S → dependencyGain D S b ≤ dependencyGain D S a

/-- Inductive greedy chain of selected sets. -/
inductive GreedyChain (D : Finset Fact) : Nat → Finset Fact → Prop
  | zero : GreedyChain D 0 ∅
  | succ {i : Nat} {S : Finset Fact} {a : Fact} :
      GreedyChain D i S → IsGreedyStep D S a → GreedyChain D (i + 1) (insert a S)

lemma dependencyCoverage_le_card_left (D S : Finset Fact) :
    dependencyCoverage D S ≤ S.card := by
  unfold dependencyCoverage
  exact Finset.card_le_card Finset.inter_subset_left

lemma dependencyCoverage_le_card_right (D S : Finset Fact) :
    dependencyCoverage D S ≤ D.card := by
  unfold dependencyCoverage
  exact Finset.card_le_card Finset.inter_subset_right

theorem dependencyCoverage_mono {D S T : Finset Fact} (hST : S ⊆ T) :
    dependencyCoverage D S ≤ dependencyCoverage D T := by
  unfold dependencyCoverage
  exact Finset.card_le_card (Finset.inter_subset_inter hST (subset_rfl))

theorem dependencyCoverage_insert
    (D S : Finset Fact) (a : Fact) :
    dependencyCoverage D (insert a S) =
      dependencyCoverage D S + dependencyGain D S a := by
  by_cases hS : a ∈ S
  · simp [dependencyCoverage, dependencyGain, hS]
  · by_cases hD : a ∈ D
    · have hnot : a ∉ S ∩ D := by simp [hS, hD]
      simp [dependencyCoverage, dependencyGain, hS, hD, hnot]
    · simp [dependencyCoverage, dependencyGain, hS, hD]

lemma dependencyGain_le_one (D S : Finset Fact) (a : Fact) :
    dependencyGain D S a ≤ 1 := by
  unfold dependencyGain
  split_ifs <;> simp

lemma dependencyGain_eq_one_of_mem
    {D S : Finset Fact} {a : Fact}
    (hD : a ∈ D) (hS : a ∉ S) :
    dependencyGain D S a = 1 := by
  simp [dependencyGain, hD, hS]

lemma dependencyGain_eq_zero_of_not_mem
    {D S : Finset Fact} {a : Fact}
    (hD : a ∉ D) :
    dependencyGain D S a = 0 := by
  simp [dependencyGain, hD]

lemma exists_uncovered_of_coverage_lt
    {D S : Finset Fact}
    (hcov : dependencyCoverage D S < D.card) :
    ∃ b, b ∈ D ∧ b ∉ S := by
  by_contra hnone
  have hsubset : D ⊆ S := by
    intro b hb
    by_contra hbs
    exact hnone ⟨b, hb, hbs⟩
  have hinter : S ∩ D = D := by
    apply Finset.Subset.antisymm
    · exact Finset.inter_subset_right
    · intro b hb
      exact by
        simpa [Finset.mem_inter] using And.intro (hsubset hb) hb
  have hcov_eq : dependencyCoverage D S = D.card := by
    simp [dependencyCoverage, hinter]
  have hnotlt : ¬ dependencyCoverage D S < D.card := by
    simp [hcov_eq]
  exact hnotlt hcov

lemma coverage_lt_of_exists_uncovered
    {D S : Finset Fact}
    (hmiss : ∃ b, b ∈ D ∧ b ∉ S) :
    dependencyCoverage D S < D.card := by
  rcases hmiss with ⟨b, hbD, hbS⟩
  have hsub : S ∩ D ⊆ D := Finset.inter_subset_right
  have hnotin : b ∉ S ∩ D := by simp [hbS]
  have hproper : S ∩ D ⊂ D := by
    refine ⟨hsub, ?_⟩
    intro hDS
    exact hnotin (hDS hbD)
  have hcardlt : (S ∩ D).card < D.card := Finset.card_lt_card hproper
  simpa [dependencyCoverage] using hcardlt

lemma greedy_step_gain_eq_one_of_room
    {D S : Finset Fact} {a : Fact}
    (hstep : IsGreedyStep D S a)
    (hcov_lt : dependencyCoverage D S < D.card) :
    dependencyGain D S a = 1 := by
  rcases exists_uncovered_of_coverage_lt (D := D) (S := S) hcov_lt with ⟨b, hbD, hbS⟩
  have hbg : dependencyGain D S b = 1 := dependencyGain_eq_one_of_mem hbD hbS
  have hle : dependencyGain D S b ≤ dependencyGain D S a := hstep.2 b hbS
  have hge : 1 ≤ dependencyGain D S a := by simpa [hbg] using hle
  exact Nat.le_antisymm (dependencyGain_le_one D S a) hge

lemma greedy_step_gain_eq_zero_of_full
    {D S : Finset Fact} {a : Fact}
    (hstep : IsGreedyStep D S a)
    (hcov_ge : D.card ≤ dependencyCoverage D S) :
    dependencyGain D S a = 0 := by
  have hcov_eq : dependencyCoverage D S = D.card :=
    Nat.le_antisymm (dependencyCoverage_le_card_right D S) hcov_ge
  have hno_uncovered : ¬ ∃ b, b ∈ D ∧ b ∉ S := by
    intro hmiss
    have hlt : dependencyCoverage D S < D.card :=
      coverage_lt_of_exists_uncovered (D := D) (S := S) hmiss
    have : ¬ dependencyCoverage D S < D.card := by simp [hcov_eq]
    exact this hlt
  have ha_not_mem_D : a ∉ D := by
    intro haD
    exact hno_uncovered ⟨a, haD, hstep.1⟩
  exact dependencyGain_eq_zero_of_not_mem ha_not_mem_D

/-- Diminishing returns for coverage gain (submodularity in gain form). -/
theorem dependencyGain_antitone_in_set
    {D S T : Finset Fact} {a : Fact} (hST : S ⊆ T) :
    dependencyGain D T a ≤ dependencyGain D S a := by
  by_cases hD : a ∈ D
  · by_cases hT : a ∈ T
    · simp [dependencyGain, hD, hT]
    · have hS : a ∉ S := by
        intro hs
        exact hT (hST hs)
      simp [dependencyGain, hD, hT, hS]
  · simp [dependencyGain, hD]

/-- Equivalent diminishing-returns form using coverage differences. -/
theorem dependencyCoverage_diminishing_returns
    {D S T : Finset Fact} {a : Fact} (hST : S ⊆ T) :
    dependencyCoverage D (insert a T) - dependencyCoverage D T ≤
      dependencyCoverage D (insert a S) - dependencyCoverage D S := by
  calc
    dependencyCoverage D (insert a T) - dependencyCoverage D T
        = dependencyGain D T a := by
            rw [dependencyCoverage_insert]
            simp
    _ ≤ dependencyGain D S a := dependencyGain_antitone_in_set (D := D) hST
    _ = dependencyCoverage D (insert a S) - dependencyCoverage D S := by
          rw [dependencyCoverage_insert]
          symm
          simp

theorem dependencyRecall_mono {D S T : Finset Fact}
    (hST : S ⊆ T) (hD : D.card ≠ 0) :
    dependencyRecall D S ≤ dependencyRecall D T := by
  unfold dependencyRecall
  simp [hD]
  refine div_le_div_of_nonneg_right ?num ?den
  · exact_mod_cast dependencyCoverage_mono (D := D) hST
  · positivity

/-- Any budget-`k` set has coverage at most `min(k, |D|)`. -/
theorem dependencyCoverage_le_min_of_card_le
    {D S : Finset Fact} {k : Nat} (hSk : S.card ≤ k) :
    dependencyCoverage D S ≤ Nat.min k D.card := by
  exact (Nat.le_min).2 ⟨
    le_trans (dependencyCoverage_le_card_left D S) hSk,
    dependencyCoverage_le_card_right D S
  ⟩

/-- There exists a budget-`k` set attaining the upper bound `min(k, |D|)`. -/
theorem exists_set_attaining_dependencyCoverage_min
    (D : Finset Fact) (k : Nat) :
    ∃ S : Finset Fact, S.card ≤ k ∧ dependencyCoverage D S = Nat.min k D.card := by
  by_cases hk : k ≤ D.card
  · obtain ⟨S, hSD, hcard⟩ := Finset.exists_subset_card_eq hk
    refine ⟨S, ?_, ?_⟩
    · simp [hcard]
    · have hinter : S ∩ D = S := Finset.inter_eq_left.mpr hSD
      simp [dependencyCoverage, hinter, hcard, Nat.min_eq_left hk]
  · have hlt : D.card < k := Nat.lt_of_not_ge hk
    refine ⟨D, le_of_lt hlt, ?_⟩
    simp [dependencyCoverage, Nat.min_eq_right (Nat.le_of_lt hlt)]

/-- Coverage achieved by a valid greedy chain: exact `min(i, |D|)` characterization. -/
theorem greedyChain_coverage_eq_min
    {D S : Finset Fact} {i : Nat}
    (hchain : GreedyChain D i S) :
    dependencyCoverage D S = Nat.min i D.card := by
  induction hchain with
  | zero =>
      simp [dependencyCoverage]
  | @succ i S a hprev hstep ih =>
      have hinsert :
          dependencyCoverage D (insert a S) =
            dependencyCoverage D S + dependencyGain D S a :=
        dependencyCoverage_insert D S a
      by_cases hlt : dependencyCoverage D S < D.card
      · have hgain : dependencyGain D S a = 1 :=
          greedy_step_gain_eq_one_of_room (D := D) hstep hlt
        have hi_lt : i < D.card := by
          by_contra hnot
          have hDi : D.card ≤ i := Nat.le_of_not_lt hnot
          have hmin_eq : Nat.min i D.card = D.card := Nat.min_eq_right hDi
          have hcov_eq_card : dependencyCoverage D S = D.card := by
            simpa [hmin_eq] using ih
          have : ¬ dependencyCoverage D S < D.card := by simp [hcov_eq_card]
          exact this hlt
        have hmin_i : Nat.min i D.card = i := Nat.min_eq_left (Nat.le_of_lt hi_lt)
        have hmin_succ : Nat.min (i + 1) D.card = i + 1 :=
          Nat.min_eq_left (Nat.succ_le_of_lt hi_lt)
        calc
          dependencyCoverage D (insert a S)
              = dependencyCoverage D S + dependencyGain D S a := hinsert
          _ = Nat.min i D.card + 1 := by simp [ih, hgain]
          _ = i + 1 := by simp [hmin_i]
          _ = Nat.min (i + 1) D.card := by symm; exact hmin_succ
      · have hfull : D.card ≤ dependencyCoverage D S := Nat.le_of_not_lt hlt
        have hgain0 : dependencyGain D S a = 0 :=
          greedy_step_gain_eq_zero_of_full (D := D) hstep hfull
        have hcov_eq_card : dependencyCoverage D S = D.card :=
          Nat.le_antisymm (dependencyCoverage_le_card_right D S) hfull
        have hDi : D.card ≤ i := by
          have hmin_eq : Nat.min i D.card = D.card := by simpa [hcov_eq_card] using ih
          by_contra hnot
          have hi_lt : i < D.card := Nat.lt_of_not_ge hnot
          have hmin_i : Nat.min i D.card = i := Nat.min_eq_left (Nat.le_of_lt hi_lt)
          have : D.card = i := by simpa [hmin_i] using hmin_eq.symm
          exact (Nat.lt_irrefl i) (this ▸ hi_lt)
        have hmin_succ : Nat.min (i + 1) D.card = D.card :=
          Nat.min_eq_right (le_trans hDi (Nat.le_succ i))
        calc
          dependencyCoverage D (insert a S)
              = dependencyCoverage D S + dependencyGain D S a := hinsert
          _ = D.card + 0 := by simp [hcov_eq_card, hgain0]
          _ = D.card := by simp
          _ = Nat.min (i + 1) D.card := by symm; exact hmin_succ

/-- Greedy-chain guarantee in the standard `(1 - e^{-1})` form. -/
theorem greedyChain_one_minus_exp_bound
    {D G : Finset Fact} {k : Nat}
    (hG : GreedyChain D k G) :
    (1 - Real.exp (-1)) * (Nat.min k D.card : ℝ) ≤ dependencyCoverage D G := by
  have hEq : dependencyCoverage D G = Nat.min k D.card :=
    greedyChain_coverage_eq_min (D := D) (S := G) (i := k) hG
  have hcoeff : (1 - Real.exp (-1)) ≤ (1 : ℝ) := by
    have hexp_nonneg : (0 : ℝ) ≤ Real.exp (-1) := by positivity
    linarith
  have hnonneg : 0 ≤ (Nat.min k D.card : ℝ) := by positivity
  have hmul : (1 - Real.exp (-1)) * (Nat.min k D.card : ℝ) ≤
      (1 : ℝ) * (Nat.min k D.card : ℝ) :=
    mul_le_mul_of_nonneg_right hcoeff hnonneg
  calc
    (1 - Real.exp (-1)) * (Nat.min k D.card : ℝ)
        ≤ (1 : ℝ) * (Nat.min k D.card : ℝ) := hmul
    _ = dependencyCoverage D G := by
          norm_num
          exact_mod_cast hEq.symm

/-- Stepwise-style geometric gap bound for any valid greedy chain under budget `k > 0`.
This states the classic contraction shape at ranking-surrogate level:
`gap_i ≤ OPT * (1 - 1/k)^i`, where `OPT = min(k, |D|)`. -/
theorem greedyChain_gap_geometric_bound
    {D S : Finset Fact} {i k : Nat}
    (hchain : GreedyChain D i S)
    (hk : 0 < k) :
    let opt := Nat.min k D.card
    ((opt - dependencyCoverage D S : Nat) : ℝ)
      ≤ (opt : ℝ) * (1 - (1 : ℝ) / (k : ℝ)) ^ i := by
  intro opt
  have hcov : dependencyCoverage D S = Nat.min i D.card :=
    greedyChain_coverage_eq_min (D := D) (S := S) (i := i) hchain
  have hopt_le_D : opt ≤ D.card := by
    dsimp [opt]
    exact Nat.min_le_right _ _
  have hmin_opt_le : Nat.min i opt ≤ Nat.min i D.card :=
    min_le_min_left _ hopt_le_D
  have hgap_nat : opt - Nat.min i D.card ≤ opt - Nat.min i opt := by
    exact Nat.sub_le_sub_left hmin_opt_le opt
  have hgap_cast :
      (((opt - dependencyCoverage D S : Nat) : ℝ))
        ≤ (((opt - Nat.min i opt : Nat) : ℝ)) := by
    have hnat : opt - dependencyCoverage D S ≤ opt - Nat.min i opt := by
      simpa [hcov] using hgap_nat
    exact_mod_cast hnat
  have hkR_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkR_ne : (k : ℝ) ≠ 0 := ne_of_gt hkR_pos
  have hopt_nonneg : 0 ≤ (opt : ℝ) := by positivity
  have hbase_nonneg : 0 ≤ (1 - (1 : ℝ) / (k : ℝ)) := by
    have hdiv_le : (1 : ℝ) / (k : ℝ) ≤ 1 := by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt hk)
      have h1_le_k_over_k : (1 : ℝ) / (k : ℝ) ≤ (k : ℝ) / (k : ℝ) := by
        exact div_le_div_of_nonneg_right hk1 (by positivity)
      simpa [hkR_ne] using h1_le_k_over_k
    linarith
  have htarget :
      (((opt - Nat.min i opt : Nat) : ℝ))
        ≤ (opt : ℝ) * (1 - (1 : ℝ) / (k : ℝ)) ^ i := by
    by_cases hi : i ≤ opt
    · have hmin_i_opt : Nat.min i opt = i := Nat.min_eq_left hi
      have hleft :
          ((opt - Nat.min i opt : Nat) : ℝ) = (opt : ℝ) - (i : ℝ) := by
        simpa [hmin_i_opt] using (Nat.cast_sub hi : ((opt - i : Nat) : ℝ) = (opt : ℝ) - (i : ℝ))
      have hopt_le_k : opt ≤ k := by
        dsimp [opt]
        exact Nat.min_le_left _ _
      have hfrac_opt_le_one : (opt : ℝ) / (k : ℝ) ≤ 1 := by
        have hoptR_le_kR : (opt : ℝ) ≤ (k : ℝ) := by exact_mod_cast hopt_le_k
        have hopt_over_k_le : (opt : ℝ) / (k : ℝ) ≤ (k : ℝ) / (k : ℝ) := by
          exact div_le_div_of_nonneg_right hoptR_le_kR (by positivity)
        simpa [hkR_ne] using hopt_over_k_le
      have hi_nonneg : 0 ≤ (i : ℝ) := by positivity
      have hmul_div :
          ((opt : ℝ) / (k : ℝ)) * (i : ℝ) ≤ (1 : ℝ) * (i : ℝ) :=
        mul_le_mul_of_nonneg_right hfrac_opt_le_one hi_nonneg
      have hlin :
          (opt : ℝ) - (i : ℝ)
            ≤ (opt : ℝ) - (((opt : ℝ) / (k : ℝ)) * (i : ℝ)) := by
        linarith
      have hber :
          (1 : ℝ) - (i : ℝ) / (k : ℝ)
            ≤ (1 - (1 : ℝ) / (k : ℝ)) ^ i := by
        have hbase_ge_neg_one : (-1 : ℝ) ≤ (1 - (1 : ℝ) / (k : ℝ)) := by
          linarith [hbase_nonneg]
        have hraw := one_add_mul_sub_le_pow (a := (1 - (1 : ℝ) / (k : ℝ))) hbase_ge_neg_one i
        have hrewrite :
            1 + (i : ℝ) * ((1 - (1 : ℝ) / (k : ℝ)) - 1)
              = (1 : ℝ) - (i : ℝ) / (k : ℝ) := by ring
        simpa [hrewrite] using hraw
      have hmul_ber :
          (opt : ℝ) * ((1 : ℝ) - (i : ℝ) / (k : ℝ))
            ≤ (opt : ℝ) * (1 - (1 : ℝ) / (k : ℝ)) ^ i :=
        mul_le_mul_of_nonneg_left hber hopt_nonneg
      have hrewrite_mul :
          (opt : ℝ) * ((1 : ℝ) - (i : ℝ) / (k : ℝ))
            = (opt : ℝ) - (((opt : ℝ) / (k : ℝ)) * (i : ℝ)) := by ring
      calc
        ((opt - Nat.min i opt : Nat) : ℝ)
            = (opt : ℝ) - (i : ℝ) := hleft
        _ ≤ (opt : ℝ) - (((opt : ℝ) / (k : ℝ)) * (i : ℝ)) := hlin
        _ = (opt : ℝ) * ((1 : ℝ) - (i : ℝ) / (k : ℝ)) := hrewrite_mul.symm
        _ ≤ (opt : ℝ) * (1 - (1 : ℝ) / (k : ℝ)) ^ i := hmul_ber
    · have hopt_lt_i : opt < i := Nat.lt_of_not_ge hi
      have hmin_i_opt : Nat.min i opt = opt := Nat.min_eq_right (Nat.le_of_lt hopt_lt_i)
      have hpow_nonneg : 0 ≤ (1 - (1 : ℝ) / (k : ℝ)) ^ i := pow_nonneg hbase_nonneg i
      calc
        ((opt - Nat.min i opt : Nat) : ℝ)
            = (0 : ℝ) := by simp [hmin_i_opt]
        _ ≤ (opt : ℝ) * (1 - (1 : ℝ) / (k : ℝ)) ^ i := by
              exact mul_nonneg hopt_nonneg hpow_nonneg
  exact le_trans hgap_cast htarget

/-- Standard greedy-progress shape under budget horizon `i ≤ k`:
`coverage_i ≥ OPT * (1 - (1 - 1/k)^i)` for `OPT = min(k, |D|)`. -/
theorem greedyChain_coverage_ge_fractional_opt
    {D S : Finset Fact} {i k : Nat}
    (hchain : GreedyChain D i S)
    (hk : 0 < k)
    (hi : i ≤ k) :
    let opt := Nat.min k D.card
    (opt : ℝ) * (1 - (1 - (1 : ℝ) / (k : ℝ)) ^ i) ≤ dependencyCoverage D S := by
  intro opt
  have hgap :
      (((opt - dependencyCoverage D S : Nat) : ℝ))
        ≤ (opt : ℝ) * (1 - (1 : ℝ) / (k : ℝ)) ^ i :=
    greedyChain_gap_geometric_bound (D := D) (S := S) (i := i) (k := k) hchain hk
  have hcov_eq : dependencyCoverage D S = Nat.min i D.card :=
    greedyChain_coverage_eq_min (D := D) (S := S) (i := i) hchain
  have hcov_le_opt : dependencyCoverage D S ≤ opt := by
    have hmin_le : Nat.min i D.card ≤ Nat.min k D.card := min_le_min_right _ hi
    simpa [opt, hcov_eq] using hmin_le
  have hgap_real :
      (opt : ℝ) - (dependencyCoverage D S : ℝ)
        ≤ (opt : ℝ) * (1 - (1 : ℝ) / (k : ℝ)) ^ i := by
    simpa [Nat.cast_sub hcov_le_opt] using hgap
  have htarget :
      (opt : ℝ) * (1 - (1 - (1 : ℝ) / (k : ℝ)) ^ i)
        = (opt : ℝ) - (opt : ℝ) * (1 - (1 : ℝ) / (k : ℝ)) ^ i := by
    ring
  calc
    (opt : ℝ) * (1 - (1 - (1 : ℝ) / (k : ℝ)) ^ i)
        = (opt : ℝ) - (opt : ℝ) * (1 - (1 : ℝ) / (k : ℝ)) ^ i := htarget
    _ ≤ dependencyCoverage D S := by
          linarith [hgap_real]

/-- Nontrivial `(1 - e^{-1})` lower bound derived from the geometric greedy-progress bound
and `Real.one_sub_div_pow_le_exp_neg`. -/
theorem greedyChain_one_minus_exp_bound_sharp
    {D G : Finset Fact} {k : Nat}
    (hG : GreedyChain D k G)
    (hk : 0 < k) :
    (1 - Real.exp (-1)) * (Nat.min k D.card : ℝ) ≤ dependencyCoverage D G := by
  let opt := Nat.min k D.card
  have hfrac :
      (opt : ℝ) * (1 - (1 - (1 : ℝ) / (k : ℝ)) ^ k) ≤ dependencyCoverage D G := by
    simpa [opt] using
      (greedyChain_coverage_ge_fractional_opt
        (D := D) (S := G) (i := k) (k := k) hG hk (le_rfl))
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hk)
  have hpow :
      (1 - (1 : ℝ) / (k : ℝ)) ^ k ≤ Real.exp (-1) := by
    simpa using (Real.one_sub_div_pow_le_exp_neg (n := k) (t := (1 : ℝ)) hkR)
  have hcoeff :
      (1 - Real.exp (-1)) ≤ (1 - (1 - (1 : ℝ) / (k : ℝ)) ^ k) := by
    linarith
  have hopt_nonneg : 0 ≤ (opt : ℝ) := by positivity
  have hmul :
      (1 - Real.exp (-1)) * (opt : ℝ) ≤
        (opt : ℝ) * (1 - (1 - (1 : ℝ) / (k : ℝ)) ^ k) := by
    have htmp :
        (1 - Real.exp (-1)) * (opt : ℝ) ≤
          (1 - (1 - (1 : ℝ) / (k : ℝ)) ^ k) * (opt : ℝ) :=
      mul_le_mul_of_nonneg_right hcoeff hopt_nonneg
    simpa [mul_comm, mul_left_comm, mul_assoc] using htmp
  simpa [opt] using le_trans hmul hfrac

/-- One-step greedy contraction at the surrogate-gap level:
`gap_{i+1} ≤ (1 - 1/k) * gap_i`, with `gap_i = OPT - c_i` and `OPT = min(k, |D|)`. -/
theorem greedyChain_step_contraction
    {D S : Finset Fact} {i k : Nat} {a : Fact}
    (hchain : GreedyChain D i S)
    (hstep : IsGreedyStep D S a)
    (hk : 0 < k) :
    let opt := Nat.min k D.card
    ((opt - dependencyCoverage D (insert a S) : Nat) : ℝ) ≤
      (1 - (1 : ℝ) / (k : ℝ)) * ((opt - dependencyCoverage D S : Nat) : ℝ) := by
  intro opt
  have hcovS : dependencyCoverage D S = Nat.min i D.card :=
    greedyChain_coverage_eq_min (D := D) (S := S) (i := i) hchain
  have hcovNext : dependencyCoverage D (insert a S) = Nat.min (i + 1) D.card :=
    greedyChain_coverage_eq_min
      (D := D) (S := insert a S) (i := i + 1)
      (GreedyChain.succ hchain hstep)
  have hopt_le_D : opt ≤ D.card := by
    dsimp [opt]
    exact Nat.min_le_right _ _
  have hopt_le_k : opt ≤ k := by
    dsimp [opt]
    exact Nat.min_le_left _ _
  have hkR_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkR_ne : (k : ℝ) ≠ 0 := ne_of_gt hkR_pos
  by_cases hi : i < opt
  · have hi_le_opt : i ≤ opt := Nat.le_of_lt hi
    have hiD : i < D.card := lt_of_lt_of_le hi hopt_le_D
    have hmin_i_D : Nat.min i D.card = i := Nat.min_eq_left (Nat.le_of_lt hiD)
    have hmin_succ_D : Nat.min (i + 1) D.card = i + 1 :=
      Nat.min_eq_left (Nat.succ_le_of_lt hiD)
    have hsucc_le_opt : i + 1 ≤ opt := Nat.succ_le_of_lt hi
    have hleft :
        ((opt - dependencyCoverage D (insert a S) : Nat) : ℝ)
          = (opt : ℝ) - (i + 1 : ℝ) := by
      calc
        ((opt - dependencyCoverage D (insert a S) : Nat) : ℝ)
            = ((opt - Nat.min (i + 1) D.card : Nat) : ℝ) := by simp [hcovNext]
        _ = ((opt - (i + 1) : Nat) : ℝ) := by simp [hmin_succ_D]
        _ = (opt : ℝ) - (i + 1 : ℝ) := by
              have hcast :
                  ((opt - (i + 1) : Nat) : ℝ) = (opt : ℝ) - ((i + 1 : Nat) : ℝ) :=
                Nat.cast_sub hsucc_le_opt
              simpa [Nat.cast_add, Nat.cast_one] using hcast
    have hright_gap :
        ((opt - dependencyCoverage D S : Nat) : ℝ) = (opt : ℝ) - (i : ℝ) := by
      calc
        ((opt - dependencyCoverage D S : Nat) : ℝ)
            = ((opt - Nat.min i D.card : Nat) : ℝ) := by simp [hcovS]
        _ = ((opt - i : Nat) : ℝ) := by simp [hmin_i_D]
        _ = (opt : ℝ) - (i : ℝ) := by exact Nat.cast_sub hi_le_opt
    set g : ℝ := ((opt - dependencyCoverage D S : Nat) : ℝ)
    have hg_nonneg : 0 ≤ g := by
      dsimp [g]
      positivity
    have hgap_nat_le_k : opt - dependencyCoverage D S ≤ k := by
      calc
        opt - dependencyCoverage D S
            ≤ opt := Nat.sub_le _ _
        _ ≤ k := hopt_le_k
    have hg_le_k : g ≤ (k : ℝ) := by
      dsimp [g]
      exact_mod_cast hgap_nat_le_k
    have hg_over_k_le_one : g / (k : ℝ) ≤ 1 := by
      have hg_over_k_le : g / (k : ℝ) ≤ (k : ℝ) / (k : ℝ) := by
        exact div_le_div_of_nonneg_right hg_le_k (by positivity)
      simpa [hkR_ne] using hg_over_k_le
    have hlin :
        g - 1 ≤ g - g / (k : ℝ) := by
      linarith
    calc
      ((opt - dependencyCoverage D (insert a S) : Nat) : ℝ)
          = (opt : ℝ) - (i + 1 : ℝ) := hleft
      _ = ((opt : ℝ) - (i : ℝ)) - 1 := by ring
      _ = g - 1 := by simp [g, hright_gap]
      _ ≤ g - g / (k : ℝ) := hlin
      _ = (1 - (1 : ℝ) / (k : ℝ)) * g := by ring
      _ = (1 - (1 : ℝ) / (k : ℝ)) * ((opt - dependencyCoverage D S : Nat) : ℝ) := by
            simp [g]
  · have hopt_le_i : opt ≤ i := Nat.le_of_not_lt hi
    have hopt_le_min_i_D : opt ≤ Nat.min i D.card := (Nat.le_min).2 ⟨hopt_le_i, hopt_le_D⟩
    have hopt_le_min_succ_D : opt ≤ Nat.min (i + 1) D.card :=
      (Nat.le_min).2 ⟨le_trans hopt_le_i (Nat.le_succ i), hopt_le_D⟩
    have hgapS_zero : opt - dependencyCoverage D S = 0 := by
      rw [hcovS]
      exact Nat.sub_eq_zero_of_le hopt_le_min_i_D
    have hgapNext_zero : opt - dependencyCoverage D (insert a S) = 0 := by
      rw [hcovNext]
      exact Nat.sub_eq_zero_of_le hopt_le_min_succ_D
    have hRHS_zero :
        (1 - (1 : ℝ) / (k : ℝ)) * ((opt - dependencyCoverage D S : Nat) : ℝ) = 0 := by
      simp [hgapS_zero]
    have hRHS_nonneg :
        0 ≤ (1 - (1 : ℝ) / (k : ℝ)) * ((opt - dependencyCoverage D S : Nat) : ℝ) := by
      exact le_of_eq hRHS_zero.symm
    calc
      ((opt - dependencyCoverage D (insert a S) : Nat) : ℝ)
          = 0 := by simp [hgapNext_zero]
      _ ≤ (1 - (1 : ℝ) / (k : ℝ)) * ((opt - dependencyCoverage D S : Nat) : ℝ) := by
            exact hRHS_nonneg

end Mettapedia.Logic.PremiseSelection
