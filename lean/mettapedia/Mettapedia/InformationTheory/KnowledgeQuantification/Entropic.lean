import Mettapedia.InformationTheory.KnowledgeQuantification.Basic
import Mettapedia.InformationTheory.ShannonEntropy.Properties
import Mettapedia.ProbabilityTheory.BayesianInference.InformationLaws

/-!
# Knowledge of a finite explanatory system

The information budget of `Basic` computed from finite distributions with the tree's own
entropy (`shannonEntropyFin`), divergence (`klSum`), mutual information (`mutualInfo`) and
Bayesian information gain (`expectedInformationGain`).  A finite system has an input law
on `X`, the theory's kernel from input to explanandum `Y`, the numbers of explananda and
inputs, and the theory's description length (D. Fanelli, *A theory and methodology to
quantify knowledge*, R. Soc. open sci. 6: 181055, 2019).

Information identities, in the tree's terms:

* `shannonEntropyFin_observationLaw`: the entropy of a mixture is the mean entropy of its
  components plus their mean divergence from the mixture (eq. 3.17);
* `expectedInformationGain_eq_sum_klSum`: the information gain is the mean divergence of
  the kernel rows from their mixture;
* `expectedInformationGain_eq_entropy_sub_conditionalEntropy`: the information gain is
  `H(Y) − H(Y | X)` (eq. 2.9), alongside the tree's `H(X) − H(X | Y)`
  (`expectedInformationGain_eq_entropy_sub`);
* `expectedInformationGain_le_entropy_input`, `..._le_entropy_explanandum`: it is at most
  either entropy;
* `neg_sum_mul_log_eq_entropy_add_klSum`: coding with a model costs the entropy plus the
  divergence (appendix C).

Bridges to `K`:

* `FiniteSystem.budget_explained_eq_mutualInfo`: the explained information is `n_Y` times the
  mutual information of input and explanandum;
* `FiniteSystem.knowledge_mem_Ico`: the range `[0, 1)`;
* `FiniteSystem.knowledge_le_half`: when every explained use needs its own measurement,
  `K ≤ 1/2` (the limit of eq. 2.17, proved for every finite system);
* `FiniteSystem.knowledge_eq_zero_of_const`: a kernel that ignores the input explains
  nothing;
* `FiniteSystem.predictiveKnowledge_le`: prediction with a fixed model never beats
  explanation (eq. 2.26).

Null and negative results (§3.5):

* `eliminationGain`: ruling out one of `n` equally likely hypotheses gains
  `log (n / (n − 1))`, one bit for two hypotheses, vanishing as `n` grows (eq. 3.23).

`Hypotheses` reads this gain as Bayesian conditioning and corrects two supporting claims of
the paper (appendices G and H).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.InformationTheory.KnowledgeQuantification

open Finset Real Filter Topology
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.ProbabilityTheory.BayesianInference

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-! ## Entropy, conditional entropy and divergence -/

theorem prob_le_one (p : Prob Y) (y : Y) : p.1 y ≤ 1 := by
  calc p.1 y ≤ ∑ y', p.1 y' :=
        Finset.single_le_sum (fun y' _ => p.2.1 y') (Finset.mem_univ y)
    _ = 1 := p.2.2

theorem shannonEntropyFin_nonneg (p : Prob Y) : 0 ≤ shannonEntropyFin Y p :=
  Finset.sum_nonneg fun y _ => negMulLog_nonneg (p.2.1 y) (prob_le_one p y)

/-- Conditional entropy `H(Y | X) = Σ_x p(x) H(Y | X = x)` of a kernel under an input law: the
conditional term of the chain rule `shannonEntropyFin_comp`. -/
def conditionalEntropy (law : Prob X) (kernel : X → Prob Y) : ℝ :=
  ∑ x, law.1 x * shannonEntropyFin Y (kernel x)

theorem conditionalEntropy_nonneg (law : Prob X) (kernel : X → Prob Y) :
    0 ≤ conditionalEntropy law kernel :=
  Finset.sum_nonneg fun x _ => mul_nonneg (law.2.1 x) (shannonEntropyFin_nonneg _)

theorem observationLaw_apply_eq_sum (law : Prob X) (kernel : X → Prob Y) (y : Y) :
    (observationLaw law kernel).1 y = ∑ x, law.1 x * (kernel x).1 y := rfl

theorem le_observationLaw_apply (law : Prob X) (kernel : X → Prob Y) (x : X) (y : Y) :
    law.1 x * (kernel x).1 y ≤ (observationLaw law kernel).1 y := by
  rw [observationLaw_apply_eq_sum]
  exact Finset.single_le_sum (f := fun x' => law.1 x' * (kernel x').1 y)
    (fun x' _ => mul_nonneg (law.2.1 x') ((kernel x').2.1 y)) (Finset.mem_univ x)

/-- **The entropy of a mixture** (eq. 3.17): the mean entropy of the components plus their
mean divergence from the mixture. -/
theorem shannonEntropyFin_observationLaw (law : Prob X) (kernel : X → Prob Y) :
    shannonEntropyFin Y (observationLaw law kernel) =
      conditionalEntropy law kernel +
        ∑ x, law.1 x * klSum (kernel x).1 (observationLaw law kernel).1 := by
  set m := (observationLaw law kernel).1 with hmdef
  have hterm : ∀ x y, law.1 x * (negMulLog ((kernel x).1 y) +
      (kernel x).1 y * Real.log ((kernel x).1 y / m y)) =
        -(law.1 x * (kernel x).1 y) * Real.log (m y) := by
    intro x y
    rcases ((kernel x).2.1 y).lt_or_eq with hk | hk
    · rcases (law.2.1 x).lt_or_eq with hw | hw
      · have hmpos : 0 < m y :=
          lt_of_lt_of_le (mul_pos hw hk) (le_observationLaw_apply law kernel x y)
        rw [Real.log_div hk.ne' hmpos.ne', Real.negMulLog]
        ring
      · rw [← hw]
        ring
    · rw [← hk]
      simp
  unfold shannonEntropyFin conditionalEntropy
  simp only [klSum_eq_sum]
  symm
  calc ∑ x, law.1 x * ∑ y, negMulLog ((kernel x).1 y) +
        ∑ x, law.1 x * ∑ y, (kernel x).1 y * Real.log ((kernel x).1 y / m y)
      = ∑ x, ∑ y, law.1 x * (negMulLog ((kernel x).1 y) +
          (kernel x).1 y * Real.log ((kernel x).1 y / m y)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum]
    _ = ∑ x, ∑ y, -(law.1 x * (kernel x).1 y) * Real.log (m y) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hterm x y
    _ = ∑ y, negMulLog (m y) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.sum_mul, Finset.sum_neg_distrib, ← observationLaw_apply_eq_sum, Real.negMulLog]

/-- **Information gain is the mean divergence of the kernel rows from their mixture.** -/
theorem expectedInformationGain_eq_sum_klSum (law : Prob X) (kernel : X → Prob Y) :
    expectedInformationGain law kernel =
      ∑ x, law.1 x * klSum (kernel x).1 (observationLaw law kernel).1 := by
  unfold expectedInformationGain
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [klSum_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  unfold conditionalMass
  rw [joint_apply]
  rcases (law.2.1 x).lt_or_eq with hw | hw
  · rcases ((kernel x).2.1 y).lt_or_eq with hk | hk
    · rw [mul_div_assoc, mul_div_cancel_left₀ _ hw.ne']
      ring
    · rw [← hk]
      simp
  · rw [← hw]
    simp

/-- **Information gain is `H(Y) − H(Y | X)`** (eq. 2.9), with the kernel's output as
explanandum. -/
theorem expectedInformationGain_eq_entropy_sub_conditionalEntropy (law : Prob X)
    (kernel : X → Prob Y) :
    expectedInformationGain law kernel =
      shannonEntropyFin Y (observationLaw law kernel) - conditionalEntropy law kernel := by
  rw [shannonEntropyFin_observationLaw, expectedInformationGain_eq_sum_klSum]
  ring

/-- The tree's posterior entropy `H(X | Y)` is nonnegative. -/
theorem expectedPosteriorEntropy_nonneg (law : Prob X) (kernel : X → Prob Y) :
    0 ≤ expectedPosteriorEntropy law kernel := by
  unfold expectedPosteriorEntropy
  rw [neg_nonneg]
  refine Finset.sum_nonpos fun y _ => Finset.sum_nonpos fun x _ => ?_
  refine mul_nonpos_of_nonneg_of_nonpos ((joint law kernel).2.1 (x, y)) ?_
  unfold conditionalMass
  refine Real.log_nonpos
    (div_nonneg ((joint law kernel).2.1 (x, y)) ((observationLaw law kernel).2.1 y)) ?_
  rcases ((observationLaw law kernel).2.1 y).lt_or_eq with hpos | hz
  · rw [div_le_one hpos, joint_apply]
    exact le_observationLaw_apply law kernel x y
  · rw [← hz, div_zero]
    norm_num

theorem expectedInformationGain_le_entropy_input (law : Prob X) (kernel : X → Prob Y) :
    expectedInformationGain law kernel ≤ shannonEntropyFin X law := by
  rw [expectedInformationGain_eq_entropy_sub]
  linarith [expectedPosteriorEntropy_nonneg law kernel]

theorem expectedInformationGain_le_entropy_explanandum (law : Prob X) (kernel : X → Prob Y) :
    expectedInformationGain law kernel ≤ shannonEntropyFin Y (observationLaw law kernel) := by
  rw [expectedInformationGain_eq_entropy_sub_conditionalEntropy]
  linarith [conditionalEntropy_nonneg law kernel]

theorem conditionalEntropy_le_entropy (law : Prob X) (kernel : X → Prob Y) :
    conditionalEntropy law kernel ≤ shannonEntropyFin Y (observationLaw law kernel) := by
  have hgain : 0 ≤ expectedInformationGain law kernel := by
    classical
    exact expectedInformationGain_nonneg law kernel
  rw [expectedInformationGain_eq_entropy_sub_conditionalEntropy] at hgain
  linarith

/-- **Cross-entropy** (appendix C): coding with `q` while the law is `p` costs the entropy of
`p` plus the divergence. -/
theorem neg_sum_mul_log_eq_entropy_add_klSum (p q : Prob Y)
    (hac : ∀ y, 0 < p.1 y → 0 < q.1 y) :
    -∑ y, p.1 y * Real.log (q.1 y) = shannonEntropyFin Y p + klSum p.1 q.1 := by
  unfold shannonEntropyFin
  rw [klSum_eq_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rcases (p.2.1 y).lt_or_eq with hp | hp
  · rw [Real.log_div hp.ne' (hac y hp).ne', Real.negMulLog]
    ring
  · rw [← hp]
    simp

/-! ## Finite explanatory systems -/

/-- A finite explanatory system: the input law, the theory's kernel from input to
explanandum, the numbers of explananda and inputs, and the theory's description length. -/
structure FiniteSystem (X Y : Type*) [Fintype X] [Fintype Y] where
  inputLaw : Prob X
  kernel : X → Prob Y
  explananda : ℝ
  inputs : ℝ
  theoryLength : ℝ

namespace FiniteSystem

variable (s : FiniteSystem X Y)

/-- The law of the explanandum. -/
def explanandumLaw : Prob Y := observationLaw s.inputLaw s.kernel

/-- The information budget of the system: `n_Y H(Y)`, `n_Y H(Y | X)`, `n_X H(X)` and the
theory length. -/
def budget : Budget :=
  ⟨s.explananda * shannonEntropyFin Y s.explanandumLaw,
    s.explananda * conditionalEntropy s.inputLaw s.kernel,
    s.inputs * shannonEntropyFin X s.inputLaw,
    s.theoryLength⟩

/-- Fanelli's `K` of the system. -/
def knowledge : ℝ := s.budget.knowledge

/-- The explained information is `n_Y` times the information gain. -/
theorem budget_explained :
    s.budget.explained = s.explananda * expectedInformationGain s.inputLaw s.kernel := by
  unfold Budget.explained budget explanandumLaw
  dsimp only
  rw [expectedInformationGain_eq_entropy_sub_conditionalEntropy]
  ring

/-- **The numerator of `K` is `n_Y I(X; Y)`**, the tree's mutual information of the joint law
of input and explanandum. -/
theorem budget_explained_eq_mutualInfo [DecidableEq X] [DecidableEq Y] :
    s.budget.explained =
      s.explananda * mutualInfo (joint s.inputLaw s.kernel).1 Prod.fst Prod.snd := by
  rw [budget_explained, expectedInformationGain_eq_mutualInfo]

theorem budget_admissible (hY : 0 < s.explananda) (hX : 0 ≤ s.inputs)
    (hL : 0 ≤ s.theoryLength) (hH : 0 < shannonEntropyFin Y s.explanandumLaw) :
    s.budget.Admissible where
  explanandum_pos := mul_pos hY hH
  residual_nonneg := mul_nonneg hY.le (conditionalEntropy_nonneg _ _)
  residual_le := mul_le_mul_of_nonneg_left (conditionalEntropy_le_entropy _ _) hY.le
  input_nonneg := mul_nonneg hX (shannonEntropyFin_nonneg _)
  theory_nonneg := hL

/-- The range `[0, 1)` for a theory of positive length. -/
theorem knowledge_mem_Ico (hY : 0 < s.explananda) (hX : 0 ≤ s.inputs)
    (hL : 0 < s.theoryLength) (hH : 0 < shannonEntropyFin Y s.explanandumLaw) :
    s.knowledge ∈ Set.Ico 0 1 :=
  (s.budget_admissible hY hX hL.le hH).knowledge_mem_Ico hL

/-- **Direct measurement bounds knowledge by one half** (eq. 2.17).  When every explained use
needs its own measurement, `n_Y ≤ n_X`, the explained information, a mutual information,
cannot exceed the input information, so `K ≤ 1/2`. -/
theorem knowledge_le_half (hY : 0 < s.explananda) (huses : s.explananda ≤ s.inputs)
    (hL : 0 ≤ s.theoryLength) (hH : 0 < shannonEntropyFin Y s.explanandumLaw) :
    s.knowledge ≤ 1 / 2 := by
  refine (s.budget_admissible hY (hY.le.trans huses) hL hH).knowledge_le_half ?_
  rw [budget_explained]
  unfold budget
  dsimp only
  calc s.explananda * expectedInformationGain s.inputLaw s.kernel
      ≤ s.explananda * shannonEntropyFin X s.inputLaw :=
        mul_le_mul_of_nonneg_left (expectedInformationGain_le_entropy_input _ _) hY.le
    _ ≤ s.inputs * shannonEntropyFin X s.inputLaw :=
        mul_le_mul_of_nonneg_right huses (shannonEntropyFin_nonneg _)

/-- A kernel that ignores the input explains nothing. -/
theorem knowledge_eq_zero_of_const (obs : Prob Y) (hconst : s.kernel = fun _ => obs) :
    s.knowledge = 0 := by
  unfold knowledge Budget.knowledge
  rw [budget_explained, hconst, expectedInformationGain_const, mul_zero, zero_div]

/-! ## Prediction -/

/-- The residual of a fixed predictive model: the conditional cross-entropy of the
explanandum under the model. -/
def predictiveResidual (model : X → Prob Y) : ℝ :=
  ∑ x, s.inputLaw.1 x * -∑ y, (s.kernel x).1 y * Real.log ((model x).1 y)

/-- The divergence of the model from the kernel, averaged over the input. -/
def modelDivergence (model : X → Prob Y) : ℝ :=
  ∑ x, s.inputLaw.1 x * klSum (s.kernel x).1 (model x).1

theorem predictiveResidual_eq (model : X → Prob Y)
    (hac : ∀ x y, 0 < (s.kernel x).1 y → 0 < (model x).1 y) :
    s.predictiveResidual model =
      conditionalEntropy s.inputLaw s.kernel + s.modelDivergence model := by
  unfold predictiveResidual modelDivergence conditionalEntropy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [neg_sum_mul_log_eq_entropy_add_klSum _ _ (hac x), mul_add]

theorem modelDivergence_nonneg (model : X → Prob Y)
    (hac : ∀ x y, 0 < (s.kernel x).1 y → 0 < (model x).1 y) :
    0 ≤ s.modelDivergence model := by
  refine Finset.sum_nonneg fun x _ => mul_nonneg (s.inputLaw.2.1 x) ?_
  refine klSumOn_nonneg _ _ _ (fun y _ => (s.kernel x).2.1 y) (fun y _ => (model x).2.1 y)
    (fun y _ => hac x y) ?_
  rw [(model x).2.2, (s.kernel x).2.2]

/-- **Predictive knowledge** (eq. 2.26): `K` with the model's cross-entropy as residual is
`adjustedKnowledge` with the model's divergence. -/
theorem predictive_eq_adjustedKnowledge (model : X → Prob Y)
    (hac : ∀ x y, 0 < (s.kernel x).1 y → 0 < (model x).1 y) :
    (s.explananda * shannonEntropyFin Y s.explanandumLaw -
        s.explananda * s.predictiveResidual model) / s.budget.total =
      s.budget.adjustedKnowledge (s.explananda * s.modelDivergence model) := by
  unfold Budget.adjustedKnowledge Budget.explained
  rw [s.predictiveResidual_eq model hac]
  unfold budget
  dsimp only
  ring_nf

/-- Prediction with a fixed model never yields more knowledge than explanation. -/
theorem predictiveKnowledge_le (model : X → Prob Y)
    (hac : ∀ x y, 0 < (s.kernel x).1 y → 0 < (model x).1 y) (hY : 0 ≤ s.explananda)
    (htot : 0 < s.budget.total) :
    (s.explananda * shannonEntropyFin Y s.explanandumLaw -
        s.explananda * s.predictiveResidual model) / s.budget.total ≤ s.knowledge := by
  rw [s.predictive_eq_adjustedKnowledge model hac]
  exact s.budget.adjustedKnowledge_le htot (mul_nonneg hY (s.modelDivergence_nonneg model hac))

end FiniteSystem

/-! ## Examples -/

/-- A fair bit observed exactly, once per explanandum, with a theory of length `L`. -/
def copyBit (L : ℝ) : FiniteSystem (Fin 2) (Fin 2) := ⟨binaryUniform, Prob.dirac, 1, 1, L⟩

theorem copyBit_budget (L : ℝ) :
    (copyBit L).budget = ⟨Real.log 2, 0, Real.log 2, L⟩ := by
  have hlaw : (copyBit L).explanandumLaw = binaryUniform := by
    unfold FiniteSystem.explanandumLaw copyBit
    exact Prob.bind_dirac_right binaryUniform
  have hcond : conditionalEntropy (copyBit L).inputLaw (copyBit L).kernel = 0 := by
    unfold conditionalEntropy copyBit
    simp [shannonEntropyFin_dirac]
  unfold FiniteSystem.budget
  rw [hlaw, hcond, shannonEntropyFin_binaryUniform]
  simp [copyBit, shannonEntropy_binaryUniform]

/-- Positive example: an exact observation of a fair bit holds `log 2 / (2 log 2 + L)`, at
most one half. -/
theorem copyBit_knowledge (L : ℝ) :
    (copyBit L).knowledge = Real.log 2 / (2 * Real.log 2 + L) := by
  unfold FiniteSystem.knowledge
  rw [copyBit_budget]
  unfold Budget.knowledge Budget.explained Budget.total
  dsimp only
  ring_nf

theorem copyBit_knowledge_pos {L : ℝ} (hL : 0 ≤ L) : 0 < (copyBit L).knowledge := by
  rw [copyBit_knowledge]
  have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  exact div_pos hlog (by linarith)

/-- Negative example: a bit observed through a kernel that ignores it explains nothing. -/
def ignoreBit (L : ℝ) : FiniteSystem (Fin 2) (Fin 2) :=
  ⟨binaryUniform, fun _ => binaryUniform, 1, 1, L⟩

theorem ignoreBit_knowledge (L : ℝ) : (ignoreBit L).knowledge = 0 :=
  (ignoreBit L).knowledge_eq_zero_of_const binaryUniform rfl

/-! ## Null and negative results -/

/-- Ruling out one of `n` equally likely hypotheses gains `log n − log (n − 1)` (eq. 3.23). -/
def eliminationGain (n : ℕ) : ℝ := Real.log n - Real.log ((n : ℝ) - 1)

theorem eliminationGain_eq_entropy_sub {n : ℕ} (hn : 2 ≤ n) :
    eliminationGain n =
      shannonEntropy (uniformDist n (by omega)) -
        shannonEntropy (uniformDist (n - 1) (by omega)) := by
  rw [shannonEntropy_uniform, shannonEntropy_uniform, eliminationGain,
    Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]

/-- Two hypotheses: a conclusive test gains one bit. -/
theorem eliminationGain_two : eliminationGain 2 = Real.log 2 := by
  norm_num [eliminationGain]

theorem eliminationGain_eq_log_div {n : ℕ} (hn : 2 ≤ n) :
    eliminationGain n = Real.log ((n : ℝ) / ((n : ℝ) - 1)) := by
  have h1 : (1 : ℝ) < n := by exact_mod_cast hn
  rw [eliminationGain, Real.log_div (by linarith : (0 : ℝ) < n).ne'
    (by linarith : (0 : ℝ) < (n : ℝ) - 1).ne']

theorem eliminationGain_pos {n : ℕ} (hn : 2 ≤ n) : 0 < eliminationGain n := by
  have h1 : (1 : ℝ) < n := by exact_mod_cast hn
  rw [eliminationGain_eq_log_div hn]
  exact Real.log_pos ((one_lt_div (by linarith)).2 (by linarith))

/-- More hypotheses, less gain from ruling one out. -/
theorem eliminationGain_lt_of_lt {m n : ℕ} (hm : 2 ≤ m) (hmn : m < n) :
    eliminationGain n < eliminationGain m := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have hlt : (m : ℝ) < n := by exact_mod_cast hmn
  rw [eliminationGain_eq_log_div hm, eliminationGain_eq_log_div (hm.trans hmn.le)]
  apply Real.log_lt_log (div_pos (by linarith) (by linarith))
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- The gain from one conclusive negative result vanishes as the hypotheses multiply. -/
theorem tendsto_eliminationGain : Tendsto eliminationGain atTop (𝓝 0) := by
  have hev : (fun n : ℕ => Real.log (1 + 1 / ((n : ℝ) - 1))) =ᶠ[atTop] eliminationGain := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have h1 : (1 : ℝ) < n := by exact_mod_cast hn
    have h2 : (n : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - 1).ne'
    rw [eliminationGain_eq_log_div hn]
    congr 1
    field_simp
    ring
  refine Tendsto.congr' hev ?_
  have hsub : Tendsto (fun n : ℕ => (n : ℝ) - 1) atTop atTop := by
    have := tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop
    simpa [sub_eq_add_neg] using this
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) - 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsub
  have harg : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) - 1)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).add hinv
    rwa [add_zero] at this
  have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp harg
  rwa [Real.log_one] at this

end Mettapedia.InformationTheory.KnowledgeQuantification
