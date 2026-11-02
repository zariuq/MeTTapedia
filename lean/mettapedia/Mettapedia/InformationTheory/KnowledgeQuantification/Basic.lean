import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Knowledge as standardized compression: the information budget

D. Fanelli, *A theory and methodology to quantify knowledge*, R. Soc. open sci. 6: 181055
(2019), doi:10.1098/rsos.181055, measures how much of the information in an explanandum
`Y` is compressed by an explanans made of an input `X` and a theory or method `τ`:

`K = n_Y (H(Y) − H(Y | X, τ)) / (n_Y H(Y) + n_X H(X) − log p(τ))`   (eq. 2.1),

where `n_Y` and `n_X` count the explananda and the inputs, and `−log p(τ)` is the
description length of the theory.  This file studies `K` as a function of the four
information quantities, collected in a `Budget`; `Entropic` computes them from finite
distributions.

* `knowledge_eq_effect_mul_efficiency`: `K = k η` (eq. 2.6), with the effect `k` and the
  efficiency `η` (the paper's hardness component `h`).
* `Admissible.knowledge_mem_Ico`: `K ∈ [0, 1)` when the theory has positive length, and
  `Admissible.knowledge_eq_one_iff`: `K = 1` only for a lossless, input-free, free theory.
* `knowledge_odds`: the odds form `K / (1 − K)` (eq. 2.14).
* `knowledge_lt_knowledge_iff`: the marginal rule.  A change of system raises `K` exactly
  when the extra explained information exceeds `K` times the extra total information.  The
  paper's progress condition (eq. 3.11, appendix F), its resolution conditions (appendix E)
  and its cumulative condition (eq. 3.21) are instances
  (`progress_iff`, `knowledge_lt_iff_residual_change`).
* `ockham_relative`: Ockham's razor is relative to the number of uses (eq. 2.24).
* `min_knowledge_lt_mergeShared`: consilience (§3.3).  Two systems unified under one theory,
  described once, hold more knowledge than the smaller of the two, and more than with the
  theory described twice (`mergeTwice_knowledge_lt_mergeShared`).
* `compresses_iff`: the explanation is shorter than the explanandum exactly when
  `K > 1 − η`, equivalently `k > (1 − η) / η`; `bloated_knowledge_pos_not_compresses`:
  `K > 0` does not imply compression.
* `mdl_choice_ne_knowledge_choice`: the paper's claim that minimizers of the two-part code
  length (eq. 2.15) maximize `K` is false; it holds at a fixed theory length
  (`twoPartLength_lt_iff_of_theory_eq`) and for lossless theories
  (`twoPartLength_lt_iff_of_lossless`).
* `Admissible.knowledge_le_explanandum_div` and `Admissible.knowledge_le_half`: the input
  bounds knowledge, and an explanation that explains no more than its input is at most one
  half (the limit 1/2 of eq. 2.17).
* `correctedKnowledge`: knowledge corrected for a biased method (eqs. 3.26–3.29), with the
  fabrication bound (eq. 3.28).
* `adjustedKnowledge`: predictive knowledge (eq. 2.26).

`K` is a ratio.  It ranks explanations by relative compression, not by absolute
description length, so it is not a substitute for a code length when a decision needs
absolute costs; `mdl_choice_ne_knowledge_choice` is the witness.

The paper also reads `K` physically, as the efficiency with which a Maxwell demon turns
stored information into work; that reading is interpretation, not a theorem here.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.InformationTheory.KnowledgeQuantification

/-- The four information quantities of an explanatory system, in one unit (bits or nats).
For `n_Y` explananda and `n_X` inputs:

* `explanandum = n_Y H(Y)`, the information to be explained;
* `residual = n_Y H(Y | X, τ)`, the information the explanation leaves;
* `input = n_X H(X)`, the information acquired as input;
* `theory = −log p(τ)`, the description length of the theory or method. -/
structure Budget where
  explanandum : ℝ
  residual : ℝ
  input : ℝ
  theory : ℝ

namespace Budget

variable (b : Budget)

/-- Information explained: `n_Y (H(Y) − H(Y | X, τ))`. -/
def explained : ℝ := b.explanandum - b.residual

/-- Information in the explanandum and the explanans together. -/
def total : ℝ := b.explanandum + b.input + b.theory

/-- What the explanation costs: the residual, the input and the theory. -/
def cost : ℝ := b.residual + b.input + b.theory

/-- Fanelli's `K` (eq. 2.1): the explained share of all the information involved. -/
def knowledge : ℝ := b.explained / b.total

/-- The effect component `k` (eq. 2.7): the explained share of the explanandum. -/
def effect : ℝ := b.explained / b.explanandum

/-- The efficiency component `η` (eq. 2.8; the paper's hardness `h`): the explanandum's
share of all the information involved. -/
def efficiency : ℝ := b.explanandum / b.total

/-- The two-part code length of the minimum description length principle (eq. 2.15): the
theory, then the explanandum encoded with it. -/
def twoPartLength : ℝ := b.theory + b.residual

/-- The explanation compresses: residual, input and theory together are shorter than the
explanandum. -/
def Compresses : Prop := b.cost < b.explanandum

/-- Rescale all four quantities, as a change of logarithm base does. -/
def scale (c : ℝ) : Budget :=
  ⟨c * b.explanandum, c * b.residual, c * b.input, c * b.theory⟩

/-- Admissible budgets: a positive explanandum, a residual between zero and the
explanandum, and nonnegative input and theory lengths. -/
structure Admissible (b : Budget) : Prop where
  explanandum_pos : 0 < b.explanandum
  residual_nonneg : 0 ≤ b.residual
  residual_le : b.residual ≤ b.explanandum
  input_nonneg : 0 ≤ b.input
  theory_nonneg : 0 ≤ b.theory

theorem total_eq_explained_add_cost : b.total = b.explained + b.cost := by
  unfold total explained cost
  ring

namespace Admissible

variable {b}

theorem total_pos (h : b.Admissible) : 0 < b.total := by
  unfold total
  linarith [h.explanandum_pos, h.input_nonneg, h.theory_nonneg]

theorem explained_nonneg (h : b.Admissible) : 0 ≤ b.explained := by
  unfold explained
  linarith [h.residual_le]

theorem explained_le (h : b.Admissible) : b.explained ≤ b.explanandum := by
  unfold explained
  linarith [h.residual_nonneg]

theorem cost_nonneg (h : b.Admissible) : 0 ≤ b.cost := by
  unfold cost
  linarith [h.residual_nonneg, h.input_nonneg, h.theory_nonneg]

/-- `K ≥ 0` (the lower end of the range `[0, 1)`). -/
theorem knowledge_nonneg (h : b.Admissible) : 0 ≤ b.knowledge :=
  div_nonneg h.explained_nonneg h.total_pos.le

theorem knowledge_le_one (h : b.Admissible) : b.knowledge ≤ 1 := by
  rw [knowledge, div_le_one h.total_pos, total_eq_explained_add_cost]
  linarith [h.cost_nonneg]

theorem knowledge_lt_one_iff (h : b.Admissible) : b.knowledge < 1 ↔ 0 < b.cost := by
  rw [knowledge, div_lt_one h.total_pos, total_eq_explained_add_cost]
  constructor <;> intro hh <;> linarith

/-- A theory of positive length gives `K < 1`. -/
theorem knowledge_lt_one (h : b.Admissible) (theory_pos : 0 < b.theory) :
    b.knowledge < 1 :=
  h.knowledge_lt_one_iff.2 (by unfold cost; linarith [h.residual_nonneg, h.input_nonneg])

/-- The range `[0, 1)` of `K` for a theory of positive length. -/
theorem knowledge_mem_Ico (h : b.Admissible) (theory_pos : 0 < b.theory) :
    b.knowledge ∈ Set.Ico 0 1 :=
  ⟨h.knowledge_nonneg, h.knowledge_lt_one theory_pos⟩

/-- `K = 1` exactly for a lossless explanation with no input and a theory of length zero. -/
theorem knowledge_eq_one_iff (h : b.Admissible) :
    b.knowledge = 1 ↔ b.residual = 0 ∧ b.input = 0 ∧ b.theory = 0 := by
  constructor
  · intro one
    have hcost : b.cost = 0 := by
      have := h.knowledge_lt_one_iff
      by_contra hne
      have hpos : 0 < b.cost := lt_of_le_of_ne h.cost_nonneg (Ne.symm hne)
      exact absurd one (ne_of_lt (this.2 hpos))
    unfold cost at hcost
    refine ⟨?_, ?_, ?_⟩ <;>
      linarith [h.residual_nonneg, h.input_nonneg, h.theory_nonneg]
  · rintro ⟨hr, hi, ht⟩
    rw [knowledge, div_eq_one_iff_eq h.total_pos.ne']
    unfold explained total
    rw [hr, hi, ht]
    ring

theorem effect_mem_Icc (h : b.Admissible) : b.effect ∈ Set.Icc 0 1 :=
  ⟨div_nonneg h.explained_nonneg h.explanandum_pos.le,
    (div_le_one h.explanandum_pos).2 h.explained_le⟩

theorem efficiency_mem_Ioc (h : b.Admissible) : b.efficiency ∈ Set.Ioc 0 1 := by
  refine ⟨div_pos h.explanandum_pos h.total_pos, (div_le_one h.total_pos).2 ?_⟩
  unfold total
  linarith [h.input_nonneg, h.theory_nonneg]

end Admissible

/-- `K = k η` (eq. 2.6): effect times efficiency. -/
theorem knowledge_eq_effect_mul_efficiency (h : b.explanandum ≠ 0) :
    b.knowledge = b.effect * b.efficiency := by
  unfold knowledge effect efficiency
  rw [div_mul_div_comm, mul_comm b.explanandum b.total, mul_div_mul_right _ _ h]

/-- Comparing two systems through their components (eq. 3.33): `b'` holds more knowledge
than `b` exactly when the ratio of their effects exceeds the inverse ratio of their
efficiencies.  The paper calls the system with the larger `K` the harder one. -/
theorem knowledge_lt_iff_effect_div {b b' : Budget} (hE : b.explanandum ≠ 0)
    (hE' : b'.explanandum ≠ 0) (hk : 0 < b.effect) (hη' : 0 < b'.efficiency) :
    b.knowledge < b'.knowledge ↔ b.efficiency / b'.efficiency < b'.effect / b.effect := by
  rw [knowledge_eq_effect_mul_efficiency b hE, knowledge_eq_effect_mul_efficiency b' hE',
    div_lt_div_iff₀ hη' hk]
  constructor <;> intro h <;> linarith [mul_comm b.effect b.efficiency,
    mul_comm b'.effect b'.efficiency]

theorem one_sub_knowledge (h : b.total ≠ 0) : 1 - b.knowledge = b.cost / b.total := by
  rw [knowledge, one_sub_div h]
  congr 1
  unfold total explained cost
  ring

/-- The odds form of `K` (eq. 2.14): explained information against what the explanation
costs. -/
theorem knowledge_odds (h : b.total ≠ 0) :
    b.knowledge / (1 - b.knowledge) = b.explained / b.cost := by
  rw [one_sub_knowledge b h, knowledge, div_div_div_cancel_right₀ h]

/-- `K` does not depend on the unit of information. -/
theorem knowledge_scale {c : ℝ} (hc : c ≠ 0) : (b.scale c).knowledge = b.knowledge := by
  unfold knowledge explained total scale
  dsimp only
  rw [show c * b.explanandum - c * b.residual = c * (b.explanandum - b.residual) by ring,
    show c * b.explanandum + c * b.input + c * b.theory =
      c * (b.explanandum + b.input + b.theory) by ring,
    mul_div_mul_left _ _ hc]

/-! ## The marginal rule -/

/-- **The marginal rule.**  With positive totals, `b'` holds more knowledge than `b` exactly
when the extra explained information exceeds `K(b)` times the extra total information. -/
theorem knowledge_lt_knowledge_iff {b b' : Budget} (h : 0 < b.total) (h' : 0 < b'.total) :
    b.knowledge < b'.knowledge ↔
      b.knowledge * (b'.total - b.total) < b'.explained - b.explained := by
  unfold knowledge
  rw [div_lt_div_iff₀ h h', div_mul_eq_mul_div, div_lt_iff₀ h]
  constructor <;> intro hh <;> linarith

/-- The paper's progress condition (eq. 3.11, appendix F).  With the explanandum fixed, a
change of input and theory raises `K` exactly when the effect grows by more than
`k η` times the added input and theory, measured in units of the explanandum. -/
theorem progress_iff {b b' : Budget} (hE : b'.explanandum = b.explanandum)
    (hpos : 0 < b.explanandum) (h : 0 < b.total) (h' : 0 < b'.total) :
    b.knowledge < b'.knowledge ↔
      b.effect * b.efficiency *
          ((b'.input + b'.theory) - (b.input + b.theory)) / b.explanandum <
        b'.effect - b.effect := by
  rw [knowledge_lt_knowledge_iff h h', ← knowledge_eq_effect_mul_efficiency b hpos.ne']
  have htot : b'.total - b.total = (b'.input + b'.theory) - (b.input + b.theory) := by
    unfold total
    rw [hE]
    ring
  have heff : b'.effect - b.effect = (b'.explained - b.explained) / b.explanandum := by
    unfold effect
    rw [hE, sub_div]
  rw [htot, heff, div_lt_div_iff_of_pos_right hpos]

/-- Explanandum, residual, input and theory may all change.  `K` rises exactly when the
residual grows by less than `(1 − K)` times the growth of the explanandum, less `K` times
the growth of input and theory.  The paper's resolution conditions (appendix E,
eqs. E 5–E 7) and its cumulative condition (eq. 3.21) are this statement. -/
theorem knowledge_lt_iff_residual_change {b b' : Budget} (h : 0 < b.total)
    (h' : 0 < b'.total) :
    b.knowledge < b'.knowledge ↔
      b'.residual - b.residual <
        (1 - b.knowledge) * (b'.explanandum - b.explanandum) -
          b.knowledge * ((b'.input - b.input) + (b'.theory - b.theory)) := by
  rw [knowledge_lt_knowledge_iff h h']
  unfold explained total
  constructor <;> intro hh <;> linarith

/-- Knowledge does not increase when the explained information does not increase and the
total does not decrease. -/
theorem knowledge_le_knowledge_of_le {b b' : Budget} (h : 0 < b.total) (hN : 0 ≤ b'.explained)
    (hexpl : b'.explained ≤ b.explained) (htot : b.total ≤ b'.total) :
    b'.knowledge ≤ b.knowledge := by
  unfold knowledge
  exact div_le_div₀ (hN.trans hexpl) hexpl h htot

/-! ## Ockham's razor -/

/-- Ockham's razor at a fixed effect: with the same explanandum, residual and input, the
shorter theory holds more knowledge. -/
theorem knowledge_lt_of_theory_lt {b b' : Budget} (hE : b'.explanandum = b.explanandum)
    (hR : b'.residual = b.residual) (hI : b'.input = b.input) (hexpl : 0 < b.explained)
    (h : 0 < b.total) (hL : b.theory < b'.theory) : b'.knowledge < b.knowledge := by
  have hexpl' : b'.explained = b.explained := by unfold explained; rw [hE, hR]
  have htot : b.total < b'.total := by unfold total; rw [hE, hI]; linarith
  unfold knowledge
  rw [hexpl']
  exact div_lt_div_of_pos_left hexpl h htot

/-- A smaller residual, all else equal, holds more knowledge. -/
theorem knowledge_lt_of_residual_lt {b b' : Budget} (hE : b'.explanandum = b.explanandum)
    (hI : b'.input = b.input) (hL : b'.theory = b.theory) (h : 0 < b.total)
    (hR : b.residual < b'.residual) : b'.knowledge < b.knowledge := by
  have htot : b'.total = b.total := by unfold total; rw [hE, hI, hL]
  unfold knowledge
  rw [htot, div_lt_div_iff_of_pos_right h]
  unfold explained
  rw [hE]
  linarith

/-- A smaller input, all else equal, holds more knowledge when something is explained. -/
theorem knowledge_lt_of_input_lt {b b' : Budget} (hE : b'.explanandum = b.explanandum)
    (hR : b'.residual = b.residual) (hL : b'.theory = b.theory) (hexpl : 0 < b.explained)
    (h : 0 < b.total) (hI : b.input < b'.input) : b'.knowledge < b.knowledge := by
  have hexpl' : b'.explained = b.explained := by unfold explained; rw [hE, hR]
  have htot : b.total < b'.total := by unfold total; rw [hE, hL]; linarith
  unfold knowledge
  rw [hexpl']
  exact div_lt_div_of_pos_left hexpl h htot

/-- For an admissible budget, `K > 0` exactly when something is explained. -/
theorem Admissible.knowledge_pos_iff {b : Budget} (h : b.Admissible) :
    0 < b.knowledge ↔ 0 < b.explained := by
  unfold knowledge
  exact div_pos_iff_of_pos_right h.total_pos

/-- A system used `n` times, with explanandum `e`, residual `r` and input `i` per use and a
theory of length `L` paid once. -/
def ofUses (n e r i L : ℝ) : Budget := ⟨n * e, n * r, n * i, L⟩

theorem knowledge_ofUses {n : ℝ} (hn : 0 < n) (e r i L : ℝ) :
    (ofUses n e r i L).knowledge = (e - r) / (e + i + L / n) := by
  unfold knowledge explained total ofUses
  dsimp only
  rw [show n * e - n * r = n * (e - r) by ring,
    show n * e + n * i + L = n * (e + i + L / n) by field_simp]
  exact mul_div_mul_left _ _ hn.ne'

/-- **Ockham's razor is relative** (eq. 2.24).  Two theories with the same effect per use,
used `n` and `n'` times: the second holds more knowledge exactly when its length per use is
smaller. -/
theorem ockham_relative {n n' e r i L L' : ℝ} (hn : 0 < n) (hn' : 0 < n') (hr : r < e)
    (hpos : 0 < e + i + L / n) (hpos' : 0 < e + i + L' / n') :
    (ofUses n e r i L).knowledge < (ofUses n' e r i L').knowledge ↔ L' / n' < L / n := by
  rw [knowledge_ofUses hn, knowledge_ofUses hn',
    div_lt_div_iff_of_pos_left (sub_pos.2 hr) hpos hpos']
  constructor <;> intro hh <;> linarith

/-! ## Consilience: one theory for two systems -/

/-- Two systems explained by the theory of the first: explananda, residuals and inputs add,
and the theory is described once. -/
def mergeShared (b b' : Budget) : Budget :=
  ⟨b.explanandum + b'.explanandum, b.residual + b'.residual, b.input + b'.input, b.theory⟩

/-- The mediant of two knowledge values, with the theory described twice. -/
def mergeTwice (b b' : Budget) : Budget :=
  ⟨b.explanandum + b'.explanandum, b.residual + b'.residual, b.input + b'.input,
    b.theory + b'.theory⟩

/-- Keeping two copies of the theory gives the mediant, which lies above the smaller of the
two knowledge values. -/
theorem min_knowledge_le_mergeTwice {b b' : Budget} (h : 0 < b.total) (h' : 0 < b'.total) :
    min b.knowledge b'.knowledge ≤ (mergeTwice b b').knowledge := by
  have hexpl : (mergeTwice b b').explained = b.explained + b'.explained := by
    unfold explained mergeTwice
    dsimp only
    ring
  have htot : (mergeTwice b b').total = b.total + b'.total := by
    unfold total mergeTwice
    dsimp only
    ring
  unfold knowledge
  rw [hexpl, htot]
  rcases le_total (b.explained / b.total) (b'.explained / b'.total) with hle | hle
  · rw [min_eq_left hle, div_le_div_iff₀ h (by linarith)]
    rw [div_le_div_iff₀ h h'] at hle
    nlinarith
  · rw [min_eq_right hle, div_le_div_iff₀ h' (by linarith)]
    rw [div_le_div_iff₀ h' h] at hle
    nlinarith

/-- **Consilience** (§3.3).  Unifying two systems under one theory, described once, holds
more knowledge than describing the theory twice, hence more than the smaller of the two
knowledge values. -/
theorem mergeTwice_knowledge_lt_mergeShared {b b' : Budget} (h : 0 < b.total)
    (hrest : 0 ≤ b'.explanandum + b'.input) (hL : b'.theory = b.theory) (hpos : 0 < b.theory)
    (hexpl : 0 < b.explained + b'.explained) :
    (mergeTwice b b').knowledge < (mergeShared b b').knowledge := by
  have hexplEq : (mergeShared b b').explained = (mergeTwice b b').explained := rfl
  have htot : (mergeShared b b').total = b.total + (b'.explanandum + b'.input) := by
    unfold total mergeShared
    dsimp only
    ring
  have htot2 : (mergeTwice b b').total = b.total + (b'.explanandum + b'.input) + b.theory := by
    unfold total mergeTwice
    dsimp only
    rw [hL]
    ring
  have hshared : 0 < (mergeShared b b').total := by
    rw [htot]
    linarith
  unfold knowledge
  rw [hexplEq]
  have hN : 0 < (mergeTwice b b').explained := by
    unfold explained mergeTwice
    dsimp only
    unfold explained at hexpl
    linarith
  apply div_lt_div_of_pos_left hN hshared
  rw [htot, htot2]
  linarith

theorem min_knowledge_lt_mergeShared {b b' : Budget} (h : 0 < b.total) (h' : 0 < b'.total)
    (hrest : 0 ≤ b'.explanandum + b'.input) (hL : b'.theory = b.theory) (hpos : 0 < b.theory)
    (hexpl : 0 < b.explained + b'.explained) :
    min b.knowledge b'.knowledge < (mergeShared b b').knowledge :=
  (min_knowledge_le_mergeTwice h h').trans_lt
    (mergeTwice_knowledge_lt_mergeShared h hrest hL hpos hexpl)

/-! ## Compression -/

/-- An explanation compresses exactly when `K > 1 − η`. -/
theorem compresses_iff (h : 0 < b.total) : b.Compresses ↔ 1 - b.efficiency < b.knowledge := by
  unfold Compresses efficiency knowledge
  rw [one_sub_div h.ne', div_lt_div_iff_of_pos_right h]
  unfold cost total explained
  constructor <;> intro hh <;> linarith

/-- An explanation compresses exactly when its effect exceeds `(1 − η) / η`. -/
theorem compresses_iff_effect (hE : 0 < b.explanandum) (h : 0 < b.total) :
    b.Compresses ↔ (1 - b.efficiency) / b.efficiency < b.effect := by
  have hratio : (1 - b.efficiency) / b.efficiency = (b.input + b.theory) / b.explanandum := by
    unfold efficiency
    rw [one_sub_div h.ne', div_div_div_cancel_right₀ h.ne']
    unfold total
    ring_nf
  rw [hratio]
  unfold effect Compresses
  rw [div_lt_div_iff_of_pos_right hE]
  unfold cost explained
  constructor <;> intro hh <;> linarith

/-- An explanation that compresses holds positive knowledge. -/
theorem knowledge_pos_of_compresses (hadm : b.Admissible) (hc : b.Compresses) :
    0 < b.knowledge := by
  unfold Compresses cost at hc
  apply div_pos _ hadm.total_pos
  unfold explained
  linarith [hadm.input_nonneg, hadm.theory_nonneg]

/-! ## Minimum description length -/

/-- A one-unit theory leaving six of ten units. -/
def shortLossy : Budget := ⟨10, 6, 0, 1⟩

/-- A five-unit theory leaving four of ten units. -/
def longerSharper : Budget := ⟨10, 4, 0, 5⟩

theorem shortLossy_admissible : shortLossy.Admissible := by
  constructor <;> norm_num [shortLossy]

theorem longerSharper_admissible : longerSharper.Admissible := by
  constructor <;> norm_num [longerSharper]

theorem shortLossy_twoPartLength : shortLossy.twoPartLength = 7 := by
  norm_num [shortLossy, twoPartLength]

theorem longerSharper_twoPartLength : longerSharper.twoPartLength = 9 := by
  norm_num [longerSharper, twoPartLength]

theorem shortLossy_knowledge : shortLossy.knowledge = 4 / 11 := by
  norm_num [shortLossy, knowledge, explained, total]

theorem longerSharper_knowledge : longerSharper.knowledge = 2 / 5 := by
  norm_num [longerSharper, knowledge, explained, total]

/-- **The two-part code and `K` choose differently.**  The paper states that the theories
minimizing `L(H) + L(D | H)` (eq. 2.15) maximize `K`.  Here the shorter two-part code (7
against 9 units) has the smaller `K` (4/11 against 2/5). -/
theorem mdl_choice_ne_knowledge_choice :
    shortLossy.twoPartLength < longerSharper.twoPartLength ∧
      shortLossy.knowledge < longerSharper.knowledge := by
  rw [shortLossy_twoPartLength, longerSharper_twoPartLength, shortLossy_knowledge,
    longerSharper_knowledge]
  norm_num

/-- The paper's claim, stated for admissible budgets sharing explanandum and input, is
false. -/
theorem not_forall_twoPartLength_lt_imp_knowledge_le :
    ¬ ∀ b b' : Budget, b.Admissible → b'.Admissible →
        b.explanandum = b'.explanandum → b.input = b'.input →
          b.twoPartLength < b'.twoPartLength → b'.knowledge ≤ b.knowledge := by
  intro claim
  have := claim shortLossy longerSharper shortLossy_admissible longerSharper_admissible
    (by norm_num [shortLossy, longerSharper]) (by norm_num [shortLossy, longerSharper])
    mdl_choice_ne_knowledge_choice.1
  exact absurd mdl_choice_ne_knowledge_choice.2 (not_lt.2 this)

/-- At a fixed theory length the two-part code and `K` rank explanations alike. -/
theorem twoPartLength_lt_iff_of_theory_eq {b b' : Budget}
    (hE : b.explanandum = b'.explanandum) (hI : b.input = b'.input)
    (hL : b.theory = b'.theory) (h : 0 < b.total) :
    b.twoPartLength < b'.twoPartLength ↔ b'.knowledge < b.knowledge := by
  have htot : b'.total = b.total := by unfold total; rw [hE, hI, hL]
  unfold knowledge
  rw [htot, div_lt_div_iff_of_pos_right h]
  unfold twoPartLength explained
  rw [hE, hL]
  constructor <;> intro hh <;> linarith

/-- For lossless explanations the two-part code and `K` rank explanations alike. -/
theorem twoPartLength_lt_iff_of_lossless {b b' : Budget}
    (hE : b.explanandum = b'.explanandum) (hI : b.input = b'.input)
    (hR : b.residual = 0) (hR' : b'.residual = 0) (hpos : 0 < b.explanandum)
    (h : 0 < b.total) (h' : 0 < b'.total) :
    b.twoPartLength < b'.twoPartLength ↔ b'.knowledge < b.knowledge := by
  have hexpl : b.explained = b.explanandum := by unfold explained; rw [hR]; ring
  have hexpl' : b'.explained = b.explanandum := by unfold explained; rw [hR', hE]; ring
  unfold knowledge
  rw [hexpl, hexpl', div_lt_div_iff_of_pos_left hpos h' h]
  unfold twoPartLength total
  rw [hR, hR', hE, hI]
  constructor <;> intro hh <;> linarith

/-- A twelve-unit theory leaving five of ten units. -/
def bloated : Budget := ⟨10, 5, 0, 12⟩

/-- **`K > 0` is not compression.**  The theory and its residual take seventeen units to
describe ten, yet `K = 5/22 > 0`. -/
theorem bloated_knowledge_pos_not_compresses :
    bloated.knowledge = 5 / 22 ∧ 0 < bloated.knowledge ∧ ¬ bloated.Compresses ∧
      bloated.explanandum < bloated.twoPartLength := by
  have hK : bloated.knowledge = 5 / 22 := by
    norm_num [bloated, knowledge, explained, total]
  refine ⟨hK, by rw [hK]; norm_num, ?_, ?_⟩
  · norm_num [bloated, Compresses, cost]
  · norm_num [bloated, twoPartLength]

/-- Positive example: a one-unit lossless theory of ten units compresses. -/
theorem lossless_short_compresses :
    (⟨10, 0, 0, 1⟩ : Budget).Compresses ∧ (⟨10, 0, 0, 1⟩ : Budget).knowledge = 10 / 11 := by
  constructor
  · norm_num [Compresses, cost]
  · norm_num [knowledge, explained, total]

/-! ## Lossless explanations -/

/-- A lossless explanation has `K = η` (eq. 3.1). -/
theorem knowledge_eq_efficiency_of_lossless (hR : b.residual = 0) :
    b.knowledge = b.efficiency := by
  simp [knowledge, efficiency, explained, hR]

/-- The difference in `K` between two lossless, input-free explanations (eq. 3.5). -/
theorem knowledge_sub_of_lossless {E L E' L' : ℝ} (h : 0 < E + L) (h' : 0 < E' + L') :
    (⟨E', 0, 0, L'⟩ : Budget).knowledge - (⟨E, 0, 0, L⟩ : Budget).knowledge =
      (E' * L - E * L') / ((E' + L') * (E + L)) := by
  unfold knowledge explained total
  dsimp only
  rw [div_sub_div _ _ (by linarith) (by linarith)]
  congr 1 <;> ring

/-- The gain from a shorter proof of the same theorem (eq. 3.4), with the explanandum as
the unit. -/
theorem knowledge_gain_shorter_proof {L L' : ℝ} (hL : 0 ≤ L) (hL' : 0 ≤ L') :
    (⟨1, 0, 0, L'⟩ : Budget).knowledge - (⟨1, 0, 0, L⟩ : Budget).knowledge =
      (L - L') / ((1 + L') * (1 + L)) := by
  rw [knowledge_sub_of_lossless (by linarith) (by linarith)]
  ring_nf

/-! ## Bounds from the input -/

namespace Admissible

variable {b}

/-- The input bounds knowledge: `K ≤ n_Y H(Y) / (n_Y H(Y) + n_X H(X))`.  With `z` one-unit
explananda and a one-unit input this is the paper's `z / (z + 1)` (eq. 3.16). -/
theorem knowledge_le_explanandum_div (h : b.Admissible) :
    b.knowledge ≤ b.explanandum / (b.explanandum + b.input) := by
  unfold knowledge total
  apply div_le_div₀ h.explanandum_pos.le h.explained_le
    (by linarith [h.explanandum_pos, h.input_nonneg])
  linarith [h.theory_nonneg]

/-- An explanation that explains no more than its input holds at most one half. -/
theorem knowledge_le_half (h : b.Admissible) (hI : b.explained ≤ b.input) :
    b.knowledge ≤ 1 / 2 := by
  rw [knowledge, div_le_iff₀ h.total_pos]
  unfold total
  linarith [h.explained_le, h.theory_nonneg]

/-- With a theory of positive length the bound one half is strict. -/
theorem knowledge_lt_half (h : b.Admissible) (hI : b.explained ≤ b.input)
    (theory_pos : 0 < b.theory) : b.knowledge < 1 / 2 := by
  rw [knowledge, div_lt_iff₀ h.total_pos]
  unfold total
  linarith [h.explained_le]

end Admissible

/-! ## Biased methods -/

/-- Bias-corrected knowledge (eq. 3.26).  The biased method shifts the conditional law of
the explanandum by `divergence` (`n_Y` times the Kullback–Leibler divergence from the
unbiased to the biased law) and costs `biasCost` more to describe (`n_b (−log p(b))`).  The
paper's bias term is `B = divergence / total` (eq. 3.27), and the correction factor
`η_u / η_b` is `(total + biasCost) / total` (`efficiency_div_efficiency_add_theory`). -/
def correctedKnowledge (divergence biasCost : ℝ) : ℝ :=
  b.knowledge - (b.total + biasCost) / b.total * (divergence / b.total)

/-- The correction factor of eq. 3.26 is the ratio of the unbiased to the biased
efficiency. -/
theorem efficiency_div_efficiency_add_theory {c : ℝ} (hE : b.explanandum ≠ 0)
    (h : b.total ≠ 0) (hc : b.total + c ≠ 0) :
    b.efficiency / (⟨b.explanandum, b.residual, b.input, b.theory + c⟩ : Budget).efficiency =
      (b.total + c) / b.total := by
  unfold efficiency total
  dsimp only
  have h1 : b.explanandum + b.input + b.theory ≠ 0 := h
  have h2 : b.explanandum + b.input + (b.theory + c) ≠ 0 := by
    rw [show b.explanandum + b.input + (b.theory + c) =
      b.explanandum + b.input + b.theory + c by ring]
    exact hc
  field_simp
  ring

theorem correctedKnowledge_le {d c : ℝ} (h : 0 < b.total) (hd : 0 ≤ d) (hc : 0 ≤ c) :
    b.correctedKnowledge d c ≤ b.knowledge := by
  unfold correctedKnowledge
  have : 0 ≤ (b.total + c) / b.total * (d / b.total) :=
    mul_nonneg (div_nonneg (by linarith) h.le) (div_nonneg hd h.le)
  linarith

/-- A bias is tolerable exactly when `K` exceeds the corrected bias term (eq. 3.29). -/
theorem correctedKnowledge_pos_iff {d c : ℝ} :
    0 < b.correctedKnowledge d c ↔ (b.total + c) / b.total * (d / b.total) < b.knowledge := by
  unfold correctedKnowledge
  exact sub_pos

/-- The paper's criterion for a pseudoscience (eq. 3.31): corrected knowledge is negative
exactly when `K` falls short of the corrected bias term. -/
theorem correctedKnowledge_neg_iff {d c : ℝ} :
    b.correctedKnowledge d c < 0 ↔ b.knowledge < (b.total + c) / b.total * (d / b.total) := by
  unfold correctedKnowledge
  exact sub_neg

/-- **Fabrication** (eq. 3.28): when the method generates the whole effect, corrected
knowledge is negative. -/
theorem correctedKnowledge_neg_of_knowledge_eq_zero {d c : ℝ} (h : 0 < b.total)
    (hK : b.knowledge = 0) (hd : 0 < d) (hc : 0 ≤ c) : b.correctedKnowledge d c < 0 := by
  unfold correctedKnowledge
  rw [hK]
  have : 0 < (b.total + c) / b.total * (d / b.total) :=
    mul_pos (div_pos (by linarith) h) (div_pos hd h)
  linarith

/-- A bias that produces exactly the claimed effect, through a method costing anything at
all, leaves negative knowledge, even when the claim is true (§3.6.1). -/
theorem correctedKnowledge_neg_of_bias_eq_knowledge {d c : ℝ} (h : 0 < b.total)
    (hB : d / b.total = b.knowledge) (hK : 0 < b.knowledge) (hc : 0 < c) :
    b.correctedKnowledge d c < 0 := by
  unfold correctedKnowledge
  rw [hB]
  have hfactor : 1 < (b.total + c) / b.total := by
    rw [lt_div_iff₀ h]
    linarith
  nlinarith

/-- Positive example: a lossless ten-unit explanation with a one-unit theory keeps positive
knowledge after a one-unit bias costing one unit of method. -/
theorem tolerable_bias_example :
    (⟨10, 0, 0, 1⟩ : Budget).correctedKnowledge 1 1 = 98 / 121 ∧
      0 < (⟨10, 0, 0, 1⟩ : Budget).correctedKnowledge 1 1 := by
  have h : (⟨10, 0, 0, 1⟩ : Budget).correctedKnowledge 1 1 = 98 / 121 := by
    norm_num [correctedKnowledge, knowledge, explained, total]
  exact ⟨h, by rw [h]; norm_num⟩

/-! ## Predictive knowledge -/

/-- Predictive knowledge (eq. 2.26): a fixed prediction leaves the residual larger by the
divergence `n_Y D(p ‖ q)` between the observed and the predicted conditional laws. -/
def adjustedKnowledge (divergence : ℝ) : ℝ := (b.explained - divergence) / b.total

theorem adjustedKnowledge_eq (d : ℝ) :
    b.adjustedKnowledge d = b.knowledge - d / b.total := by
  unfold adjustedKnowledge knowledge
  rw [sub_div]

/-- Prediction never yields more knowledge than explanation of the same data. -/
theorem adjustedKnowledge_le {d : ℝ} (h : 0 < b.total) (hd : 0 ≤ d) :
    b.adjustedKnowledge d ≤ b.knowledge := by
  rw [adjustedKnowledge_eq]
  linarith [div_nonneg hd h.le]

theorem adjustedKnowledge_eq_knowledge_iff {d : ℝ} (h : 0 < b.total) :
    b.adjustedKnowledge d = b.knowledge ↔ d = 0 := by
  rw [adjustedKnowledge_eq, sub_eq_self, div_eq_zero_iff]
  constructor
  · rintro (hd | ht)
    · exact hd
    · exact absurd ht h.ne'
  · intro hd
    exact Or.inl hd

end Budget

end Mettapedia.InformationTheory.KnowledgeQuantification
