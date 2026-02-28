import Mettapedia.Logic.PLNFirstOrder.QuantifierSemantics

/-!
# Fuzzy Quantifier Semantics (Chapter 11)

Explicit quantifier semantics parameterized by:

- `ε`   : proxy tolerance around 0/1,
- `LPC` : lower proxy confidence,
- `UPC` : upper proxy confidence,
- `PCL` : proxy confidence threshold for crisp-like `ForAll` / `ThereExists` views.

This module stays generic over a finite-domain profile `U → ℝ` so it can be fed by
ITV coordinates (`lower`, `upper`, `strength`, `credibility`, `width`) or by direct
numerical fixtures.
-/

namespace Mettapedia.Logic.PLNFirstOrder

open Classical

/-- Chapter-11 fuzzy quantifier parameters. -/
structure FuzzyQuantifierParams where
  ε : ℝ
  LPC : ℝ
  UPC : ℝ
  PCL : ℝ
  hε : 0 ≤ ε ∧ ε ≤ 1
  hLPC : 0 ≤ LPC ∧ LPC ≤ 1
  hUPC : 0 ≤ UPC ∧ UPC ≤ 1
  hPCL : 0 ≤ PCL ∧ PCL ≤ 1
  hLPC_le_UPC : LPC ≤ UPC

section Profiles

variable {U : Type*} [Fintype U]

/-- Numeric proxy for being "essentially true" (`≈ 1`). -/
def nearOne (p : FuzzyQuantifierParams) (x : ℝ) : Prop :=
  1 - p.ε ≤ x ∧ x ≤ 1

/-- Numeric proxy for being "essentially false" (`≈ 0`). -/
def nearZero (p : FuzzyQuantifierParams) (x : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ p.ε

/-- Number of witnesses satisfying a predicate. -/
noncomputable def witnessCount (pred : U → Prop) [DecidablePred pred] : ℕ :=
  Fintype.card {u // pred u}

/-- Fraction of witnesses satisfying a predicate (`0` on empty domain). -/
noncomputable def witnessFraction (pred : U → Prop) [DecidablePred pred] : ℝ :=
  if _h0 : Fintype.card U = 0 then
    0
  else
    (witnessCount pred : ℝ) / (Fintype.card U : ℝ)

theorem witnessFraction_nonneg (pred : U → Prop) [DecidablePred pred] :
    0 ≤ witnessFraction pred := by
  unfold witnessFraction
  by_cases h0 : Fintype.card U = 0
  · simp [h0]
  · have hden_pos_nat : 0 < Fintype.card U := Nat.pos_of_ne_zero h0
    have hden_nonneg : 0 ≤ (Fintype.card U : ℝ) := by positivity
    have hnum_nonneg : 0 ≤ (witnessCount pred : ℝ) := by positivity
    simp [h0, div_nonneg hnum_nonneg hden_nonneg]

theorem witnessFraction_le_one (pred : U → Prop) [DecidablePred pred] :
    witnessFraction pred ≤ 1 := by
  unfold witnessFraction
  by_cases h0 : Fintype.card U = 0
  · simp [h0]
  · have hden_pos_nat : 0 < Fintype.card U := Nat.pos_of_ne_zero h0
    have hden_pos : 0 < (Fintype.card U : ℝ) := by
      exact_mod_cast hden_pos_nat
    have hnum_le_nat : witnessCount pred ≤ Fintype.card U := by
      simpa [witnessCount] using (Fintype.card_subtype_le (p := pred))
    have hnum_le : (witnessCount pred : ℝ) ≤ (Fintype.card U : ℝ) := by
      exact_mod_cast hnum_le_nat
    have hdiv' :
        (witnessCount pred : ℝ) / (Fintype.card U : ℝ) ≤
          (Fintype.card U : ℝ) / (Fintype.card U : ℝ) := by
      exact div_le_div_of_nonneg_right hnum_le (le_of_lt hden_pos)
    have hden_ne : (Fintype.card U : ℝ) ≠ 0 := ne_of_gt hden_pos
    have hdiv : (witnessCount pred : ℝ) / (Fintype.card U : ℝ) ≤ 1 := by
      simpa [hden_ne] using hdiv'
    simpa [h0] using hdiv

theorem witnessCount_mono
    (pred₁ pred₂ : U → Prop) [DecidablePred pred₁] [DecidablePred pred₂]
    (hImpl : ∀ u, pred₁ u → pred₂ u) :
    witnessCount pred₁ ≤ witnessCount pred₂ := by
  classical
  unfold witnessCount
  refine Fintype.card_le_of_injective
    (fun x : {u // pred₁ u} => (⟨x.1, hImpl x.1 x.2⟩ : {u // pred₂ u})) ?_
  intro x y hxy
  cases x with
  | mk x hx =>
    cases y with
    | mk y hy =>
      simp at hxy
      simp [hxy]

theorem witnessFraction_mono
    (pred₁ pred₂ : U → Prop) [DecidablePred pred₁] [DecidablePred pred₂]
    (hImpl : ∀ u, pred₁ u → pred₂ u) :
    witnessFraction pred₁ ≤ witnessFraction pred₂ := by
  unfold witnessFraction
  by_cases h0 : Fintype.card U = 0
  · simp [h0]
  · have hden_nonneg : 0 ≤ (Fintype.card U : ℝ) := by positivity
    have hcount : witnessCount pred₁ ≤ witnessCount pred₂ :=
      witnessCount_mono pred₁ pred₂ hImpl
    have hcount' : (witnessCount pred₁ : ℝ) ≤ (witnessCount pred₂ : ℝ) := by
      exact_mod_cast hcount
    have hdiv :
        (witnessCount pred₁ : ℝ) / (Fintype.card U : ℝ) ≤
          (witnessCount pred₂ : ℝ) / (Fintype.card U : ℝ) := by
      exact div_le_div_of_nonneg_right hcount' hden_nonneg
    simpa [h0] using hdiv

/-- Fraction of witnesses that are `nearOne`. -/
noncomputable def nearOneFraction
    (p : FuzzyQuantifierParams) (profile : U → ℝ) : ℝ :=
  witnessFraction (fun u => nearOne p (profile u))

/-- Fraction of witnesses that are `nearZero`. -/
noncomputable def nearZeroFraction
    (p : FuzzyQuantifierParams) (profile : U → ℝ) : ℝ :=
  witnessFraction (fun u => nearZero p (profile u))

theorem nearOneFraction_in_unit
    (p : FuzzyQuantifierParams) (profile : U → ℝ) :
    nearOneFraction p profile ∈ Set.Icc 0 1 :=
  ⟨witnessFraction_nonneg _, witnessFraction_le_one _⟩

theorem nearZeroFraction_in_unit
    (p : FuzzyQuantifierParams) (profile : U → ℝ) :
    nearZeroFraction p profile ∈ Set.Icc 0 1 :=
  ⟨witnessFraction_nonneg _, witnessFraction_le_one _⟩

theorem nearOneFraction_mono_of_pointwise
    (p : FuzzyQuantifierParams)
    (profile₁ profile₂ : U → ℝ)
    (hle : ∀ u, profile₁ u ≤ profile₂ u)
    (hub : ∀ u, profile₂ u ≤ 1) :
    nearOneFraction p profile₁ ≤ nearOneFraction p profile₂ := by
  unfold nearOneFraction
  exact witnessFraction_mono
    (pred₁ := fun u => nearOne p (profile₁ u))
    (pred₂ := fun u => nearOne p (profile₂ u))
    (hImpl := by
      intro u hu
      exact ⟨le_trans hu.1 (hle u), hub u⟩)

/-- Conservativity schema:
if the induced `nearOne` witness signature is unchanged, near-one mass is unchanged. -/
theorem nearOneFraction_eq_of_signatureEq
    (p : FuzzyQuantifierParams)
    (profile₁ profile₂ : U → ℝ)
    (hSig : ∀ u, nearOne p (profile₁ u) ↔ nearOne p (profile₂ u)) :
    nearOneFraction p profile₁ = nearOneFraction p profile₂ := by
  have hPredEq :
      (fun u => nearOne p (profile₁ u)) = (fun u => nearOne p (profile₂ u)) := by
    funext u
    exact propext (hSig u)
  unfold nearOneFraction
  simp [hPredEq]

/-- Score used for existential-style Chapter-11 checks. -/
noncomputable def fuzzyExistsScore
    (p : FuzzyQuantifierParams) (profile : U → ℝ) : ℝ :=
  nearOneFraction p profile

/-- Generic fuzzy quantifier truth: near-one frequency lies in `[LPC, UPC]`. -/
noncomputable def fuzzyIntervalHolds
    (p : FuzzyQuantifierParams) (profile : U → ℝ) : Prop :=
  p.LPC ≤ nearOneFraction p profile ∧ nearOneFraction p profile ≤ p.UPC

/-- Crisp-leaning `ForAll`: near-one frequency is at least `PCL`. -/
noncomputable def fuzzyForAllHolds
    (p : FuzzyQuantifierParams) (profile : U → ℝ) : Prop :=
  p.PCL ≤ nearOneFraction p profile

/-- Crisp-leaning `ThereExists`: at least `PCL` mass is not near-zero. -/
noncomputable def fuzzyThereExistsHolds
    (p : FuzzyQuantifierParams) (profile : U → ℝ) : Prop :=
  p.PCL ≤ 1 - nearZeroFraction p profile

/-- Profile-level conjunction with a constant score, used in Ch.11 rule-4 canaries. -/
def conjoinProfile (g : ℝ) (profile : U → ℝ) : U → ℝ :=
  fun u => min g (profile u)

/-- Monotonicity schema:
pointwise profile increase (under `≤ 1`) cannot decrease fuzzy existential score. -/
theorem fuzzyExistsScore_mono_of_pointwise
    (p : FuzzyQuantifierParams)
    (profile₁ profile₂ : U → ℝ)
    (hle : ∀ u, profile₁ u ≤ profile₂ u)
    (hub : ∀ u, profile₂ u ≤ 1) :
    fuzzyExistsScore p profile₁ ≤ fuzzyExistsScore p profile₂ := by
  unfold fuzzyExistsScore
  exact nearOneFraction_mono_of_pointwise p profile₁ profile₂ hle hub

/-- Monotonicity schema for `ForAll`:
pointwise profile increase preserves fuzzy-`ForAll` truth. -/
theorem fuzzyForAllHolds_mono_of_pointwise
    (p : FuzzyQuantifierParams)
    (profile₁ profile₂ : U → ℝ)
    (hle : ∀ u, profile₁ u ≤ profile₂ u)
    (hub : ∀ u, profile₂ u ≤ 1)
    (hForAll : fuzzyForAllHolds p profile₁) :
    fuzzyForAllHolds p profile₂ := by
  unfold fuzzyForAllHolds at *
  exact le_trans hForAll (fuzzyExistsScore_mono_of_pointwise p profile₁ profile₂ hle hub)

/-- Conservativity schema for interval truth:
if the induced `nearOne` witness signature is unchanged, interval truth is unchanged. -/
theorem fuzzyIntervalHolds_iff_of_signatureEq
    (p : FuzzyQuantifierParams)
    (profile₁ profile₂ : U → ℝ)
    (hSig : ∀ u, nearOne p (profile₁ u) ↔ nearOne p (profile₂ u)) :
    fuzzyIntervalHolds p profile₁ ↔ fuzzyIntervalHolds p profile₂ := by
  have hEq : nearOneFraction p profile₁ = nearOneFraction p profile₂ :=
    nearOneFraction_eq_of_signatureEq p profile₁ profile₂ hSig
  unfold fuzzyIntervalHolds
  simp [hEq]

/-- Conservativity schema for `ForAll` truth under unchanged `nearOne` signature. -/
theorem fuzzyForAllHolds_iff_of_signatureEq
    (p : FuzzyQuantifierParams)
    (profile₁ profile₂ : U → ℝ)
    (hSig : ∀ u, nearOne p (profile₁ u) ↔ nearOne p (profile₂ u)) :
    fuzzyForAllHolds p profile₁ ↔ fuzzyForAllHolds p profile₂ := by
  have hEq : nearOneFraction p profile₁ = nearOneFraction p profile₂ :=
    nearOneFraction_eq_of_signatureEq p profile₁ profile₂ hSig
  unfold fuzzyForAllHolds
  simp [hEq]

/-- Quantifier-fuzzification composition operator over unit-interval scores. -/
structure QFMCompose where
  comp : ℝ → ℝ → ℝ
  monotone_on_unit :
    ∀ {a₁ a₂ b₁ b₂ : ℝ},
      a₁ ∈ Set.Icc (0 : ℝ) 1 →
      a₂ ∈ Set.Icc (0 : ℝ) 1 →
      b₁ ∈ Set.Icc (0 : ℝ) 1 →
      b₂ ∈ Set.Icc (0 : ℝ) 1 →
      a₁ ≤ a₂ →
      b₁ ≤ b₂ →
      comp a₁ b₁ ≤ comp a₂ b₂

/-- Multiplicative QFM operator on `[0,1]`, matching the current Ch.11 composition canaries. -/
def qfmMul : QFMCompose where
  comp := fun x y => x * y
  monotone_on_unit := by
    intro a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ hA hB
    have hb₁_nonneg : 0 ≤ b₁ := hb₁.1
    have ha₂_nonneg : 0 ≤ a₂ := ha₂.1
    have hleft : a₁ * b₁ ≤ a₂ * b₁ := mul_le_mul_of_nonneg_right hA hb₁_nonneg
    have hright : a₂ * b₁ ≤ a₂ * b₂ := mul_le_mul_of_nonneg_left hB ha₂_nonneg
    exact le_trans hleft hright

/-- Minimum-based QFM operator on `[0,1]`. -/
def qfmMin : QFMCompose where
  comp := fun x y => min x y
  monotone_on_unit := by
    intro a₁ a₂ b₁ b₂ _ha₁ _ha₂ _hb₁ _hb₂ hA hB
    exact min_le_min hA hB

/-- Lukasiewicz-style QFM operator (bounded sum with floor at `0`). -/
def qfmLukasiewicz : QFMCompose where
  comp := fun x y => max 0 (x + y - 1)
  monotone_on_unit := by
    intro a₁ a₂ b₁ b₂ _ha₁ _ha₂ _hb₁ _hb₂ hA hB
    have hsum : a₁ + b₁ - 1 ≤ a₂ + b₂ - 1 := by nlinarith
    exact max_le_max le_rfl hsum

/-- Probabilistic-sum QFM operator. -/
def qfmProbSum : QFMCompose where
  comp := fun x y => x + y - x * y
  monotone_on_unit := by
    intro a₁ a₂ b₁ b₂ _ha₁ ha₂ hb₁ _hb₂ hA hB
    have hb1_le_one : b₁ ≤ 1 := hb₁.2
    have ha2_le_one : a₂ ≤ 1 := ha₂.2
    have hleft :
        a₁ + b₁ - a₁ * b₁ ≤ a₂ + b₁ - a₂ * b₁ := by
      have hnonneg : 0 ≤ 1 - b₁ := by linarith
      have hscale : a₁ * (1 - b₁) ≤ a₂ * (1 - b₁) := by
        exact mul_le_mul_of_nonneg_right hA hnonneg
      nlinarith [hscale]
    have hright :
        a₂ + b₁ - a₂ * b₁ ≤ a₂ + b₂ - a₂ * b₂ := by
      have hnonneg : 0 ≤ 1 - a₂ := by linarith
      have hscale : b₁ * (1 - a₂) ≤ b₂ * (1 - a₂) := by
        exact mul_le_mul_of_nonneg_right hB hnonneg
      nlinarith [hscale]
    exact le_trans hleft hright

/-- Reusable API object for QFM-composed syllogism bounds. -/
structure QFMSyllogismEnvelope where
  lower : ℝ
  upper : ℝ
  score : ℝ
  lower_le_score : lower ≤ score
  score_le_upper : score ≤ upper

/-- Generic QFM syllogism transport:
compose interval bounds from two fuzzy quantifier premises into composed-score bounds. -/
theorem qfm_compose_interval_of_fuzzyIntervals
    (q : QFMCompose)
    (pAB pBC : FuzzyQuantifierParams)
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds pAB profileAB)
    (hBC : fuzzyIntervalHolds pBC profileBC) :
    q.comp pAB.LPC pBC.LPC ≤
        q.comp (nearOneFraction pAB profileAB) (nearOneFraction pBC profileBC) ∧
      q.comp (nearOneFraction pAB profileAB) (nearOneFraction pBC profileBC) ≤
        q.comp pAB.UPC pBC.UPC := by
  have hABu : nearOneFraction pAB profileAB ∈ Set.Icc (0 : ℝ) 1 :=
    nearOneFraction_in_unit pAB profileAB
  have hBCu : nearOneFraction pBC profileBC ∈ Set.Icc (0 : ℝ) 1 :=
    nearOneFraction_in_unit pBC profileBC
  constructor
  · exact q.monotone_on_unit pAB.hLPC hABu pBC.hLPC hBCu hAB.1 hBC.1
  · exact q.monotone_on_unit hABu pAB.hUPC hBCu pBC.hUPC hAB.2 hBC.2

/-- Multiplicative QFM specialization of interval transport. -/
theorem qfmMul_interval_of_fuzzyIntervals
    (pAB pBC : FuzzyQuantifierParams)
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds pAB profileAB)
    (hBC : fuzzyIntervalHolds pBC profileBC) :
    pAB.LPC * pBC.LPC ≤
        nearOneFraction pAB profileAB * nearOneFraction pBC profileBC ∧
      nearOneFraction pAB profileAB * nearOneFraction pBC profileBC ≤
        pAB.UPC * pBC.UPC := by
  simpa [qfmMul] using
    qfm_compose_interval_of_fuzzyIntervals qfmMul pAB pBC profileAB profileBC hAB hBC

/-- Minimum QFM specialization of interval transport. -/
theorem qfmMin_interval_of_fuzzyIntervals
    (pAB pBC : FuzzyQuantifierParams)
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds pAB profileAB)
    (hBC : fuzzyIntervalHolds pBC profileBC) :
    min pAB.LPC pBC.LPC ≤
        min (nearOneFraction pAB profileAB) (nearOneFraction pBC profileBC) ∧
      min (nearOneFraction pAB profileAB) (nearOneFraction pBC profileBC) ≤
        min pAB.UPC pBC.UPC := by
  simpa [qfmMin] using
    qfm_compose_interval_of_fuzzyIntervals qfmMin pAB pBC profileAB profileBC hAB hBC

/-- Lukasiewicz QFM specialization of interval transport. -/
theorem qfmLukasiewicz_interval_of_fuzzyIntervals
    (pAB pBC : FuzzyQuantifierParams)
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds pAB profileAB)
    (hBC : fuzzyIntervalHolds pBC profileBC) :
    max 0 (pAB.LPC + pBC.LPC - 1) ≤
        max 0 (nearOneFraction pAB profileAB + nearOneFraction pBC profileBC - 1) ∧
      max 0 (nearOneFraction pAB profileAB + nearOneFraction pBC profileBC - 1) ≤
        max 0 (pAB.UPC + pBC.UPC - 1) := by
  simpa [qfmLukasiewicz] using
    qfm_compose_interval_of_fuzzyIntervals qfmLukasiewicz pAB pBC profileAB profileBC hAB hBC

/-- Probabilistic-sum QFM specialization of interval transport. -/
theorem qfmProbSum_interval_of_fuzzyIntervals
    (pAB pBC : FuzzyQuantifierParams)
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds pAB profileAB)
    (hBC : fuzzyIntervalHolds pBC profileBC) :
    (pAB.LPC + pBC.LPC - pAB.LPC * pBC.LPC) ≤
        (nearOneFraction pAB profileAB + nearOneFraction pBC profileBC -
          nearOneFraction pAB profileAB * nearOneFraction pBC profileBC) ∧
      (nearOneFraction pAB profileAB + nearOneFraction pBC profileBC -
          nearOneFraction pAB profileAB * nearOneFraction pBC profileBC) ≤
        (pAB.UPC + pBC.UPC - pAB.UPC * pBC.UPC) := by
  simpa [qfmProbSum] using
    qfm_compose_interval_of_fuzzyIntervals qfmProbSum pAB pBC profileAB profileBC hAB hBC

/-- One-call API lemma:
bundle operator + selector fixtures + profile assumptions into a reusable bound object. -/
noncomputable def qfm_compose_interval_bundle
    (q : QFMCompose)
    (pAB pBC : FuzzyQuantifierParams)
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds pAB profileAB)
    (hBC : fuzzyIntervalHolds pBC profileBC) :
    QFMSyllogismEnvelope :=
  let h := qfm_compose_interval_of_fuzzyIntervals q pAB pBC profileAB profileBC hAB hBC
  { lower := q.comp pAB.LPC pBC.LPC
    upper := q.comp pAB.UPC pBC.UPC
    score := q.comp (nearOneFraction pAB profileAB) (nearOneFraction pBC profileBC)
    lower_le_score := h.1
    score_le_upper := h.2 }

/-- If `LPC ≤ PCL`, interval-style truth implies crisp-leaning `ForAll`. -/
theorem fuzzyInterval_implies_fuzzyForAll
    (p : FuzzyQuantifierParams) (profile : U → ℝ)
    (h : p.PCL ≤ p.LPC)
    (hInt : fuzzyIntervalHolds p profile) :
    fuzzyForAllHolds p profile := by
  unfold fuzzyIntervalHolds fuzzyForAllHolds at *
  exact le_trans h hInt.1

/-- Fuzzy existential generalization:
if one witness is near-one, the existential score is strictly positive. -/
theorem fuzzyExistsScore_pos_of_witness_nearOne
    [Nonempty U]
    (p : FuzzyQuantifierParams) (profile : U → ℝ) (c : U)
    (hc : nearOne p (profile c)) :
    0 < fuzzyExistsScore p profile := by
  have hcount_pos : 0 < witnessCount (fun u => nearOne p (profile u)) := by
    unfold witnessCount
    exact Fintype.card_pos_iff.mpr ⟨⟨c, hc⟩⟩
  have hcard_pos_nat : 0 < Fintype.card U := by
    exact Fintype.card_pos_iff.mpr ⟨Classical.choice inferInstance⟩
  have hcard_ne : Fintype.card U ≠ 0 := Nat.ne_of_gt hcard_pos_nat
  have hcount_pos_real : 0 < (witnessCount (fun u => nearOne p (profile u)) : ℝ) := by
    exact_mod_cast hcount_pos
  have hcard_pos_real : 0 < (Fintype.card U : ℝ) := by
    exact_mod_cast hcard_pos_nat
  unfold fuzzyExistsScore nearOneFraction witnessFraction
  have hdiv : 0 < (witnessCount (fun u => nearOne p (profile u)) : ℝ) / (Fintype.card U : ℝ) :=
    div_pos hcount_pos_real hcard_pos_real
  simpa [hcard_ne] using hdiv

/-- Fuzzy universal specification (threshold-1 form):
if fuzzy-`ForAll` holds at threshold `PCL = 1`, every instance is near-one. -/
theorem nearOne_of_fuzzyForAll_eq_one
    [Nonempty U]
    (p : FuzzyQuantifierParams) (profile : U → ℝ) (c : U)
    (hForAll : fuzzyForAllHolds p profile)
    (hPCL : p.PCL = 1) :
    nearOne p (profile c) := by
  have hfrac_ge : (1 : ℝ) ≤ nearOneFraction p profile := by
    simpa [fuzzyForAllHolds, hPCL] using hForAll
  have hfrac_le : nearOneFraction p profile ≤ 1 := (nearOneFraction_in_unit p profile).2
  have hfrac_eq : nearOneFraction p profile = 1 := le_antisymm hfrac_le hfrac_ge
  by_contra hc
  have hcard_lt : witnessCount (fun u => nearOne p (profile u)) < Fintype.card U := by
    simpa [witnessCount] using
      (Fintype.card_subtype_lt (p := fun u => nearOne p (profile u)) hc)
  have hcard_pos_nat : 0 < Fintype.card U := by
    exact Fintype.card_pos_iff.mpr ⟨c⟩
  have hcard_ne : Fintype.card U ≠ 0 := Nat.ne_of_gt hcard_pos_nat
  have hnum_lt : (witnessCount (fun u => nearOne p (profile u)) : ℝ) < (Fintype.card U : ℝ) := by
    exact_mod_cast hcard_lt
  have hden_pos : 0 < (Fintype.card U : ℝ) := by
    exact_mod_cast hcard_pos_nat
  have hfrac_lt : nearOneFraction p profile < 1 := by
    unfold nearOneFraction witnessFraction
    have hdiv_lt :
        (witnessCount (fun u => nearOne p (profile u)) : ℝ) / (Fintype.card U : ℝ) <
          (Fintype.card U : ℝ) / (Fintype.card U : ℝ) := by
      exact div_lt_div_of_pos_right hnum_lt hden_pos
    have hden_ne : (Fintype.card U : ℝ) ≠ 0 := by
      exact_mod_cast hcard_ne
    have : (witnessCount (fun u => nearOne p (profile u)) : ℝ) / (Fintype.card U : ℝ) < 1 := by
      simpa [hden_ne] using hdiv_lt
    simpa [hcard_ne] using this
  have hbad : (1 : ℝ) < 1 := by
    rw [hfrac_eq] at hfrac_lt
    exact hfrac_lt
  exact (lt_irrefl (1 : ℝ)) hbad

end Profiles

end Mettapedia.Logic.PLNFirstOrder
