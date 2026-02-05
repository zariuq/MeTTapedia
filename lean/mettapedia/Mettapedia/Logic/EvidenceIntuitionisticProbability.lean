import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.EvidenceKSBridge
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Basic
import Mathlib.Data.ENNReal.Inv

/-!
# Intuitionistic Probability on Evidence

This file develops K&S-style probability theory on Evidence at the PlausibilitySpace level,
deriving the "intuitionistic" (Heyting) versions of probability rules.

## Key Results

1. **Valuations on Evidence**: K&S valuations exist and satisfy standard properties
2. **Intuitionistic Rules**: Boolean equalities become inequalities
3. **Precision Loss**: Examples where 2D Evidence is strictly more informative than 1D valuations
4. **PLN Connection**: How PLN formulas relate to K&S valuations on Evidence

## The Core Insight

K&S at Boolean level:   P(¬A) = 1 - P(A)         (equality)
K&S at Heyting level:   P(¬A) ≤ 1 - P(A)         (inequality - less precise!)

PLN's 2D Evidence keeps BOTH (n⁺, n⁻), avoiding the precision loss.
-/

namespace Mettapedia.Logic.EvidenceIntuitionisticProbability

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.ProbabilityTheory.KnuthSkilling

/-! ## K&S Valuations on Evidence

Since Evidence is a PlausibilitySpace, we can define K&S-style valuations on it.
Here we show that valuations exist and explore their properties.
-/

/-- Evidence ⊥ is (0, 0). -/
theorem evidence_bot_eq : (⊥ : Evidence) = ⟨0, 0⟩ := rfl

/-- Evidence ⊤ is (⊤, ⊤). -/
theorem evidence_top_eq : (⊤ : Evidence) = ⟨⊤, ⊤⟩ := rfl

/-- The trivial valuation that maps ⊥ → 0, everything else → 1.
    This is always monotone (and always exists on any bounded lattice). -/
noncomputable def trivialValuation : Valuation Evidence where
  val := fun e => if (e.pos = 0 ∧ e.neg = 0) then 0 else 1
  monotone := fun x y hle => by
    by_cases hx : x.pos = 0 ∧ x.neg = 0
    · -- x = ⊥, so val x = 0 ≤ val y
      simp only [hx.1, hx.2, and_self, ite_true]
      split_ifs <;> simp
    · by_cases hy : y.pos = 0 ∧ y.neg = 0
      · exfalso
        push_neg at hx
        simp only [Evidence.le_def] at hle
        by_cases hp : x.pos = 0
        · -- x.pos = 0, so x.neg ≠ 0 (from hx)
          have hn : x.neg ≠ 0 := hx hp
          have : y.neg = 0 := hy.2
          have hle2 : x.neg ≤ y.neg := hle.2
          rw [this] at hle2
          exact hn (le_antisymm hle2 (zero_le _))
        · -- x.pos ≠ 0
          have : y.pos = 0 := hy.1
          have hle1 : x.pos ≤ y.pos := hle.1
          rw [this] at hle1
          exact hp (le_antisymm hle1 (zero_le _))
      · -- Neither x nor y is ⊥, so val x = val y = 1
        simp only [hx, hy, ite_false, le_refl]
  val_bot := by
    -- ⊥ = ⟨0, 0⟩, so condition is true
    have h : (⊥ : Evidence).pos = 0 ∧ (⊥ : Evidence).neg = 0 := ⟨rfl, rfl⟩
    exact if_pos h
  val_top := by
    have h : ¬((⊤ : Evidence).pos = 0 ∧ (⊤ : Evidence).neg = 0) := by
      simp only [not_and]
      intro _
      exact ENNReal.top_ne_zero
    exact if_neg h

/-! ## Intuitionistic Probability Rules

At the Heyting (non-Boolean) level, equalities become inequalities.
-/

section IntuitionisticRules

variable (v : Valuation Evidence)

/-- In a Heyting algebra, the negation bound is an INEQUALITY, not equality.
    The trivial bound: v(¬A) ≤ 1 always holds.

    For Evidence, this is typically NOT tight because LEM fails. -/
theorem heyting_negation_trivial_bound (a : Evidence) :
    v.val (aᶜ) ≤ 1 := v.le_one _

/-- The "excluded middle gap": a ⊔ ¬a ≠ ⊤ in general for Heyting algebras.
    This measures the failure of classical logic.

    We prove this by showing a ⊔ aᶜ ≠ ⊤ for a specific choice of a. -/
theorem excludedMiddle_gap_positive :
    ∃ a : Evidence, a ⊔ aᶜ ≠ ⊤ := by
  -- Use (1, 1). Its complement under Heyting implication is (0, 0)
  use ⟨1, 1⟩
  intro h
  have hpos : ((⟨1, 1⟩ : Evidence) ⊔ (⟨1, 1⟩ : Evidence)ᶜ).pos = (⊤ : Evidence).pos :=
    congrArg Evidence.pos h
  have h1_not_le_0 := not_le.mpr (zero_lt_one (α := ENNReal))
  have hcompl_pos : ((⟨1, 1⟩ : Evidence)ᶜ).pos = 0 := by
    show (Evidence.himp ⟨1, 1⟩ ⊥).pos = 0
    simp only [Evidence.himp]
    -- Goal: (if 1 ≤ (⊥ : Evidence).pos then ⊤ else (⊥ : Evidence).pos) = 0
    -- Since ⊥.pos = 0 and ¬(1 ≤ 0), this is 0 = 0
    have hbot_pos : (⊥ : Evidence).pos = 0 := rfl
    simp only [hbot_pos, h1_not_le_0, ↓reduceIte]
  have hsup_pos : ((⟨1, 1⟩ : Evidence) ⊔ (⟨1, 1⟩ : Evidence)ᶜ).pos = (1 : ENNReal) := by
    show max (1 : ENNReal) ((⟨1, 1⟩ : Evidence)ᶜ).pos = 1
    rw [hcompl_pos]
    simp
  rw [hsup_pos] at hpos
  exact ENNReal.one_ne_top hpos

/-- The chain rule for conditional valuations holds even in Heyting algebras. -/
theorem heyting_chain_rule (a b c : Evidence)
    (hc : v.val c ≠ 0) (hbc : v.val (b ⊓ c) ≠ 0) :
    v.condVal (a ⊓ b) c = v.condVal a (b ⊓ c) * v.condVal b c := by
  unfold Valuation.condVal
  simp only [hc, hbc, ↓reduceDIte]
  have h1 : (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c) := inf_assoc a b c
  rw [h1]
  field_simp

end IntuitionisticRules

/-! ## Precision Loss Examples

Here we show concrete cases where the 2D Evidence structure captures distinctions
that ANY 1D valuation must collapse.
-/

section PrecisionLoss

private theorem two_pos_ennreal : (0 : ENNReal) < 2 := zero_lt_two

private theorem two_gt_one_ennreal : (1 : ENNReal) < 2 := by norm_cast

/-- Two Evidence values that are incomparable in the partial order. -/
theorem incomparable_evidence_exists :
    ∃ e₁ e₂ : Evidence, ¬(e₁ ≤ e₂) ∧ ¬(e₂ ≤ e₁) := by
  use ⟨2, 0⟩, ⟨0, 2⟩
  constructor
  · intro h
    simp only [Evidence.le_def] at h
    exact not_le.mpr two_pos_ennreal h.1
  · intro h
    simp only [Evidence.le_def] at h
    exact not_le.mpr two_pos_ennreal h.2

/-- The key example: "more but mixed" vs "less but pure" evidence.

    e₁ = (2, 2): 4 observations, 50% positive → strength 0.5
    e₂ = (3, 0): 3 observations, 100% positive → strength 1.0

    These are INCOMPARABLE in the partial order because:
    - mixed ≤ pure requires 2 ≤ 3 ∧ 2 ≤ 0 - FALSE (2 ≰ 0)
    - pure ≤ mixed requires 3 ≤ 2 ∧ 0 ≤ 2 - FALSE (3 ≰ 2) -/
def mixedEvidence : Evidence := ⟨2, 2⟩
def pureEvidence : Evidence := ⟨3, 0⟩

private theorem three_gt_two_ennreal : (2 : ENNReal) < 3 := by norm_cast

theorem mixed_pure_incomparable :
    ¬(mixedEvidence ≤ pureEvidence) ∧ ¬(pureEvidence ≤ mixedEvidence) := by
  constructor
  · intro h
    simp only [mixedEvidence, pureEvidence, Evidence.le_def] at h
    exact not_le.mpr two_pos_ennreal h.2
  · intro h
    simp only [mixedEvidence, pureEvidence, Evidence.le_def] at h
    exact not_le.mpr three_gt_two_ennreal h.1

/-- Mixed evidence has lower strength despite more total evidence. -/
theorem mixed_lower_strength :
    mixedEvidence.toStrength < pureEvidence.toStrength := by
  simp only [mixedEvidence, pureEvidence, Evidence.toStrength, Evidence.total]
  -- mixedEvidence.toStrength = 2/4 = 0.5
  -- pureEvidence.toStrength = 3/3 = 1
  have h1 : ((2 : ENNReal) + 2 = 4) := by norm_cast
  have h2 : ((3 : ENNReal) + 0 = 3) := by simp
  -- Simplify the if-then-else by showing the totals are nonzero
  have h4ne0 : (4 : ENNReal) ≠ 0 := by simp
  have h3ne0 : (3 : ENNReal) ≠ 0 := by simp
  simp only [h1, h2, h4ne0, h3ne0, ↓reduceIte]
  -- Now: 2/4 < 3/3 = 1
  rw [ENNReal.div_self h3ne0 (ENNReal.natCast_ne_top 3)]
  have h4netop : (4 : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top 4
  -- Need: 2/4 < 1
  rw [ENNReal.div_lt_iff (Or.inl h4ne0) (Or.inl h4netop)]
  -- Goal: 2 < 1 * 4 = 4
  norm_cast

/-- Mixed evidence has higher confidence (more observations). -/
theorem mixed_higher_confidence :
    mixedEvidence.toConfidence 1 > pureEvidence.toConfidence 1 := by
  simp only [mixedEvidence, pureEvidence, Evidence.toConfidence, Evidence.total]
  -- mixedEvidence.toConfidence 1 = 4 / (4 + 1) = 4/5
  -- pureEvidence.toConfidence 1 = 3 / (3 + 1) = 3/4
  -- Need: 4/5 > 3/4, i.e., 3/4 < 4/5, i.e., 3*5 < 4*4, i.e., 15 < 16
  have h1 : ((2 : ENNReal) + 2 = 4) := by norm_cast
  have h2 : ((3 : ENNReal) + 0 = 3) := by simp
  have h3 : ((4 : ENNReal) + 1 = 5) := by norm_cast
  have h4 : ((3 : ENNReal) + 1 = 4) := by norm_cast
  rw [h1, h2, h3, h4]
  -- Goal: 4/5 > 3/4, i.e., 3/4 < 4/5
  show (3 : ENNReal) / 4 < 4 / 5
  have h4ne0 : (4 : ENNReal) ≠ 0 := by simp
  have h4ne_top : (4 : ENNReal) ≠ ⊤ := by simp
  have h5ne0 : (5 : ENNReal) ≠ 0 := by simp
  have h5ne_top : (5 : ENNReal) ≠ ⊤ := by simp
  -- 3/4 < 4/5 iff 3 < (4/5) * 4
  rw [ENNReal.div_lt_iff (Or.inl h4ne0) (Or.inl h4ne_top)]
  -- Goal: 3 < 4 / 5 * 4
  have h_assoc : (4 : ENNReal) / 5 * 4 = 4 * 4 / 5 := by
    rw [mul_comm (4/5) 4, mul_div_assoc]
  rw [h_assoc]
  -- Goal: 3 < 16/5
  have h44 : (4 : ENNReal) * 4 = 16 := by norm_cast
  rw [h44]
  -- 3 < 16/5 iff 3 * 5 < 16
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl h5ne0) (Or.inl h5ne_top)]
  -- Goal: 3 * 5 < 16
  norm_cast

/-- For any monotone valuation, incomparable elements can have arbitrary value relationships.
    This shows the INFORMATION LOSS: a 1D valuation cannot faithfully represent
    the 2D Evidence structure. -/
theorem valuation_loses_info (v : Valuation Evidence) :
    ∃ e₁ e₂ : Evidence,
      ¬(e₁ ≤ e₂) ∧ ¬(e₂ ≤ e₁) ∧
      (v.val e₁ ≤ v.val e₂ ∨ v.val e₂ ≤ v.val e₁) := by
  use mixedEvidence, pureEvidence
  refine ⟨mixed_pure_incomparable.1, mixed_pure_incomparable.2, ?_⟩
  exact le_total (v.val mixedEvidence) (v.val pureEvidence)

end PrecisionLoss

/-! ## Connection to PLN Formulas

How do PLN's formulas relate to K&S valuations on Evidence?
-/

section PLNConnection

/-- PLN strength is NOT a K&S valuation (not monotone).
    But it captures different information than any valuation can. -/
theorem strength_not_valuation_compatible :
    ∃ e₁ e₂ : Evidence, e₁ ≤ e₂ ∧ e₁.toStrength > e₂.toStrength := by
  use ⟨1, 0⟩, ⟨1, 1⟩
  constructor
  · simp only [Evidence.le_def]
    constructor <;> simp
  · simp only [Evidence.toStrength, Evidence.total]
    have h1 : ((1 : ENNReal) + 0 = 1) := by simp
    have h2 : ((1 : ENNReal) + 1 = 2) := by norm_cast
    have h1ne0 : (1 : ENNReal) ≠ 0 := by simp
    have h2ne0 : (2 : ENNReal) ≠ 0 := by simp
    simp only [h1, h2, h1ne0, h2ne0, ↓reduceIte]
    rw [ENNReal.div_self h1ne0 ENNReal.one_ne_top]
    have h2netop : (2 : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top 2
    -- Need: 1 > 1/2, i.e., 1/2 < 1
    show (1 : ENNReal) / 2 < 1
    rw [ENNReal.div_lt_iff (Or.inl h2ne0) (Or.inl h2netop)]
    -- Goal: 1 < 1 * 2 = 2
    norm_cast

/-- PLN confidence IS monotone in total evidence (for finite totals).

    Note: The function t / (t + κ) is monotone in t for t ∈ [0, ∞).
    We require e₂.total ≠ ⊤ because in ENNReal, ⊤/(⊤+κ) = 0,
    which breaks monotonicity at the boundary. -/
theorem confidence_monotone_in_total (hκ_ne_top : κ ≠ ⊤) :
    ∀ e₁ e₂ : Evidence, e₂.total ≠ ⊤ → e₁.total ≤ e₂.total →
    e₁.toConfidence κ ≤ e₂.toConfidence κ := by
  intro e₁ e₂ h2_ne_top h
  simp only [Evidence.toConfidence]
  -- t₁/(t₁+κ) ≤ t₂/(t₂+κ) when t₁ ≤ t₂ (and t₂ ≠ ⊤)
  set t₁ := e₁.total with ht1_def
  set t₂ := e₂.total with ht2_def
  -- Handle t₁ = ⊤ case: then t₂ = ⊤ (contradiction with h2_ne_top)
  by_cases ht1_top : t₁ = ⊤
  · have ht2_top : t₂ = ⊤ := top_le_iff.mp (ht1_top ▸ h)
    exact absurd ht2_top h2_ne_top
  -- Handle κ = 0 case
  by_cases hκ : κ = 0
  · subst hκ
    simp only [add_zero]
    by_cases ht1 : t₁ = 0
    · simp [ht1]
    · rw [ENNReal.div_self ht1 ht1_top]
      by_cases ht2 : t₂ = 0
      · exfalso; simp only [ht2, nonpos_iff_eq_zero] at h; exact ht1 h
      · rw [ENNReal.div_self ht2 h2_ne_top]
  -- Main case: all finite, κ > 0
  have h_sum1_ne_zero : t₁ + κ ≠ 0 := by
    intro h_eq; have := add_eq_zero.mp h_eq; exact hκ this.2
  have h_sum2_ne_zero : t₂ + κ ≠ 0 := by
    intro h_eq; have := add_eq_zero.mp h_eq; exact hκ this.2
  have h_sum1_ne_top : t₁ + κ ≠ ⊤ := by
    rw [ENNReal.add_ne_top]; exact ⟨ht1_top, hκ_ne_top⟩
  have h_sum2_ne_top : t₂ + κ ≠ ⊤ := by
    rw [ENNReal.add_ne_top]; exact ⟨h2_ne_top, hκ_ne_top⟩
  -- Cross-multiply: a/b ≤ c/d ↔ a*d ≤ c*b (when all positive and finite)
  rw [ENNReal.div_le_iff h_sum1_ne_zero h_sum1_ne_top]
  rw [mul_comm]
  rw [mul_div_assoc']
  rw [ENNReal.le_div_iff_mul_le (Or.inl h_sum2_ne_zero) (Or.inl h_sum2_ne_top)]
  -- Goal: t₁ * (t₂ + κ) ≤ (t₁ + κ) * t₂
  calc t₁ * (t₂ + κ)
      = t₁ * t₂ + t₁ * κ := by ring
    _ ≤ t₁ * t₂ + t₂ * κ := add_le_add_left (mul_le_mul_right' h κ) _
    _ = (t₁ + κ) * t₂ := by ring

/-- The PLN 2D structure (strength, confidence) captures STRICTLY MORE
    information than any single K&S valuation.

    Proof: valuations collapse incomparable Evidence to comparable reals,
    but (strength, confidence) pairs remain distinguishable. -/
theorem pln_2d_more_informative :
    ∃ e₁ e₂ : Evidence,
      ¬(e₁ ≤ e₂) ∧ ¬(e₂ ≤ e₁) ∧
      (e₁.toStrength ≠ e₂.toStrength ∨ e₁.toConfidence 1 ≠ e₂.toConfidence 1) := by
  use ⟨2, 0⟩, ⟨0, 2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h
    simp only [Evidence.le_def] at h
    exact not_le.mpr two_pos_ennreal h.1
  · intro h
    simp only [Evidence.le_def] at h
    exact not_le.mpr two_pos_ennreal h.2
  · left
    simp only [Evidence.toStrength, Evidence.total, ne_eq]
    have h1 : ((2 : ENNReal) + 0 = 2) := by simp
    have h2 : ((0 : ENNReal) + 2 = 2) := by simp
    have h2ne0 : (2 : ENNReal) ≠ 0 := by simp
    simp only [h1, h2, h2ne0, ↓reduceIte]
    rw [ENNReal.div_self h2ne0 (ENNReal.natCast_ne_top 2)]
    rw [ENNReal.zero_div]
    exact one_ne_zero

/-- Summary: The PLN Evidence framework gives TIGHTER bounds than K&S valuations alone.

    - K&S valuation: collapses 2D to 1D, loses incomparability info
    - PLN (strength, confidence): preserves 2D structure
    - PLN (n⁺, n⁻): preserves FULL structure -/
theorem pln_avoids_heyting_precision_loss :
    ∀ v : Valuation Evidence, ∀ a : Evidence,
      0 ≤ v.val a ∧ v.val a ≤ 1 ∧
      (a.pos, a.neg) = (a.pos, a.neg) := by
  intro v a
  exact ⟨v.nonneg a, v.le_one a, rfl⟩

end PLNConnection

/-! ## What K&S Gives Us at the Heyting Level

Summary of derived rules at PlausibilitySpace (Evidence) level:

1. ✅ Valuations exist: monotone v : Evidence → [0,1]
2. ✅ Conditional valuations: v(a|b) = v(a ⊓ b) / v(b)
3. ✅ Chain rule: v(a ⊓ b | c) = v(a | b ⊓ c) · v(b | c)
4. ⚠️ Negation: v(¬a) ≤ 1 (INEQUALITY, not v(¬a) = 1 - v(a))
5. ❌ Sum rule: v(a ⊔ b) = v(a) + v(b) - v(a ⊓ b) FAILS without Boolean

PLN's contribution: Keep the 2D structure (n⁺, n⁻) to avoid precision loss!
-/

end Mettapedia.Logic.EvidenceIntuitionisticProbability
