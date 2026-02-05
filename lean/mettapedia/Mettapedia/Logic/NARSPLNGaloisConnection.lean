/-
# Galois Connection Between NARS and PLN

This file establishes the adjunction L ⊣ U between NARS and PLN truth value systems.

## The Theory

- **L (Lower adjoint)**: NARS → PLN - embeds NARS with uniform prior
- **U (Upper adjoint)**: PLN → NARS - forgets prior information
- **Adjunction**: L(x) ≤ y ⟺ x ≤ U(y)

This formalizes the claim that:
- PLN is "more informative" because it includes prior structure
- NARS is a "projection" of PLN that forgets priors
- The adjunction shows NARS can be simulated in PLN

## References

- Goertzel et al., "PLN and NARS Comparison" (2024)
- Wang, "Non-Axiomatic Logic" (2013)
-/

import Mathlib.Tactic
import Mathlib.Order.GaloisConnection.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.EvidenceClass
import Mettapedia.Logic.NARSMettaTruthFunctions
import Mettapedia.Logic.NARSEvidenceBridge
import Mettapedia.Logic.NARSSecondOrderProbability

namespace Mettapedia.Logic.NARSPLNGaloisConnection

open scoped ENNReal
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.NARSMettaTruthFunctions
open Mettapedia.Logic.NARSEvidenceBridge
open Mettapedia.Logic.NARSSecondOrderProbability

/-! ## NARS Space with Informativeness Order

The informativeness order on NARS truth values is defined by evidence weight.
More confidence means more evidence, hence more informative.
-/

/-- A NARS truth value with explicit validity bounds.
    This is a subtype of TV that enforces the probabilistic constraints. -/
structure NARSTruthValue where
  f : ℝ
  c : ℝ
  f_nonneg : 0 ≤ f
  f_le_one : f ≤ 1
  c_nonneg : 0 ≤ c
  c_lt_one : c < 1

namespace NARSTruthValue

/-- Convert NARSTruthValue to TV. -/
def toTV (n : NARSTruthValue) : TV := ⟨n.f, n.c⟩

/-- NARSTruthValue satisfies IsProbTV. -/
theorem isProbTV (n : NARSTruthValue) : IsProbTV n.toTV :=
  ⟨n.f_nonneg, n.f_le_one, n.c_nonneg, n.c_lt_one⟩

/-- Evidence weight of a NARS truth value. -/
noncomputable def weight (n : NARSTruthValue) : ℝ := c2w n.c

/-- Evidence weight is non-negative. -/
theorem weight_nonneg (n : NARSTruthValue) : 0 ≤ n.weight := by
  unfold weight c2w
  have h : 0 < 1 - n.c := sub_pos.mpr n.c_lt_one
  exact div_nonneg n.c_nonneg (le_of_lt h)

end NARSTruthValue

/-- Informativeness order on NARS: compare by evidence weight. -/
instance : LE NARSTruthValue where
  le n1 n2 := n1.weight ≤ n2.weight

/-- Informativeness is a preorder. -/
instance : Preorder NARSTruthValue where
  le := (· ≤ ·)
  le_refl n := le_refl n.weight
  le_trans n1 n2 n3 (h1 : n1.weight ≤ n2.weight) (h2 : n2.weight ≤ n3.weight) :=
    (le_trans h1 h2 : n1.weight ≤ n3.weight)

/-! ## PLN Space with Informativeness Order

PLN beliefs consist of evidence counts with an explicit prior context.
The informativeness order is based on total evidence count.
-/

/-- A PLN belief: evidence + prior context. -/
structure PLNBelief where
  evidence : Evidence
  prior : BinaryContext

namespace PLNBelief

/-- Total evidence count. -/
noncomputable def totalEvidence (b : PLNBelief) : ℝ≥0∞ := b.evidence.total

end PLNBelief

/-- Informativeness order on PLN: compare by total evidence. -/
instance : LE PLNBelief where
  le b1 b2 := b1.totalEvidence ≤ b2.totalEvidence

/-- Informativeness is a preorder. -/
instance : Preorder PLNBelief where
  le := (· ≤ ·)
  le_refl b := le_refl b.totalEvidence
  le_trans b1 b2 b3 (h1 : b1.totalEvidence ≤ b2.totalEvidence) (h2 : b2.totalEvidence ≤ b3.totalEvidence) :=
    (le_trans h1 h2 : b1.totalEvidence ≤ b3.totalEvidence)

/-! ## The Functors L and U -/

/-- L (Lower adjoint): NARS → PLN

Embeds a NARS truth value into PLN by:
1. Converting confidence to evidence counts via c2w
2. Adding a uniform (Laplace) prior

This is the "canonical embedding" of NARS into PLN. -/
noncomputable def L (n : NARSTruthValue) : PLNBelief :=
  let w := c2w n.c
  { evidence := ⟨ENNReal.ofReal (n.f * w), ENNReal.ofReal ((1 - n.f) * w)⟩
  , prior := BinaryContext.uniform }

/-- Helper: total / (total + 1) < 1 for finite total. -/
theorem ennreal_div_add_one_lt_one (total : ℝ≥0∞) (htop : total ≠ ⊤) :
    total / (total + 1) < 1 := by
  have hne_top : total + 1 ≠ ⊤ := by
    rw [ENNReal.add_ne_top]; exact ⟨htop, ENNReal.one_ne_top⟩
  have hne_zero : total + 1 ≠ 0 := by simp
  rw [ENNReal.div_lt_iff (Or.inl hne_zero) (Or.inl hne_top)]
  simp only [one_mul]
  exact ENNReal.lt_add_right htop one_ne_zero

/-- When total = ⊤, we have ⊤ / (⊤ + 1) = 0. -/
theorem ennreal_top_div_top_add_one : (⊤ : ℝ≥0∞) / (⊤ + 1) = 0 := by
  simp only [ENNReal.top_div]
  simp

/-- U (Upper adjoint): PLN → NARS

Projects a PLN belief to NARS by:
1. Computing the posterior mean (strength)
2. Converting total evidence to confidence via w2c

This "forgets" the prior structure. -/
noncomputable def U (b : PLNBelief) : NARSTruthValue where
  f := if b.evidence.total = 0 then 0.5 else (b.evidence.pos / b.evidence.total).toReal
  c := (b.evidence.total / (b.evidence.total + 1)).toReal
  f_nonneg := by
    split_ifs with h
    · linarith
    · exact ENNReal.toReal_nonneg
  f_le_one := by
    split_ifs with h
    · linarith
    · have hle : b.evidence.pos / b.evidence.total ≤ 1 := by
        apply ENNReal.div_le_of_le_mul
        rw [one_mul]
        exact le_add_of_nonneg_right (zero_le _)
      have hne_top : b.evidence.pos / b.evidence.total ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top hle
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono ENNReal.one_ne_top hle
  c_nonneg := ENNReal.toReal_nonneg
  c_lt_one := by
    by_cases htop : b.evidence.total = ⊤
    · simp only [htop, ennreal_top_div_top_add_one, ENNReal.toReal_zero]
      linarith
    · have hlt := ennreal_div_add_one_lt_one b.evidence.total htop
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_strict_mono ENNReal.one_ne_top hlt

/-! ## Key Lemmas for the Galois Connection -/

/-- L preserves evidence weight: total(L(n)) = ofReal(c2w(n.c)).

This is the key property that connects NARS confidence to PLN evidence. -/
theorem L_total_eq_weight (n : NARSTruthValue) :
    (L n).totalEvidence = ENNReal.ofReal (c2w n.c) := by
  simp only [L, PLNBelief.totalEvidence, Evidence.total]
  -- pos + neg = f*w + (1-f)*w = w
  have hf : 0 ≤ n.f := n.f_nonneg
  have h1f : 0 ≤ 1 - n.f := sub_nonneg.mpr n.f_le_one
  have hw : 0 ≤ c2w n.c := n.weight_nonneg
  have hfw : 0 ≤ n.f * c2w n.c := mul_nonneg hf hw
  have h1fw : 0 ≤ (1 - n.f) * c2w n.c := mul_nonneg h1f hw
  rw [← ENNReal.ofReal_add hfw h1fw]
  congr 1
  ring

/-- U recovers weight as confidence: c2w((U b).c) ≈ total(b).

Note: This is only exact when total(b) ∈ ℝ (not ⊤). -/
theorem U_weight_eq_total (b : PLNBelief) (htop : b.evidence.total ≠ ⊤) :
    c2w (U b).c = b.evidence.total.toReal := by
  simp only [U, c2w]
  set total := b.evidence.total with htotal_def
  have hne_top : total + 1 ≠ ⊤ := by
    rw [ENNReal.add_ne_top]; exact ⟨htop, ENNReal.one_ne_top⟩
  have hlt := ennreal_div_add_one_lt_one total htop
  have hc : (total / (total + 1)).toReal < 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_strict_mono ENNReal.one_ne_top hlt
  have hne1 : 1 - (total / (total + 1)).toReal ≠ 0 := by linarith
  -- c / (1 - c) where c = total / (total + 1)
  -- = (total/(total+1)) / (1 - total/(total+1))
  -- = (total/(total+1)) / (1/(total+1))
  -- = total
  have hdiv_ne_top : total / (total + 1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_of_lt hlt)
  rw [ENNReal.toReal_div]
  -- Now goal is (total.toReal / (total+1).toReal) / (1 - (total.toReal / (total+1).toReal))
  have hadd_pos : (0 : ℝ) < (total + 1).toReal := by
    rw [ENNReal.toReal_add htop ENNReal.one_ne_top]
    simp only [ENNReal.toReal_one]
    linarith [ENNReal.toReal_nonneg (a := total)]
  have hadd_ne_zero : (total + 1).toReal ≠ 0 := ne_of_gt hadd_pos
  -- 1 - total.toReal/(total+1).toReal = 1/(total+1).toReal
  have h1mc : 1 - total.toReal / (total + 1).toReal = 1 / (total + 1).toReal := by
    rw [ENNReal.toReal_add htop ENNReal.one_ne_top]
    simp only [ENNReal.toReal_one]
    field_simp
    ring
  rw [h1mc]
  -- (total.toReal / (total+1).toReal) / (1 / (total+1).toReal) = total.toReal
  field_simp

/-- Round-trip: U ∘ L preserves confidence. -/
theorem U_L_conf_round_trip (n : NARSTruthValue) : (U (L n)).c = n.c := by
  simp only [U, L, Evidence.total]
  have hw : c2w n.c ≥ 0 := n.weight_nonneg
  have hf : 0 ≤ n.f := n.f_nonneg
  have h1f : 0 ≤ 1 - n.f := sub_nonneg.mpr n.f_le_one
  have hfw : 0 ≤ n.f * c2w n.c := mul_nonneg hf hw
  have h1fw : 0 ≤ (1 - n.f) * c2w n.c := mul_nonneg h1f hw
  -- Total = f*w + (1-f)*w = w = c2w(c)
  have htotal : ENNReal.ofReal (n.f * c2w n.c) + ENNReal.ofReal ((1 - n.f) * c2w n.c) =
      ENNReal.ofReal (c2w n.c) := by
    rw [← ENNReal.ofReal_add hfw h1fw]
    congr 1; ring
  rw [htotal]
  -- Now: (w / (w + 1)).toReal = w2c(w) = c
  have hne_top : ENNReal.ofReal (c2w n.c) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hne_top' : ENNReal.ofReal (c2w n.c) + 1 ≠ ⊤ := by
    rw [ENNReal.add_ne_top]; exact ⟨hne_top, ENNReal.one_ne_top⟩
  rw [ENNReal.toReal_div]
  rw [ENNReal.toReal_add hne_top ENNReal.one_ne_top]
  simp only [ENNReal.toReal_one, ENNReal.toReal_ofReal hw]
  -- Now: c2w(c) / (c2w(c) + 1) = w2c(c2w(c)) = c
  exact w2c_c2w_id n.c n.c_nonneg n.c_lt_one

/-- Round-trip: U ∘ L preserves frequency (when c > 0). -/
theorem U_L_freq_round_trip (n : NARSTruthValue) (hc : n.c > 0) : (U (L n)).f = n.f := by
  simp only [U, L, Evidence.total]
  have hw : c2w n.c ≥ 0 := n.weight_nonneg
  have hf : 0 ≤ n.f := n.f_nonneg
  have h1f : 0 ≤ 1 - n.f := sub_nonneg.mpr n.f_le_one
  have hfw : 0 ≤ n.f * c2w n.c := mul_nonneg hf hw
  have h1fw : 0 ≤ (1 - n.f) * c2w n.c := mul_nonneg h1f hw
  have htotal : ENNReal.ofReal (n.f * c2w n.c) + ENNReal.ofReal ((1 - n.f) * c2w n.c) =
      ENNReal.ofReal (c2w n.c) := by
    rw [← ENNReal.ofReal_add hfw h1fw]
    congr 1; ring
  rw [htotal]
  -- w ≠ 0 when c > 0
  have hw0 : c2w n.c ≠ 0 := by
    unfold c2w
    have h1c : 0 < 1 - n.c := sub_pos.mpr n.c_lt_one
    exact div_ne_zero (ne_of_gt hc) (ne_of_gt h1c)
  have hw_pos : 0 < c2w n.c := lt_of_le_of_ne hw (Ne.symm hw0)
  have hne0 : ENNReal.ofReal (c2w n.c) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact hw_pos
  simp only [hne0, ↓reduceIte]
  -- pos / total = (f * w) / w = f
  rw [ENNReal.toReal_div]
  rw [ENNReal.toReal_ofReal hfw, ENNReal.toReal_ofReal hw]
  rw [mul_div_assoc, div_self hw0]
  simp

/-! ## The Galois Connection

The main theorem: L ⊣ U forms a Galois connection between NARS and PLN.
-/

/-- The Galois connection: L(n) ≤ b ↔ n ≤ U(b) (for finite evidence)

This says that embedding NARS into PLN and then comparing is equivalent to
first projecting PLN to NARS and then comparing.

Note: This requires finite PLN evidence because ENNReal has ⊤ / ⊤ = 0, which
makes U(b) discontinuous at infinity. For finite evidence, the adjunction
properly captures that PLN is more informative than NARS.

Proof idea:
- L(n) ≤ b means total(L(n)) ≤ total(b), i.e., c2w(n.c) ≤ total(b)
- n ≤ U(b) means c2w(n.c) ≤ c2w(U(b).c) ≈ total(b)
- These are equivalent by the weight-total correspondence
-/
theorem galoisConnection_L_U_finite (b : PLNBelief) (hb : b.evidence.total ≠ ⊤) (n : NARSTruthValue) :
    (L n).totalEvidence ≤ b.totalEvidence ↔ n.weight ≤ (U b).weight := by
  constructor
  · -- L(n) ≤ b → n ≤ U(b)
    intro hLn
    rw [L_total_eq_weight] at hLn
    simp only [PLNBelief.totalEvidence] at hLn
    have heq := U_weight_eq_total b hb
    simp only [NARSTruthValue.weight]
    rw [heq]
    rw [← ENNReal.ofReal_toReal hb] at hLn
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hLn
  · -- n ≤ U(b) → L(n) ≤ b
    intro hU
    simp only [NARSTruthValue.weight] at hU
    rw [L_total_eq_weight]
    simp only [PLNBelief.totalEvidence]
    have heq := U_weight_eq_total b hb
    rw [heq] at hU
    rw [ENNReal.ofReal_le_iff_le_toReal hb]
    exact hU

/-- For finite PLN beliefs, L and U form an adjunction on informativeness. -/
theorem L_le_iff_le_U (b : PLNBelief) (hb : b.evidence.total ≠ ⊤) (n : NARSTruthValue) :
    L n ≤ b ↔ n ≤ U b :=
  galoisConnection_L_U_finite b hb n

/-! ## Consequences of the Galois Connection -/

/-!
TODO: Relate the uniform-prior PLN strength to the NARS frequency in the large-evidence limit.

This should be stated as an actual asymptotic theorem (e.g. a `tendsto` statement) and should
reuse the existing quantitative bounds for Beta-family posteriors (Laplace/Jeffreys, etc.) rather
than being encoded as a `True` placeholder.
-/

end Mettapedia.Logic.NARSPLNGaloisConnection
