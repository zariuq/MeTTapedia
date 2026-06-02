import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLNConjunction

/-!
# PLN Confidence-Weight View and the Historical Raw-Min Bug

This file formalizes a critical insight connecting:
1. The hypergeometric mode bound: mode ≤ min(a, b)
2. PLN's confidence-weight transformation
3. Why count-level arguments must be stated in weight/evidence space

## The Core Insight

The hypergeometric distribution operates on **counts** (evidence weights).
The mode bound `mode ≤ min(a, b)` tells us that combined evidence
is bounded by the minimum of input evidence counts.

Since confidence `c` is a nonlinear transformation of weight `w`:
  c = w / (w + k)

the historical bug was not the order operation `min c₁ c₂` by itself.
For fixed `k`, confidence and weight are monotone coordinates, so taking
the smaller confidence corresponds to the smaller weight. The bug was
feeding that confidence back through `w2c` as if it were already a
weight:

  w2c(min(c₁, c₂))

The safe count-level route is:
1. Convert confidences to weights: w = c2w(c)
2. Take min in weight space: min(w₁, w₂)
3. Convert back to confidence: w2c(min(w₁, w₂))

## Historical Note

This file explains the PLN bug discovered in early 2025 where
`w2c(min(c₁, c₂))` was incorrectly used instead of
`w2c(min(c2w(c₁), c2w(c₂)))`, causing 10-50% underestimation.

## References

- Goertzel et al., "Probabilistic Logic Networks" (2009)
- Nil's nuPLN.tex, Section on conjunction confidence

## Related Files

- `PLNConjunction.lean`: Hypergeometric distribution and mode bounds
- `PLNFrechetBounds.lean`: Measure-theoretic Fréchet bounds (proven)
- `EvidenceQuantale.lean`: Quantale structure on BinaryEvidence
-/

namespace Mettapedia.Logic.PLNConfidenceWeight

open scoped ENNReal
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNConjunction

/-! ## The Confidence-Weight Bijection

The fundamental transformation between bounded confidence and unbounded weight.
-/

/-- Weight-to-Confidence transformation.
    c = w / (w + k) where k > 0 is a prior weight constant.

    Properties:
    - w = 0 → c = 0
    - w = k → c = 0.5
    - w → ∞ → c → 1

    This is a saturation/sigmoid-like function.
-/
noncomputable def w2c (w k : ℝ≥0∞) : ℝ≥0∞ := w / (w + k)

/-- Confidence-to-Weight transformation (inverse of w2c).
    w = k × c / (1 - c)

    For c < 1, this gives the unique weight that produces confidence c.
    For c ≥ 1, returns ⊤ (infinite weight for certainty).
-/
noncomputable def c2w (c k : ℝ≥0∞) : ℝ≥0∞ :=
  if c < 1 then k * c / (1 - c) else ⊤

/-! ## Basic Properties of the Bijection -/

/-- w2c at 0 is 0 -/
theorem w2c_zero (k : ℝ≥0∞) : w2c 0 k = 0 := by
  unfold w2c
  simp

/-- c2w at 0 is 0 -/
theorem c2w_zero (k : ℝ≥0∞) : c2w 0 k = 0 := by
  unfold c2w
  simp

/-- w2c is bounded by 1 (for positive k) -/
theorem w2c_le_one (w k : ℝ≥0∞) (_hk : k ≠ 0) : w2c w k ≤ 1 := by
  unfold w2c
  apply ENNReal.div_le_of_le_mul
  simp only [one_mul]
  exact le_add_right (le_refl w)


/-! ## What Is Actually Required of a Confidence Coordinate

The two binary evidence counts have two finite coordinates: direction
(`n⁺ / (n⁺+n⁻)`) and total weight (`n⁺+n⁻`).  PLN's confidence formula is
one useful bounded coordinate for the total weight, but it is not forced
by the mere need to reconstruct the counts.  What is forced is weaker:
the confidence coordinate must have a known left inverse on admissible
nonnegative weights.
-/

/-- An evidence-weight coordinate is any coordinate system that can recover a
nonnegative evidence weight from its displayed confidence coordinate. -/
structure EvidenceWeightCoordinate where
  encode : ℝ → ℝ
  decode : ℝ → ℝ
  decode_encode_of_nonneg : ∀ {w : ℝ}, 0 ≤ w → decode (encode w) = w

namespace EvidenceWeightCoordinate

/-- The true mathematical requirement: the displayed coordinate must be
injective on admissible nonnegative weights. -/
theorem encode_injective_on_nonneg (χ : EvidenceWeightCoordinate)
    {w₁ w₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (h : χ.encode w₁ = χ.encode w₂) :
    w₁ = w₂ := by
  calc
    w₁ = χ.decode (χ.encode w₁) := (χ.decode_encode_of_nonneg hw₁).symm
    _ = χ.decode (χ.encode w₂) := by rw [h]
    _ = w₂ := χ.decode_encode_of_nonneg hw₂

/-- A displayed confidence-like value indexed by the coordinate that produced
it.  Operations that consume two such values can require the same index, making
cross-coordinate mixing explicit instead of accidental. -/
structure TypedConfidence (χ : EvidenceWeightCoordinate) where
  display : ℝ

namespace TypedConfidence

/-- Encode a nonnegative evidence weight as a typed display value. -/
noncomputable def ofWeight (χ : EvidenceWeightCoordinate) (w : ℝ) :
    TypedConfidence χ where
  display := χ.encode w

/-- Decode the typed display value back to its evidence weight according to its
own coordinate. -/
noncomputable def weight {χ : EvidenceWeightCoordinate}
    (c : TypedConfidence χ) : ℝ :=
  χ.decode c.display

/-- Typed confidence values recover the evidence weight that produced them,
for any valid coordinate. -/
@[simp] theorem weight_ofWeight (χ : EvidenceWeightCoordinate)
    {w : ℝ} (hw : 0 ≤ w) :
    (ofWeight χ w).weight = w := by
  exact χ.decode_encode_of_nonneg hw

/-- Typed confidence encoding is injective on admissible nonnegative weights. -/
theorem ofWeight_injective_on_nonneg
    (χ : EvidenceWeightCoordinate) {w₁ w₂ : ℝ}
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (h : ofWeight χ w₁ = ofWeight χ w₂) :
    w₁ = w₂ := by
  apply χ.encode_injective_on_nonneg hw₁ hw₂
  exact congrArg TypedConfidence.display h

/-- Minimum of two nonnegative evidence weights is nonnegative.  Kept local to
the typed-confidence layer to avoid relying on lemma-name drift. -/
theorem min_weight_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ min a b := by
  by_cases h : a ≤ b
  · simpa [min_eq_left h] using ha
  · have hb_le : b ≤ a := le_of_not_ge h
    simpa [min_eq_right hb_le] using hb

/-- Combine two confidence displays by taking the minimum of their decoded
evidence weights and re-encoding in the same coordinate.  The shared type index
is the compatibility guard: values produced by different coordinates cannot be
passed to this operation without an explicit conversion. -/
noncomputable def minByWeight {χ : EvidenceWeightCoordinate}
    (c₁ c₂ : TypedConfidence χ) : TypedConfidence χ :=
  ofWeight χ (min c₁.weight c₂.weight)

/-- The typed minimum operation really computes the minimum in evidence-weight
space when its inputs decode to admissible nonnegative weights. -/
@[simp] theorem weight_minByWeight {χ : EvidenceWeightCoordinate}
    (c₁ c₂ : TypedConfidence χ)
    (h₁ : 0 ≤ c₁.weight) (h₂ : 0 ≤ c₂.weight) :
    (minByWeight c₁ c₂).weight = min c₁.weight c₂.weight := by
  unfold minByWeight
  exact χ.decode_encode_of_nonneg (min_weight_nonneg h₁ h₂)

/-- Same-coordinate minimum is symmetric. -/
theorem minByWeight_comm {χ : EvidenceWeightCoordinate}
    (c₁ c₂ : TypedConfidence χ) :
    minByWeight c₁ c₂ = minByWeight c₂ c₁ := by
  simp [minByWeight, min_comm]

/-- Combine two confidence displays by adding their decoded evidence weights
and re-encoding in the same coordinate.  This is the typed version of
revision-style evidence accumulation. -/
noncomputable def addByWeight {χ : EvidenceWeightCoordinate}
    (c₁ c₂ : TypedConfidence χ) : TypedConfidence χ :=
  ofWeight χ (c₁.weight + c₂.weight)

/-- The typed additive operation really computes addition in evidence-weight
space when its inputs decode to admissible nonnegative weights. -/
@[simp] theorem weight_addByWeight {χ : EvidenceWeightCoordinate}
    (c₁ c₂ : TypedConfidence χ)
    (h₁ : 0 ≤ c₁.weight) (h₂ : 0 ≤ c₂.weight) :
    (addByWeight c₁ c₂).weight = c₁.weight + c₂.weight := by
  unfold addByWeight
  exact χ.decode_encode_of_nonneg (add_nonneg h₁ h₂)

end TypedConfidence

/-- Raw count-reconstruction property for a proposed strength/confidence
encoding.  It says that every nonzero finite nonnegative binary count pair can
be encoded as `(strength, displayedWeight)` and decoded back exactly. -/
def CountReconstruction (encode decode : ℝ → ℝ) : Prop :=
  ∀ {nPlus nMinus : ℝ},
    0 ≤ nPlus → 0 ≤ nMinus → nPlus + nMinus ≠ 0 →
      (let n := nPlus + nMinus
       let stv : ℝ × ℝ := (nPlus / n, encode n)
       let m := decode stv.2
       (stv.1 * m, (1 - stv.1) * m)) = (nPlus, nMinus)

/-- The minimal left-inverse condition on a displayed evidence-weight
coordinate. -/
def LeftInverseOnPositive (encode decode : ℝ → ℝ) : Prop :=
  ∀ {w : ℝ}, 0 < w → decode (encode w) = w

/-- Necessity, not just sufficiency: if a strength plus confidence
coordinate reconstructs every positive finite binary count pair, then the
confidence decoder must be a left inverse of the encoder on positive
total weights.  This is the real mathematical constraint hidden beneath
the choice of a particular PLN confidence formula. -/
theorem decode_encode_of_count_reconstruction
    (encode decode : ℝ → ℝ)
    (h :
      ∀ {nPlus nMinus : ℝ},
        0 ≤ nPlus → 0 ≤ nMinus → nPlus + nMinus ≠ 0 →
          (let n := nPlus + nMinus
           let stv : ℝ × ℝ := (nPlus / n, encode n)
           let m := decode stv.2
           (stv.1 * m, (1 - stv.1) * m)) = (nPlus, nMinus))
    {w : ℝ} (hw : 0 < w) :
    decode (encode w) = w := by
  have hrec := h (nPlus := w) (nMinus := 0) (le_of_lt hw) (le_refl 0) (by linarith)
  dsimp at hrec
  have hfirst := congrArg Prod.fst hrec
  dsimp at hfirst
  field_simp [ne_of_gt hw] at hfirst
  simpa using hfirst

/-- A left inverse on positive evidence weights suffices for exact binary
count reconstruction. -/
theorem count_reconstruction_of_leftInverseOnPositive
    (encode decode : ℝ → ℝ)
    (h : LeftInverseOnPositive encode decode) :
    CountReconstruction encode decode := by
  intro nPlus nMinus hPlus hMinus hTotal
  have hNonneg : 0 ≤ nPlus + nMinus := add_nonneg hPlus hMinus
  have hPositive : 0 < nPlus + nMinus :=
    lt_of_le_of_ne hNonneg (by
      intro hzero
      exact hTotal hzero.symm)
  unfold CountReconstruction at *
  dsimp
  rw [h hPositive]
  ext
  · field_simp [hTotal]
  · field_simp [hTotal]
    ring

/-- Exact characterization of the freedom in the confidence coordinate:
reconstructing binary evidence counts from strength plus a displayed
confidence-like coordinate is equivalent to the decoder being a left inverse of
the encoder on positive evidence weights.  No PLN-specific formula is forced by
reconstruction alone. -/
theorem countReconstruction_iff_leftInverseOnPositive
    (encode decode : ℝ → ℝ) :
    CountReconstruction encode decode ↔ LeftInverseOnPositive encode decode := by
  constructor
  · intro h w hw
    exact decode_encode_of_count_reconstruction encode decode h hw
  · exact count_reconstruction_of_leftInverseOnPositive encode decode

/-- Encode finite binary evidence counts as a strength plus an arbitrary
evidence-weight coordinate for total evidence. -/
noncomputable def encodeCounts (χ : EvidenceWeightCoordinate) (nPlus nMinus : ℝ) : ℝ × ℝ :=
  let n := nPlus + nMinus
  (nPlus / n, χ.encode n)

/-- Decode a strength plus coordinatized total back into finite binary evidence counts. -/
noncomputable def decodeCounts (χ : EvidenceWeightCoordinate) (stv : ℝ × ℝ) : ℝ × ℝ :=
  let n := χ.decode stv.2
  (stv.1 * n, (1 - stv.1) * n)

/-- Any evidence-weight coordinate with a left inverse reconstructs the original
finite binary counts from `(strength, confidence)` whenever total evidence
is positive.  No PLN-specific formula is used here. -/
theorem decode_encode_counts
    (χ : EvidenceWeightCoordinate) {nPlus nMinus : ℝ}
    (hPlus : 0 ≤ nPlus) (hMinus : 0 ≤ nMinus)
    (hTotal : nPlus + nMinus ≠ 0) :
    χ.decodeCounts (χ.encodeCounts nPlus nMinus) = (nPlus, nMinus) := by
  have hNonneg : 0 ≤ nPlus + nMinus := add_nonneg hPlus hMinus
  unfold encodeCounts decodeCounts
  rw [χ.decode_encode_of_nonneg hNonneg]
  ext
  · field_simp [hTotal]
  · field_simp [hTotal]
    ring

/-- PLN's usual odds-linear coordinate: confidence odds are proportional to
evidence weight. -/
noncomputable def plnOddsCoordinate (k : ℝ) (hk : 0 < k) : EvidenceWeightCoordinate where
  encode w := w / (w + k)
  decode c := k * c / (1 - c)
  decode_encode_of_nonneg := by
    intro w hw
    have hden_pos : 0 < w + k := by linarith
    have hden_ne : w + k ≠ 0 := ne_of_gt hden_pos
    field_simp [hden_ne, ne_of_gt hk]
    ring

/-- A deliberately different, more cautious coordinate.  It permanently reserves
half the display range for unknown model/context risk:

`c = w / (2w + k)`, so even infinite evidence approaches `1/2` rather than
`1`.  Despite that different interpretation, it is still a perfectly valid
coordinate for total evidence because `w = k c / (1 - 2c)`. -/
noncomputable def reserveHalfCoordinate (k : ℝ) (hk : 0 < k) : EvidenceWeightCoordinate where
  encode w := w / (2 * w + k)
  decode c := k * c / (1 - 2 * c)
  decode_encode_of_nonneg := by
    intro w hw
    have hden_pos : 0 < 2 * w + k := by nlinarith
    have hden_ne : 2 * w + k ≠ 0 := ne_of_gt hden_pos
    field_simp [hden_ne, ne_of_gt hk]
    ring

@[simp] theorem plnOddsCoordinate_encode_zero (k : ℝ) (hk : 0 < k) :
    (plnOddsCoordinate k hk).encode 0 = 0 := by
  simp [plnOddsCoordinate]

@[simp] theorem reserveHalfCoordinate_encode_zero (k : ℝ) (hk : 0 < k) :
    (reserveHalfCoordinate k hk).encode 0 = 0 := by
  simp [reserveHalfCoordinate]

/-- The cautious coordinate really is qualitatively different from PLN's coordinate:
for nonnegative finite evidence, its confidence coordinate is always below
`1/2`. -/
theorem reserveHalfCoordinate_encode_lt_half (k : ℝ) (hk : 0 < k)
    {w : ℝ} (hw : 0 ≤ w) :
    (reserveHalfCoordinate k hk).encode w < (1 / 2 : ℝ) := by
  unfold reserveHalfCoordinate
  have hden_pos : 0 < 2 * w + k := by nlinarith
  rw [div_lt_iff₀ hden_pos]
  nlinarith

/-- A raw displayed number is not enough provenance.  The same display value
`1/3` decodes to different evidence weights under two valid coordinates. -/
theorem TypedConfidence.same_display_can_decode_differently :
    let χp := plnOddsCoordinate 1 (by norm_num)
    let χr := reserveHalfCoordinate 1 (by norm_num)
    let cp : TypedConfidence χp := ⟨(1 / 3 : ℝ)⟩
    let cr : TypedConfidence χr := ⟨(1 / 3 : ℝ)⟩
    cp.display = cr.display ∧ cp.weight ≠ cr.weight := by
  dsimp [TypedConfidence.weight, plnOddsCoordinate, reserveHalfCoordinate]
  constructor
  · rfl
  · norm_num

/-- The cautious coordinate is not a toy: it reconstructs binary evidence just
as well as PLN's odds-linear confidence coordinate. -/
theorem reserveHalfCoordinate_decode_encode_counts
    (k : ℝ) (hk : 0 < k) {nPlus nMinus : ℝ}
    (hPlus : 0 ≤ nPlus) (hMinus : 0 ≤ nMinus)
    (hTotal : nPlus + nMinus ≠ 0) :
    (reserveHalfCoordinate k hk).decodeCounts
        ((reserveHalfCoordinate k hk).encodeCounts nPlus nMinus) =
      (nPlus, nMinus) :=
  decode_encode_counts (reserveHalfCoordinate k hk) hPlus hMinus hTotal

/-- Conversely, PLN's coordinate works for the same reason: not because the
formula is uniquely forced by the two-count problem, but because it has the
required left inverse on nonnegative weights. -/
theorem plnOddsCoordinate_decode_encode_counts
    (k : ℝ) (hk : 0 < k) {nPlus nMinus : ℝ}
    (hPlus : 0 ≤ nPlus) (hMinus : 0 ≤ nMinus)
    (hTotal : nPlus + nMinus ≠ 0) :
    (plnOddsCoordinate k hk).decodeCounts
        ((plnOddsCoordinate k hk).encodeCounts nPlus nMinus) =
      (nPlus, nMinus) :=
  decode_encode_counts (plnOddsCoordinate k hk) hPlus hMinus hTotal

/-! ### Extra laws that narrow the coordinate freedom

The left-inverse law above is the minimal requirement for reconstructing
binary evidence counts from a strength plus a displayed confidence-like
coordinate.  Additional semantics can narrow the choice.  In particular,
Walley's IDM predictive interval has width `s/(n+s)`.  If the displayed
credibility is required to be exactly the complement of that width, the PLN
odds coordinate is forced.
-/

/-- A coordinate is monotone on admissible evidence weights. -/
def MonotoneOnNonneg (χ : EvidenceWeightCoordinate) : Prop :=
  ∀ {w₁ w₂ : ℝ}, 0 ≤ w₁ → w₁ ≤ w₂ → χ.encode w₁ ≤ χ.encode w₂

/-- A coordinate's displayed value lies in the half-open unit interval on
admissible evidence weights. -/
def UnitIcoOnNonneg (χ : EvidenceWeightCoordinate) : Prop :=
  ∀ {w : ℝ}, 0 ≤ w → χ.encode w ∈ Set.Ico (0 : ℝ) 1

theorem plnOddsCoordinate_monotone_on_nonneg (k : ℝ) (hk : 0 < k) :
    MonotoneOnNonneg (plnOddsCoordinate k hk) := by
  intro w₁ w₂ hw₁ hle
  have hw₂ : 0 ≤ w₂ := le_trans hw₁ hle
  have hden₁ : 0 < w₁ + k := by linarith
  have hden₂ : 0 < w₂ + k := by linarith
  unfold plnOddsCoordinate
  rw [div_le_div_iff₀ hden₁ hden₂]
  nlinarith [mul_le_mul_of_nonneg_right hle (le_of_lt hk)]

theorem reserveHalfCoordinate_monotone_on_nonneg (k : ℝ) (hk : 0 < k) :
    MonotoneOnNonneg (reserveHalfCoordinate k hk) := by
  intro w₁ w₂ hw₁ hle
  have hw₂ : 0 ≤ w₂ := le_trans hw₁ hle
  have hden₁ : 0 < 2 * w₁ + k := by nlinarith
  have hden₂ : 0 < 2 * w₂ + k := by nlinarith
  unfold reserveHalfCoordinate
  rw [div_le_div_iff₀ hden₁ hden₂]
  nlinarith [mul_le_mul_of_nonneg_right hle (le_of_lt hk)]

theorem plnOddsCoordinate_encode_in_Ico (k : ℝ) (hk : 0 < k) :
    UnitIcoOnNonneg (plnOddsCoordinate k hk) := by
  intro w hw
  have hden : 0 < w + k := by linarith
  constructor
  · unfold plnOddsCoordinate
    exact div_nonneg hw (le_of_lt hden)
  · unfold plnOddsCoordinate
    rw [div_lt_one hden]
    linarith

theorem reserveHalfCoordinate_encode_in_Ico (k : ℝ) (hk : 0 < k) :
    UnitIcoOnNonneg (reserveHalfCoordinate k hk) := by
  intro w hw
  constructor
  · unfold reserveHalfCoordinate
    have hden : 0 ≤ 2 * w + k := by nlinarith
    exact div_nonneg hw hden
  · have hhalf := reserveHalfCoordinate_encode_lt_half k hk hw
    nlinarith

/-- Odds-linearity is a genuine extra law: if confidence odds are exactly
evidence weight in units of `k`, then the PLN confidence formula is forced. -/
theorem encode_eq_plnOdds_of_odds_linear
    (encode : ℝ → ℝ) (k : ℝ) (hk : 0 < k)
    {w : ℝ} (hw : 0 ≤ w)
    (hbelow : encode w < 1)
    (hodds : encode w / (1 - encode w) = w / k) :
    encode w = w / (w + k) := by
  have hleft_ne : 1 - encode w ≠ 0 := by linarith
  have hk_ne : k ≠ 0 := ne_of_gt hk
  have hsum_pos : 0 < w + k := by linarith
  have hsum_ne : w + k ≠ 0 := ne_of_gt hsum_pos
  have hlin : k * encode w = w * (1 - encode w) := by
    have h := hodds
    field_simp [hleft_ne, hk_ne] at h
    linarith
  field_simp [hsum_ne]
  nlinarith

/-- The Walley IDM predictive interval width for total evidence `n` and IDM
strength `s`. -/
noncomputable def walleyPredictiveWidth (n s : ℝ) : ℝ := s / (n + s)

/-- Walley's complement-of-width credibility for total evidence `n` and IDM
strength `s`. -/
noncomputable def walleyPredictiveCredibility (n s : ℝ) : ℝ := n / (n + s)

theorem walley_width_add_plnOdds (s : ℝ) (hs : 0 < s)
    {n : ℝ} (hn : 0 ≤ n) :
    walleyPredictiveWidth n s + (plnOddsCoordinate s hs).encode n = 1 := by
  unfold walleyPredictiveWidth plnOddsCoordinate
  have hden : 0 < n + s := by linarith
  field_simp [hden.ne']
  ring

/-- If an evidence-weight coordinate is required to be compatible with Walley's IDM
predictive interval by the law `width + credibility = 1`, then it must agree
with the PLN odds coordinate.  This is the precise sense in which the ITV/IDM
semantics narrows the otherwise-large space of valid confidence coordinates. -/
theorem walley_width_complement_forces_plnOdds
    (χ : EvidenceWeightCoordinate) (s : ℝ) (hs : 0 < s)
    (hcompat : ∀ {n : ℝ}, 0 ≤ n →
      walleyPredictiveWidth n s + χ.encode n = 1)
    {n : ℝ} (hn : 0 ≤ n) :
    χ.encode n = (plnOddsCoordinate s hs).encode n := by
  have hχ := hcompat hn
  have hpln := walley_width_add_plnOdds s hs hn
  linarith

/-- The cautious reserve-half coordinate is still a valid invertible evidence
coordinate, but it is not compatible with the Walley IDM law
`width + credibility = 1`. -/
theorem reserveHalfCoordinate_not_walley_width_complement
    (s : ℝ) (hs : 0 < s) :
    ¬ (∀ {n : ℝ}, 0 ≤ n →
      walleyPredictiveWidth n s + (reserveHalfCoordinate s hs).encode n = 1) := by
  intro hcompat
  have h := hcompat (n := s) (le_of_lt hs)
  unfold walleyPredictiveWidth reserveHalfCoordinate at h
  have hs_ne : s ≠ 0 := ne_of_gt hs
  field_simp [hs_ne] at h
  nlinarith [hs]

end EvidenceWeightCoordinate


/-! ## The Historical Bug: A Confidence Treated as a Weight

This section keeps the old raw-min confidence bug explicit. The corrected
formula is defined in weight space because the semantic justification is a
bound on counts. With a fixed `k`, the final result is the same as taking
the min of the two well-formed confidence values; what is wrong is the
extra `w2c` applied to a value that is already a confidence.
-/

/-- The WRONG way: taking min in confidence space.
    This is what the buggy PLN implementation did.
-/
noncomputable def minConfidenceBuggy (c₁ c₂ k : ℝ≥0∞) : ℝ≥0∞ :=
  w2c (min c₁ c₂) k

/-- The CORRECT way: taking min in weight space.
    Convert to weights, take min, convert back.
-/
noncomputable def minConfidenceCorrect (c₁ c₂ k : ℝ≥0∞) : ℝ≥0∞ :=
  w2c (min (c2w c₁ k) (c2w c₂ k)) k

/-- Both formulas agree when both inputs are 0 -/
theorem formulas_agree_at_zero (k : ℝ≥0∞) :
    minConfidenceBuggy 0 0 k = minConfidenceCorrect 0 0 k := by
  unfold minConfidenceBuggy minConfidenceCorrect
  simp only [min_self, c2w_zero, w2c_zero]

/-- Definition unfold for `minConfidenceCorrect`: this is bookkeeping,
not a derivation of the confidence transform. -/
theorem minConfidenceCorrect_unfold (c₁ c₂ k : ℝ≥0∞) :
    let w₁ := c2w c₁ k
    let w₂ := c2w c₂ k
    minConfidenceCorrect c₁ c₂ k = w2c (min w₁ w₂) k := rfl

/-! ## Connection to Hypergeometric Mode Bound

The hypergeometric mode bound justifies taking min in weight space.
-/

/-- The hypergeometric mode bound restated in terms of evidence totals.

    The mode of the hypergeometric (most likely intersection size) satisfies:
    mode ≤ min(|A|, |B|)

    In evidence terms: the most likely combined weight ≤ min of input weights.
    This is theorem `hypergeometricMode_in_range` from PLNConjunction.
-/
theorem evidence_combination_bounded (n a b : ℕ) (ha : a ≤ n) (hb : b ≤ n) :
    hypergeometricMode n a b ≤ min a b :=
  hypergeometricMode_in_range n a b ha hb

/-- The mode bound operates on COUNTS (weights), not confidences.

    This is why we must convert to weight space before taking min.
    The hypergeometric mode formula ⌊(a+1)(b+1)/(n+2)⌋ operates on
    raw counts a and b, not their confidence transformations.
-/
theorem mode_bound_is_weight_space :
    ∀ n a b : ℕ, hypergeometricMode n a b = ((a + 1) * (b + 1)) / (n + 2) := by
  intro n a b
  rfl

/-! ## Practical Implications

These theorems have direct practical implications for PLN implementations.
-/

/-- CRITICAL RULE: Track weight, not just confidence!

    The clean confidence combination formula is stated over underlying
    weights/counts. A confidence value can be inverted only when the
    evidence-scale `k` and the intended confidence convention are fixed;
    it still carries no provenance, overlap, or stamp information.

    Options:
    1. Store full evidence (n⁺, n⁻) - BEST
    2. Store (strength, weight) pairs
    3. Store (strength, confidence, k) - recovers total weight only

    Storing only (strength, confidence) is insufficient for serious PLN
    inference unless `k` and evidence independence/provenance assumptions
    are fixed elsewhere.
-/
structure ProperTruthValue where
  strength : ℝ≥0∞      -- s = n⁺ / (n⁺ + n⁻)
  weight : ℝ≥0∞        -- w = n⁺ + n⁻ (total evidence)

/-- Convert BinaryEvidence to ProperTruthValue -/
noncomputable def toProperTV (e : BinaryEvidence) : ProperTruthValue where
  strength := BinaryEvidence.toStrength e
  weight := e.total

/-- Correct confidence combination using ProperTruthValue -/
noncomputable def combineConfidenceCorrect (tv₁ tv₂ : ProperTruthValue) (k : ℝ≥0∞) : ℝ≥0∞ :=
  w2c (min tv₁.weight tv₂.weight) k

/-- What the buggy formula would compute (for comparison) -/
noncomputable def combineConfidenceBuggy (tv₁ tv₂ : ProperTruthValue) (k : ℝ≥0∞) : ℝ≥0∞ :=
  let c₁ := w2c tv₁.weight k
  let c₂ := w2c tv₂.weight k
  w2c (min c₁ c₂) k  -- BUG: treats confidences as weights!

/-- Definition unfold for `combineConfidenceCorrect`: it works directly
on weights by construction. -/
theorem combineConfidenceCorrect_unfold (tv₁ tv₂ : ProperTruthValue) (k : ℝ≥0∞) :
    combineConfidenceCorrect tv₁ tv₂ k = w2c (min tv₁.weight tv₂.weight) k := rfl

/-- The correct formula is symmetric in its inputs -/
theorem combineCorrect_comm (tv₁ tv₂ : ProperTruthValue) (k : ℝ≥0∞) :
    combineConfidenceCorrect tv₁ tv₂ k = combineConfidenceCorrect tv₂ tv₁ k := by
  unfold combineConfidenceCorrect
  rw [min_comm]

/-- The correct formula is bounded by 1 (for positive k) -/
theorem combineCorrect_le_one (tv₁ tv₂ : ProperTruthValue) (k : ℝ≥0∞) (hk : k ≠ 0) :
    combineConfidenceCorrect tv₁ tv₂ k ≤ 1 := by
  unfold combineConfidenceCorrect
  exact w2c_le_one _ _ hk

/-- Concrete canary for the historical bug: with unit evidence weights and
`k = 1`, the buggy formula strictly underestimates the weight-space formula.
This is not definitional bookkeeping; it witnesses the operational difference
between `w2c(min(c₁,c₂))` and `w2c(min(w₁,w₂))`. -/
theorem combineConfidenceBuggy_underestimates_unit_weight :
    combineConfidenceBuggy ⟨0, 1⟩ ⟨0, 1⟩ 1 <
      combineConfidenceCorrect ⟨0, 1⟩ ⟨0, 1⟩ 1 := by
  norm_num [combineConfidenceBuggy, combineConfidenceCorrect, w2c]
  rw [← ENNReal.toReal_lt_toReal
    (ENNReal.div_ne_top
      (by norm_num : (2⁻¹ : ℝ≥0∞) ≠ ⊤)
      (by norm_num : (2⁻¹ + 1 : ℝ≥0∞) ≠ 0))
    (by norm_num : (2⁻¹ : ℝ≥0∞) ≠ ⊤)]
  rw [ENNReal.toReal_div, ENNReal.toReal_add]
  · rw [ENNReal.toReal_inv]
    norm_num
  · exact ENNReal.inv_ne_top.2 (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  · norm_num

/-! ## Summary

The hypergeometric mode bound `mode ≤ min(a, b)` justifies:

1. **Reason in weight space**: Combined evidence ≤ min of input evidence weights
2. **The correct formula**: `c_combined = w2c(min(w₁, w₂))`
3. **Why buggy fails**: `w2c(min(c₁,c₂))` treats confidence as weight
4. **Error magnitude**: Up to 50% underestimation for high-confidence inputs
5. **Practical rule**: Track weight/counts, plus provenance/overlap when composing evidence

The PLN BinaryEvidence structure `(n⁺, n⁻)` correctly tracks this information.
The lesson: confidence is a derived view, computed from weight when needed.
Do not treat confidence as an evidence weight, and do not let scalar
confidence hide the count/provenance state that generated it.
-/

end Mettapedia.Logic.PLNConfidenceWeight
