import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.EvidenceBeta
import Mettapedia.Logic.EvidenceClass
import Mettapedia.Logic.PLNConfidenceWeight
import Mettapedia.Logic.PLNWeightTV
import KnuthSkilling.Additive.Main
-- import Mettapedia.Logic.HigherOrder.PLNKyburgReduction  -- TODO: Re-add in Phase 4 for Kyburg theorems

/-!
# Indefinite Truth Values: Core PLN Record and Constructor Semantics

Implements the core PLN `IndefiniteTruthValue` record shape
`<L, U, credibility>` following the OpenCog/PLN literature
(Goertzel et al. 2009), together with explicit constructors that supply the
semantics of the interval endpoints.  The raw record is intentionally not the
whole theory: `lower` and `upper` become meaningful only relative to a
constructor/provenance layer such as Walley IDM or a chosen Bayesian credible
interval backend.

## The Three-Component Model

```
structure ITV where
  lower : ℝ              -- Lower endpoint / lower probability under a selected semantics
  upper : ℝ              -- Upper endpoint / upper probability under a selected semantics
  credibility : ℝ        -- Evidence-concentration coordinate after a chosen scale/link
```

## Key Property: Orthogonality

For the general ITV record, credibility and interval width are
independent coordinates:
- High credibility + wide interval = much evidence but still uncertain
- High credibility + narrow interval = much evidence and tight bounds
- Low credibility + any width = little evidence

Example: under a semantics whose endpoints are lower/upper probabilities,
`<0.3, 0.7, 0.9>` means:
- the selected probability quantity lies in the constructor-supplied interval
  [0.3, 0.7];
- the evidence-concentration coordinate displays 0.9;
- this could arise from many observations whose retained model still leaves a
  wide interval.

Without the constructor semantics, the record is only a bounded triple.

## Theoretical Foundation

### Knuth-Skilling Connection
From `ProbabilityTheory/KnuthSkilling/Additive/*.lean`:
- K-S axioms lead to additive valuation/measure representations when the
  ordering and algebraic hypotheses are strong enough.
- When the representation is not unique, the natural imprecise reading is a
  family of admissible completions; lower/upper endpoints are then envelopes
  over that family.
- A unique completion collapses the interval to a point; a non-singleton
  family gives honest interval/credal semantics.

### Beta Distribution Bridge
From `EvidenceBeta.lean` and the surrounding evidence files:
- BinaryEvidence (n⁺, n⁻) encodes Beta(α₀+n⁺, β₀+n⁻)
- Bayesian constructors use Beta credible intervals, with an explicit backend
  and interval level.
- Their credibility field is the evidence concentration
  `total/(total+κ)` for the chosen prior concentration `κ`.

### Heyting Algebra Structure
From `PLNIntuitionisticBridge.lean`:
- Intervals [L, U] form Heyting algebra
- Operations: meet, join, implication (intuitionistic logic)
- BinaryEvidence forms separate Heyting algebra (product of chains)

### BinaryEvidence Quantale
From `EvidenceQuantale.lean`:
- BinaryEvidence has quantale structure: tensor ⊗ and hplus ⊕
- Credibility composes via quantale operations
- **Separate from** interval arithmetic

## Degrees of Freedom

The record `ITV` only fixes four invariants: `lower ≤ upper`, both bounds
in `[0,1]`, and credibility in `[0,1]`. Everything else is selected by a
constructor:

- `width = upper - lower` is fixed once the bounds are chosen.
- `strength = (lower + upper)/2` is the current midpoint view, not a theorem
  saying every interval semantics must use the midpoint for decisions.
- Bayesian constructors choose a prior context, interval level, and backend;
  their credibility is the BinaryEvidence concentration using
  `κ = α₀ + β₀`, independent of interval backend/level in this file.
- Walley IDM predictive intervals choose the IDM strength `s > 0`; then
  lower, upper, width, and credibility are fixed by the IDM formulas, and
  credibility is exactly the complement of predictive width.

Thus `lower`/`upper` should not be read as unconditional "true bounds" without
the constructor semantics.  In Walley's IDM they are lower/upper predictive
probabilities relative to the IDM credal set.  In Bayesian credible intervals
they are posterior credible endpoints.  In frequentist intervals they would be
coverage-procedure endpoints, not a posterior probability statement.

## Resolution of PLNSoundnessCounterexample

The counterexample in `PLNSoundnessCounterexample.lean` proved that
BinaryEvidence-based confidence `c = w/(w+1)` and error bounds `|P-s| ≤ e`
cannot be unified via `e = 1-c` after combination.

**This ITV model resolves the issue** by separating the axes:
- Intervals [L, U] track constructor-supplied endpoint semantics, such as
  Bayesian credible endpoints or Walley lower/upper probabilities.
- Credibility tracks BinaryEvidence amount / concentration.
- No forced relationship `width = 1 - credibility` for arbitrary ITVs or
  Bayesian credible intervals
- Walley IDM predictive intervals are a special case: their width is
  `s/(n+s)`, so the precision proxy `n/(n+s)` is exactly `1 - width`
- In the constructors here, both are derived from the same BinaryEvidence
  `(n⁺, n⁻)` via different pathways.

## References

- Goertzel et al. (2009), "Probabilistic Logic Networks"
- Walley (1991), "Statistical Reasoning with Imprecise Probabilities"
- Kyburg (1988), "Higher Order Probabilities and Vagueness"
- Knuth (2003), "Deriving Laws from Ordering Relations"
-/

namespace Mettapedia.Logic.PLNIndefiniteTruth

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.EvidenceBeta
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWeightTV

/-! ## The ITV Structure -/

/-- Indefinite Truth Value: <lower, upper, credibility>

**Semantics**:
- `lower`/`upper` are interval endpoints whose interpretation is supplied by
  the constructor: Walley lower/upper probabilities, Bayesian credible
  endpoints, or frequentist coverage endpoints.
- credibility = w/(w+1) measures BinaryEvidence accumulation (quantale element)
- Width (upper - lower) measures epistemic uncertainty
- Credibility measures evidential support (how much data)

**Key**: For arbitrary ITVs these are orthogonal.  A selected interval
semantics may impose an extra law: Walley IDM predictive intervals satisfy
`width + credibility = 1`, while Bayesian credible intervals do not impose
that simple algebraic complement.
-/
structure ITV where
  lower : ℝ
  upper : ℝ
  credibility : ℝ
  -- Invariants
  lower_le_upper : lower ≤ upper
  lower_in_unit : lower ∈ Set.Icc 0 1
  upper_in_unit : upper ∈ Set.Icc 0 1
  credibility_in_unit : credibility ∈ Set.Icc 0 1

namespace ITV

open Mettapedia.Logic.PLNWeightTV

/-! ## Basic Properties -/

/-- Derived: point strength estimate (midpoint of interval) -/
noncomputable def strength (itv : ITV) : ℝ := (itv.lower + itv.upper) / 2

/-- Derived: interval width (epistemic uncertainty) -/
noncomputable def width (itv : ITV) : ℝ := itv.upper - itv.lower

/-- Strength is in [0, 1] -/
theorem strength_in_unit (itv : ITV) : itv.strength ∈ Set.Icc 0 1 := by
  unfold strength
  constructor
  · apply div_nonneg
    · linarith [itv.lower_in_unit.1, itv.upper_in_unit.1]
    · norm_num
  · have h1 : itv.lower + itv.upper ≤ 2 := by
      linarith [itv.lower_in_unit.2, itv.upper_in_unit.2]
    calc (itv.lower + itv.upper) / 2
        ≤ 2 / 2 := by apply div_le_div_of_nonneg_right h1; norm_num
      _ = 1 := by norm_num

/-- Width is non-negative -/
theorem width_nonneg (itv : ITV) : 0 ≤ itv.width := by
  unfold width
  linarith [itv.lower_le_upper]

/-- Width is at most 1 -/
theorem width_le_one (itv : ITV) : itv.width ≤ 1 := by
  unfold width
  linarith [itv.lower_in_unit.1, itv.upper_in_unit.2]

/-- A full-width ITV with an arbitrary credibility in `[0,1]`.  This is a
small canary for the generic ITV record: interval width alone does not
determine credibility unless a particular interval semantics adds that law. -/
def fullWidthWithCredibility (c : ℝ) (hc : c ∈ Set.Icc 0 1) : ITV where
  lower := 0
  upper := 1
  credibility := c
  lower_le_upper := by norm_num
  lower_in_unit := by norm_num
  upper_in_unit := by norm_num
  credibility_in_unit := hc

@[simp] theorem fullWidthWithCredibility_width (c : ℝ) (hc : c ∈ Set.Icc 0 1) :
    (fullWidthWithCredibility c hc).width = 1 := by
  simp [fullWidthWithCredibility, width]

@[simp] theorem fullWidthWithCredibility_credibility (c : ℝ) (hc : c ∈ Set.Icc 0 1) :
    (fullWidthWithCredibility c hc).credibility = c := by
  rfl

/-- A degenerate interval at point `p` with an arbitrary credibility in
`[0,1]`. -/
def pointWithCredibility (p c : ℝ) (hp : p ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) :
    ITV where
  lower := p
  upper := p
  credibility := c
  lower_le_upper := le_rfl
  lower_in_unit := hp
  upper_in_unit := hp
  credibility_in_unit := hc

@[simp] theorem pointWithCredibility_width
    (p c : ℝ) (hp : p ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) :
    (pointWithCredibility p c hp hc).width = 0 := by
  simp [pointWithCredibility, width]

@[simp] theorem pointWithCredibility_credibility
    (p c : ℝ) (hp : p ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) :
    (pointWithCredibility p c hp hc).credibility = c := by
  rfl

/-- Generic ITVs do not determine credibility from interval width alone:
there are two ITVs with the same width and different credibility. -/
theorem generic_width_does_not_determine_credibility :
    ∃ itv₀ itv₁ : ITV,
      itv₀.width = itv₁.width ∧ itv₀.credibility ≠ itv₁.credibility := by
  refine ⟨fullWidthWithCredibility 0 (by norm_num),
          fullWidthWithCredibility 1 (by norm_num), ?_⟩
  simp

/-- Generic ITVs also do not determine interval width from credibility alone. -/
theorem generic_credibility_does_not_determine_width :
    ∃ itv₀ itv₁ : ITV,
      itv₀.credibility = itv₁.credibility ∧ itv₀.width ≠ itv₁.width := by
  refine ⟨fullWidthWithCredibility (1 / 2) (by norm_num),
          pointWithCredibility 0 (1 / 2) (by norm_num) (by norm_num), ?_⟩
  simp

/-! ## Construction from BinaryEvidence -/

/-- Construct ITV from BinaryEvidence via Bayesian Beta credible interval backend.

Given BinaryEvidence (n⁺, n⁻) with context (prior κ, etc.):
1. Map to Beta parameters: α = α₀ + n⁺, β = β₀ + n⁻
2. Compute credible interval [L, U] (chosen backend)
3. Compute credibility: c = (n⁺ + n⁻) / (n⁺ + n⁻ + κ) = w/(w+1)

**Parameters**:
- `e` : BinaryEvidence counts
- `ctx` : Binary context (prior parameters)
- `level` : Confidence level for credible interval (e.g., 0.95)
- `backend` : interval constructor (`normalApprox` or `exactInvCDF`)
-/
noncomputable def fromBayesCredibleWithBackend
    (backend : CredibleIntervalBackend)
    (e : BinaryEvidence) (ctx : BinaryContext)
    (level : ℝ) (hlevel : 0 < level ∧ level < 1) : ITV :=
  -- Convert BinaryEvidence to Beta parameters
  let n_pos := e.pos.toReal
  let n_neg := e.neg.toReal
  let α₀ := ctx.α₀.toReal
  let β₀ := ctx.β₀.toReal
  -- Compute Beta credible interval (with safeguards for α₀, β₀ > 0)
  let α := α₀ + n_pos
  let β := β₀ + n_neg
  -- Default to small positive values if prior parameters are 0
  let α_safe := max 0.5 α
  let β_safe := max 0.5 β
  have hα : 0 < α_safe := by
    unfold α_safe
    apply lt_max_iff.mpr
    left
    norm_num
  have hβ : 0 < β_safe := by
    unfold β_safe
    apply lt_max_iff.mpr
    left
    norm_num
  let ci := betaCredibleInterval backend α_safe β_safe level hα hβ hlevel
  -- Compute credibility from BinaryEvidence (κ = prior sample size = α₀ + β₀)
  let κ := ctx.α₀ + ctx.β₀
  let cred := BinaryEvidence.toConfidence κ e
  { lower := ci.lower
    upper := ci.upper
    credibility := cred.toReal
    lower_le_upper := ci.lower_le_upper
    lower_in_unit := by
      constructor
      · exact ci.lower_nonneg
      · calc ci.lower
            ≤ ci.upper := ci.lower_le_upper
          _ ≤ 1 := ci.upper_le_one
    upper_in_unit := by
      constructor
      · calc (0 : ℝ)
            ≤ ci.lower := ci.lower_nonneg
          _ ≤ ci.upper := ci.lower_le_upper
      · exact ci.upper_le_one
    credibility_in_unit := by
      constructor
      · apply ENNReal.toReal_nonneg
      · -- cred = e.total / (e.total + κ) ≤ 1
        -- Proof: numerator ≤ denominator, so cred.toReal ≤ 1
        unfold cred BinaryEvidence.toConfidence κ
        apply ENNReal.toReal_le_of_le_ofReal (by norm_num : (0 : ℝ) ≤ 1)
        apply ENNReal.div_le_of_le_mul
        simp }

@[simp] theorem fromBayesCredibleWithBackend_credibility
    (backend : CredibleIntervalBackend)
    (e : BinaryEvidence) (ctx : BinaryContext)
    (level : ℝ) (hlevel : 0 < level ∧ level < 1) :
    (fromBayesCredibleWithBackend backend e ctx level hlevel).credibility =
      (BinaryEvidence.toConfidence (ctx.α₀ + ctx.β₀) e).toReal := by
  simp [fromBayesCredibleWithBackend]

/-- In this model, the Bayesian ITV credibility coordinate is fixed by the
evidence concentration and prior sample size. The credible-interval backend
and level affect the bounds, not this credibility field. -/
theorem fromBayesCredibleWithBackend_credibility_independent_of_backend_level
    (backend₁ backend₂ : CredibleIntervalBackend)
    (e : BinaryEvidence) (ctx : BinaryContext)
    (level₁ level₂ : ℝ)
    (hlevel₁ : 0 < level₁ ∧ level₁ < 1)
    (hlevel₂ : 0 < level₂ ∧ level₂ < 1) :
    (fromBayesCredibleWithBackend backend₁ e ctx level₁ hlevel₁).credibility =
      (fromBayesCredibleWithBackend backend₂ e ctx level₂ hlevel₂).credibility := by
  simp

/-- Construct ITV from BinaryEvidence via Bayesian Beta credible interval
using normal approximation. -/
noncomputable def fromBayesCredibleNormalApprox (e : BinaryEvidence) (ctx : BinaryContext)
    (level : ℝ) (hlevel : 0 < level ∧ level < 1) : ITV :=
  fromBayesCredibleWithBackend .normalApprox e ctx level hlevel

/-- Construct ITV from BinaryEvidence via Bayesian Beta credible interval
using the exact-invCDF backend. -/
noncomputable def fromBayesCredibleExactInvCDF (e : BinaryEvidence) (ctx : BinaryContext)
    (level : ℝ) (hlevel : 0 < level ∧ level < 1) : ITV :=
  fromBayesCredibleWithBackend .exactInvCDF e ctx level hlevel

/-- Construct ITV at 95% Bayesian credible-interval level. -/
noncomputable def fromBayesCredible95 (e : BinaryEvidence) (ctx : BinaryContext) : ITV :=
  fromBayesCredibleNormalApprox e ctx 0.95 ⟨by norm_num, by norm_num⟩

/-- Construct ITV at 90% Bayesian credible-interval level. -/
noncomputable def fromBayesCredible90 (e : BinaryEvidence) (ctx : BinaryContext) : ITV :=
  fromBayesCredibleNormalApprox e ctx 0.90 ⟨by norm_num, by norm_num⟩

/-- Construct ITV at 95% Bayesian credible-interval level
using the exact-invCDF backend. -/
noncomputable def fromBayesCredible95ExactInvCDF (e : BinaryEvidence) (ctx : BinaryContext) : ITV :=
  fromBayesCredibleExactInvCDF e ctx 0.95 ⟨by norm_num, by norm_num⟩

/-- Construct ITV at 90% Bayesian credible-interval level
using the exact-invCDF backend. -/
noncomputable def fromBayesCredible90ExactInvCDF (e : BinaryEvidence) (ctx : BinaryContext) : ITV :=
  fromBayesCredibleExactInvCDF e ctx 0.90 ⟨by norm_num, by norm_num⟩

/-- Construct ITV from BinaryEvidence via Walley's IDM predictive bounds.

For binary outcomes with positive count `n⁺`, negative count `n⁻`, and IDM strength `s > 0`:
- lower = `n⁺ / (n⁺ + n⁻ + s)`
- upper = `(n⁺ + s) / (n⁺ + n⁻ + s)`

This is a predictive-interval semantics (IDM), distinct from Bayesian credible intervals.
`credibility` is the precision proxy `n/(n+s)` where `n = n⁺ + n⁻`.
-/
noncomputable def fromWalleyIDMPredictive (e : BinaryEvidence) (s : ℝ) (hs : 0 < s) : ITV :=
  let n_pos := e.pos.toReal
  let n_neg := e.neg.toReal
  let n_total := n_pos + n_neg
  let denom := n_total + s
  let lower := n_pos / denom
  let upper := (n_pos + s) / denom
  let cred := n_total / denom
  have h_npos_nonneg : 0 ≤ n_pos := ENNReal.toReal_nonneg
  have h_nneg_nonneg : 0 ≤ n_neg := ENNReal.toReal_nonneg
  have h_denom_pos : 0 < denom := by
    unfold denom n_total
    linarith [h_npos_nonneg, h_nneg_nonneg, hs]
  have h_lower_nonneg : 0 ≤ lower := by
    unfold lower
    exact div_nonneg h_npos_nonneg (le_of_lt h_denom_pos)
  have h_upper_nonneg : 0 ≤ upper := by
    unfold upper
    apply div_nonneg
    · linarith [h_npos_nonneg, hs.le]
    · exact le_of_lt h_denom_pos
  have h_lower_le_upper : lower ≤ upper := by
    unfold lower upper
    apply div_le_div_of_nonneg_right
    · linarith [hs.le]
    · exact le_of_lt h_denom_pos
  have h_upper_le_one : upper ≤ 1 := by
    unfold upper
    apply (div_le_one h_denom_pos).2
    unfold denom n_total
    linarith [h_nneg_nonneg]
  have h_cred_nonneg : 0 ≤ cred := by
    unfold cred
    exact div_nonneg (by linarith [h_npos_nonneg, h_nneg_nonneg]) (le_of_lt h_denom_pos)
  have h_cred_le_one : cred ≤ 1 := by
    unfold cred
    apply (div_le_one h_denom_pos).2
    unfold denom
    linarith [hs.le]
  { lower := lower
    upper := upper
    credibility := cred
    lower_le_upper := h_lower_le_upper
    lower_in_unit := ⟨h_lower_nonneg, le_trans h_lower_le_upper h_upper_le_one⟩
    upper_in_unit := ⟨h_upper_nonneg, h_upper_le_one⟩
    credibility_in_unit := ⟨h_cred_nonneg, h_cred_le_one⟩ }

@[simp] theorem fromWalleyIDMPredictive_lower
    (e : BinaryEvidence) (s : ℝ) (hs : 0 < s) :
    (fromWalleyIDMPredictive e s hs).lower =
      e.pos.toReal / (e.pos.toReal + e.neg.toReal + s) := by
  simp [fromWalleyIDMPredictive]

@[simp] theorem fromWalleyIDMPredictive_upper
    (e : BinaryEvidence) (s : ℝ) (hs : 0 < s) :
    (fromWalleyIDMPredictive e s hs).upper =
      (e.pos.toReal + s) / (e.pos.toReal + e.neg.toReal + s) := by
  simp [fromWalleyIDMPredictive]

@[simp] theorem fromWalleyIDMPredictive_credibility
    (e : BinaryEvidence) (s : ℝ) (hs : 0 < s) :
    (fromWalleyIDMPredictive e s hs).credibility =
      (e.pos.toReal + e.neg.toReal) / (e.pos.toReal + e.neg.toReal + s) := by
  simp [fromWalleyIDMPredictive]

theorem fromWalleyIDMPredictive_width_eq
    (e : BinaryEvidence) (s : ℝ) (hs : 0 < s) :
    (fromWalleyIDMPredictive e s hs).width =
      s / (e.pos.toReal + e.neg.toReal + s) := by
  unfold ITV.width
  rw [fromWalleyIDMPredictive_upper, fromWalleyIDMPredictive_lower]
  have hden_pos : 0 < e.pos.toReal + e.neg.toReal + s := by
    have hpos_nonneg : 0 ≤ e.pos.toReal := ENNReal.toReal_nonneg
    have hneg_nonneg : 0 ≤ e.neg.toReal := ENNReal.toReal_nonneg
    linarith
  field_simp [hden_pos.ne']
  ring

theorem fromWalleyIDMPredictive_width_add_credibility
    (e : BinaryEvidence) (s : ℝ) (hs : 0 < s) :
    (fromWalleyIDMPredictive e s hs).width +
      (fromWalleyIDMPredictive e s hs).credibility = 1 := by
  rw [fromWalleyIDMPredictive_width_eq, fromWalleyIDMPredictive_credibility]
  have hden_pos : 0 < e.pos.toReal + e.neg.toReal + s := by
    have hpos_nonneg : 0 ≤ e.pos.toReal := ENNReal.toReal_nonneg
    have hneg_nonneg : 0 ≤ e.neg.toReal := ENNReal.toReal_nonneg
    linarith
  field_simp [hden_pos.ne']
  ring

/-- Under the current ITV midpoint view, the Walley IDM predictive interval has
representative strength `(n⁺ + s/2)/(n⁺+n⁻+s)`. This is a midpoint-view
choice; the Walley interval itself is carried by the lower/upper bounds. -/
theorem fromWalleyIDMPredictive_strength_eq
    (e : BinaryEvidence) (s : ℝ) (hs : 0 < s) :
    (fromWalleyIDMPredictive e s hs).strength =
      (e.pos.toReal + s / 2) / (e.pos.toReal + e.neg.toReal + s) := by
  unfold ITV.strength
  rw [fromWalleyIDMPredictive_lower, fromWalleyIDMPredictive_upper]
  have hden_pos : 0 < e.pos.toReal + e.neg.toReal + s := by
    have hpos_nonneg : 0 ≤ e.pos.toReal := ENNReal.toReal_nonneg
    have hneg_nonneg : 0 ≤ e.neg.toReal := ENNReal.toReal_nonneg
    linarith
  field_simp [hden_pos.ne']
  ring

/-- Walley's IDM precision proxy is the PLN odds coordinate applied to the total
evidence count with `k = s`.  This is stronger than generic ITV
orthogonality: it is a property of the selected Walley predictive
semantics. -/
theorem fromWalleyIDMPredictive_credibility_eq_plnOddsCoordinate
    (e : BinaryEvidence) (s : ℝ) (hs : 0 < s) :
    (fromWalleyIDMPredictive e s hs).credibility =
      (Mettapedia.Logic.PLNConfidenceWeight.EvidenceWeightCoordinate.plnOddsCoordinate s hs).encode
        (e.pos.toReal + e.neg.toReal) := by
  rw [fromWalleyIDMPredictive_credibility]
  simp [Mettapedia.Logic.PLNConfidenceWeight.EvidenceWeightCoordinate.plnOddsCoordinate]

theorem fromWalleyIDMPredictive_width_eq_one_sub_credibility
    (e : BinaryEvidence) (s : ℝ) (hs : 0 < s) :
    (fromWalleyIDMPredictive e s hs).width =
      1 - (fromWalleyIDMPredictive e s hs).credibility := by
  have h := fromWalleyIDMPredictive_width_add_credibility e s hs
  linarith

/-! ## Conversion to/from WTV -/

/-- Convert ITV to WTV (using midpoint strength and credibility) -/
noncomputable def toWTV (itv : ITV) : WTV :=
  { strength := itv.strength
    weight := c2w itv.credibility
    strength_nonneg := itv.strength_in_unit.1
    strength_le_one := itv.strength_in_unit.2
    weight_nonneg := by
      unfold c2w
      split_ifs with h
      · apply div_nonneg itv.credibility_in_unit.1
        linarith [itv.credibility_in_unit.2]
      · norm_num }

/-- Convert WTV to ITV (using confidence as point estimate, zero width).

Note: This loses interval information! WTV only has a point estimate.
The resulting ITV has lower = upper = strength (degenerate interval).
-/
noncomputable def ofWTV (wtv : WTV) : ITV :=
  { lower := wtv.strength
    upper := wtv.strength
    credibility := wtv.confidence
    lower_le_upper := by rfl
    lower_in_unit := ⟨wtv.strength_nonneg, wtv.strength_le_one⟩
    upper_in_unit := ⟨wtv.strength_nonneg, wtv.strength_le_one⟩
    credibility_in_unit := wtv.confidence_bounds }

/-! ## Examples -/

/-- Example: Balanced evidence (5 successes, 5 failures) with Jeffreys prior.
Sanity check: all ITV components satisfy foundational bounds. -/
example : let e : BinaryEvidence := ⟨5, 5⟩
          let ctx := BinaryContext.jeffreys
          let itv := fromBayesCredible95 e ctx
          itv.strength ∈ Set.Icc 0 1 ∧
          itv.credibility ∈ Set.Icc 0 1 ∧
          itv.width ∈ Set.Icc 0 1 := by
  intro e ctx itv
  constructor
  · exact itv.strength_in_unit
  constructor
  · exact itv.credibility_in_unit
  · exact ⟨itv.width_nonneg, itv.width_le_one⟩

/-- Example: Strong evidence (20 successes, 2 failures).
Sanity check: interval endpoints are ordered and bounded. -/
example : let e : BinaryEvidence := ⟨20, 2⟩
          let ctx := BinaryContext.jeffreys
          let itv := fromBayesCredible95 e ctx
          itv.lower ≤ itv.upper ∧
          itv.lower ∈ Set.Icc 0 1 ∧
          itv.upper ∈ Set.Icc 0 1 := by
  intro e ctx itv
  constructor
  · exact itv.lower_le_upper
  constructor
  · exact itv.lower_in_unit
  · exact itv.upper_in_unit

/-- Example: High-evidence symmetric case (`50/50` observations).
Sanity check: credibility and width are both bounded in `[0,1]`. -/
example : let e : BinaryEvidence := ⟨50, 50⟩
          let ctx := BinaryContext.jeffreys
          let itv := fromBayesCredible95 e ctx
          itv.credibility ∈ Set.Icc 0 1 ∧
          itv.width ∈ Set.Icc 0 1 := by
  intro e ctx itv
  constructor
  · exact itv.credibility_in_unit
  · exact ⟨itv.width_nonneg, itv.width_le_one⟩

/-! ## Heyting Operations

Operations on intervals following Heyting algebra structure.
Credibility composes separately via the BinaryEvidence quantale.
-/

/-- Conjunction for independent propositions.

**Intervals**: Multiply (for P(A∧B) = P(A)·P(B) under independence)
**Credibility**: Compose via quantale (w₁ * w₂ → w_out)

Note: For dependent propositions, use conditional probability adjustments.
-/
noncomputable def conjunction (itv1 itv2 : ITV) : ITV where
  lower := itv1.lower * itv2.lower
  upper := itv1.upper * itv2.upper
  credibility := w2c (c2w itv1.credibility * c2w itv2.credibility)
  lower_le_upper := by
    apply mul_le_mul
    · exact itv1.lower_le_upper
    · exact itv2.lower_le_upper
    · exact itv2.lower_in_unit.1
    · linarith [itv1.lower_in_unit.1, itv1.lower_in_unit.2, itv1.upper_in_unit.1, itv1.upper_in_unit.2]
  lower_in_unit := by
    constructor
    · apply mul_nonneg itv1.lower_in_unit.1 itv2.lower_in_unit.1
    · calc itv1.lower * itv2.lower
          ≤ itv1.lower * 1 := by apply mul_le_mul_of_nonneg_left itv2.lower_in_unit.2 itv1.lower_in_unit.1
        _ = itv1.lower := by ring
        _ ≤ 1 := itv1.lower_in_unit.2
  upper_in_unit := by
    constructor
    · apply mul_nonneg itv1.upper_in_unit.1 itv2.upper_in_unit.1
    · calc itv1.upper * itv2.upper
          ≤ 1 * itv2.upper := by apply mul_le_mul_of_nonneg_right itv1.upper_in_unit.2 itv2.upper_in_unit.1
        _ = itv2.upper := by ring
        _ ≤ 1 := itv2.upper_in_unit.2
  credibility_in_unit := by
    -- Prove w2c(c2w(c1) * c2w(c2)) ∈ [0, 1]
    -- Strategy: c2w produces non-negative weights, w2c maps any non-negative weight to [0,1]
    have hw : 0 ≤ c2w itv1.credibility * c2w itv2.credibility := by
      apply mul_nonneg
      · by_cases h1 : itv1.credibility < 1
        · exact Mettapedia.Logic.PLNWeightTV.WTV.c2w_nonneg itv1.credibility itv1.credibility_in_unit.1 h1
        · unfold c2w; simp only [h1, ↓reduceIte]; norm_num
      · by_cases h2 : itv2.credibility < 1
        · exact Mettapedia.Logic.PLNWeightTV.WTV.c2w_nonneg itv2.credibility itv2.credibility_in_unit.1 h2
        · unfold c2w; simp only [h2, ↓reduceIte]; norm_num
    exact Mettapedia.Logic.PLNWeightTV.WTV.w2c_bounds _ hw

/-- Disjunction for independent propositions.

**Intervals**: Heyting join structure (max lower, add uppers capped at 1)
**Credibility**: Compose via quantale (same as conjunction)
-/
noncomputable def disjunction (itv1 itv2 : ITV) : ITV where
  lower := max itv1.lower itv2.lower
  upper := min 1 (itv1.upper + itv2.upper)
  credibility := w2c (c2w itv1.credibility * c2w itv2.credibility)
  lower_le_upper := by
    -- max(L₁, L₂) ≤ min(1, U₁+U₂)
    apply max_le
    · -- L₁ ≤ min(1, U₁+U₂)
      apply le_min
      · exact le_trans itv1.lower_le_upper itv1.upper_in_unit.2
      · linarith [itv1.lower_le_upper, itv2.upper_in_unit.1]
    · -- L₂ ≤ min(1, U₁+U₂)
      apply le_min
      · exact le_trans itv2.lower_le_upper itv2.upper_in_unit.2
      · linarith [itv2.lower_le_upper, itv1.upper_in_unit.1]
  lower_in_unit := by
    constructor
    · apply le_max_iff.mpr
      left
      exact itv1.lower_in_unit.1
    · apply max_le
      · calc itv1.lower
            ≤ itv1.upper := itv1.lower_le_upper
          _ ≤ 1 := itv1.upper_in_unit.2
      · calc itv2.lower
            ≤ itv2.upper := itv2.lower_le_upper
          _ ≤ 1 := itv2.upper_in_unit.2
  upper_in_unit := by
    constructor
    · apply le_min
      · norm_num
      · linarith [itv1.upper_in_unit.1, itv2.upper_in_unit.1]
    · exact min_le_left 1 (itv1.upper + itv2.upper)
  credibility_in_unit := by
    -- Same as conjunction: quantale composition preserves [0, 1]
    have hw : 0 ≤ c2w itv1.credibility * c2w itv2.credibility := by
      apply mul_nonneg
      · by_cases h1 : itv1.credibility < 1
        · exact Mettapedia.Logic.PLNWeightTV.WTV.c2w_nonneg itv1.credibility itv1.credibility_in_unit.1 h1
        · unfold c2w; simp only [h1, ↓reduceIte]; norm_num
      · by_cases h2 : itv2.credibility < 1
        · exact Mettapedia.Logic.PLNWeightTV.WTV.c2w_nonneg itv2.credibility itv2.credibility_in_unit.1 h2
        · unfold c2w; simp only [h2, ↓reduceIte]; norm_num
    exact Mettapedia.Logic.PLNWeightTV.WTV.w2c_bounds _ hw

/-- Implication: Heyting arrow on intervals.

**Intervals**: [L₁, U₁] → [L₂, U₂] = [max(0, L₂-U₁), min(1, 1-L₁+U₂)]
**Credibility**: Requires conditional BinaryEvidence analysis (more complex)
-/
noncomputable def implication (itv1 itv2 : ITV) : ITV where
  lower := max 0 (itv2.lower - itv1.upper)
  upper := min 1 (1 - itv1.lower + itv2.upper)
  credibility := min itv1.credibility itv2.credibility  -- Conservative estimate
  lower_le_upper := by
    -- max(0, L₂-U₁) ≤ min(1, 1-L₁+U₂)
    apply max_le
    · -- 0 ≤ min(1, 1-L₁+U₂)
      apply le_min
      · norm_num
      · linarith [itv1.lower_in_unit.1, itv1.lower_in_unit.2, itv2.upper_in_unit.1, itv2.upper_in_unit.2]
    · -- L₂-U₁ ≤ min(1, 1-L₁+U₂)
      apply le_min
      · linarith [itv2.lower_in_unit.1, itv2.lower_in_unit.2, itv1.upper_in_unit.1]
      · linarith [itv1.lower_in_unit.1, itv1.lower_in_unit.2, itv1.lower_le_upper,
                   itv2.lower_in_unit.1, itv2.lower_in_unit.2, itv2.lower_le_upper,
                   itv1.upper_in_unit.1, itv1.upper_in_unit.2, itv2.upper_in_unit.1, itv2.upper_in_unit.2]
  lower_in_unit := by
    constructor
    · exact le_max_left 0 _
    · -- max(0, L₂-U₁) ≤ 1
      apply max_le
      · norm_num
      · linarith [itv2.lower_in_unit.1, itv2.lower_in_unit.2, itv1.upper_in_unit.1]
  upper_in_unit := by
    constructor
    · -- 0 ≤ min(1, 1-L₁+U₂)
      apply le_min
      · norm_num
      · linarith [itv1.lower_in_unit.1, itv1.lower_in_unit.2, itv2.upper_in_unit.1, itv2.upper_in_unit.2]
    · exact min_le_left 1 _
  credibility_in_unit := by
    constructor
    · cases' le_total itv1.credibility itv2.credibility with h h
      · rw [min_eq_left h]; exact itv1.credibility_in_unit.1
      · rw [min_eq_right h]; exact itv2.credibility_in_unit.1
    · cases' le_total itv1.credibility itv2.credibility with h h
      · rw [min_eq_left h]; exact itv1.credibility_in_unit.2
      · rw [min_eq_right h]; exact itv2.credibility_in_unit.2

/-- Negation: ¬[L, U] = [1-U, 1-L]
Credibility remains unchanged (same evidence). -/
def negation (itv : ITV) : ITV where
  lower := 1 - itv.upper
  upper := 1 - itv.lower
  credibility := itv.credibility
  lower_le_upper := by linarith [itv.lower_le_upper]
  lower_in_unit := by
    constructor
    · linarith [itv.upper_in_unit.2]
    · linarith [itv.lower_in_unit.1, itv.lower_le_upper]
  upper_in_unit := by
    constructor
    · linarith [itv.lower_in_unit.2, itv.lower_le_upper]
    · linarith [itv.lower_in_unit.1]
  credibility_in_unit := itv.credibility_in_unit

end ITV

/-! ## Summary

We have implemented:

1. **ITV structure** with lower, upper, credibility (3 components)
2. **Orthogonality** between credibility and interval width (by design)
3. **fromBayesCredibleNormalApprox** for Bayesian credible-interval semantics
4. **fromWalleyIDMPredictive** for Walley IDM predictive-interval semantics
5. **Conversions** to/from WTV (with information loss warnings)
6. **Examples** showing the three-component model in action

Next steps (Phase 3-4):
- Heyting operations (conjunction, disjunction, implication)
- Key theorems (orthogonality proof, soundness, Kyburg connection)
- Integration with PLNInferenceCalculus

This resolves the counterexample in `PLNSoundnessCounterexample.lean` by
keeping intervals and credibility separate (no forced e = 1-c relationship).
-/

end Mettapedia.Logic.PLNIndefiniteTruth
