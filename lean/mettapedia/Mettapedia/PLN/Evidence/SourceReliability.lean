import Mettapedia.PLN.Evidence.BinEvNat
import Mettapedia.PLN.Evidence.EvidenceKind

/-!
# Source Reliability Model (Dawid-Skene Layer)

The MODEL (not the EM algorithm) for source-specific reliability:
each evidence source has an accuracy profile that determines how much
its contributions should be trusted.

## Design

This is EvidentialLedger Layer 2: the reliability layer that sits
ABOVE the additive evidence composition (Layer 1). It does NOT
replace additive aggregation — it ADJUSTS the contributions before
they enter the additive fold.

Key separation (Dawid & Skene 1979):
- Layer 1 (EvidentialLedger): aggregate → evidence
- Layer 2 (this file): reliability → adjusted evidence → aggregate

## What This File Does

1. Defines `ReliabilityProfile`: per-source accuracy (tp_rate, tn_rate)
2. Defines `reliabilityAdjust`: scale evidence by accuracy
3. Proves: perfect accuracy preserves, zero accuracy zeroes, monotonicity
4. Defines `defaultReliability`: EvidenceKind-dependent priors

## What This File Does NOT Do

- EM algorithm for learning reliability from data (future work)
- Confusion matrices or Rasch models (more complex reliability models)
- Integration with `WeightedSourceItem` (already have `weight : Nat`)

## References

- Dawid & Skene 1979: "ML Estimation of Observer Error-Rates Using EM"
- O'Hagan 2019: expert elicitation with reliability priors
- Colson & Cooke 2018: classical model for expert validation

0 sorry.
-/

namespace Mettapedia.PLN.Evidence.SourceReliability

open Mettapedia.PLN.Evidence

/-! ## 1. Reliability profile -/

/-- Per-source reliability profile.
    `tpRate` = P(source reports + | truth is +) (sensitivity)
    `tnRate` = P(source reports − | truth is −) (specificity)
    Both in [0, 1000] (× 1000 encoding for kernel-checkable arithmetic). -/
structure ReliabilityProfile where
  tpRate : Nat  -- true positive rate × 1000 (1000 = perfect)
  tnRate : Nat  -- true negative rate × 1000 (1000 = perfect)
  calibrationObs : Nat  -- number of calibration observations
  deriving DecidableEq, BEq, Repr

/-! ## 2. Named profiles -/

/-- Perfect reliability: source always reports correctly. -/
def perfectProfile : ReliabilityProfile := ⟨1000, 1000, 0⟩

/-- Uninformative profile: source reports randomly. -/
def uninformativeProfile : ReliabilityProfile := ⟨500, 500, 0⟩

/-- Zero reliability: source always reports opposite. -/
def invertedProfile : ReliabilityProfile := ⟨0, 0, 0⟩

/-! ## 3. Reliability adjustment -/

/-- Adjust raw evidence by source reliability.
    Positive evidence scaled by true positive rate.
    Negative evidence scaled by true negative rate. -/
def reliabilityAdjust (p : ReliabilityProfile) (raw : BinEvNat) : BinEvNat :=
  ⟨p.tpRate * raw.pos / 1000, p.tnRate * raw.neg / 1000⟩

/-! ## 4. Properties -/

/-- Perfect reliability preserves raw evidence. -/
theorem perfect_preserves (raw : BinEvNat) :
    reliabilityAdjust perfectProfile raw = raw := by
  simp [reliabilityAdjust, perfectProfile]

/-- Uninformative reliability halves everything. -/
theorem uninformative_halves (raw : BinEvNat) :
    (reliabilityAdjust uninformativeProfile raw).pos = raw.pos / 2 ∧
    (reliabilityAdjust uninformativeProfile raw).neg = raw.neg / 2 := by
  simp [reliabilityAdjust, uninformativeProfile]
  omega

/-- Inverted reliability zeroes everything. -/
theorem inverted_zeroes (raw : BinEvNat) :
    reliabilityAdjust invertedProfile raw = ⟨0, 0⟩ := by
  simp [reliabilityAdjust, invertedProfile]

/-- Higher tp rate → more positive evidence preserved. -/
theorem tpRate_monotone (p₁ p₂ : ReliabilityProfile) (raw : BinEvNat)
    (h : p₁.tpRate ≤ p₂.tpRate) :
    (reliabilityAdjust p₁ raw).pos ≤ (reliabilityAdjust p₂ raw).pos := by
  simp [reliabilityAdjust]
  exact Nat.div_le_div_right (Nat.mul_le_mul_right raw.pos h)

/-- Higher tn rate → more negative evidence preserved. -/
theorem tnRate_monotone (p₁ p₂ : ReliabilityProfile) (raw : BinEvNat)
    (h : p₁.tnRate ≤ p₂.tnRate) :
    (reliabilityAdjust p₁ raw).neg ≤ (reliabilityAdjust p₂ raw).neg := by
  simp [reliabilityAdjust]
  exact Nat.div_le_div_right (Nat.mul_le_mul_right raw.neg h)

/-! ## 5. EvidenceKind-dependent default reliability

Different epistemic kinds get different default reliability priors.
Empirical evidence (checkLang, data) gets high default reliability.
Expert-elicited gets moderate. Model-derived and text-interpreted
get lower defaults. -/

def defaultReliability : EvidenceKind → ReliabilityProfile
  | .empirical         => ⟨950, 950, 50⟩   -- high: data-backed
  | .expertElicited    => ⟨800, 800, 10⟩   -- moderate: structured judgment
  | .modelDerived      => ⟨700, 700, 5⟩    -- lower: model may be miscalibrated
  | .textInterpreted   => ⟨600, 600, 2⟩    -- low: human interpretation of text
  | .logicalDerivation => ⟨900, 900, 20⟩   -- high: formal entailment

/-- Empirical evidence has higher default reliability than text-interpreted. -/
theorem empirical_more_reliable_than_text :
    (defaultReliability .empirical).tpRate >
    (defaultReliability .textInterpreted).tpRate := by decide

/-- Logical derivation has higher reliability than model-derived. -/
theorem logical_more_reliable_than_model :
    (defaultReliability .logicalDerivation).tpRate >
    (defaultReliability .modelDerived).tpRate := by decide

/-! ## 6. Summary -/

theorem reliability_summary :
    -- Perfect preserves
    reliabilityAdjust perfectProfile ⟨10, 5⟩ = ⟨10, 5⟩ ∧
    -- Inverted zeroes
    reliabilityAdjust invertedProfile ⟨10, 5⟩ = ⟨0, 0⟩ ∧
    -- Empirical > text-interpreted
    (defaultReliability .empirical).tpRate > (defaultReliability .textInterpreted).tpRate := by
  decide

end Mettapedia.PLN.Evidence.SourceReliability
