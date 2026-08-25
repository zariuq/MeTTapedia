import Mettapedia.PLN.TruthValues.PLNTruthTower

/-!
# Finite evidence with a future horizon

This module isolates the common finite algebra behind several interval
readouts.  A binary evidence state supplies positive and negative weight, and
a strictly positive horizon records how much unresolved evidence may arrive in
the next comparison window.  The induced interval is

`[n⁺/(n+k), (n⁺+k)/(n+k)]`

with evidence credibility `n/(n+k)`.

The object is deliberately interpretation-neutral.  Walley's binary IDM gives
the bounds a coherent lower/upper predictive-probability interpretation.
Pei Wang's NARS gives the same numbers an experience-grounded interpretation
relative to a retained body and scope of evidence.  Those interpretations are
connected in dedicated bridge modules rather than identified here.
-/

namespace Mettapedia.PLN.TruthValues.EvidenceHorizonInterval

open Mettapedia.PLN.TruthValues.PLNTruthTower
open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth

/-- Finite nonnegative binary evidence together with a strictly positive
future-evidence horizon. -/
structure EvidenceHorizon where
  counts : BinaryCounts
  horizon : ℝ
  horizon_pos : 0 < horizon

namespace EvidenceHorizon

/-- Two interval records are equal when their three informative coordinates
are equal; proof fields carry no additional data. -/
theorem itv_ext {left right : ITV}
    (lower_eq : left.lower = right.lower)
    (upper_eq : left.upper = right.upper)
    (credibility_eq : left.credibility = right.credibility) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Total current evidence plus the future horizon. -/
noncomputable def denominator (x : EvidenceHorizon) : ℝ :=
  x.counts.total + x.horizon

theorem denominator_pos (x : EvidenceHorizon) : 0 < x.denominator := by
  unfold denominator
  linarith [x.counts.total_nonneg, x.horizon_pos]

theorem denominator_ne_zero (x : EvidenceHorizon) : x.denominator ≠ 0 :=
  ne_of_gt x.denominator_pos

/-- Lower frequency after an entirely negative horizon. -/
noncomputable def lower (x : EvidenceHorizon) : ℝ :=
  x.counts.nPlus / x.denominator

/-- Upper frequency after an entirely positive horizon. -/
noncomputable def upper (x : EvidenceHorizon) : ℝ :=
  (x.counts.nPlus + x.horizon) / x.denominator

/-- Current evidence as a fraction of current-plus-future evidence. -/
noncomputable def credibility (x : EvidenceHorizon) : ℝ :=
  x.counts.total / x.denominator

/-- The interpretation-neutral interval readout of finite evidence and a
future horizon. -/
noncomputable def toITV (x : EvidenceHorizon) : ITV where
  lower := x.lower
  upper := x.upper
  credibility := x.credibility
  lower_le_upper := by
    unfold lower upper
    exact div_le_div_of_nonneg_right
      (by linarith [x.horizon_pos]) (le_of_lt x.denominator_pos)
  lower_in_unit := by
    constructor
    · exact div_nonneg x.counts.nPlus_nonneg (le_of_lt x.denominator_pos)
    · apply (div_le_one x.denominator_pos).2
      unfold denominator BinaryCounts.total
      linarith [x.counts.nMinus_nonneg, x.horizon_pos]
  upper_in_unit := by
    constructor
    · exact div_nonneg
        (by linarith [x.counts.nPlus_nonneg, x.horizon_pos])
        (le_of_lt x.denominator_pos)
    · apply (div_le_one x.denominator_pos).2
      unfold denominator BinaryCounts.total
      linarith [x.counts.nMinus_nonneg]
  credibility_in_unit := by
    constructor
    · exact div_nonneg x.counts.total_nonneg (le_of_lt x.denominator_pos)
    · apply (div_le_one x.denominator_pos).2
      unfold denominator
      linarith [x.horizon_pos]

@[simp] theorem toITV_lower (x : EvidenceHorizon) :
    x.toITV.lower = x.lower := rfl

@[simp] theorem toITV_upper (x : EvidenceHorizon) :
    x.toITV.upper = x.upper := rfl

@[simp] theorem toITV_credibility (x : EvidenceHorizon) :
    x.toITV.credibility = x.credibility := rfl

/-- Interval width is precisely the unresolved future fraction. -/
theorem toITV_width (x : EvidenceHorizon) :
    x.toITV.width = x.horizon / x.denominator := by
  unfold ITV.width
  rw [toITV_upper, toITV_lower]
  unfold lower upper
  rw [div_sub_div_same]
  congr 1
  ring

/-- Width and evidence credibility are complementary for this selected
finite-horizon readout. -/
theorem width_add_credibility (x : EvidenceHorizon) :
    x.toITV.width + x.toITV.credibility = 1 := by
  rw [toITV_width, toITV_credibility]
  unfold credibility
  rw [← add_div]
  calc
    (x.horizon + x.counts.total) / x.denominator =
        x.denominator / x.denominator := by
          congr 1
          unfold denominator
          ac_rfl
    _ = 1 := div_self x.denominator_ne_zero

/-- Common positive rescaling of current evidence and future horizon. -/
def scale (x : EvidenceHorizon) (factor : ℝ) (factor_pos : 0 < factor) :
    EvidenceHorizon where
  counts :=
    { nPlus := factor * x.counts.nPlus
      nMinus := factor * x.counts.nMinus
      nPlus_nonneg := mul_nonneg factor_pos.le x.counts.nPlus_nonneg
      nMinus_nonneg := mul_nonneg factor_pos.le x.counts.nMinus_nonneg }
  horizon := factor * x.horizon
  horizon_pos := mul_pos factor_pos x.horizon_pos

@[simp] theorem scale_denominator
    (x : EvidenceHorizon) (factor : ℝ) (factor_pos : 0 < factor) :
    (x.scale factor factor_pos).denominator = factor * x.denominator := by
  unfold scale denominator BinaryCounts.total
  ring

@[simp] theorem scale_lower
    (x : EvidenceHorizon) (factor : ℝ) (factor_pos : 0 < factor) :
    (x.scale factor factor_pos).lower = x.lower := by
  unfold lower
  rw [scale_denominator]
  simp only [scale]
  field_simp [ne_of_gt factor_pos, x.denominator_ne_zero]

@[simp] theorem scale_upper
    (x : EvidenceHorizon) (factor : ℝ) (factor_pos : 0 < factor) :
    (x.scale factor factor_pos).upper = x.upper := by
  unfold upper
  rw [scale_denominator]
  simp only [scale]
  field_simp [ne_of_gt factor_pos, x.denominator_ne_zero]

@[simp] theorem scale_credibility
    (x : EvidenceHorizon) (factor : ℝ) (factor_pos : 0 < factor) :
    (x.scale factor factor_pos).credibility = x.credibility := by
  unfold credibility BinaryCounts.total
  rw [scale_denominator]
  simp only [scale]
  field_simp [ne_of_gt factor_pos, x.denominator_ne_zero]

/-- Frequency bounds are invariant under a common change of evidence unit. -/
theorem scale_toITV
    (x : EvidenceHorizon) (factor : ℝ) (factor_pos : 0 < factor) :
    (x.scale factor factor_pos).toITV = x.toITV := by
  apply itv_ext <;> simp

/-- Regard existing extended-nonnegative binary evidence as a finite real
evidence horizon.  Finiteness is reflected by `ENNReal.toReal`; infinite
evidence belongs to a different semantic layer. -/
noncomputable def ofBinaryEvidence
    (e : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (horizon : ℝ) (horizon_pos : 0 < horizon) : EvidenceHorizon where
  counts :=
    { nPlus := e.pos.toReal
      nMinus := e.neg.toReal
      nPlus_nonneg := ENNReal.toReal_nonneg
      nMinus_nonneg := ENNReal.toReal_nonneg }
  horizon := horizon
  horizon_pos := horizon_pos

/-- The existing Walley-IDM constructor is an instance of the general finite
evidence-horizon interval. -/
theorem ofBinaryEvidence_toITV_eq_fromWalleyIDMPredictive
    (e : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (horizon : ℝ) (horizon_pos : 0 < horizon) :
    (ofBinaryEvidence e horizon horizon_pos).toITV =
      ITV.fromWalleyIDMPredictive e horizon horizon_pos := by
  apply itv_ext <;>
    simp [ofBinaryEvidence, lower, upper, credibility, denominator,
      BinaryCounts.total]

end EvidenceHorizon

end Mettapedia.PLN.TruthValues.EvidenceHorizonInterval
