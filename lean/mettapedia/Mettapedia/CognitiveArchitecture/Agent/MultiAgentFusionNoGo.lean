import Mathlib

/-!
# A Local-Compatibility No-Go for Multi-Agent Evidence Fusion

Source provenance: adapted from GödelClaw commit
`3a52d481c13b23926fcc42c9d171f33823d1f1c0`; only module packaging and
taxonomy-facing names were changed during integration.

Three pairwise probability charts can agree on every one-variable overlap yet
fail to arise from any single classical joint distribution.  This file gives
an exact rational witness.

The result does not prohibit multi-agent systems.  It prohibits a particular
fusion rule: treating pairwise overlap compatibility as sufficient evidence
that one global classical model exists.
-/

namespace Mettapedia.CognitiveArchitecture.Agent.MultiAgentFusionNoGo

/-- A probability chart for two signs, ordered as `--`, `-+`, `+-`, `++`. -/
structure PairChart where
  mm : ℚ
  mp : ℚ
  pm : ℚ
  pp : ℚ
deriving DecidableEq, Repr

/-- The shared local chart used by the counterexample. -/
def antiChart : PairChart where
  mm := 1 / 16
  mp := 7 / 16
  pm := 7 / 16
  pp := 1 / 16

def PairChart.leftMinus (chart : PairChart) : ℚ := chart.mm + chart.mp
def PairChart.leftPlus (chart : PairChart) : ℚ := chart.pm + chart.pp
def PairChart.rightMinus (chart : PairChart) : ℚ := chart.mm + chart.pm
def PairChart.rightPlus (chart : PairChart) : ℚ := chart.mp + chart.pp
def PairChart.total (chart : PairChart) : ℚ :=
  chart.mm + chart.mp + chart.pm + chart.pp

/-- Every one-variable marginal of `antiChart` is uniform. -/
theorem antiChart_has_uniform_overlaps :
    antiChart.leftMinus = 1 / 2 ∧
    antiChart.leftPlus = 1 / 2 ∧
    antiChart.rightMinus = 1 / 2 ∧
    antiChart.rightPlus = 1 / 2 ∧
    antiChart.total = 1 := by
  norm_num [antiChart, PairChart.leftMinus, PairChart.leftPlus,
    PairChart.rightMinus, PairChart.rightPlus, PairChart.total]

/-- A candidate classical joint distribution for three signs `X`, `Y`, `Z`.
The field names give their signs in that order. -/
structure Joint3 where
  mmm : ℚ
  mmp : ℚ
  mpm : ℚ
  mpp : ℚ
  pmm : ℚ
  pmp : ℚ
  ppm : ℚ
  ppp : ℚ
  mmm_nonneg : 0 ≤ mmm
  mmp_nonneg : 0 ≤ mmp
  mpm_nonneg : 0 ≤ mpm
  mpp_nonneg : 0 ≤ mpp
  pmm_nonneg : 0 ≤ pmm
  pmp_nonneg : 0 ≤ pmp
  ppm_nonneg : 0 ≤ ppm
  ppp_nonneg : 0 ≤ ppp
  total : mmm + mmp + mpm + mpp + pmm + pmp + ppm + ppp = 1

def Joint3.xy (joint : Joint3) : PairChart where
  mm := joint.mmm + joint.mmp
  mp := joint.mpm + joint.mpp
  pm := joint.pmm + joint.pmp
  pp := joint.ppm + joint.ppp

def Joint3.xz (joint : Joint3) : PairChart where
  mm := joint.mmm + joint.mpm
  mp := joint.mmp + joint.mpp
  pm := joint.pmm + joint.ppm
  pp := joint.pmp + joint.ppp

def Joint3.yz (joint : Joint3) : PairChart where
  mm := joint.mmm + joint.pmm
  mp := joint.mmp + joint.pmp
  pm := joint.mpm + joint.ppm
  pp := joint.mpp + joint.ppp

/-- A joint distribution realizes the local evidence when all three of its
pairwise marginals equal the supplied chart. -/
def RealizesAllPairs (joint : Joint3) (chart : PairChart) : Prop :=
  joint.xy = chart ∧ joint.xz = chart ∧ joint.yz = chart

/-- The three locally compatible anti-correlated charts have no classical
global realization.

Proof idea: each deterministic three-sign assignment disagrees on either zero
or two pairs, so a joint distribution has total pairwise disagreement at most
two.  The proposed charts demand `3 * (7/8) = 21/8`, which is larger than two.
-/
theorem antiChart_has_no_global_joint :
    ¬ ∃ joint : Joint3, RealizesAllPairs joint antiChart := by
  rintro ⟨joint, hxy, hxz, hyz⟩
  have hxy_mp := congrArg PairChart.mp hxy
  have hxy_pm := congrArg PairChart.pm hxy
  have hxz_mp := congrArg PairChart.mp hxz
  have hxz_pm := congrArg PairChart.pm hxz
  have hyz_mp := congrArg PairChart.mp hyz
  have hyz_pm := congrArg PairChart.pm hyz
  simp only [Joint3.xy, Joint3.xz, Joint3.yz, antiChart] at hxy_mp hxy_pm hxz_mp hxz_pm hyz_mp hyz_pm
  linarith [joint.total, joint.mmm_nonneg, joint.ppp_nonneg]

/-- Pairwise overlap compatibility alone is therefore insufficient for a
multi-agent fusion step that promises one classical global distribution. -/
theorem pairwise_compatible_not_gluable :
    (antiChart.leftMinus = antiChart.rightMinus) ∧
    (antiChart.leftPlus = antiChart.rightPlus) ∧
    ¬ ∃ joint : Joint3, RealizesAllPairs joint antiChart := by
  constructor
  · norm_num [antiChart, PairChart.leftMinus, PairChart.rightMinus]
  constructor
  · norm_num [antiChart, PairChart.leftPlus, PairChart.rightPlus]
  · exact antiChart_has_no_global_joint

end Mettapedia.CognitiveArchitecture.Agent.MultiAgentFusionNoGo

#print axioms Mettapedia.CognitiveArchitecture.Agent.MultiAgentFusionNoGo.antiChart_has_uniform_overlaps
#print axioms Mettapedia.CognitiveArchitecture.Agent.MultiAgentFusionNoGo.antiChart_has_no_global_joint
#print axioms Mettapedia.CognitiveArchitecture.Agent.MultiAgentFusionNoGo.pairwise_compatible_not_gluable
