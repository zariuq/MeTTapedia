import Mettapedia.CognitiveArchitecture.MetaMo.Main
import Mettapedia.NARS.Control.ONA

/-!
# ONA control observations in MetaMo

This module compares two distinct constructions:

* Patrick Hammer and Tony Lofthouse's ONA control architecture supplies bounded
  priorities, normalized concept usefulness, attention thresholds, and finite
  scheduling contracts.
* Ben Goertzel and Ying Lian's MetaMo supplies quantale-module dynamics for
  modulating a family of intensities.

The bridge embeds selected ONA control observations into a pointwise MetaMo
module. It does not identify ONA's scheduler with MetaMo dynamics. In
particular, unrestricted MetaMo amplification need not preserve ONA's unit
bounds; the negative theorem below makes that boundary explicit.

References:

* P. Hammer and T. Lofthouse, *OpenNARS for Applications: Architecture and
  Control*, AGI 2020.
* B. Goertzel and Y. Lian, *Weakness and Its Quantale: Plausibility Theory from
  First Principles*.
-/

namespace Mettapedia.NARS.Bridges.CognitiveArchitecture.MetaMo

open Mettapedia.CognitiveArchitecture.MetaMo
open Mettapedia.NARS.Control.ONA
open scoped ENNReal

/-! ## Architecture-neutral observation coordinates -/

/-- ONA control quantities that can be observed as nonnegative intensities.
These are observation coordinates, not a replacement for ONA's event, memory,
or cycle state. -/
inductive ControlCoordinate where
  | eventPriority
  | conceptPriority
  | conceptUsefulness
  | attentionThreshold
  deriving DecidableEq, Fintype

/-- A nonnegative control-intensity profile. The generic pointwise module in
`MetaMo.Basic` provides its `QModule` structure. -/
abbrev ControlProfile := ControlCoordinate → ℝ≥0∞

/-- The ONA unit-interval discipline, stated independently of how a profile is
modulated in MetaMo. -/
def UnitBounded (profile : ControlProfile) : Prop :=
  ∀ coordinate, profile coordinate ≤ 1

/-- Embed a real-valued control observation into the nonnegative MetaMo
carrier. Negative inputs are truncated by `ENNReal.ofReal`. -/
noncomputable def intensity (value : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal value

/-- A source-faithful ONA event supplies the event-priority coordinate; the
remaining coordinates require concept and scheduler state and therefore remain
zero in this partial observation. -/
noncomputable def ofEvent {Term Source : Type*}
    (event : Event Term Source) : ControlProfile
  | .eventPriority => intensity event.priority
  | _ => 0

/-- ONA's event-priority invariant survives the observation map. -/
theorem ofEvent_unitBounded {Term Source : Type*} (event : Event Term Source) :
    UnitBounded (ofEvent event) := by
  intro coordinate
  cases coordinate <;> simp [ofEvent, intensity, event.priority_le_one]

/-- A concept-usage observation occupies exactly the normalized-usefulness
coordinate. -/
noncomputable def ofUsage (now : ℕ) (record : UsageRecord) : ControlProfile
  | .conceptUsefulness => intensity (record.usefulness now)
  | _ => 0

/-- Hammer--Lofthouse normalization puts every observed concept usefulness
strictly below one, hence inside the bridge's closed unit bound. -/
theorem ofUsage_unitBounded (now : ℕ) (record : UsageRecord) :
    UnitBounded (ofUsage now record) := by
  intro coordinate
  cases coordinate <;>
    simp [ofUsage, intensity, (record.usefulness_mem_Ico now).2.le]

/-! ## MetaMo laws and the unit-bound seam -/

/-- MetaMo appraisal and decision commute on ONA control-observation profiles.
This follows from the shared pointwise module, not from an extra ONA axiom. -/
theorem appraisal_decision_commute
    (sensitivity decisionWeight : ℝ≥0∞) (profile : ControlProfile) :
    appraisalFunctor sensitivity (decisionFunctor decisionWeight profile) =
      decisionFunctor decisionWeight (appraisalFunctor sensitivity profile) :=
  Mettapedia.CognitiveArchitecture.MetaMo.appraisal_decision_commute
    sensitivity decisionWeight profile

/-- The induced MetaMo dynamics are monotone in the observed control profile. -/
theorem dynamics_mono (sensitivity decisionWeight : ℝ≥0∞)
    {left right : ControlProfile} (profiles_le : left ≤ right) :
    motivationalDynamics sensitivity decisionWeight left ≤
      motivationalDynamics sensitivity decisionWeight right :=
  motivationalDynamics_mono sensitivity decisionWeight profiles_le

/-- Dampening by a scalar at most one preserves ONA's unit-interval control
discipline. -/
theorem appraisal_preserves_unitBounded {sensitivity : ℝ≥0∞}
    (sensitivity_le_one : sensitivity ≤ 1) {profile : ControlProfile}
    (profile_bounded : UnitBounded profile) :
    UnitBounded (appraisalFunctor sensitivity profile) := by
  intro coordinate
  simp only [appraisalFunctor_apply, pi_smul_apply]
  change sensitivity * profile coordinate ≤ 1
  calc
    sensitivity * profile coordinate ≤ 1 * 1 :=
      mul_le_mul sensitivity_le_one (profile_bounded coordinate) bot_le bot_le
    _ = 1 := one_mul 1

/-- A concrete unit-bounded ONA-style observation used to test the bridge. -/
noncomputable def normalizedUsefulnessExample : ControlProfile
  | .conceptUsefulness => ENNReal.ofReal (3 / 4 : ℝ)
  | _ => 0

theorem normalizedUsefulnessExample_unitBounded :
    UnitBounded normalizedUsefulnessExample := by
  intro coordinate
  cases coordinate <;>
    norm_num [normalizedUsefulnessExample, ENNReal.ofReal_le_one]

/-- Negative control: unrestricted MetaMo amplification is not an ONA state
transition. Doubling a normalized usefulness of `3/4` leaves the unit interval,
so bounded ONA profiles require bounded scalars or a separately proved clamp. -/
theorem unrestricted_appraisal_can_break_unitBound :
    ¬ UnitBounded
      (appraisalFunctor (2 : ℝ≥0∞) normalizedUsefulnessExample) := by
  intro bounded
  have at_usefulness := bounded ControlCoordinate.conceptUsefulness
  change (2 : ℝ≥0∞) * ENNReal.ofReal (3 / 4 : ℝ) ≤ 1 at at_usefulness
  have real_le := ENNReal.toReal_mono ENNReal.one_ne_top at_usefulness
  norm_num at real_le

#print axioms ofEvent_unitBounded
#print axioms appraisal_decision_commute
#print axioms appraisal_preserves_unitBounded
#print axioms unrestricted_appraisal_can_break_unitBound

end Mettapedia.NARS.Bridges.CognitiveArchitecture.MetaMo
