import Mettapedia.FluidDynamics.NavierStokes.ModeStateLogEnergyChartFork
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Generic Energy-Profile Fork on the Shared Mode State

This file packages a reusable theorem pattern on the shared `ModeState`.
Any globally continuous energy profile `ρ` satisfying

* `0 ≤ ρ(u)` for `u ≥ 0`,
* `ρ(u) ≤ u` for `u ≥ 0`,
* `ρ(0) = 0`,
* `ρ(u) > 0` for `u > 0`,

lands in the same soft-vs-hard fork:

* the summably compensated soft radius is continuous and truncation-friendly;
* the corresponding hard detector is tail-spike stable and therefore not
  continuous at `modeZero`.

The identity profile, the clipped log profile `u ↦ log(1 + max u 0)`, the
bounded rational saturation `u ↦ u / (1 + u)`, and the smooth exponential
saturation `u ↦ 1 - exp(-u)` on nonnegative inputs, and a mathlib smooth
transition profile `u ↦ u * smoothTransition(u)` are provided as canonical
instances. A positive-parameter scaled smooth-transition family
`u ↦ u * smoothTransition(cu)` is also formalized.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter
open scoped Classical

section ModeStateEnergyProfileFork

/-- A globally continuous radial energy profile that is nonnegative,
dominated by the identity on nonnegative inputs, and strictly positive on
positive inputs. -/
structure EnergyProfile where
  profile : ℝ → ℝ
  continuous_profile : Continuous profile
  profile_nonneg : ∀ u, 0 ≤ u → 0 ≤ profile u
  profile_le : ∀ u, 0 ≤ u → profile u ≤ u
  profile_zero : profile 0 = 0
  profile_pos : ∀ u, 0 < u → 0 < profile u

/-- Soft profiled energy term. -/
def profiledEnergyTerm (P : EnergyProfile) (m : ℕ) (x : ModeState) (n : ℕ) : ℝ :=
  P.profile ((sobolevAmplification m x n) ^ (2 : ℕ)) * sobolevEnergyWeight m n

/-- Soft profiled energy radius. -/
def profiledEnergyRadius (P : EnergyProfile) (m : ℕ) (x : ModeState) : ℝ :=
  ∑' n, profiledEnergyTerm P m x n

/-- Zeroth visible mode plus the profiled energy radius. -/
def profiledEnergyStatistic (P : EnergyProfile) (m : ℕ) (x : ModeState) : ℝ :=
  x.coeff 0 + profiledEnergyRadius P m x

/-- Hard detector induced by the profile. -/
def hardProfileThresholdRadius (P : EnergyProfile) (m : ℕ) (x : ModeState) : ℝ :=
  if ∃ n, 0 < P.profile ((sobolevAmplification m x n) ^ (2 : ℕ)) then 1 else 0

theorem continuous_profiledEnergyTerm (P : EnergyProfile) (m n : ℕ) :
    Continuous fun x : ModeState => profiledEnergyTerm P m x n := by
  simpa [profiledEnergyTerm] using
    ((P.continuous_profile.comp ((continuous_sobolevAmplification m n).pow 2)).mul
      (continuous_const : Continuous fun _ : ModeState => sobolevEnergyWeight m n))

theorem profiledEnergyTerm_le_sobolevEnergyTerm
    (P : EnergyProfile) (m : ℕ) (x : ModeState) (n : ℕ) :
    profiledEnergyTerm P m x n ≤ sobolevEnergyTerm m x n := by
  have hsq_nonneg : 0 ≤ (sobolevAmplification m x n) ^ (2 : ℕ) := by positivity
  exact mul_le_mul_of_nonneg_right
    (P.profile_le _ hsq_nonneg) (sobolevEnergyWeight_nonneg m n)

theorem norm_profiledEnergyTerm_le_inverseSquare
    (P : EnergyProfile) (m : ℕ) (x : ModeState) (n : ℕ) :
    ‖profiledEnergyTerm P m x n‖ ≤ inverseSquareModeWeights.weight n := by
  have hprof_nonneg : 0 ≤ P.profile ((sobolevAmplification m x n) ^ (2 : ℕ)) := by
    have hsq_nonneg : 0 ≤ (sobolevAmplification m x n) ^ (2 : ℕ) := by positivity
    exact P.profile_nonneg _ hsq_nonneg
  have hterm_nonneg : 0 ≤ profiledEnergyTerm P m x n := by
    exact mul_nonneg hprof_nonneg (sobolevEnergyWeight_nonneg m n)
  have hsoft_nonneg : 0 ≤ sobolevEnergyTerm m x n := by
    exact mul_nonneg (by positivity) (sobolevEnergyWeight_nonneg m n)
  calc
    ‖profiledEnergyTerm P m x n‖ = profiledEnergyTerm P m x n := by
      rw [Real.norm_eq_abs, abs_of_nonneg hterm_nonneg]
    _ ≤ sobolevEnergyTerm m x n := profiledEnergyTerm_le_sobolevEnergyTerm P m x n
    _ ≤ inverseSquareModeWeights.weight n := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hsoft_nonneg] using
        norm_sobolevEnergyTerm_le_inverseSquare m x n

theorem continuous_profiledEnergyRadius (P : EnergyProfile) (m : ℕ) :
    Continuous (profiledEnergyRadius P m) := by
  unfold profiledEnergyRadius
  refine continuous_tsum (fun n => continuous_profiledEnergyTerm P m n)
    inverseSquareModeWeights.summable_weight ?_
  intro n x
  exact norm_profiledEnergyTerm_le_inverseSquare P m x n

theorem continuous_profiledEnergyStatistic (P : EnergyProfile) (m : ℕ) :
    Continuous (profiledEnergyStatistic P m) := by
  unfold profiledEnergyStatistic
  exact (continuous_coeffObservable 0).add (continuous_profiledEnergyRadius P m)

theorem tendsto_profiledEnergyRadius_truncateModes
    (P : EnergyProfile) (m : ℕ) (x : ModeState) :
    Tendsto (fun N => profiledEnergyRadius P m (truncateModes N x))
      Filter.atTop (nhds (profiledEnergyRadius P m x)) := by
  exact (continuous_profiledEnergyRadius P m).continuousAt.tendsto.comp
    (tendsto_truncateModes_modeState x)

theorem tendsto_profiledEnergyStatistic_truncateModes
    (P : EnergyProfile) (m : ℕ) (x : ModeState) :
    Tendsto (fun N => profiledEnergyStatistic P m (truncateModes N x))
      Filter.atTop (nhds (profiledEnergyStatistic P m x)) := by
  exact (continuous_profiledEnergyStatistic P m).continuousAt.tendsto.comp
    (tendsto_truncateModes_modeState x)

theorem continuous_profiledEnergy_cutoffPotential
    (P : EnergyProfile) (m : ℕ) {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    Continuous (cutoffPotential cutoff (profiledEnergyRadius P m) (profiledEnergyStatistic P m)) := by
  exact continuous_cutoffPotential hcutoff
    (continuous_profiledEnergyRadius P m) (continuous_profiledEnergyStatistic P m)

theorem continuous_profiledEnergy_coleHopfPhi
    (P : EnergyProfile) (m : ℕ) {ν : ℝ} {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    Continuous (coleHopfPhi ν
      (cutoffPotential cutoff (profiledEnergyRadius P m) (profiledEnergyStatistic P m))) := by
  exact continuous_cutoffColeHopfPhi hcutoff
    (continuous_profiledEnergyRadius P m) (continuous_profiledEnergyStatistic P m)

theorem hardProfileThresholdRadius_tailSpikeStableAt_one
    (P : EnergyProfile) (m : ℕ) :
    TailSpikeStableAt (hardProfileThresholdRadius P m) 1 := by
  intro N
  unfold hardProfileThresholdRadius
  split_ifs with h
  · rfl
  · exfalso
    apply h
    refine ⟨N, ?_⟩
    have hsq_pos : 0 < (((N + 1 : ℝ) ^ m) ^ (2 : ℕ)) := by positivity
    have hprof_pos : 0 < P.profile ((((N + 1 : ℝ) ^ m) ^ (2 : ℕ))) :=
      P.profile_pos _ hsq_pos
    simpa [sobolevAmplification, tailSpikeMode] using hprof_pos

theorem hardProfileThresholdRadius_modeZero
    (P : EnergyProfile) (m : ℕ) :
    hardProfileThresholdRadius P m modeZero = 0 := by
  unfold hardProfileThresholdRadius
  split_ifs with h
  · rcases h with ⟨n, hn⟩
    simp [sobolevAmplification, modeZero, P.profile_zero] at hn
  · rfl

theorem not_continuousAt_hardProfileThresholdRadius_modeZero
    (P : EnergyProfile) (m : ℕ) :
    ¬ ContinuousAt (hardProfileThresholdRadius P m) modeZero := by
  refine not_continuousAt_of_tailSpikeStableAt
    (hardProfileThresholdRadius_tailSpikeStableAt_one P m) ?_
  simp [hardProfileThresholdRadius_modeZero]

theorem not_continuousAt_hardProfileThreshold_cutoffPotential_modeZero
    (P : EnergyProfile) (m : ℕ) :
    ¬ ContinuousAt
      (cutoffPotential (fun r => r) (hardProfileThresholdRadius P m) unitStatisticMode)
      modeZero := by
  exact not_continuousAt_cutoffPotential_of_tailSpikeStableAt
    (hardProfileThresholdRadius_tailSpikeStableAt_one P m)
    tendsto_unitStatisticMode_tailSpikeMode
    (by
      unfold cutoffPotential
      rw [hardProfileThresholdRadius_modeZero]
      norm_num [unitStatisticMode, modeZero])

theorem not_continuousAt_hardProfileThreshold_coleHopfPhi_modeZero
    (P : EnergyProfile) (m : ℕ) :
    ¬ ContinuousAt
      (coleHopfPhi 1
        (cutoffPotential (fun r => r) (hardProfileThresholdRadius P m) unitStatisticMode))
      modeZero := by
  exact not_continuousAt_coleHopfPhi_of_tailSpikeStableAt
    (hardProfileThresholdRadius_tailSpikeStableAt_one P m)
    tendsto_unitStatisticMode_tailSpikeMode
    (by norm_num)
    (by
      unfold cutoffPotential
      rw [hardProfileThresholdRadius_modeZero]
      norm_num [unitStatisticMode, modeZero])

theorem hardProfileThresholdRadius_eq_hardSobolevRadius
    (P : EnergyProfile) (m : ℕ) :
    hardProfileThresholdRadius P m = hardSobolevRadius m := by
  funext x
  have hiff :
      (∃ n, 0 < P.profile ((sobolevAmplification m x n) ^ (2 : ℕ))) ↔
        ∃ n, sobolevAmplification m x n ≠ 0 := by
    constructor
    · intro h
      rcases h with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      intro hzero
      have hsq_zero : (sobolevAmplification m x n) ^ (2 : ℕ) = 0 := by
        simp [hzero]
      have hprof_zero : P.profile ((sobolevAmplification m x n) ^ (2 : ℕ)) = 0 := by
        simpa [hsq_zero] using P.profile_zero
      rw [hprof_zero] at hn
      linarith
    · intro h
      rcases h with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hsq_pos : 0 < (sobolevAmplification m x n) ^ (2 : ℕ) := by
        nlinarith [sq_pos_of_ne_zero hn]
      exact P.profile_pos _ hsq_pos
  by_cases h : ∃ n, sobolevAmplification m x n ≠ 0
  · have hp :
        ∃ n, 0 < P.profile ((sobolevAmplification m x n) ^ (2 : ℕ)) := hiff.mpr h
    simp [hardProfileThresholdRadius, hardSobolevRadius, hp, h]
  · have hp :
        ¬ ∃ n, 0 < P.profile ((sobolevAmplification m x n) ^ (2 : ℕ)) := by
        intro hp
        exact h (hiff.mp hp)
    simp [hardProfileThresholdRadius, hardSobolevRadius, hp, h]

/-- The identity profile recovers the raw soft energy on the good side. -/
def identityEnergyProfile : EnergyProfile where
  profile := fun u => u
  continuous_profile := continuous_id
  profile_nonneg := by
    intro u hu
    exact hu
  profile_le := by
    intro u hu
    exact le_rfl
  profile_zero := by simp
  profile_pos := by
    intro u hu
    exact hu

/-- A globally continuous clipped log profile agreeing with `log (1 + u)` on
nonnegative inputs. -/
def logOnePlusMaxEnergyProfile : EnergyProfile where
  profile := fun u => Real.log (1 + max u 0)
  continuous_profile := by
    have harg : Continuous fun u : ℝ => 1 + max u 0 := by
      exact continuous_const.add (continuous_id.max continuous_const)
    refine harg.log ?_
    intro u
    have hmax_nonneg : 0 ≤ max u 0 := le_max_right _ _
    linarith
  profile_nonneg := by
    intro u hu
    have hmax : max u 0 = u := max_eq_left hu
    rw [show 1 + max u 0 = 1 + u by simp [hmax]]
    apply Real.log_nonneg
    linarith
  profile_le := by
    intro u hu
    have hmax : max u 0 = u := max_eq_left hu
    have harg_pos : 0 < 1 + max u 0 := by
      rw [hmax]
      linarith
    have h := Real.log_le_sub_one_of_pos harg_pos
    simpa [hmax] using h
  profile_zero := by
    simp
  profile_pos := by
    intro u hu
    have hmax : max u 0 = u := max_eq_left hu.le
    have hgt : 1 < 1 + max u 0 := by
      rw [hmax]
      linarith
    simpa [hmax] using Real.log_pos hgt

/-- A bounded rational saturation profile agreeing with `u / (1 + u)` on
nonnegative inputs. -/
def rationalMaxEnergyProfile : EnergyProfile where
  profile := fun u => max u 0 / (1 + max u 0)
  continuous_profile := by
    have hmax : Continuous fun u : ℝ => max u 0 := continuous_id.max continuous_const
    exact hmax.div (continuous_const.add hmax) (by
      intro u
      have hmax_nonneg : 0 ≤ max u 0 := le_max_right _ _
      linarith)
  profile_nonneg := by
    intro u hu
    have hmax : max u 0 = u := max_eq_left hu
    rw [show max u 0 / (1 + max u 0) = u / (1 + u) by simp [hmax]]
    exact div_nonneg hu (by linarith)
  profile_le := by
    intro u hu
    have hmax : max u 0 = u := max_eq_left hu
    rw [show max u 0 / (1 + max u 0) = u / (1 + u) by simp [hmax]]
    exact div_le_self hu (by linarith)
  profile_zero := by
    simp
  profile_pos := by
    intro u hu
    have hmax : max u 0 = u := max_eq_left hu.le
    rw [show max u 0 / (1 + max u 0) = u / (1 + u) by simp [hmax]]
    exact div_pos hu (by linarith)

/-- A smooth bounded saturation profile agreeing with `1 - exp(-u)` on
nonnegative inputs. -/
def expNegMaxEnergyProfile : EnergyProfile where
  profile := fun u => 1 - Real.exp (- max u 0)
  continuous_profile := by
    have hmax : Continuous fun u : ℝ => max u 0 := continuous_id.max continuous_const
    exact continuous_const.sub (Real.continuous_exp.comp (continuous_neg.comp hmax))
  profile_nonneg := by
    intro u hu
    have hmax : max u 0 = u := max_eq_left hu
    have hexp_le : Real.exp (-u) ≤ 1 := by
      have : Real.exp (-u) ≤ Real.exp 0 := by
        gcongr
        linarith
      simpa using this
    have : 0 ≤ 1 - Real.exp (-u) := by
      exact sub_nonneg.mpr hexp_le
    simpa [hmax] using this
  profile_le := by
    intro u hu
    have hmax : max u 0 = u := max_eq_left hu
    have h := Real.add_one_le_exp (-u)
    have : 1 - Real.exp (-u) ≤ u := by
      linarith
    simpa [hmax] using this
  profile_zero := by
    simp
  profile_pos := by
    intro u hu
    have hmax : max u 0 = u := max_eq_left hu.le
    have hexp_lt : Real.exp (-u) < 1 := by
      have : Real.exp (-u) < Real.exp 0 := by
        gcongr
        linarith
      simpa using this
    have : 0 < 1 - Real.exp (-u) := by
      exact sub_pos.mpr hexp_lt
    simpa [hmax] using this

/-- A smooth transition profile `u * smoothTransition u`. It is identically
zero on nonpositive inputs and agrees with `u` for large positive inputs. -/
def smoothTransitionEnergyProfile : EnergyProfile where
  profile := fun u => u * Real.smoothTransition u
  continuous_profile := continuous_id.mul Real.smoothTransition.continuous
  profile_nonneg := by
    intro u hu
    exact mul_nonneg hu (Real.smoothTransition.nonneg u)
  profile_le := by
    intro u hu
    simpa using mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one u) hu
  profile_zero := by
    simp
  profile_pos := by
    intro u hu
    exact mul_pos hu (Real.smoothTransition.pos_of_pos hu)

/-- A positive-scale smooth transition family `u * smoothTransition (c u)`. -/
def scaledSmoothTransitionEnergyProfile (c : ℝ) (hc : 0 < c) : EnergyProfile where
  profile := fun u => u * Real.smoothTransition (c * u)
  continuous_profile := by
    exact continuous_id.mul
      (Real.smoothTransition.continuous.comp (continuous_const.mul continuous_id))
  profile_nonneg := by
    intro u hu
    exact mul_nonneg hu (Real.smoothTransition.nonneg (c * u))
  profile_le := by
    intro u hu
    simpa using mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one (c * u)) hu
  profile_zero := by
    simp
  profile_pos := by
    intro u hu
    have hcu : 0 < c * u := mul_pos hc hu
    exact mul_pos hu (Real.smoothTransition.pos_of_pos hcu)

theorem profiledEnergyTerm_identity_eq_sobolevEnergyTerm
    (m : ℕ) (x : ModeState) (n : ℕ) :
    profiledEnergyTerm identityEnergyProfile m x n = sobolevEnergyTerm m x n := by
  simp [profiledEnergyTerm, identityEnergyProfile, sobolevEnergyTerm]

theorem profiledEnergyRadius_identity_eq_sobolevEnergyRadius
    (m : ℕ) :
    profiledEnergyRadius identityEnergyProfile m = sobolevEnergyRadius m := by
  funext x
  unfold profiledEnergyRadius sobolevEnergyRadius
  simp [profiledEnergyTerm_identity_eq_sobolevEnergyTerm]

theorem profiledEnergyTerm_logOnePlusMax_eq_logEnergyTerm
    (m : ℕ) (x : ModeState) (n : ℕ) :
    profiledEnergyTerm logOnePlusMaxEnergyProfile m x n = logEnergyTerm m x n := by
  have hsq_nonneg : 0 ≤ (sobolevAmplification m x n) ^ (2 : ℕ) := by positivity
  simp [profiledEnergyTerm, logOnePlusMaxEnergyProfile, logEnergyTerm, max_eq_left hsq_nonneg]

theorem profiledEnergyRadius_logOnePlusMax_eq_logEnergyRadius
    (m : ℕ) :
    profiledEnergyRadius logOnePlusMaxEnergyProfile m = logEnergyRadius m := by
  funext x
  unfold profiledEnergyRadius logEnergyRadius
  simp [profiledEnergyTerm_logOnePlusMax_eq_logEnergyTerm]

theorem hardProfileThresholdRadius_logOnePlusMax_eq_hardLogEnergyThresholdRadius
    (m : ℕ) :
    hardProfileThresholdRadius logOnePlusMaxEnergyProfile m = hardLogEnergyThresholdRadius m := by
  funext x
  let p : Prop := ∃ n, 0 < logOnePlusMaxEnergyProfile.profile ((sobolevAmplification m x n) ^ (2 : ℕ))
  let q : Prop := ∃ n, 0 < Real.log (1 + (sobolevAmplification m x n) ^ (2 : ℕ))
  have hpq : p ↔ q := by
    constructor
    · intro h
      rcases h with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hsq_nonneg : 0 ≤ (sobolevAmplification m x n) ^ (2 : ℕ) := by positivity
      simpa [p, q, logOnePlusMaxEnergyProfile, max_eq_left hsq_nonneg] using hn
    · intro h
      rcases h with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hsq_nonneg : 0 ≤ (sobolevAmplification m x n) ^ (2 : ℕ) := by positivity
      simpa [p, q, logOnePlusMaxEnergyProfile, max_eq_left hsq_nonneg] using hn
  by_cases hp : p
  · have hq : q := hpq.mp hp
    simp [hardProfileThresholdRadius, hardLogEnergyThresholdRadius, p, q, hp, hq]
  · have hq : ¬ q := by
      intro hq
      exact hp (hpq.mpr hq)
    simp [hardProfileThresholdRadius, hardLogEnergyThresholdRadius, p, q, hp, hq]

theorem hardProfileThresholdRadius_rationalMax_eq_hardSobolevRadius
    (m : ℕ) :
    hardProfileThresholdRadius rationalMaxEnergyProfile m = hardSobolevRadius m := by
  simpa using
    hardProfileThresholdRadius_eq_hardSobolevRadius
      (P := rationalMaxEnergyProfile) m

theorem hardProfileThresholdRadius_expNegMax_eq_hardSobolevRadius
    (m : ℕ) :
    hardProfileThresholdRadius expNegMaxEnergyProfile m = hardSobolevRadius m := by
  simpa using
    hardProfileThresholdRadius_eq_hardSobolevRadius
      (P := expNegMaxEnergyProfile) m

theorem hardProfileThresholdRadius_smoothTransition_eq_hardSobolevRadius
    (m : ℕ) :
    hardProfileThresholdRadius smoothTransitionEnergyProfile m = hardSobolevRadius m := by
  simpa using
    hardProfileThresholdRadius_eq_hardSobolevRadius
      (P := smoothTransitionEnergyProfile) m

theorem hardProfileThresholdRadius_scaledSmoothTransition_eq_hardSobolevRadius
    (c : ℝ) (hc : 0 < c) (m : ℕ) :
    hardProfileThresholdRadius (scaledSmoothTransitionEnergyProfile c hc) m = hardSobolevRadius m := by
  simpa using
    hardProfileThresholdRadius_eq_hardSobolevRadius
      (P := scaledSmoothTransitionEnergyProfile c hc) m

end ModeStateEnergyProfileFork

end NavierStokes
end FluidDynamics
end Mettapedia
