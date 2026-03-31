import Mettapedia.FluidDynamics.NavierStokes.GeometricSharedApproximation

/-!
# Cole-Hopf-Shaped Shared Geometric Approximation

This file upgrades the explicit shared geometric approximation from the simpler
toy `Φ` model to a more manuscript-shaped one:

- `Φ` is the actual chart heat datum `φ = exp(-W₀/(2ν))`;
- `dΦ` is modeled as `φ` times selected coefficients of the same truncated
  state;
- positivity and finite carré-du-champ energy bounds are proved for that same
  shared truncation family.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter

section GeometricColeHopfSharedApproximation

variable {Time ι X : Type*}
variable [One Time] [Mul Time] [Fintype ι]

/-- Time-independent heat datum built from the concrete manuscript chart datum. -/
def WeightedObservable.coleHopfPhiTime
    (L : WeightedObservable) (ν : ℝ) (cutoff : ℝ → ℝ) :
    ModeState → Time → ℝ :=
  fun x _ => manuscriptPhi ν cutoff L x

/-- Time-independent directional derivative model:
the same heat datum times finitely many selected coefficients. -/
def WeightedObservable.coleHopfdPhi
    (L : WeightedObservable) (selector : ι → ℕ) (ν : ℝ) (cutoff : ℝ → ℝ) :
    ModeState → Time → ι → ℝ :=
  fun x _ i => manuscriptPhi ν cutoff L x * x.coeff (selector i)

omit [One Time] [Mul Time] [Fintype ι] in
theorem WeightedObservable.coleHopfPhiTime_tendsto
    (L : WeightedObservable) {ν : ℝ} {cutoff : ℝ → ℝ}
    (hcutoff : Continuous cutoff) (x : ModeState) (t : Time) :
    Tendsto (fun N => L.coleHopfPhiTime ν cutoff (truncateModes N x) t)
      Filter.atTop (nhds (L.coleHopfPhiTime ν cutoff x t)) := by
  simpa [WeightedObservable.coleHopfPhiTime] using manuscriptPhi_tendsto L hcutoff x

omit [One Time] [Mul Time] [Fintype ι] in
theorem WeightedObservable.coleHopfdPhi_tendsto
    (L : WeightedObservable) (selector : ι → ℕ) {ν : ℝ} {cutoff : ℝ → ℝ}
    (hcutoff : Continuous cutoff) (x : ModeState) (t : Time) (i : ι) :
    Tendsto (fun N => L.coleHopfdPhi selector ν cutoff (truncateModes N x) t i)
      Filter.atTop (nhds (L.coleHopfdPhi selector ν cutoff x t i)) := by
  unfold WeightedObservable.coleHopfdPhi
  exact (manuscriptPhi_tendsto L hcutoff x).mul
    (truncateModes_coeff_tendsto x (selector i))

omit [One Time] [Mul Time] in
theorem WeightedObservable.coleHopfdPhi_energy_le
    (L : WeightedObservable) (selector : ι → ℕ)
    {ν B : ℝ} (hν : 0 < ν) {cutoff : ℝ → ℝ}
    (hB : 0 ≤ B) (hcutoff : ∀ r, |cutoff r| ≤ B)
    (x : ModeState) (t : Time) :
    gamma (fun i => L.coleHopfdPhi selector ν cutoff x t i) ≤
      (Real.exp ((B * observableEnvelopeSum L) / (2 * ν))) ^ 2 * (Fintype.card ι : ℝ) := by
  have hphi_nonneg : 0 ≤ manuscriptPhi ν cutoff L x := (manuscriptPhi_pos L ν x).le
  have hupper := manuscriptPhi_upper_bound L hν hB hcutoff x
  have hM_nonneg : 0 ≤ Real.exp ((B * observableEnvelopeSum L) / (2 * ν)) := (Real.exp_pos _).le
  have hsquare :
      manuscriptPhi ν cutoff L x ^ 2 ≤ (Real.exp ((B * observableEnvelopeSum L) / (2 * ν))) ^ 2 := by
    nlinarith
  calc
    gamma (fun i => L.coleHopfdPhi selector ν cutoff x t i)
      = manuscriptPhi ν cutoff L x ^ 2 * gamma (fun i => x.coeff (selector i)) := by
          simp [WeightedObservable.coleHopfdPhi, gamma_smul]
    _ ≤ manuscriptPhi ν cutoff L x ^ 2 * (Fintype.card ι : ℝ) := by
          exact mul_le_mul_of_nonneg_left (gamma_selectedCoeff_le_card selector x) (sq_nonneg _)
    _ ≤ (Real.exp ((B * observableEnvelopeSum L) / (2 * ν))) ^ 2 * (Fintype.card ι : ℝ) := by
          exact mul_le_mul_of_nonneg_right hsquare (by positivity)

/-- More manuscript-shaped shared approximation instance:
the actual chart heat datum `φ` is the `Φ`-field. -/
def WeightedObservable.geometricColeHopfSharedApproximation
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (ν B : ℝ)
    (hν : 0 < ν)
    (hB : 0 ≤ B)
    (cutoff : ℝ → ℝ)
    (hcutoff_cont : Continuous cutoff)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound) :
    SharedApproximationPackage (Time := Time) (ι := ι) (X := X)
      radiusSq (matchingObservable L) where
  toKernelSemigroupData := trivialKernelSemigroupData
  approx := truncateModes
  radius_tendsto := truncateModes_radiusSq_tendsto
  statistic_tendsto := truncateModes_matchingObservable_tendsto L
  Phi := L.coleHopfPhiTime ν cutoff
  dPhi := L.coleHopfdPhi selector ν cutoff
  ν := ν
  mPhi := Real.exp (-(B * observableEnvelopeSum L) / (2 * ν))
  energyBound := (Real.exp ((B * observableEnvelopeSum L) / (2 * ν))) ^ 2 * (Fintype.card ι : ℝ)
  curlFrame := curlFrame
  curlBound := curlBound
  mPhi_pos := Real.exp_pos _
  energyBound_nonneg := by positivity
  curlBound_nonneg := curlBound_nonneg
  Phi_tendsto := by
    intro x t
    exact L.coleHopfPhiTime_tendsto hcutoff_cont x t
  dPhi_tendsto := by
    intro x t i
    exact L.coleHopfdPhi_tendsto selector hcutoff_cont x t i
  Phi_lower_eventually := by
    intro x t
    exact Eventually.of_forall fun n => by
      simpa [WeightedObservable.coleHopfPhiTime] using
        manuscriptPhi_lower_bound L hν hB hcutoff (truncateModes n x)
  dPhi_energy_eventually := by
    intro x t
    exact Eventually.of_forall fun n => by
      simpa [WeightedObservable.coleHopfdPhi] using
        L.coleHopfdPhi_energy_le selector hν hB hcutoff (truncateModes n x) t
  curl_energy := hcurl

theorem WeightedObservable.geometricColeHopfSharedApproximation_Phi_lower_eventually
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (ν B : ℝ)
    (hν : 0 < ν)
    (hB : 0 ≤ B)
    (cutoff : ℝ → ℝ)
    (hcutoff_cont : Continuous cutoff)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) (t : Time) :
    ∀ᶠ n in Filter.atTop,
      Real.exp (-(B * observableEnvelopeSum L) / (2 * ν)) ≤ manuscriptPhi ν cutoff L (truncateModes n x) := by
  let S :=
    L.geometricColeHopfSharedApproximation
      (Time := Time) (ι := ι) (X := X)
      selector ν B hν hB cutoff hcutoff_cont hcutoff curlFrame curlBound curlBound_nonneg hcurl
  simpa [WeightedObservable.coleHopfPhiTime] using S.Phi_lower_eventually x t

theorem WeightedObservable.geometricColeHopfSharedApproximation_dPhi_energy_eventually
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (ν B : ℝ)
    (hν : 0 < ν)
    (hB : 0 ≤ B)
    (cutoff : ℝ → ℝ)
    (hcutoff_cont : Continuous cutoff)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) (t : Time) :
    ∀ᶠ n in Filter.atTop,
      gamma (fun i => manuscriptPhi ν cutoff L (truncateModes n x) * (truncateModes n x).coeff (selector i)) ≤
        (Real.exp ((B * observableEnvelopeSum L) / (2 * ν))) ^ 2 * (Fintype.card ι : ℝ) := by
  let S :=
    L.geometricColeHopfSharedApproximation
      (Time := Time) (ι := ι) (X := X)
      selector ν B hν hB cutoff hcutoff_cont hcutoff curlFrame curlBound curlBound_nonneg hcurl
  simpa [WeightedObservable.coleHopfdPhi] using S.dPhi_energy_eventually x t

end GeometricColeHopfSharedApproximation

end NavierStokes
end FluidDynamics
end Mettapedia
