import Mettapedia.FluidDynamics.NavierStokes.GeometricColeHopfSharedApproximation
import Mathlib.Data.NNReal.Basic

/-!
# Cole-Hopf Shared Approximation with Heat-Decayed Coefficients

This file strengthens the earlier Cole-Hopf-shaped shared approximation by
replacing the static selected-coefficient `dΦ` model with an explicit
nonnegative-time heat-decayed one.  The chart heat datum is still the concrete
`φ = exp(-W₀/(2ν))`, but the identity-side derivative model now carries an
actual decay factor `exp(-t * k)`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter

section GeometricColeHopfHeatApproximation

variable {ι X : Type*}
variable [Fintype ι]

/-- Simple nonnegative-time decay for the `k`-th selected mode. -/
def heatDecay (t : NNReal) (k : ℕ) : ℝ :=
  Real.exp (-((t : ℝ) * (k : ℝ)))

theorem heatDecay_nonneg (t : NNReal) (k : ℕ) : 0 ≤ heatDecay t k := by
  exact (Real.exp_pos _).le

theorem heatDecay_le_one (t : NNReal) (k : ℕ) : heatDecay t k ≤ 1 := by
  have hprod : 0 ≤ (t : ℝ) * (k : ℝ) := by positivity
  have harg : -((t : ℝ) * (k : ℝ)) ≤ 0 := by nlinarith
  simpa [heatDecay] using (Real.exp_le_exp.mpr harg)

theorem heatDecay_sq_le_one (t : NNReal) (k : ℕ) : heatDecay t k ^ 2 ≤ 1 := by
  have hnonneg := heatDecay_nonneg t k
  have hone := heatDecay_le_one t k
  nlinarith

/-- Heat-decayed selected coefficient family. -/
def heatedSelectedDerivative (selector : ι → ℕ) : ModeState → NNReal → ι → ℝ :=
  fun x t i => heatDecay t (selector i) * x.coeff (selector i)

omit [Fintype ι] in
theorem heatedSelectedDerivative_tendsto
    (selector : ι → ℕ) (x : ModeState) (t : NNReal) (i : ι) :
    Tendsto (fun N => heatedSelectedDerivative selector (truncateModes N x) t i)
      Filter.atTop (nhds (heatedSelectedDerivative selector x t i)) := by
  unfold heatedSelectedDerivative
  exact (truncateModes_coeff_tendsto x (selector i)).const_mul (heatDecay t (selector i))

theorem heatedSelectedDerivative_energy_le
    (selector : ι → ℕ) (x : ModeState) (t : NNReal) :
    gamma (fun i => heatedSelectedDerivative selector x t i) ≤ (Fintype.card ι : ℝ) := by
  unfold gamma heatedSelectedDerivative
  calc
    ∑ i, (heatDecay t (selector i) * x.coeff (selector i)) ^ 2
      ≤ ∑ i, (x.coeff (selector i)) ^ 2 := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hsq_nonneg : 0 ≤ (x.coeff (selector i)) ^ 2 := sq_nonneg _
        calc
          (heatDecay t (selector i) * x.coeff (selector i)) ^ 2
            = heatDecay t (selector i) ^ 2 * (x.coeff (selector i)) ^ 2 := by ring
          _ ≤ 1 * (x.coeff (selector i)) ^ 2 := by
            exact mul_le_mul_of_nonneg_right (heatDecay_sq_le_one t (selector i)) hsq_nonneg
          _ = (x.coeff (selector i)) ^ 2 := by ring
    _ ≤ (Fintype.card ι : ℝ) := by
      simpa [gamma] using gamma_selectedCoeff_le_card selector x

/-- Cole-Hopf-shaped time-dependent derivative model with heat-decayed selected
coefficients. -/
def WeightedObservable.coleHopfHeatdPhi
    (L : WeightedObservable) (selector : ι → ℕ) (ν : ℝ) (cutoff : ℝ → ℝ) :
    ModeState → NNReal → ι → ℝ :=
  fun x t i => manuscriptPhi ν cutoff L x * heatedSelectedDerivative selector x t i

omit [Fintype ι] in
theorem WeightedObservable.coleHopfHeatdPhi_tendsto
    (L : WeightedObservable) (selector : ι → ℕ) {ν : ℝ} {cutoff : ℝ → ℝ}
    (hcutoff : Continuous cutoff) (x : ModeState) (t : NNReal) (i : ι) :
    Tendsto (fun N => L.coleHopfHeatdPhi selector ν cutoff (truncateModes N x) t i)
      Filter.atTop (nhds (L.coleHopfHeatdPhi selector ν cutoff x t i)) := by
  unfold WeightedObservable.coleHopfHeatdPhi
  exact (manuscriptPhi_tendsto L hcutoff x).mul
    (heatedSelectedDerivative_tendsto selector x t i)

theorem WeightedObservable.coleHopfHeatdPhi_energy_le
    (L : WeightedObservable) (selector : ι → ℕ)
    {ν B : ℝ} (hν : 0 < ν) {cutoff : ℝ → ℝ}
    (hB : 0 ≤ B) (hcutoff : ∀ r, |cutoff r| ≤ B)
    (x : ModeState) (t : NNReal) :
    gamma (fun i => L.coleHopfHeatdPhi selector ν cutoff x t i) ≤
      (Real.exp ((B * observableEnvelopeSum L) / (2 * ν))) ^ 2 * (Fintype.card ι : ℝ) := by
  have hsquare :
      manuscriptPhi ν cutoff L x ^ 2 ≤ (Real.exp ((B * observableEnvelopeSum L) / (2 * ν))) ^ 2 := by
    have hphi_nonneg : 0 ≤ manuscriptPhi ν cutoff L x := (manuscriptPhi_pos L ν x).le
    have hupper := manuscriptPhi_upper_bound L hν hB hcutoff x
    nlinarith
  calc
    gamma (fun i => L.coleHopfHeatdPhi selector ν cutoff x t i)
      = manuscriptPhi ν cutoff L x ^ 2 *
          gamma (fun i => heatedSelectedDerivative selector x t i) := by
            simp [WeightedObservable.coleHopfHeatdPhi, gamma_smul]
    _ ≤ manuscriptPhi ν cutoff L x ^ 2 * (Fintype.card ι : ℝ) := by
          exact mul_le_mul_of_nonneg_left
            (heatedSelectedDerivative_energy_le selector x t) (sq_nonneg _)
    _ ≤ (Real.exp ((B * observableEnvelopeSum L) / (2 * ν))) ^ 2 * (Fintype.card ι : ℝ) := by
          exact mul_le_mul_of_nonneg_right hsquare (by positivity)

/-- Shared approximation package with a genuinely time-decayed finite-mode
derivative model on nonnegative time. -/
def WeightedObservable.geometricColeHopfHeatApproximation
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
    SharedApproximationPackage (Time := NNReal) (ι := ι) (X := X)
      radiusSq (matchingObservable L) where
  toKernelSemigroupData := trivialKernelSemigroupData (Time := NNReal)
  approx := truncateModes
  radius_tendsto := truncateModes_radiusSq_tendsto
  statistic_tendsto := truncateModes_matchingObservable_tendsto L
  Phi := L.coleHopfPhiTime (Time := NNReal) ν cutoff
  dPhi := L.coleHopfHeatdPhi selector ν cutoff
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
    exact L.coleHopfHeatdPhi_tendsto selector hcutoff_cont x t i
  Phi_lower_eventually := by
    intro x t
    exact Eventually.of_forall fun n => by
      simpa [WeightedObservable.coleHopfPhiTime] using
        manuscriptPhi_lower_bound L hν hB hcutoff (truncateModes n x)
  dPhi_energy_eventually := by
    intro x t
    exact Eventually.of_forall fun n => by
      simpa [WeightedObservable.coleHopfHeatdPhi] using
        L.coleHopfHeatdPhi_energy_le selector hν hB hcutoff (truncateModes n x) t
  curl_energy := hcurl

theorem WeightedObservable.geometricColeHopfHeatApproximation_Phi_lower_eventually
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
    (x : ModeState) (t : NNReal) :
    ∀ᶠ n in Filter.atTop,
      Real.exp (-(B * observableEnvelopeSum L) / (2 * ν)) ≤ manuscriptPhi ν cutoff L (truncateModes n x) := by
  let S :=
    L.geometricColeHopfHeatApproximation
      (ι := ι) (X := X)
      selector ν B hν hB cutoff hcutoff_cont hcutoff
      curlFrame curlBound curlBound_nonneg hcurl
  simpa [WeightedObservable.coleHopfPhiTime] using S.Phi_lower_eventually x t

theorem WeightedObservable.geometricColeHopfHeatApproximation_dPhi_energy_eventually
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
    (x : ModeState) (t : NNReal) :
    ∀ᶠ n in Filter.atTop,
      gamma (fun i =>
        manuscriptPhi ν cutoff L (truncateModes n x) *
          (heatDecay t (selector i) * (truncateModes n x).coeff (selector i))) ≤
        (Real.exp ((B * observableEnvelopeSum L) / (2 * ν))) ^ 2 * (Fintype.card ι : ℝ) := by
  let S :=
    L.geometricColeHopfHeatApproximation
      (ι := ι) (X := X)
      selector ν B hν hB cutoff hcutoff_cont hcutoff
      curlFrame curlBound curlBound_nonneg hcurl
  simpa [WeightedObservable.coleHopfHeatdPhi, heatedSelectedDerivative] using
    S.dPhi_energy_eventually x t

end GeometricColeHopfHeatApproximation

end NavierStokes
end FluidDynamics
end Mettapedia
