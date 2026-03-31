import Mettapedia.FluidDynamics.NavierStokes.IdentityEnergy

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section Interface

variable {Time ι X : Type*} [Fintype ι]

/-- Abstract data for the identity-only Cole-Hopf/vorticity bridge.

This intentionally does not attempt to formalize the actual SG diffusion or
semigroup laws. It records only the hypotheses the algebraic spine needs:
uniform positivity of `Φ(t)`, a uniform identity-energy bound on its directional
derivatives, and a uniform frame-curl bound for the push-down frame. -/
structure ColeHopfIdentityData where
  Phi : Time → ℝ
  dPhi : Time → ι → ℝ
  ν : ℝ
  mPhi : ℝ
  energyBound : ℝ
  curlFrame : ι → X → ℝ
  curlBound : ℝ
  mPhi_pos : 0 < mPhi
  energyBound_nonneg : 0 ≤ energyBound
  curlBound_nonneg : 0 ≤ curlBound
  Phi_lower : ∀ t, mPhi ≤ Phi t
  dPhi_energy : ∀ t, gamma (dPhi t) ≤ energyBound
  curl_energy : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound

/-- Coefficients of `W(t) = -2 ν log Φ(t)` at the identity, abstracted as
directional derivatives. -/
noncomputable def ColeHopfIdentityData.Wcoeff
    (S : ColeHopfIdentityData (Time := Time) (ι := ι) (X := X))
    (t : Time) : ι → ℝ :=
  fun i => (-2 * S.ν) * (S.dPhi t i / S.Phi t)

/-- Vorticity obtained by pushing the identity coefficients through the curl frame. -/
noncomputable def ColeHopfIdentityData.vorticity
    (S : ColeHopfIdentityData (Time := Time) (ι := ι) (X := X))
    (t : Time) (x : X) : ℝ :=
  frameEval (S.Wcoeff t) S.curlFrame x

/-- Abstract log-potential identity energy bound derived from the interface. -/
theorem ColeHopfIdentityData.gamma_Wcoeff_le
    (S : ColeHopfIdentityData (Time := Time) (ι := ι) (X := X)) (t : Time) :
    gamma (S.Wcoeff t) ≤ (4 * S.ν ^ 2 / S.mPhi ^ 2) * S.energyBound := by
  unfold ColeHopfIdentityData.Wcoeff
  have hbase :=
    gamma_negTwoNuLog_le (D := S.dPhi t) (ν := S.ν) S.mPhi_pos (S.Phi_lower t)
  have hfactor_nonneg : 0 ≤ 4 * S.ν ^ 2 / S.mPhi ^ 2 := by
    positivity
  exact hbase.trans (mul_le_mul_of_nonneg_left (S.dPhi_energy t) hfactor_nonneg)

/-- Abstract pointwise vorticity bound derived from the identity-energy and
frame-curl hypotheses. -/
  theorem ColeHopfIdentityData.abs_vorticity_le
    (S : ColeHopfIdentityData (Time := Time) (ι := ι) (X := X))
    (t : Time) (x : X) :
    |S.vorticity t x| ≤
      Real.sqrt ((4 * S.ν ^ 2 / S.mPhi ^ 2) * S.energyBound) * Real.sqrt S.curlBound := by
  unfold ColeHopfIdentityData.vorticity
  exact NavierStokes.abs_vorticity_le (coeff := S.Wcoeff t) (curlFrame := S.curlFrame)
    (hcoeff := S.gamma_Wcoeff_le t) (hcurl := S.curl_energy x)

/-- Uniform version of the same bound over all times and points. -/
theorem ColeHopfIdentityData.abs_vorticity_le_uniform
    (S : ColeHopfIdentityData (Time := Time) (ι := ι) (X := X)) :
    ∀ t x, |S.vorticity t x| ≤
      Real.sqrt ((4 * S.ν ^ 2 / S.mPhi ^ 2) * S.energyBound) * Real.sqrt S.curlBound :=
  fun t x => S.abs_vorticity_le t x

end Interface

end NavierStokes
end FluidDynamics
end Mettapedia
