import Mettapedia.FluidDynamics.NavierStokes.ColeHopfInterface
import Mathlib.Topology.Order.OrderClosed

/-!
# Finite-Mode-to-Limit Interface for the NS Grassroots Lane

This file packages the manuscript's positive proof pattern:

- prove positivity / identity-energy bounds for finite truncations first;
- prove the truncations converge;
- transfer those bounds to the limiting profile.

The goal is not to formalize the actual SG truncation argument.  It is to make
the exact shape of the needed repair theorem explicit and reusable.
-/

set_option autoImplicit false

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter
open scoped BigOperators

section FiniteModeLimit

variable {Time ι X : Type*} [Fintype ι]

/-- Closed-order inheritance for lower bounds along a convergent real sequence. -/
theorem le_of_tendsto_of_eventually_ge
    {u : ℕ → ℝ} {c m : ℝ}
    (hu : Tendsto u Filter.atTop (nhds c))
    (hbound : ∀ᶠ n in Filter.atTop, m ≤ u n) :
    m ≤ c := by
  exact isClosed_Ici.mem_of_tendsto hu hbound

/-- Pointwise convergence of finite coefficient families implies convergence of
their finite carré-du-champ energies. -/
theorem gamma_tendsto_of_pointwise
    {Dseq : ℕ → ι → ℝ} {D : ι → ℝ}
    (hD : ∀ i, Tendsto (fun n => Dseq n i) Filter.atTop (nhds (D i))) :
    Tendsto (fun n => gamma (Dseq n)) Filter.atTop (nhds (gamma D)) := by
  classical
  unfold gamma
  have hsum :
      ∀ s : Finset ι,
        Tendsto (fun n => s.sum (fun i => (Dseq n i) ^ 2))
          Filter.atTop (nhds (s.sum (fun i => (D i) ^ 2))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp
    | @insert a s ha hs =>
        have ha' : Tendsto (fun n => (Dseq n a) ^ 2) Filter.atTop (nhds ((D a) ^ 2)) := by
          have hmul :
              Tendsto (fun n => Dseq n a * Dseq n a)
                Filter.atTop (nhds (D a * D a)) :=
            (hD a).mul (hD a)
          simpa [pow_two] using hmul
        simpa [Finset.sum_insert ha] using ha'.add hs
  simpa using hsum Finset.univ

/-- Eventual finite-mode energy bounds pass to the limit once the coefficients
converge pointwise. -/
theorem gamma_le_of_pointwise_of_eventually_le
    {Dseq : ℕ → ι → ℝ} {D : ι → ℝ} {A : ℝ}
    (hD : ∀ i, Tendsto (fun n => Dseq n i) Filter.atTop (nhds (D i)))
    (hbound : ∀ᶠ n in Filter.atTop, gamma (Dseq n) ≤ A) :
    gamma D ≤ A := by
  exact isClosed_Iic.mem_of_tendsto (gamma_tendsto_of_pointwise hD) hbound

/-- Abstract finite-mode approximation data for the identity-only Cole-Hopf
bridge.  The approximants are where the manuscript expects the first real
analytic estimates to be proved. -/
structure FiniteModeColeHopfData where
  Phi : Time → ℝ
  dPhi : Time → ι → ℝ
  approxPhi : ℕ → Time → ℝ
  approxdPhi : ℕ → Time → ι → ℝ
  ν : ℝ
  mPhi : ℝ
  energyBound : ℝ
  curlFrame : ι → X → ℝ
  curlBound : ℝ
  mPhi_pos : 0 < mPhi
  energyBound_nonneg : 0 ≤ energyBound
  curlBound_nonneg : 0 ≤ curlBound
  Phi_tendsto :
    ∀ t, Tendsto (fun n => approxPhi n t) Filter.atTop (nhds (Phi t))
  dPhi_tendsto :
    ∀ t i, Tendsto (fun n => approxdPhi n t i) Filter.atTop (nhds (dPhi t i))
  Phi_lower_eventually :
    ∀ t, ∀ᶠ n in Filter.atTop, mPhi ≤ approxPhi n t
  dPhi_energy_eventually :
    ∀ t, ∀ᶠ n in Filter.atTop, gamma (approxdPhi n t) ≤ energyBound
  curl_energy :
    ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound

theorem FiniteModeColeHopfData.Phi_lower
    (S : FiniteModeColeHopfData (Time := Time) (ι := ι) (X := X))
    (t : Time) :
    S.mPhi ≤ S.Phi t := by
  exact le_of_tendsto_of_eventually_ge (S.Phi_tendsto t) (S.Phi_lower_eventually t)

theorem FiniteModeColeHopfData.dPhi_energy
    (S : FiniteModeColeHopfData (Time := Time) (ι := ι) (X := X))
    (t : Time) :
    gamma (S.dPhi t) ≤ S.energyBound := by
  exact gamma_le_of_pointwise_of_eventually_le
    (fun i => S.dPhi_tendsto t i) (S.dPhi_energy_eventually t)

/-- Once the finite-mode convergence and eventual bounds are supplied, the
existing identity-only Cole-Hopf interface is available on the limit data. -/
def FiniteModeColeHopfData.toColeHopfIdentityData
    (S : FiniteModeColeHopfData (Time := Time) (ι := ι) (X := X)) :
    ColeHopfIdentityData (Time := Time) (ι := ι) (X := X) where
  Phi := S.Phi
  dPhi := S.dPhi
  ν := S.ν
  mPhi := S.mPhi
  energyBound := S.energyBound
  curlFrame := S.curlFrame
  curlBound := S.curlBound
  mPhi_pos := S.mPhi_pos
  energyBound_nonneg := S.energyBound_nonneg
  curlBound_nonneg := S.curlBound_nonneg
  Phi_lower := S.Phi_lower
  dPhi_energy := S.dPhi_energy
  curl_energy := S.curl_energy

theorem FiniteModeColeHopfData.gamma_Wcoeff_le
    (S : FiniteModeColeHopfData (Time := Time) (ι := ι) (X := X))
    (t : Time) :
    gamma (S.toColeHopfIdentityData.Wcoeff t) ≤
      (4 * S.ν ^ 2 / S.mPhi ^ 2) * S.energyBound := by
  simpa using S.toColeHopfIdentityData.gamma_Wcoeff_le t

theorem FiniteModeColeHopfData.abs_vorticity_le
    (S : FiniteModeColeHopfData (Time := Time) (ι := ι) (X := X))
    (t : Time) (x : X) :
    |S.toColeHopfIdentityData.vorticity t x| ≤
      Real.sqrt ((4 * S.ν ^ 2 / S.mPhi ^ 2) * S.energyBound) * Real.sqrt S.curlBound := by
  simpa using S.toColeHopfIdentityData.abs_vorticity_le t x

theorem FiniteModeColeHopfData.abs_vorticity_le_uniform
    (S : FiniteModeColeHopfData (Time := Time) (ι := ι) (X := X)) :
    ∀ t x, |S.toColeHopfIdentityData.vorticity t x| ≤
      Real.sqrt ((4 * S.ν ^ 2 / S.mPhi ^ 2) * S.energyBound) * Real.sqrt S.curlBound :=
  fun t x => S.abs_vorticity_le t x

end FiniteModeLimit

end NavierStokes
end FluidDynamics
end Mettapedia
