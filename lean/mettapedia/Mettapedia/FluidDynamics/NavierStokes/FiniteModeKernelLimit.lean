import Mettapedia.FluidDynamics.NavierStokes.FiniteModeLimit
import Mettapedia.FluidDynamics.NavierStokes.KernelSemigroupInterface

/-!
# Finite-Mode-to-Kernel Limit Interface for the NS Grassroots Lane

This file combines two already-local shells:

- the finite-mode positivity / identity-energy transfer layer;
- the local Markov-kernel semigroup shell.

So if a future NS route supplies both a kernel semigroup and finite-mode
truncation estimates converging to the limit data, the current vorticity bridge
is available directly on the kernel-founded limit object.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section FiniteModeKernelLimit

variable {Time ι X : Type*} [One Time] [Mul Time] [Fintype ι]

/-- Kernel-semigroup version of `FiniteModeColeHopfData`. -/
structure FiniteModeColeHopfKernelData extends
    KernelSemigroupData (Time := Time),
    FiniteModeColeHopfData (Time := Time) (ι := ι) (X := X)

/-- The local kernel shell and the finite-mode limit shell combine into the
existing kernel-founded Cole-Hopf interface. -/
def FiniteModeColeHopfKernelData.toColeHopfKernelSemigroupData
    (S : FiniteModeColeHopfKernelData (Time := Time) (ι := ι) (X := X)) :
    ColeHopfKernelSemigroupData (Time := Time) (ι := ι) (X := X) where
  toKernelSemigroupData := S.toKernelSemigroupData
  toColeHopfIdentityData := S.toFiniteModeColeHopfData.toColeHopfIdentityData

theorem FiniteModeColeHopfKernelData.gamma_Wcoeff_le
    (S : FiniteModeColeHopfKernelData (Time := Time) (ι := ι) (X := X))
    (t : Time) :
    gamma (S.toColeHopfKernelSemigroupData.Wcoeff t) ≤
      (4 * S.ν ^ 2 / S.mPhi ^ 2) * S.energyBound := by
  simpa using S.toColeHopfKernelSemigroupData.gamma_Wcoeff_le t

theorem FiniteModeColeHopfKernelData.abs_vorticity_le
    (S : FiniteModeColeHopfKernelData (Time := Time) (ι := ι) (X := X))
    (t : Time) (x : X) :
    |S.toColeHopfKernelSemigroupData.vorticity t x| ≤
      Real.sqrt ((4 * S.ν ^ 2 / S.mPhi ^ 2) * S.energyBound) * Real.sqrt S.curlBound := by
  simpa using S.toColeHopfKernelSemigroupData.abs_vorticity_le t x

theorem FiniteModeColeHopfKernelData.abs_vorticity_le_uniform
    (S : FiniteModeColeHopfKernelData (Time := Time) (ι := ι) (X := X)) :
    ∀ t x, |S.toColeHopfKernelSemigroupData.vorticity t x| ≤
      Real.sqrt ((4 * S.ν ^ 2 / S.mPhi ^ 2) * S.energyBound) * Real.sqrt S.curlBound :=
  fun t x => S.abs_vorticity_le t x

end FiniteModeKernelLimit

end NavierStokes
end FluidDynamics
end Mettapedia
