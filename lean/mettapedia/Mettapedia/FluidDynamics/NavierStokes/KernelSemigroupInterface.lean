import Mettapedia.FluidDynamics.NavierStokes.ColeHopfInterface
import Mettapedia.ProbabilityTheory.MarkovCategory.Kernels

/-!
# Kernel-Founded Semigroup Interface for the NS Grassroots Lane

This file ties the current identity-only Cole-Hopf algebra to a stable local
probability shell already present in Mettapedia: measurable spaces with Markov
kernels as morphisms.  It does not add analytic claims.  It only says that if a
future NS evolution is represented as a local kernel semigroup, then the
existing identity-energy bridge can be reused unchanged.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open ProbabilityTheory
open Mettapedia.ProbabilityTheory

section KernelSemigroup

variable {Time ι X : Type*} [One Time] [Mul Time] [Fintype ι]

/-- A minimal local kernel-semigroup shell.

`evolve s` is the kernel for time `s`, `evolve 1` is the identity, and
`evolve_mul` says that running `s` first and then `t` agrees with `s * t`. -/
structure KernelSemigroupData where
  Ω : KernelMarkovObj
  evolve : Time → ProbabilityTheory.Kernel Ω Ω
  evolve_one : evolve 1 = ProbabilityTheory.Kernel.id
  evolve_mul :
    ∀ s t, ProbabilityTheory.Kernel.comp (evolve t) (evolve s) = evolve (s * t)

@[simp] theorem KernelSemigroupData.evolve_one_eq_id
    (S : KernelSemigroupData (Time := Time)) :
    S.evolve 1 = ProbabilityTheory.Kernel.id :=
  S.evolve_one

theorem KernelSemigroupData.evolve_comp_eq
    (S : KernelSemigroupData (Time := Time)) (s t : Time) :
    ProbabilityTheory.Kernel.comp (S.evolve t) (S.evolve s) = S.evolve (s * t) :=
  S.evolve_mul s t

/-- Kernel-founded version of the current Cole-Hopf identity interface.

The Markov-kernel semigroup lives locally in Mettapedia's probability layer.
The identity-only energy/vorticity bounds are still carried by the existing
`ColeHopfIdentityData` fields. -/
structure ColeHopfKernelSemigroupData extends
    KernelSemigroupData (Time := Time),
    ColeHopfIdentityData (Time := Time) (ι := ι) (X := X)

@[simp] theorem ColeHopfKernelSemigroupData.toColeHopfIdentityData_Wcoeff
    (S : ColeHopfKernelSemigroupData (Time := Time) (ι := ι) (X := X))
    (t : Time) :
    S.toColeHopfIdentityData.Wcoeff t = S.Wcoeff t :=
  rfl

@[simp] theorem ColeHopfKernelSemigroupData.toColeHopfIdentityData_vorticity
    (S : ColeHopfKernelSemigroupData (Time := Time) (ι := ι) (X := X))
    (t : Time) (x : X) :
    S.toColeHopfIdentityData.vorticity t x = S.vorticity t x :=
  rfl

/-- The existing log-potential coefficient bound survives unchanged after adding
the local kernel-semigroup shell. -/
theorem ColeHopfKernelSemigroupData.gamma_Wcoeff_le
    (S : ColeHopfKernelSemigroupData (Time := Time) (ι := ι) (X := X))
    (t : Time) :
    gamma (S.Wcoeff t) ≤ (4 * S.ν ^ 2 / S.mPhi ^ 2) * S.energyBound := by
  simpa using S.toColeHopfIdentityData.gamma_Wcoeff_le t

/-- The existing pointwise vorticity bound also survives unchanged. -/
theorem ColeHopfKernelSemigroupData.abs_vorticity_le
    (S : ColeHopfKernelSemigroupData (Time := Time) (ι := ι) (X := X))
    (t : Time) (x : X) :
    |S.vorticity t x| ≤
      Real.sqrt ((4 * S.ν ^ 2 / S.mPhi ^ 2) * S.energyBound) * Real.sqrt S.curlBound := by
  simpa using S.toColeHopfIdentityData.abs_vorticity_le t x

/-- Uniform version of the same bound over all times and points. -/
theorem ColeHopfKernelSemigroupData.abs_vorticity_le_uniform
    (S : ColeHopfKernelSemigroupData (Time := Time) (ι := ι) (X := X)) :
    ∀ t x, |S.vorticity t x| ≤
      Real.sqrt ((4 * S.ν ^ 2 / S.mPhi ^ 2) * S.energyBound) * Real.sqrt S.curlBound :=
  fun t x => S.abs_vorticity_le t x

end KernelSemigroup

end NavierStokes
end FluidDynamics
end Mettapedia
