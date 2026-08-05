import Mathlib

/-!
# Equivariant finite linear kernels

Neural functionals process weights, gradients, masks, or other arrays whose
coordinates carry a group action.  A finite linear layer is equivariant
exactly when its kernel coefficients are constant on simultaneous input-output
orbits.  This file proves both directions over arbitrary finite input types,
arbitrary output types, arbitrary group actions, and arbitrary semirings.

The converse is important: orbit sharing is not merely sufficient.  Testing
the operator on coordinate basis vectors recovers every kernel coefficient,
so equivariance forces the sharing law.

The final fixtures separate a two-orbit diagonal/off-diagonal kernel from a
raw-coordinate kernel that privileges coordinate zero.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks

section Actions

variable {G I R : Type*} [Group G] [MulAction G I]

/-- Contravariant reindexing of a feature vector by a group element. -/
def actVector (g : G) (x : I → R) : I → R :=
  fun i => x (g⁻¹ • i)

@[simp] theorem actVector_apply (g : G) (x : I → R) (i : I) :
    actVector g x i = x (g⁻¹ • i) := rfl

@[simp] theorem actVector_one (x : I → R) :
    actVector (1 : G) x = x := by
  funext i
  simp [actVector]

@[simp] theorem actVector_mul (g h : G) (x : I → R) :
    actVector (g * h) x = actVector g (actVector h x) := by
  funext i
  simp [actVector, mul_smul]

end Actions

section Kernels

variable {G Input Output R : Type*}
  [Group G] [MulAction G Input] [MulAction G Output]

/-- Kernel coefficients are shared along simultaneous input-output orbits. -/
def KernelInvariant (G : Type*) [Group G]
    [MulAction G Input] [MulAction G Output]
    (K : Output → Input → R) : Prop :=
  ∀ (g : G) (out : Output) (input : Input),
    K (g • out) (g • input) = K out input

variable [Fintype Input] [Semiring R]

/-- The finite linear map represented by a kernel. -/
def kernelApply (K : Output → Input → R) (x : Input → R)
    (out : Output) : R :=
  ∑ input, K out input * x input

/-- Evaluation form of equivariance for a finite linear kernel map. -/
def KernelEquivariant (G : Type*) [Group G]
    [MulAction G Input] [MulAction G Output]
    (K : Output → Input → R) : Prop :=
  ∀ (g : G) (x : Input → R) (out : Output),
    kernelApply K (actVector g x) (g • out) = kernelApply K x out

/-- Orbit-shared coefficients make the induced linear map equivariant. -/
theorem kernelInvariant_implies_kernelEquivariant
    {K : Output → Input → R} (hK : KernelInvariant G K) :
    KernelEquivariant G K := by
  intro g x out
  unfold kernelApply actVector
  calc
    (∑ input, K (g • out) input * x (g⁻¹ • input)) =
        ∑ input, K (g • out) (g • input) * x input := by
      simpa [MulAction.toPerm_apply] using
        (Equiv.sum_comp (MulAction.toPerm g)
          (fun input =>
            K (g • out) input * x (g⁻¹ • input))).symm
    _ = ∑ input, K out input * x input := by
      apply Finset.sum_congr rfl
      intro input _
      rw [hK]

end Kernels

section Basis

variable {G Input Output R : Type*}
  [Group G] [MulAction G Input] [MulAction G Output]

/-- Coordinate probe used to recover one kernel coefficient. -/
def basisVector [DecidableEq Input] [Zero R] [One R]
    (input : Input) : Input → R :=
  fun candidate => if candidate = input then 1 else 0

@[simp] theorem actVector_basisVector
    [DecidableEq Input] [Zero R] [One R]
    (g : G) (input : Input) :
    actVector g (basisVector (R := R) input) =
      basisVector (R := R) (g • input) := by
  funext candidate
  simp [actVector, basisVector, inv_smul_eq_iff]

variable [Fintype Input] [Semiring R] [DecidableEq Input]

@[simp] theorem kernelApply_basisVector
    (K : Output → Input → R) (out : Output) (input : Input) :
    kernelApply K (basisVector input) out = K out input := by
  simp [kernelApply, basisVector]

/-- Equivariance forces every coefficient to obey orbit sharing. -/
theorem kernelEquivariant_implies_kernelInvariant
    {K : Output → Input → R} (hK : KernelEquivariant G K) :
    KernelInvariant G K := by
  intro g out input
  have h := hK g (basisVector input) out
  simpa using h

/-- The orbit-parameter-sharing characterization of finite linear
equivariance. -/
theorem kernelInvariant_iff_kernelEquivariant
    (K : Output → Input → R) :
    KernelInvariant G K ↔ KernelEquivariant G K :=
  ⟨kernelInvariant_implies_kernelEquivariant,
    kernelEquivariant_implies_kernelInvariant⟩

end Basis

section Pointwise

variable {G I R S : Type*} [Group G] [MulAction G I]

/-- A coordinatewise nonlinearity. -/
def pointwiseMap (f : R → S) (x : I → R) : I → S :=
  fun i => f (x i)

/-- Every coordinatewise nonlinearity commutes with reindexing. -/
theorem pointwiseMap_equivariant (f : R → S) (g : G)
    (x : I → R) (i : I) :
    pointwiseMap f (actVector g x) (g • i) = pointwiseMap f x i := by
  simp [pointwiseMap]

end Pointwise

section Fixtures

variable {I R : Type*} [DecidableEq I]

/-- One coefficient for the diagonal orbit and one for its complement. -/
def diagonalOrbitKernel (diagonal offDiagonal : R) : I → I → R :=
  fun i j => if i = j then diagonal else offDiagonal

theorem diagonalOrbitKernel_invariant (diagonal offDiagonal : R) :
    KernelInvariant (Equiv.Perm I)
      (diagonalOrbitKernel (I := I) diagonal offDiagonal) := by
  intro g i j
  simp [diagonalOrbitKernel]

variable [Fintype I] [Semiring R]

theorem diagonalOrbitKernel_equivariant (diagonal offDiagonal : R) :
    KernelEquivariant (Equiv.Perm I)
      (diagonalOrbitKernel (I := I) diagonal offDiagonal) :=
  kernelInvariant_implies_kernelEquivariant
    (diagonalOrbitKernel_invariant diagonal offDiagonal)

/-- A nonconstant input for the positive two-coordinate fixture. -/
def orbitFixtureInput : Fin 2 → ℝ :=
  fun i => if i = 0 then 3 else 5

theorem diagonalOrbitKernel_example :
    kernelApply (diagonalOrbitKernel (I := Fin 2) (2 : ℝ) 1)
        orbitFixtureInput 0 = 11 ∧
      kernelApply (diagonalOrbitKernel (I := Fin 2) (2 : ℝ) 1)
        orbitFixtureInput 1 = 13 := by
  norm_num [kernelApply, diagonalOrbitKernel, orbitFixtureInput,
    Fin.sum_univ_two]

/-- A raw-coordinate kernel that treats coordinate zero specially. -/
def fixedZeroKernel : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

def finTwoSwap : Equiv.Perm (Fin 2) :=
  Equiv.swap 0 1

theorem fixedZeroKernel_not_invariant :
    ¬ KernelInvariant (Equiv.Perm (Fin 2)) fixedZeroKernel := by
  intro h
  have h00 := h finTwoSwap 0 0
  norm_num [fixedZeroKernel, finTwoSwap] at h00

theorem fixedZeroKernel_equivariance_failure :
    kernelApply fixedZeroKernel
        (actVector finTwoSwap (basisVector (R := ℝ) 0))
        (finTwoSwap • 0) ≠
      kernelApply fixedZeroKernel (basisVector (R := ℝ) 0) 0 := by
  norm_num [kernelApply, fixedZeroKernel, actVector, basisVector,
    finTwoSwap, Equiv.smul_def, Fin.sum_univ_two]

theorem fixedZeroKernel_not_equivariant :
    ¬ KernelEquivariant (Equiv.Perm (Fin 2)) fixedZeroKernel := by
  intro h
  exact fixedZeroKernel_not_invariant
    (kernelEquivariant_implies_kernelInvariant h)

#print axioms kernelInvariant_iff_kernelEquivariant
#print axioms pointwiseMap_equivariant
#print axioms diagonalOrbitKernel_equivariant
#print axioms fixedZeroKernel_not_equivariant

end Fixtures

end Mettapedia.MachineLearning.NeuralNetworks
