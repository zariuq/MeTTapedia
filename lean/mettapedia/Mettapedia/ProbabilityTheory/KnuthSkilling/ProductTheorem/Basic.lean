import Mathlib.Topology.Order.MonotoneContinuity
import Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem.FunctionalEquation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Literature.FunctionalEquations

/-!
# Knuth–Skilling Product Theorem: Bridge to the Product Equation

This file supplies the *algebra-to-functional-equation* bridge used in
Knuth & Skilling (2012), §"Independence" and Appendix B.

After Appendix A regrades `⊕` to real addition, K&S introduce a second scalar
operation `⊗` corresponding to direct products of independent lattices.

Axioms (paper eqs. (\"Axiom 3\"–\"Axiom 4\")):
- Distributivity over `+` (for fixed `t`): `(x ⊗ t) + (y ⊗ t) = (x + y) ⊗ t`
- Associativity of `⊗`: `(u ⊗ v) ⊗ w = u ⊗ (v ⊗ w)`

K&S then apply the Appendix A associativity theorem *again* (now to `⊗`) to get
an order-isomorphism `Θ` such that:

`Θ (x ⊗ t) = Θ x + Θ t`.

From distributivity + invertibility of `Θ`, they derive the **product equation**

`Ψ(τ + ξ) + Ψ(τ + η) = Ψ(τ + ζ(ξ,η))`

for `Ψ := Θ⁻¹` (paper eq. (\"prodeqn\")), and solve it in Appendix B.

This file formalizes only this derivation of the product equation.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem

open Classical
open Set
open scoped Topology

/-- Positive real numbers, used as the scalar range of measures in Appendix B. -/
abbrev PosReal := Ioi (0 : ℝ)

/-- Addition on positive reals (closed since `0 < x` and `0 < y` implies `0 < x + y`). -/
@[simp] noncomputable def addPos (x y : PosReal) : PosReal :=
  ⟨(x : ℝ) + (y : ℝ), by
    -- NB: for `PosReal := Ioi 0`, the predicate is `fun r => r ∈ Ioi 0`.
    -- Provide the membership proof explicitly to avoid definitional-equality issues.
    simpa [PosReal] using add_pos x.2 y.2⟩

@[simp] theorem coe_addPos (x y : PosReal) : ((addPos x y : PosReal) : ℝ) = (x : ℝ) + (y : ℝ) := by
  rfl

/-- Multiplication on positive reals (closed since `0 < x` and `0 < y` implies `0 < x * y`). -/
@[simp] def mulPos (x y : PosReal) : PosReal :=
  ⟨(x : ℝ) * (y : ℝ), by
    simpa [PosReal] using mul_pos x.2 y.2⟩

@[simp] theorem coe_mulPos (x y : PosReal) : ((mulPos x y : PosReal) : ℝ) = (x : ℝ) * (y : ℝ) := by
  rfl

/-- The distributivity axiom for `⊗` over `+` (paper eq. (\"axiom3\"))

`(x ⊗ t) + (y ⊗ t) = (x + y) ⊗ t`.

We package it for `PosReal` using `addPos` for closure. -/
def DistributesOverAdd (tensor : PosReal → PosReal → PosReal) : Prop :=
  ∀ x y t : PosReal, tensor (addPos x y) t = addPos (tensor x t) (tensor y t)

namespace Derived

open Mettapedia.ProbabilityTheory.KnuthSkilling.Literature

variable {tensor : PosReal → PosReal → PosReal}

/-- `Ψ := Θ⁻¹` as a real-valued function (paper uses `Ψ = Θ^{-1}`),
from an additive order-isomorphism representation of `tensor`. -/
noncomputable def Psi (hRep : AdditiveOrderIsoRep PosReal tensor) : ℝ → ℝ :=
  fun r => ((hRep.Θ.symm r : PosReal) : ℝ)

/-- `ζ(ξ,η) := Θ(x+y)` where `x = Ψ ξ`, `y = Ψ η`.

This matches the paper definition `ζ = Θ(x+y)` (see around TeX eq. (\"prodeqn\")). -/
noncomputable def zeta (hRep : AdditiveOrderIsoRep PosReal tensor) : ℝ → ℝ → ℝ :=
  fun ξ η => hRep.Θ (addPos (hRep.Θ.symm ξ) (hRep.Θ.symm η))

/-- Positivity of `Psi`: its values lie in `Ioi 0`. -/
theorem Psi_pos (hRep : AdditiveOrderIsoRep PosReal tensor) (r : ℝ) : 0 < Psi hRep r :=
  (hRep.Θ.symm r).2

/-- `Psi` is strictly monotone (since it is `Subtype.val ∘ Θ.symm`). -/
theorem Psi_strictMono (hRep : AdditiveOrderIsoRep PosReal tensor) : StrictMono (Psi hRep) := by
  intro x y hxy
  have hxy' : hRep.Θ.symm x < hRep.Θ.symm y := hRep.Θ.symm.strictMono hxy
  simpa [Psi] using hxy'

/-- `Psi` is continuous (order isomorphisms are continuous for order topology). -/
theorem Psi_continuous (hRep : AdditiveOrderIsoRep PosReal tensor) : Continuous (Psi hRep) := by
  -- `Θ.symm` is continuous as an order isomorphism; `Subtype.val` is continuous.
  simpa [Psi] using (continuous_subtype_val.comp hRep.Θ.symm.continuous)

/-- The K&S product equation derived from:

1. An additive order-isomorphism representation `Θ(x ⊗ t) = Θ x + Θ t` (paper eq. (\"thetaproduct\"))
2. Distributivity `(x ⊗ t) + (y ⊗ t) = (x+y) ⊗ t` (paper eq. (\"axiom3\")).

This is exactly the paper transition to the product equation (TeX eq. (\"prodeqn\")). -/
theorem productEquation_of_distributes
    (hRep : AdditiveOrderIsoRep PosReal tensor)
    (hDistrib : DistributesOverAdd tensor) :
    ProductEquation (Psi hRep) (zeta hRep) := by
  intro τ ξ η
  -- Set `x = Θ⁻¹ ξ`, `y = Θ⁻¹ η`, `t = Θ⁻¹ τ`.
  let x : PosReal := hRep.Θ.symm ξ
  let y : PosReal := hRep.Θ.symm η
  let t : PosReal := hRep.Θ.symm τ

  -- Distributivity at the level of `PosReal`.
  have hdis : tensor (addPos x y) t = addPos (tensor x t) (tensor y t) := hDistrib x y t

  -- Compute `x ⊗ t = Θ⁻¹(ξ+τ)` and similarly for `y ⊗ t`.
  have hx : tensor x t = hRep.Θ.symm (ξ + τ) := by
    apply hRep.Θ.injective
    calc
      hRep.Θ (tensor x t) = hRep.Θ x + hRep.Θ t := hRep.map_op x t
      _ = ξ + τ := by
        simp [x, t, add_comm]
      _ = hRep.Θ (hRep.Θ.symm (ξ + τ)) := by simp

  have hy : tensor y t = hRep.Θ.symm (η + τ) := by
    apply hRep.Θ.injective
    calc
      hRep.Θ (tensor y t) = hRep.Θ y + hRep.Θ t := hRep.map_op y t
      _ = η + τ := by
        simp [y, t, add_comm]
      _ = hRep.Θ (hRep.Θ.symm (η + τ)) := by simp

  -- Compute `(x+y) ⊗ t = Θ⁻¹(ζ(ξ,η)+τ)`.
  have hxy : tensor (addPos x y) t = hRep.Θ.symm (zeta hRep ξ η + τ) := by
    apply hRep.Θ.injective
    calc
      hRep.Θ (tensor (addPos x y) t) = hRep.Θ (addPos x y) + hRep.Θ t := hRep.map_op (addPos x y) t
      _ = zeta hRep ξ η + τ := by
        simp [zeta, x, y, t, add_comm]
      _ = hRep.Θ (hRep.Θ.symm (zeta hRep ξ η + τ)) := by simp

  -- Now rewrite distributivity into the product equation after coercions to ℝ.
  -- (All terms are in `PosReal`, so `addPos` agrees with real addition under coercion.)
  have : (tensor (addPos x y) t : ℝ) = (addPos (tensor x t) (tensor y t) : ℝ) := by
    exact congrArg (fun u : PosReal => (u : ℝ)) hdis

  -- Rewrite each side using `hx`, `hy`, `hxy`, and the definitions of `Psi`.
  -- Note: the product equation uses `τ + ξ` rather than `ξ + τ`; commute where needed.
  -- Also, `Psi` is defined using `Θ.symm`.
  --
  -- First, convert `ξ + τ` to `τ + ξ` etc.
  have hx' : (tensor x t : ℝ) = Psi hRep (τ + ξ) := by
    have hx_comm : tensor x t = hRep.Θ.symm (τ + ξ) := by
      simpa [add_comm] using hx
    simpa [Psi] using congrArg (fun u : PosReal => (u : ℝ)) hx_comm

  have hy' : (tensor y t : ℝ) = Psi hRep (τ + η) := by
    have hy_comm : tensor y t = hRep.Θ.symm (τ + η) := by
      simpa [add_comm] using hy
    simpa [Psi] using congrArg (fun u : PosReal => (u : ℝ)) hy_comm

  have hxy' : (tensor (addPos x y) t : ℝ) = Psi hRep (τ + zeta hRep ξ η) := by
    have hxy_comm : tensor (addPos x y) t = hRep.Θ.symm (τ + zeta hRep ξ η) := by
      simpa [add_comm] using hxy
    simpa [Psi] using congrArg (fun u : PosReal => (u : ℝ)) hxy_comm

  -- Finish: expand `addPos` coercion.
  --
  -- LHS of `this` is `Ψ(τ+ζ)`.
  -- RHS of `this` is `Ψ(τ+ξ)+Ψ(τ+η)`.
  --
  -- Rearrange to match `ProductEquation` statement.
  calc
    Psi hRep (τ + ξ) + Psi hRep (τ + η)
        = (addPos (tensor x t) (tensor y t) : ℝ) := by
            simp [hx', hy', addPos]
    _ = (tensor (addPos x y) t : ℝ) := by
            simpa [this] using this.symm
    _ = Psi hRep (τ + zeta hRep ξ η) := by
            simpa [hxy']

end Derived

end Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem
