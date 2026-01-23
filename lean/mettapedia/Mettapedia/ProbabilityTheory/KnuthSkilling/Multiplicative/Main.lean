import Mathlib.Analysis.SpecialFunctions.Exp
import Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.FunctionalEquation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.ScaledMultRep

/-!
# Knuth–Skilling Appendix B: Product Rule from the Product Equation

This file completes the Appendix B pipeline in the *fixed* formalization:

1. Use `Multiplicative.Basic` to derive the product equation for `Ψ := Θ⁻¹` from
   distributivity (Axiom 3) and an additive order-isomorphism representation of `⊗`.
2. Apply `Multiplicative.productEquation_solution_of_continuous_strictMono`
   to conclude `Ψ(x) = C * exp (A * x)`.
3. Deduce that `⊗` is multiplication up to a global scale constant `C`, and obtain a
   canonical normalization where the scale is exactly multiplication.

This corresponds to the "Independence" subsection of the paper (TeX around lines 653–689)
plus the Appendix B functional equation solution.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative

open Classical
open Set
open scoped Topology

open Mettapedia.ProbabilityTheory.KnuthSkilling.Literature

variable {tensor : PosReal → PosReal → PosReal}

/-- The inverse `Ψ := Θ⁻¹` satisfies the Appendix B product equation. -/
theorem productEquation_Psi
    (hRep : AdditiveOrderIsoRep PosReal tensor)
    (hDistrib : DistributesOverAdd tensor) :
    ProductEquation (Derived.Psi hRep) (Derived.zeta hRep) :=
  Derived.productEquation_of_distributes (tensor := tensor) hRep hDistrib

/-- Appendix B: `Ψ = Θ⁻¹` is an exponential, given the product equation regularity.

In our setting, continuity and strict monotonicity are *derived* because `Θ` is an order isomorphism.
-/
theorem Psi_is_exp
    (hRep : AdditiveOrderIsoRep PosReal tensor)
    (hDistrib : DistributesOverAdd tensor) :
    ∃ (C A : ℝ), 0 < C ∧ ∀ x : ℝ, Derived.Psi hRep x = C * Real.exp (A * x) := by
  refine
    productEquation_solution_of_continuous_strictMono
      (hEq := productEquation_Psi (tensor := tensor) hRep hDistrib)
      (hPos := fun x => Derived.Psi_pos (tensor := tensor) hRep x)
      (hCont := Derived.Psi_continuous (tensor := tensor) hRep)
      (hMono := Derived.Psi_strictMono (tensor := tensor) hRep)

/-- The direct-product scalar operation is multiplication up to a global constant.

More precisely, if `C := Ψ(0)`, then
`(x ⊗ y) = (x * y) / C` (after coercion to `ℝ`).

This matches the paper's statement that one may set `C = 1` "without loss of generality".
-/
theorem tensor_coe_eq_mul_div_const
    (hRep : AdditiveOrderIsoRep PosReal tensor)
    (hDistrib : DistributesOverAdd tensor) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : PosReal, ((tensor x y : PosReal) : ℝ) = ((x : ℝ) * (y : ℝ)) / C := by
  rcases Psi_is_exp (tensor := tensor) hRep hDistrib with ⟨C, A, hC, hPsi⟩
  refine ⟨C, hC, ?_⟩
  intro x y
  have hC_ne : C ≠ 0 := ne_of_gt hC

  -- Evaluate the exponential representation at `Θ x`, `Θ y`, and `Θ (x ⊗ y)`.
  have hx : (x : ℝ) = C * Real.exp (A * hRep.Θ x) := by
    simpa [Derived.Psi] using (hPsi (hRep.Θ x))
  have hy : (y : ℝ) = C * Real.exp (A * hRep.Θ y) := by
    simpa [Derived.Psi] using (hPsi (hRep.Θ y))

  have hxy : ((tensor x y : PosReal) : ℝ) = C * Real.exp (A * (hRep.Θ x + hRep.Θ y)) := by
    -- `Θ (x ⊗ y) = Θ x + Θ y` by the representation.
    have : hRep.Θ (tensor x y) = hRep.Θ x + hRep.Θ y := hRep.map_op x y
    -- Rewrite `Ψ(Θ(x⊗y))` using the formula for `Ψ` and `Θ(x⊗y)`.
    calc
      ((tensor x y : PosReal) : ℝ)
          = Derived.Psi hRep (hRep.Θ (tensor x y)) := by simp [Derived.Psi]
      _ = C * Real.exp (A * (hRep.Θ (tensor x y))) := by simpa using (hPsi (hRep.Θ (tensor x y)))
      _ = C * Real.exp (A * (hRep.Θ x + hRep.Θ y)) := by simp [this]

  -- Convert the RHS to `(x*y)/C`.
  -- We use `exp(A*(a+b)) = exp(A*a) * exp(A*b)`.
  calc
    ((tensor x y : PosReal) : ℝ)
        = C * (Real.exp (A * hRep.Θ x) * Real.exp (A * hRep.Θ y)) := by
            -- unfold the exponential of a sum
            simp [hxy, mul_add, Real.exp_add]
    _ = ((C * Real.exp (A * hRep.Θ x)) * (C * Real.exp (A * hRep.Θ y))) / C := by
            -- factor a `C` out of the product
            field_simp [hC_ne]
    _ = ((x : ℝ) * (y : ℝ)) / C := by
            -- rewrite using `hx` and `hy`
            simp [hx, hy, mul_assoc, mul_left_comm]

/-- Canonical normalization: rescale measures by `C` so that `⊗` becomes literal multiplication.

If `m(x) := x / C`, then `m(x ⊗ y) = m(x) * m(y)`.
-/
theorem tensor_mul_rule_normalized
    (hRep : AdditiveOrderIsoRep PosReal tensor)
    (hDistrib : DistributesOverAdd tensor) :
    ∃ C : ℝ, 0 < C ∧
      (∀ x : PosReal, 0 < ((x : ℝ) / C)) ∧
      (∀ x y : PosReal,
        ((tensor x y : PosReal) : ℝ) / C = (((x : ℝ) / C) * ((y : ℝ) / C))) := by
  rcases tensor_coe_eq_mul_div_const (tensor := tensor) hRep hDistrib with ⟨C, hC, hMul⟩
  refine ⟨C, hC, ?_, ?_⟩
  · intro x
    have hC_ne : C ≠ 0 := ne_of_gt hC
    have hx_pos : 0 < (x : ℝ) := x.2
    exact div_pos hx_pos hC
  · intro x y
    have hC_ne : C ≠ 0 := ne_of_gt hC
    -- Reduce to a ring equality by clearing denominators.
    -- Using `hMul` first makes the remaining goal purely algebraic.
    have : ((tensor x y : PosReal) : ℝ) / C = (((x : ℝ) * (y : ℝ)) / C) / C := by
      simp [hMul x y]
    -- Now show `((x*y)/C)/C = (x/C)*(y/C)` by field arithmetic.
    calc
      ((tensor x y : PosReal) : ℝ) / C
          = (((x : ℝ) * (y : ℝ)) / C) / C := this
    _ = ((x : ℝ) / C) * ((y : ℝ) / C) := by
          field_simp [hC_ne]

/-- If `⊗` is multiplication up to a global constant `C`, then it admits a concrete additive
order-isomorphism representation with a logarithmic `Θ`.

This is the paper's `Θ(x) = (1/A) * log(x/C)` specialization (with `A = 1` and the shift by
`log C` absorbed into the choice of `Θ`), matching TeX around eq. (\"directprodrule\"). -/
noncomputable def additiveOrderIsoRep_of_mul_div_const
    {tensor : PosReal → PosReal → PosReal}
    (C : ℝ) (hC : 0 < C)
    (hMul : ∀ x y : PosReal, ((tensor x y : PosReal) : ℝ) = ((x : ℝ) * (y : ℝ)) / C) :
    AdditiveOrderIsoRep PosReal tensor where
  Θ := (Real.expOrderIso.symm).trans (OrderIso.addRight (-Real.log C))
  map_op := by
    intro x y
    apply Real.exp_injective

    have hC_ne : C ≠ 0 := ne_of_gt hC
    have hlogC : Real.exp (Real.log C) = C := Real.exp_log hC

    -- Helper: `exp (expOrderIso.symm z) = z` for `z : Ioi 0`.
    have hexp_log : ∀ z : PosReal, Real.exp (Real.expOrderIso.symm z) = (z : ℝ) := by
      intro z
      have h0 : Real.expOrderIso (Real.expOrderIso.symm z) = z := Real.expOrderIso.apply_symm_apply z
      have h1 : ((Real.expOrderIso (Real.expOrderIso.symm z) : PosReal) : ℝ) = (z : ℝ) :=
        congrArg (fun u : PosReal => (u : ℝ)) h0
      have h2 := h1
      rw [Real.coe_expOrderIso_apply] at h2
      exact h2

    -- Expand `Θ` as `log(z) - log(C)`.
    have hΘ : ∀ z : PosReal,
        ((Real.expOrderIso.symm).trans (OrderIso.addRight (-Real.log C))) z
          = Real.expOrderIso.symm z + (-Real.log C) := by
      intro z
      simp [OrderIso.addRight_apply]

    -- Compute `exp(Θ(tensor x y))` and `exp(Θ x + Θ y)` and compare.
    calc
      Real.exp (((Real.expOrderIso.symm).trans (OrderIso.addRight (-Real.log C))) (tensor x y))
          = ((tensor x y : PosReal) : ℝ) / C := by
              -- `exp(log(z) - log C) = z / C`.
              rw [hΘ]
              simp [Real.exp_add, Real.exp_neg, hexp_log (tensor x y), hlogC, div_eq_mul_inv]
      _ = (((x : ℝ) * (y : ℝ)) / C) / C := by
              simp [hMul x y]
      _ = Real.exp
            ((((Real.expOrderIso.symm).trans (OrderIso.addRight (-Real.log C))) x) +
              (((Real.expOrderIso.symm).trans (OrderIso.addRight (-Real.log C))) y)) := by
              -- RHS expands to `(x/C) * (y/C)`.
              rw [hΘ x, hΘ y]
              simp [Real.exp_add, Real.exp_neg, hexp_log x, hexp_log y, hlogC, div_eq_mul_inv,
                mul_assoc, mul_left_comm, mul_comm]

/-! ## ScaledMultRep Interface

The K&S Appendix B path provides the `ScaledMultRep` interface. -/

/-- K&S Appendix B provides the `ScaledMultRep` interface.

This is the K&S path: uses `AdditiveOrderIsoRep` from Appendix A to derive scaled multiplication. -/
noncomputable def scaledMultRep_of_additiveOrderIsoRep
    {tensor : PosReal → PosReal → PosReal}
    (hRep : AdditiveOrderIsoRep PosReal tensor)
    (hDistrib : DistributesOverAdd tensor) :
    ScaledMultRep tensor :=
  ScaledMultRep.ofExists (tensor_coe_eq_mul_div_const hRep hDistrib)

end Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative
