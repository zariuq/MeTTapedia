import Mettapedia.ProbabilityTheory.KnuthSkilling.Literature.FunctionalEquations
import Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.FunctionalEquation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.StrictMonoSolution

/-!
# K&S Interfaces: Single Source of Truth for Reusable Results

This file exports the **central abstractions and key theorems** from the K&S formalization.
All downstream code should import this file rather than reaching into implementation details.

## What This File Provides

### From Appendix A (Representation Theorem)
- `AdditiveOrderIsoRep α op`: The central interface - an order isomorphism Θ : α ≃o ℝ
  such that Θ(op x y) = Θ x + Θ y

### From Appendix B (Product Theorem)
- `ProductEquation Ψ ζ`: The functional equation Ψ(τ + ξ) + Ψ(τ + η) = Ψ(τ + ζ(ξ,η))
- `productEquation_strictMono_pos_continuous`: **KEY** - Continuity is DERIVED, not assumed!
- `productEquation_solution_of_strictMono`: The main Appendix B theorem (fully proven)

**Note**: The optional historical module
`Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.Proofs.Direct.FibonacciProof` imports heavy
number-theory dependencies; it is intentionally not imported here.

## Design Principle

**One interface, many realizers**: Multiple proof routes (Grid, Cuts, Alimov) all produce
`AdditiveOrderIsoRep`. Downstream theorems depend only on this interface.

```
  Appendix A proofs ──┬──► AdditiveOrderIsoRep ──► Downstream theorems
                      │         ▲                    (inclusion-exclusion,
  (Grid, Cuts,        │         │                     MathlibBridge, etc.)
   Alimov, ...)       │         │
                      │    Appendix B results
                      │    (tensor = scaled mult,
                      │     continuity derived)
```
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling

/-! ## Re-export: AdditiveOrderIsoRep (The Central Interface) -/

/-- The central interface from Appendix A: an operation `op` is additively representable
if there exists an order isomorphism Θ : α ≃o ℝ with Θ(op x y) = Θ x + Θ y.

This is the OUTPUT of Appendix A and the INPUT to everything downstream.
Multiple proof routes (separation+grid, separation+cuts, no-anomalous-pairs) all
produce this same type. -/
abbrev AdditiveOrderIsoRep := Literature.AdditiveOrderIsoRep

namespace AdditiveOrderIsoRep

export Literature.AdditiveOrderIsoRep (Θ map_op op_comm op_assoc strictMono_left strictMono_right)

end AdditiveOrderIsoRep

/-! ## Re-export: ProductEquation (Appendix B Functional Equation) -/

/-- The Appendix B product equation: Ψ(τ + ξ) + Ψ(τ + η) = Ψ(τ + ζ(ξ,η)).

This equation arises from distributivity (Axiom 3) when ⊗ has an additive representation. -/
abbrev ProductEquation := Multiplicative.ProductEquation

/-! ## Key Appendix B Results -/

/-- **KEY THEOREM**: Continuity is DERIVED from ProductEquation + StrictMono + Positivity.

This is crucial because K&S's approach avoids assuming continuity - it falls out from
the algebraic structure plus monotonicity. The proof uses:
1. Doubling property: Ψ(θ + na) = 2^n · Ψ(θ)
2. Dense range: {m · C/2^k : m ≥ 1, k ∈ ℕ} is dense in (0, ∞)
3. Monotonicity forces continuity (no jumps possible with dense range)
-/
theorem continuity_from_productEquation_strictMono_pos
    (Ψ : ℝ → ℝ) (ζ : ℝ → ℝ → ℝ)
    (hProd : ProductEquation Ψ ζ)
    (hPos : ∀ x, 0 < Ψ x)
    (hMono : StrictMono Ψ) : Continuous Ψ :=
  Multiplicative.productEquation_strictMono_pos_continuous Ψ ζ hProd hPos hMono

/-- **MAIN APPENDIX B THEOREM** (StrictMono case): If Ψ satisfies the product equation,
is positive, and is strictly monotone, then Ψ(x) = C · exp(A · x) for some C > 0, A ∈ ℝ.

This theorem is FULLY PROVEN. Continuity is derived (not assumed) via
`continuity_from_productEquation_strictMono_pos`. -/
theorem appendixB_exponential_strictMono
    (Ψ : ℝ → ℝ) (ζ : ℝ → ℝ → ℝ)
    (hProd : ProductEquation Ψ ζ)
    (hPos : ∀ x, 0 < Ψ x)
    (hMono : StrictMono Ψ) :
    ∃ C A : ℝ, 0 < C ∧ ∀ x : ℝ, Ψ x = C * Real.exp (A * x) :=
  Multiplicative.productEquation_solution_of_strictMono Ψ ζ hProd hPos hMono

/-- **MAIN APPENDIX B THEOREM** (StrictAnti case): Same conclusion for strictly decreasing Ψ. -/
theorem appendixB_exponential_strictAnti
    (Ψ : ℝ → ℝ) (ζ : ℝ → ℝ → ℝ)
    (hProd : ProductEquation Ψ ζ)
    (hPos : ∀ x, 0 < Ψ x)
    (hAnti : StrictAnti Ψ) :
    ∃ C A : ℝ, 0 < C ∧ ∀ x : ℝ, Ψ x = C * Real.exp (A * x) :=
  Multiplicative.productEquation_solution_of_strictAnti Ψ ζ hProd hPos hAnti

/-! ## Corollary: Tensor is Scaled Multiplication

When we have an additive order-isomorphism representation of ⊗ (from Appendix A)
plus distributivity (Axiom 3), we can conclude ⊗ = scaled multiplication.

**Note**: For the full tensor theorems, import `Multiplicative.Main` (K&S path) or
`Multiplicative/Proofs/Direct/DirectProof.lean` (alternative path). This file focuses on the
most commonly-used results.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling
