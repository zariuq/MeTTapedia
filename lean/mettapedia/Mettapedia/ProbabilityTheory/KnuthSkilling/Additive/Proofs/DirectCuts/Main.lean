import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Algebra
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.DirectCuts.DirectCuts

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.DirectCuts

open Classical
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra

/-!
# K&S Representation Theorem: Alternative Proof (Direct Cuts)

This file packages the Dedekind-cuts construction from
`Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.DirectCuts.DirectCuts`
as a single “public theorem” that matches the main API statement.

## Why this file exists

Lean can’t attach two different proofs to the same constant.  So we keep:
- the grid/induction proof as the mainline (`Additive/Proofs/GridInduction/Main.lean`), and
- this cuts-based proof as an alternative entrypoint.

Paper cross-reference:
- `paper/ks-formalization.tex`, Section “The Representation Theorem” (label `thm:ks-main`).
- For the “cuts/log” alternative, see the discussion around Hölder-style constructions.
-/

variable {α : Type*} [KnuthSkillingAlgebraBase α] [KSSeparation α]

/-!
## Main theorem (cuts version)
-/

/-- **K&S Appendix A representation theorem (cuts proof)**.

Assumptions:
- `KnuthSkillingAlgebraBase α` (order + associativity + identity + `ident` is minimum)
- `KSSeparation α` (iterate/power “sandwich” axiom)
- `KSSeparationStrict α` (strict upper-bound variant; often derived from density)

Conclusion:
There exists an order embedding `Θ : α → ℝ` with `Θ ident = 0` and `Θ (x ⊕ y) = Θ x + Θ y`.
-/
theorem associativity_representation_cuts
    (α : Type*) [KnuthSkillingAlgebraBase α] [KSSeparation α] [KSSeparationStrict α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  classical
  -- Handle the trivial algebra case: all elements are `ident`.
  by_cases htriv : ∀ x : α, x = ident
  · refine ⟨fun _ => 0, ?_, rfl, fun _ _ => ?_⟩
    · intro a b
      simp [htriv a, htriv b]
    · simp
  -- Non-trivial: pick a base element `a₀ > ident` and use `Θ_cuts a₀`.
  push_neg at htriv
  obtain ⟨a₀, ha₀_ne⟩ := htriv
  have ha₀ : ident < a₀ := lt_of_le_of_ne (ident_le a₀) (Ne.symm ha₀_ne)
  refine ⟨Θ_cuts a₀ ha₀, ?_, Θ_cuts_ident a₀ ha₀, fun x y => Θ_cuts_add a₀ ha₀ x y⟩
  · have hstrict : StrictMono (Θ_cuts a₀ ha₀) := Θ_cuts_strictMono (a := a₀) ha₀
    intro a b
    constructor
    · intro hab
      exact hstrict.monotone hab
    · intro hab
      by_contra hba
      have hlt : b < a := lt_of_not_ge hba
      exact (not_le_of_gt (hstrict hlt)) hab

/-- Convenience wrapper: density upgrades `KSSeparation` to `KSSeparationStrict`,
so the cuts-based representation theorem can be used without mentioning strict separation. -/
theorem associativity_representation_cuts_of_denselyOrdered
    (α : Type*) [KnuthSkillingAlgebraBase α] [KSSeparation α] [DenselyOrdered α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  letI : KSSeparationStrict α := KSSeparation.toKSSeparationStrict_of_denselyOrdered (α := α)
  exact associativity_representation_cuts (α := α)

end Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.DirectCuts
