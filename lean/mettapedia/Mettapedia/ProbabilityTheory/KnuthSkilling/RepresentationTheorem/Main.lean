import Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Globalization
import Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.HolderEmbedding

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem

open Classical
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.HolderEmbedding

/-!
# K&S Representation Theorem: Main Theorem (Public API)

This file is intentionally short: it exposes the representation theorem statement and the main
corollary (commutativity), assuming the globalization class.

For the globalization construction itself (the “triple family trick”), see:
`Mettapedia/ProbabilityTheory/KnuthSkilling/RepresentationTheorem/Globalization.lean`.

Paper cross-reference:
- `paper/ks-formalization.tex`, Subsection “The Representation Theorem” (inside Section `sec:main`).
- Background statement “KS Representation” (label `thm:ks-main`).
- Section “Commutativity from Separation” (label `sec:commutativity`) for the separation ⇒ commutativity story.
-/

/-- **K&S Appendix A main theorem**: existence of an order embedding `Θ : α → ℝ` turning `op` into `+`.

Lean architecture note:
- In the paper, the theorem is presented as a single statement about `KnuthSkillingAlgebra` +
  separation assumptions.
- In Lean, the substantive Appendix A induction is packaged as the typeclass
  `RepresentationGlobalization`, and this theorem simply exposes the `exists_Theta` field as the public
  API. -/
theorem associativity_representation
    (α : Type*) [KnuthSkillingAlgebra α] [KSSeparation α] [RepresentationGlobalization α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  exact RepresentationGlobalization.exists_Theta (α := α)

/-- Convenience wrapper: with `[KSSeparation α]` and dense order, the globalization instance is
automatic, so the representation theorem can be used without mentioning `RepresentationGlobalization`. -/
theorem associativity_representation_of_KSSeparation_of_denselyOrdered
    (α : Type*) [KnuthSkillingAlgebra α] [KSSeparation α] [DenselyOrdered α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  -- `KSSeparation` upgrades to `KSSeparationStrict` under density, which provides globalization.
  exact associativity_representation (α := α)

/-- Convenience wrapper: a weaker “density above `ident`” hypothesis also suffices to upgrade
`KSSeparation` to `KSSeparationStrict`, and thus obtain the representation theorem. -/
theorem associativity_representation_of_KSSeparation_of_exists_between_pos
    (α : Type*) [KnuthSkillingAlgebra α] [KSSeparation α]
    (hBetween : ∀ {x y : α}, ident < x → x < y → ∃ z, x < z ∧ z < y) :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  letI : KSSeparationStrict α :=
    KSSeparation.toKSSeparationStrict_of_exists_between_pos (α := α) (hBetween := hBetween)
  exact associativity_representation (α := α)

/-- Commutativity as a corollary of the representation theorem. -/
theorem op_comm_of_associativity
    (α : Type*) [KnuthSkillingAlgebra α] [KSSeparation α] [RepresentationGlobalization α] :
    ∀ x y : α, op x y = op y x := by
  classical
  obtain ⟨Θ, hΘ_order, _, hΘ_add⟩ := associativity_representation (α := α)
  exact commutativity_from_representation Θ hΘ_order hΘ_add

/-! ## Unified Representation Interface for KSSeparation Path

We connect the KSSeparation path to the unified RepresentationResult structure
defined in `HolderEmbedding.lean`. This allows uniform reasoning across paths.

**KSSeparation path characteristics:**
- Requires: `[KnuthSkillingAlgebra α] [KSSeparation α] [RepresentationGlobalization α]`
- Provides: `NormalizedRepresentationResult α` (with Θ ident = 0)

**Comparison with Hölder path:**
- Hölder: `NoAnomalousPairs α` → `RepresentationResult α` (identity-free)
- Hölder: `NoAnomalousPairs α` → `NormalizedRepresentationResult α` (with identity)
- KSSeparation: `KSSeparation α` + globalization → `NormalizedRepresentationResult α`

**Note on identity:**
The KSSeparation path currently uses `ident` in its hypotheses (e.g., `ident < a`).
A future refactoring could use `ℕ+` powers instead, making identity optional.
For now, KSSeparation produces only the normalized result. -/

variable {α : Type*} [KnuthSkillingAlgebra α]

/-- KSSeparation path produces a NormalizedRepresentationResult.
    This connects the KSSeparation path to the unified interface.

    Note: Unlike the Hölder path, KSSeparation currently requires identity in
    its hypotheses (`ident < a` for positivity), so we don't have an identity-free
    version. Future work could refactor to use `ℕ+` powers. -/
noncomputable def ksseparation_normalized_representation
    [KSSeparation α] [RepresentationGlobalization α] : NormalizedRepresentationResult α :=
  let h := associativity_representation α
  { Θ := Classical.choose h
    order_preserving := (Classical.choose_spec h).1
    additive := (Classical.choose_spec h).2.2
    ident_zero := (Classical.choose_spec h).2.1 }

/-- The KSSeparation path provides canonical normalization Θ(ident) = 0.
    This is inherited from the identity being available in the hypothesis. -/
theorem ksseparation_provides_canonical_normalization
    [KSSeparation α] [RepresentationGlobalization α] :
    (ksseparation_normalized_representation (α := α)).Θ ident = 0 :=
  ksseparation_normalized_representation.ident_zero

/-! ## Path Comparison Summary

| Path | Hypothesis | Identity-Free? | Provides |
|------|------------|----------------|----------|
| Hölder | `NoAnomalousPairs α` | Yes | `RepresentationResult α` |
| Hölder | `NoAnomalousPairs α` | With ident | `NormalizedRepresentationResult α` |
| KSSeparation | `KSSeparation α` | No (uses ident) | `NormalizedRepresentationResult α` |

**Key insight**: The Hölder path is more general because:
1. It works without identity (semigroup-only)
2. `KSSeparation` + `IdentIsMinimum` implies `NoAnomalousPairs`

Thus the Hölder path subsumes the KSSeparation path when identity is available,
and extends to the identity-free case. -/

end Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem
