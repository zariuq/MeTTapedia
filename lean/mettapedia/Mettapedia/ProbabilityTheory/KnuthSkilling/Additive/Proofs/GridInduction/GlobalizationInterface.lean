import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Algebra

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Additive

open Classical

/-!
# Grid Induction: Globalization Interfaces (Lightweight)

This file contains *only* the typeclass interfaces used to state the Appendix A
representation theorem in a proof-agnostic way.

Key design goal: keep the dependency surface small.

- The heavy grid/induction construction (the "triple family trick") lives in:
  `Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.Globalization`.
- The Hölder/ordered-semigroup embedding path should be able to import *just* these
  interfaces without pulling the whole grid machinery into the default build.
-/

section WithIdentity

open KnuthSkillingMonoidBase

/-- Globalization step for the (identity-normalized) representation theorem:
existence of an additive order embedding `Θ : α → ℝ` with `Θ ident = 0`. -/
class RepresentationGlobalization (α : Type*) [KnuthSkillingMonoidBase α] : Prop where
  /-- Existence of an order embedding `Θ : α → ℝ` turning `op` into `+`. -/
  exists_Theta :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y

end WithIdentity

section IdentityFree

open KSSemigroupBase

/-! ## Identity-Free Globalization Interface (No Normalization) -/

/-- Identity-free globalization: existence of an additive order embedding.

This interface makes **no** normalization claim (no distinguished "zero"). -/
class RepresentationGlobalizationSemigroup (α : Type*) [KSSemigroupBase α] : Prop where
  /-- Existence of an order embedding `Θ : α → ℝ` turning `op` into `+`. -/
  exists_Theta :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y

/-- Identity-free globalization normalized to an *anchor* element.

This is provided for completeness; it is rarely used in the K&S development.
-/
class RepresentationGlobalizationAnchor (α : Type*) [KSSemigroupBase α] [KSSeparationSemigroup α]
    (anchor : α) (h_anchor : IsPositive anchor) : Prop where
  /-- Existence of an order embedding `Θ : α → ℝ` turning `op` into `+`, with `Θ(anchor) = 0`. -/
  exists_Theta :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ anchor = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y

end IdentityFree

section Bridge

/-!
## Bridge: normalized globalization ⇒ identity-free globalization

If we have `Θ ident = 0`, we can forget this normalization and obtain the
identity-free interface directly.
-/

instance representationGlobalizationSemigroup_of_representationGlobalization
    (α : Type*) [KnuthSkillingMonoidBase α] [RepresentationGlobalization α] :
    RepresentationGlobalizationSemigroup α where
  exists_Theta := by
    obtain ⟨Θ, hΘ_order, _hΘ_ident, hΘ_add⟩ :=
      RepresentationGlobalization.exists_Theta (α := α)
    exact ⟨Θ, hΘ_order, hΘ_add⟩

end Bridge

end Mettapedia.ProbabilityTheory.KnuthSkilling.Additive

