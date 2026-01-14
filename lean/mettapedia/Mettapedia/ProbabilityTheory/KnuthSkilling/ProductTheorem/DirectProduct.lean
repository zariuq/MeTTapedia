import Mathlib.Data.Set.Prod
import Mettapedia.ProbabilityTheory.KnuthSkilling.Basic

/-!
# Lattice-level direct product (K&S “Independence”)

Knuth & Skilling (2012), §"Independence", introduces a **direct product** operation `×`
between (event) lattices. Informally, for events `x` in one lattice and `t` in another,
their product `x × t` is an event in a composite lattice.

This module packages the minimal lattice-level structure needed to talk about `×` in Lean:

* `prod : α → β → γ` producing the composite event,
* distributivity over `⊔` and `⊓` in each argument,
* and interaction with `⊥`.

Why not use the plain lattice product `α × β`?
Because for rectangles one wants (schematically) `(x ⊔ y) × t = (x × t) ⊔ (y × t)` and
`Disjoint x y → Disjoint (x × t) (y × t)`. In the coordinatewise lattice on `α × β`,
`(x,t) ⊓ (y,t) = (x ⊓ y, t)` is not `⊥` unless `t = ⊥`, so disjointness is not preserved.

The canonical concrete model is sets:
`prod := Set.prod` (`×ˢ`), mapping `Set Ω × Set Λ → Set (Ω × Λ)`.
The distributive laws are the familiar set equalities `(A ∪ B)×T = A×T ∪ B×T`, etc.

This is the lattice-level source of the scalar distributivity axiom
`(x ⊗ t) + (y ⊗ t) = (x + y) ⊗ t` used in Appendix B after Appendix A regrades `⊕` to `+`.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem

open Classical

/-- Event-level direct product between plausibility spaces.

`prod a b` should be read as the rectangle/event `a × b`. -/
structure DirectProduct (α β γ : Type*)
    [PlausibilitySpace α] [PlausibilitySpace β] [PlausibilitySpace γ] where
  prod : α → β → γ
  prod_bot_left : ∀ b : β, prod ⊥ b = ⊥
  prod_bot_right : ∀ a : α, prod a ⊥ = ⊥
  prod_sup_left : ∀ a₁ a₂ : α, ∀ b : β, prod (a₁ ⊔ a₂) b = prod a₁ b ⊔ prod a₂ b
  prod_sup_right : ∀ a : α, ∀ b₁ b₂ : β, prod a (b₁ ⊔ b₂) = prod a b₁ ⊔ prod a b₂
  prod_inf_left : ∀ a₁ a₂ : α, ∀ b : β, prod (a₁ ⊓ a₂) b = prod a₁ b ⊓ prod a₂ b
  prod_inf_right : ∀ a : α, ∀ b₁ b₂ : β, prod a (b₁ ⊓ b₂) = prod a b₁ ⊓ prod a b₂

namespace DirectProduct

variable {α β γ : Type*} [PlausibilitySpace α] [PlausibilitySpace β] [PlausibilitySpace γ]
variable (P : DirectProduct α β γ)

@[simp] theorem prod_bot_left' (b : β) : P.prod ⊥ b = (⊥ : γ) := P.prod_bot_left b
@[simp] theorem prod_bot_right' (a : α) : P.prod a ⊥ = (⊥ : γ) := P.prod_bot_right a

@[simp] theorem prod_sup_left' (a₁ a₂ : α) (b : β) :
    P.prod (a₁ ⊔ a₂) b = P.prod a₁ b ⊔ P.prod a₂ b :=
  P.prod_sup_left a₁ a₂ b

@[simp] theorem prod_sup_right' (a : α) (b₁ b₂ : β) :
    P.prod a (b₁ ⊔ b₂) = P.prod a b₁ ⊔ P.prod a b₂ :=
  P.prod_sup_right a b₁ b₂

@[simp] theorem prod_inf_left' (a₁ a₂ : α) (b : β) :
    P.prod (a₁ ⊓ a₂) b = P.prod a₁ b ⊓ P.prod a₂ b :=
  P.prod_inf_left a₁ a₂ b

@[simp] theorem prod_inf_right' (a : α) (b₁ b₂ : β) :
    P.prod a (b₁ ⊓ b₂) = P.prod a b₁ ⊓ P.prod a b₂ :=
  P.prod_inf_right a b₁ b₂

/-- Disjointness is preserved in the left argument (for any fixed right factor). -/
theorem disjoint_prod_left {a₁ a₂ : α} {b : β} (h : Disjoint a₁ a₂) :
    Disjoint (P.prod a₁ b) (P.prod a₂ b) := by
  -- `Disjoint` in a lattice is `inf = ⊥`.
  refine (disjoint_iff).2 ?_
  calc
    P.prod a₁ b ⊓ P.prod a₂ b
        = P.prod (a₁ ⊓ a₂) b := by
            simp [P.prod_inf_left a₁ a₂ b]
    _ = P.prod ⊥ b := by simp [disjoint_iff.mp h]
    _ = ⊥ := P.prod_bot_left b

/-- Disjointness is preserved in the right argument (for any fixed left factor). -/
theorem disjoint_prod_right {a : α} {b₁ b₂ : β} (h : Disjoint b₁ b₂) :
    Disjoint (P.prod a b₁) (P.prod a b₂) := by
  refine (disjoint_iff).2 ?_
  calc
    P.prod a b₁ ⊓ P.prod a b₂
        = P.prod a (b₁ ⊓ b₂) := by
            simp [P.prod_inf_right a b₁ b₂]
    _ = P.prod a ⊥ := by simp [disjoint_iff.mp h]
    _ = ⊥ := P.prod_bot_right a

end DirectProduct

/-!
## The canonical model: sets

For any `Ω` and `Λ`, the powerset lattices `Set Ω`, `Set Λ` embed into `Set (Ω × Λ)` via
`Set.prod` (`×ˢ`). The distributive laws are built into Mathlib as simp lemmas.
-/

namespace SetModel

open Set

/-- `Set.prod` (`×ˢ`) as a direct product of plausibility spaces. -/
noncomputable def setDirectProduct (Ω Λ : Type*) :
    DirectProduct (Set Ω) (Set Λ) (Set (Ω × Λ)) where
  prod := fun A B => A ×ˢ B
  prod_bot_left := by intro B; simp
  prod_bot_right := by intro A; simp
  prod_sup_left := by intro A₁ A₂ B; simp
  prod_sup_right := by intro A B₁ B₂; simp
  prod_inf_left := by intro A₁ A₂ B; ext p; simp [and_left_comm, and_assoc]
  prod_inf_right := by intro A B₁ B₂; ext p; simp [and_left_comm, and_assoc]

end SetModel

end Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem
