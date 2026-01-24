import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Basic

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Additive

open Classical
open KSSemigroupBase
open KnuthSkillingMonoidBase

/-!
# Representation Interfaces (Identity-Free by Default)

This file defines the unified representation interfaces used throughout the K&S Appendix A story.
The **default** interface is identity-free (`KSSemigroupBase`), and the normalized/identity
variant is provided separately for probability-theory use.
-/

/-- **Representation result** (identity-free version).
    Captures the minimal structure: order embedding + additive homomorphism. -/
structure RepresentationResult (α : Type*) [KSSemigroupBase α] where
  /-- The representation function Θ : α → ℝ -/
  Θ : α → ℝ
  /-- Order-preserving: a ≤ b ↔ Θ a ≤ Θ b -/
  order_preserving : ∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b
  /-- Additive homomorphism: Θ(x ⊕ y) = Θ x + Θ y -/
  additive : ∀ x y : α, Θ (op x y) = Θ x + Θ y

/-- **Normalized representation result** (with identity).
    Extends `RepresentationResult` with canonical normalization Θ(ident) = 0. -/
structure NormalizedRepresentationResult (α : Type*) [KnuthSkillingMonoidBase α]
    extends RepresentationResult α where
  /-- Canonical normalization: Θ(ident) = 0 -/
  ident_zero : Θ ident = 0

/-! ### Basic Lemmas -/

/-- Strict order-preserving: a < b ↔ Θ a < Θ b. -/
theorem RepresentationResult.strict_order_preserving {α : Type*} [KSSemigroupBase α]
    (r : RepresentationResult α) : ∀ a b : α, a < b ↔ r.Θ a < r.Θ b := by
  intro a b
  constructor
  · intro hab
    have h1 : a ≤ b := le_of_lt hab
    have h2 : ¬(b ≤ a) := not_le_of_gt hab
    have hΘ1 : r.Θ a ≤ r.Θ b := (r.order_preserving a b).mp h1
    have hΘ2 : ¬(r.Θ b ≤ r.Θ a) := fun h => h2 ((r.order_preserving b a).mpr h)
    exact lt_of_le_of_ne hΘ1 (fun heq => hΘ2 (le_of_eq heq.symm))
  · intro hΘ
    have h1 : r.Θ a ≤ r.Θ b := le_of_lt hΘ
    have h2 : ¬(r.Θ b ≤ r.Θ a) := not_le_of_gt hΘ
    have ha1 : a ≤ b := (r.order_preserving a b).mpr h1
    have ha2 : ¬(b ≤ a) := fun h => h2 ((r.order_preserving b a).mp h)
    exact lt_of_le_of_ne ha1 (fun heq => ha2 (le_of_eq heq.symm))

/-- Representation is injective (order embedding). -/
theorem RepresentationResult.injective {α : Type*} [KSSemigroupBase α]
    (r : RepresentationResult α) : Function.Injective r.Θ := by
  intro a b hab
  have h1 : r.Θ a ≤ r.Θ b := le_of_eq hab
  have h2 : r.Θ b ≤ r.Θ a := le_of_eq hab.symm
  have ha1 : a ≤ b := (r.order_preserving a b).mpr h1
  have ha2 : b ≤ a := (r.order_preserving b a).mpr h2
  exact le_antisymm ha1 ha2

/-- Additivity + identity forces Θ(ident) = 0. -/
theorem RepresentationResult.ident_zero_of_ident {α : Type*} [KnuthSkillingMonoidBase α]
    (r : RepresentationResult α) : r.Θ ident = 0 := by
  have h := r.additive ident ident
  -- op ident ident = ident, so Θ ident = Θ ident + Θ ident
  have h' : r.Θ ident = r.Θ ident + r.Θ ident := by
    simpa [op_ident_left] using h
  linarith

/-- Convert a representation into a normalized representation when identity exists. -/
def RepresentationResult.toNormalized {α : Type*} [KnuthSkillingMonoidBase α]
    (r : RepresentationResult α) : NormalizedRepresentationResult α :=
  { r with ident_zero := r.ident_zero_of_ident }

/-! ### Public Typeclass Interfaces -/

/-- **Identity-free representation theorem** (default).
    Exposes existence of an order-preserving additive representation. -/
class HasRepresentationTheorem (α : Type*) [KSSemigroupBase α] : Prop where
  exists_representation :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y

/-- **Normalized representation theorem** (identity-based convenience).
    Exposes existence of an order-preserving additive representation with Θ(ident) = 0. -/
class HasNormalizedRepresentation (α : Type*) [KnuthSkillingMonoidBase α] : Prop where
  exists_representation :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y

/-! ### Convenience Lemmas / Instances -/

/-- Extract a representation from the identity-free interface. -/
theorem exists_Theta_of_hasRepresentationTheorem
    (α : Type*) [KSSemigroupBase α] [HasRepresentationTheorem α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  simpa using (HasRepresentationTheorem.exists_representation (α := α))

/-- Extract a normalized representation from the identity-based interface. -/
theorem exists_Theta_of_hasNormalizedRepresentation
    (α : Type*) [KnuthSkillingMonoidBase α] [HasNormalizedRepresentation α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  simpa using (HasNormalizedRepresentation.exists_representation (α := α))

/-- Forget normalization: a normalized representation is a representation. -/
instance hasRepresentation_of_hasNormalized
    (α : Type*) [KnuthSkillingMonoidBase α] [HasNormalizedRepresentation α] :
    HasRepresentationTheorem α where
  exists_representation := by
    obtain ⟨Θ, hΘ_order, _hΘ_ident, hΘ_add⟩ :=
      HasNormalizedRepresentation.exists_representation (α := α)
    exact ⟨Θ, hΘ_order, hΘ_add⟩

/-- Identity makes every representation automatically normalized. -/
instance hasNormalized_of_hasRepresentation
    (α : Type*) [KnuthSkillingMonoidBase α] [HasRepresentationTheorem α] :
    HasNormalizedRepresentation α where
  exists_representation := by
    classical
    obtain ⟨Θ, hΘ_order, hΘ_add⟩ :=
      HasRepresentationTheorem.exists_representation (α := α)
    have hΘ_ident : Θ ident = 0 := by
      -- Θ ident = Θ ident + Θ ident
      have h := hΘ_add ident ident
      have h' : Θ ident = Θ ident + Θ ident := by
        simpa [op_ident_left] using h
      linarith
    exact ⟨Θ, hΘ_order, hΘ_ident, hΘ_add⟩

end Mettapedia.ProbabilityTheory.KnuthSkilling.Additive
