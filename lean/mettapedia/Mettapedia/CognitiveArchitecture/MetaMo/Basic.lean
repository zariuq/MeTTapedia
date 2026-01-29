/-
# MetaMo: Motivational Meta-Model

Formalization of Ben Goertzel & Ying Lian's Motivational Meta-Model (MetaMo)
from "Weakness and Its Quantale: Plausibility Theory from First Principles"

MetaMo provides a mathematical framework for AGI motivational dynamics based on:
- Q-modules (motivational state spaces) over commutative quantales
- Appraisal functors (sensitivity to environmental stimuli)
- Decision functors (action selection based on goals)
- Contractive dynamics guaranteeing stable equilibria

## Core Mathematical Structure

A Q-module Θ over a commutative quantale (Q, ⊗, ⊕) consists of:
- A complete lattice (Θ, ⊔)
- A scalar multiplication • : Q × Θ → Θ satisfying:
  - (q₁ ⊗ q₂) • θ = q₁ • (q₂ • θ)  (associativity)
  - ⊤ • θ = θ                         (identity)
  - q • (θ₁ ⊔ θ₂) = (q • θ₁) ⊔ (q • θ₂) (distributivity)

## References

- Goertzel & Lian, "Weakness and Its Quantale" (Appendix on MetaMo)
- Rosenthal, "Quantales and their Applications"
-/

import Mettapedia.Algebra.QuantaleWeakness

namespace Mettapedia.CognitiveArchitecture.MetaMo

open Mettapedia.Algebra.QuantaleWeakness

/-! ## Q-Module Structure

The fundamental structure for motivational state spaces.
-/

/-- A Q-module over a commutative quantale Q.

This generalizes the standard module structure to quantales, where the base "ring"
is replaced by a quantale (a complete lattice with a monoid structure such that
multiplication distributes over arbitrary suprema).

The carrier Θ represents the space of motivational states, and the scalar
multiplication represents how quantale elements (interpreted as intensities,
confidences, or weights) modulate motivational states.
-/
class QModule (Q : Type*) (Θ : Type*)
    [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
    [CompleteLattice Θ] where
  /-- Scalar multiplication: a quantale element modulates a motivational state -/
  smul : Q → Θ → Θ
  /-- The identity element acts trivially -/
  smul_one : ∀ θ : Θ, smul 1 θ = θ
  /-- Scalar multiplication is associative with quantale multiplication -/
  smul_assoc : ∀ (q₁ q₂ : Q) (θ : Θ), smul (q₁ * q₂) θ = smul q₁ (smul q₂ θ)
  /-- Scalar multiplication distributes over lattice joins in Θ -/
  smul_sup : ∀ (q : Q) (θ₁ θ₂ : Θ), smul q (θ₁ ⊔ θ₂) = smul q θ₁ ⊔ smul q θ₂

/-- Notation: q • θ for scalar multiplication -/
scoped infixr:73 " • " => QModule.smul

variable {Q : Type*} {Θ : Type*}
  [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
  [CompleteLattice Θ] [QModule Q Θ]

/-! ### Basic Q-Module Lemmas -/

/-- The identity element acts as identity -/
@[simp]
theorem one_smul (θ : Θ) : (1 : Q) • θ = θ := QModule.smul_one θ

/-- Scalar multiplication is associative -/
theorem mul_smul (q₁ q₂ : Q) (θ : Θ) : (q₁ * q₂) • θ = q₁ • (q₂ • θ) :=
  QModule.smul_assoc q₁ q₂ θ

/-- Scalar multiplication distributes over joins -/
theorem smul_sup (q : Q) (θ₁ θ₂ : Θ) : q • (θ₁ ⊔ θ₂) = q • θ₁ ⊔ q • θ₂ :=
  QModule.smul_sup q θ₁ θ₂

/-- Scalar multiplication preserves the order when Q is ordered -/
theorem smul_mono_right (q : Q) {θ₁ θ₂ : Θ} (h : θ₁ ≤ θ₂) : q • θ₁ ≤ q • θ₂ := by
  have hsup : θ₁ ⊔ θ₂ = θ₂ := sup_eq_right.mpr h
  calc q • θ₁ ≤ q • θ₁ ⊔ q • θ₂ := le_sup_left
       _ = q • (θ₁ ⊔ θ₂) := (smul_sup q θ₁ θ₂).symm
       _ = q • θ₂ := by rw [hsup]

/-- Commutativity of successive scalar multiplications follows from quantale commutativity -/
theorem smul_smul_comm (q₁ q₂ : Q) (θ : Θ) : q₁ • (q₂ • θ) = q₂ • (q₁ • θ) := by
  rw [← mul_smul, ← mul_smul, mul_comm]

/-! ## Motivational State Type

The standard motivational state space is the unit interval [0,1], but we keep
the formalization general.
-/

/-- A motivational state is a value in the Q-module carrier -/
abbrev MotivationalState (Q : Type*) (Θ : Type*)
    [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
    [CompleteLattice Θ] [QModule Q Θ] := Θ

/-! ## Example: Self-Module

Any commutative quantale Q is a Q-module over itself via multiplication.
This is the simplest non-trivial example.
-/

/-- A commutative quantale is a module over itself via multiplication -/
instance selfQModule (Q : Type*) [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q] :
    QModule Q Q where
  smul := (· * ·)
  smul_one θ := one_mul θ
  smul_assoc q₁ q₂ θ := by
    show (q₁ * q₂) * θ = q₁ * (q₂ * θ)
    exact mul_assoc q₁ q₂ θ
  smul_sup q θ₁ θ₂ := by
    show q * (θ₁ ⊔ θ₂) = q * θ₁ ⊔ q * θ₂
    -- Use quantale distributivity: q * sSup S = ⨆ s ∈ S, q * s
    have hdist : q * sSup {θ₁, θ₂} = ⨆ y ∈ ({θ₁, θ₂} : Set Q), q * y :=
      IsQuantale.mul_sSup_distrib q {θ₁, θ₂}
    -- sSup {θ₁, θ₂} = θ₁ ⊔ θ₂
    have hsup : sSup ({θ₁, θ₂} : Set Q) = θ₁ ⊔ θ₂ := sSup_pair
    rw [← hsup, hdist]
    -- ⨆ y ∈ {θ₁, θ₂}, q * y = q * θ₁ ⊔ q * θ₂
    exact iSup_pair

/-! ## Q-Module Endomorphisms

A Q-module endomorphism is a map f : Θ → Θ that commutes with scalar multiplication.
Appraisal and decision functors will be instances of these.
-/

/-- A Q-module endomorphism preserves the scalar multiplication structure -/
@[ext]
structure QModuleEndo (Q : Type*) (Θ : Type*)
    [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
    [CompleteLattice Θ] [QModule Q Θ] where
  /-- The underlying function -/
  toFun : Θ → Θ
  /-- Commutes with scalar multiplication -/
  map_smul : ∀ (q : Q) (θ : Θ), toFun (q • θ) = q • toFun θ

instance : CoeFun (QModuleEndo Q Θ) (fun _ => Θ → Θ) :=
  ⟨QModuleEndo.toFun⟩

namespace QModuleEndo

/-- Identity endomorphism -/
def id : QModuleEndo Q Θ where
  toFun := _root_.id
  map_smul _ _ := rfl

/-- Composition of endomorphisms -/
def comp (g f : QModuleEndo Q Θ) : QModuleEndo Q Θ where
  toFun := g.toFun ∘ f.toFun
  map_smul q θ := by
    show g (f (q • θ)) = q • g (f θ)
    rw [f.map_smul, g.map_smul]

@[simp]
theorem id_apply (θ : Θ) : (QModuleEndo.id : QModuleEndo Q Θ) θ = θ := rfl

@[simp]
theorem comp_apply (g f : QModuleEndo Q Θ) (θ : Θ) : (g.comp f) θ = g (f θ) := rfl

/-- Composition is associative -/
theorem comp_assoc (h g f : QModuleEndo Q Θ) : h.comp (g.comp f) = (h.comp g).comp f := rfl

/-- Identity is left unit -/
theorem id_comp (f : QModuleEndo Q Θ) : QModuleEndo.id.comp f = f := by
  ext θ; rfl

/-- Identity is right unit -/
theorem comp_id (f : QModuleEndo Q Θ) : f.comp QModuleEndo.id = f := by
  ext θ; rfl

end QModuleEndo

/-! ## Scalar Multiplication Endomorphisms

The key endomorphisms in MetaMo are those induced by scalar multiplication:
given q ∈ Q, define f_q(θ) = q • θ.
-/

/-- The endomorphism induced by scalar multiplication -/
def smulEndo (q : Q) : QModuleEndo Q Θ where
  toFun := fun θ => q • θ
  map_smul q' θ := by
    show q • (q' • θ) = q' • (q • θ)
    exact smul_smul_comm q q' θ

@[simp]
theorem smulEndo_apply (q : Q) (θ : Θ) : smulEndo q θ = q • θ := rfl

/-- Composition of scalar endomorphisms corresponds to quantale multiplication -/
theorem smulEndo_comp (q₁ q₂ : Q) :
    (smulEndo q₁ : QModuleEndo Q Θ).comp (smulEndo q₂) = smulEndo (q₁ * q₂) := by
  ext θ
  simp only [QModuleEndo.comp_apply, smulEndo_apply]
  exact (mul_smul q₁ q₂ θ).symm

/-- Scalar endomorphisms commute (since Q is commutative) -/
theorem smulEndo_comm (q₁ q₂ : Q) :
    (smulEndo q₁ : QModuleEndo Q Θ).comp (smulEndo q₂) =
    (smulEndo q₂ : QModuleEndo Q Θ).comp (smulEndo q₁) := by
  rw [smulEndo_comp, smulEndo_comp, mul_comm]

end Mettapedia.CognitiveArchitecture.MetaMo
