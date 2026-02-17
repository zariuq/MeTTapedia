import Mettapedia.OSLF.Framework.RewriteSystem
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Observational Quotients: Independence + Symmetry Parameters

This module provides a small reusable layer for the "weakest core modulo
observations" style used in OSLF/GSLT workflows:

- labeled rewrite steps
- an explicit independence relation on labels
- explicit symmetry actions on states
- orbit quotients
- factorization of invariant observations through the quotient

The design is intentionally compact so concrete systems (GF, PLN, ρ-calculus,
etc.) can instantiate and extend it.
-/

namespace Mettapedia.OSLF.Framework

/-- A labeled one-step rewrite relation. -/
structure LabeledRewrite (Label α : Type*) where
  step : Label → α → α → Prop

/-- A user-provided independence relation on labels. -/
structure LabelIndependence (Label : Type*) where
  indep : Label → Label → Prop
  symm : Symmetric indep

/-- Local commutation square for two labels at a source state. -/
def CommuteAt {Label α : Type*} (rw : LabeledRewrite Label α)
    (ℓ₁ ℓ₂ : Label) : Prop :=
  ∀ x y₁ y₂, rw.step ℓ₁ x y₁ → rw.step ℓ₂ x y₂ →
    ∃ z, rw.step ℓ₂ y₁ z ∧ rw.step ℓ₁ y₂ z

/-- Group action used as a symmetry family on states. -/
structure SymmetryAction (Γ α : Type*) [Group Γ] where
  act : Γ → α → α
  one_act : ∀ x, act 1 x = x
  mul_act : ∀ g h x, act (g * h) x = act g (act h x)

/-- Symmetry action preserves labeled one-step rewrites. -/
def StepEquivariant {Label Γ α : Type*} [Group Γ]
    (rw : LabeledRewrite Label α) (A : SymmetryAction Γ α) : Prop :=
  ∀ g ℓ x y, rw.step ℓ x y → rw.step ℓ (A.act g x) (A.act g y)

/-- Orbit relation induced by a symmetry action. -/
def OrbitRel {Γ α : Type*} [Group Γ] (A : SymmetryAction Γ α) : α → α → Prop :=
  fun x y => ∃ g, A.act g x = y

namespace OrbitRel

variable {Γ α : Type*} [Group Γ] (A : SymmetryAction Γ α)

theorem refl : Reflexive (OrbitRel A) := by
  intro x
  exact ⟨1, A.one_act x⟩

theorem symm : Symmetric (OrbitRel A) := by
  intro x y hxy
  rcases hxy with ⟨g, rfl⟩
  refine ⟨g⁻¹, ?_⟩
  calc
    A.act g⁻¹ (A.act g x) = A.act (g⁻¹ * g) x := by
      rw [A.mul_act]
    _ = A.act 1 x := by simp
    _ = x := A.one_act x

  theorem trans : Transitive (OrbitRel A) := by
  intro x y z hxy hyz
  rcases hxy with ⟨g, rfl⟩
  rcases hyz with ⟨h, rfl⟩
  refine ⟨h * g, ?_⟩
  simp [A.mul_act]

theorem equivalence : Equivalence (OrbitRel A) :=
  by
    refine ⟨refl A, ?_, ?_⟩
    intro x y hxy
    exact symm A hxy
    intro x y z hxy hyz
    exact trans A hxy hyz

end OrbitRel

/-- Setoid of states modulo symmetry-orbit equivalence. -/
def orbitSetoid {Γ α : Type*} [Group Γ] (A : SymmetryAction Γ α) : Setoid α :=
  ⟨OrbitRel A, OrbitRel.equivalence A⟩

/-- Observations invariant under symmetry actions. -/
def ObsInvariant {Γ α β : Type*} [Group Γ]
    (A : SymmetryAction Γ α) (obs : α → β) : Prop :=
  ∀ g x, obs (A.act g x) = obs x

theorem obs_eq_of_orbit {Γ α β : Type*} [Group Γ]
    (A : SymmetryAction Γ α) (obs : α → β)
    (hInv : ObsInvariant A obs) {x y : α}
    (hxy : OrbitRel A x y) : obs x = obs y := by
  rcases hxy with ⟨g, rfl⟩
  simp [hInv g x]

/-- Invariant observations descend to the orbit quotient. -/
def obsFactor {Γ α β : Type*} [Group Γ]
    (A : SymmetryAction Γ α) (obs : α → β)
    (hInv : ObsInvariant A obs) :
    Quotient (orbitSetoid A) → β :=
  Quotient.lift obs (by
    intro x y hxy
    exact obs_eq_of_orbit A obs hInv hxy)

theorem obsFactor_spec {Γ α β : Type*} [Group Γ]
    (A : SymmetryAction Γ α) (obs : α → β)
    (hInv : ObsInvariant A obs) (x : α) :
    obsFactor A obs hInv (Quotient.mk (orbitSetoid A) x) = obs x := rfl

/-- Minimal package combining labeled steps, independence, and symmetries. -/
structure ObservableKernel (Label Γ α : Type*) [Group Γ] where
  rewrite : LabeledRewrite Label α
  indep : LabelIndependence Label
  symm : SymmetryAction Γ α
  equivariant : StepEquivariant rewrite symm

namespace ObservableKernel

variable {Label Γ α : Type*} [Group Γ] (K : ObservableKernel Label Γ α)

/-- Any label-independent pair that is also commuting yields a local square law. -/
def IndependentCommuting (ℓ₁ ℓ₂ : Label) : Prop :=
  K.indep.indep ℓ₁ ℓ₂ ∧ CommuteAt K.rewrite ℓ₁ ℓ₂

theorem independent_symm (ℓ₁ ℓ₂ : Label) :
    K.indep.indep ℓ₁ ℓ₂ → K.indep.indep ℓ₂ ℓ₁ :=
  by
    intro h
    exact K.indep.symm h

end ObservableKernel

end Mettapedia.OSLF.Framework
