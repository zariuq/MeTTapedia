import Mathlib.Order.Hom.CompleteLattice

/-!
# Θ-Completions and Credal / Interval Semantics

This module provides a small API for turning a *family of completions* (often written `Θ`) into
either:

* **point semantics** (when `Θ` is unique), or
* **credal / interval semantics** (when there are multiple compatible `Θ`).

We keep this file intentionally abstract: it depends only on `CompleteLattice` structure on the
codomain. This makes it reusable across Hypercube vertices with different value-quantales.

In the K&S story, `Θ : α → ℝ` is the representation into an additive scale. When the axioms pin down
`Θ` uniquely (up to the expected normalizations), one gets point-valued probability; when they do
not, one naturally gets an *interval envelope* (“imprecise probability” / a credal set).
-/

namespace Mettapedia.ProbabilityTheory.Hypercube

namespace ThetaSemantics

open Set

variable {α β : Type*}

/-- A point semantics is just a single completion `Θ`. -/
structure PointSemantics (α β : Type*) where
  Θ : α → β

/-- Interval semantics packages lower/upper envelopes. -/
structure IntervalSemantics (α β : Type*) where
  lower : α → β
  upper : α → β

@[ext]
theorem IntervalSemantics.ext {s t : IntervalSemantics α β}
    (hL : s.lower = t.lower) (hU : s.upper = t.upper) : s = t := by
  cases s
  cases t
  cases hL
  cases hU
  rfl

/-! ## Envelopes induced by a family of completions -/

/-- The set of possible values at `x` induced by a set of candidate completions. -/
def thetaValues (Θs : Set (α → β)) (x : α) : Set β :=
  (fun Θ => Θ x) '' Θs

@[simp]
theorem thetaValues_singleton (Θ : α → β) (x : α) :
    thetaValues (Set.singleton Θ) x = {Θ x} := by
  ext y
  constructor
  · rintro ⟨Θ', hΘ', rfl⟩
    have hEq : Θ' = Θ := Set.mem_singleton_iff.mp hΘ'
    simp [hEq]
  · intro hy
    refine ⟨Θ, Set.mem_singleton Θ, ?_⟩
    simpa using hy.symm

/-! ## “Unique Θ ⇒ point semantics” as a provable collapse -/

theorem thetaValues_eq_singleton_of_subsingleton {Θs : Set (α → β)}
    (hsub : Θs.Subsingleton) (hne : Θs.Nonempty) (x : α) :
    thetaValues Θs x = {(hne.choose) x} := by
  ext y
  constructor
  · rintro ⟨Θ, hΘ, rfl⟩
    have hΘeq : Θ = hne.choose := hsub hΘ hne.choose_spec
    simp [hΘeq]
  · intro hy
    have hΘ0 : hne.choose ∈ Θs := hne.choose_spec
    refine ⟨hne.choose, hΘ0, ?_⟩
    simpa using hy.symm

section CompleteLattice

variable [CompleteLattice β]

/-- Lower envelope induced by a set of candidate completions. -/
noncomputable def lower (Θs : Set (α → β)) (x : α) : β :=
  sInf (thetaValues Θs x)

/-- Upper envelope induced by a set of candidate completions. -/
noncomputable def upper (Θs : Set (α → β)) (x : α) : β :=
  sSup (thetaValues Θs x)

/-- Interval semantics induced by a family of completions. -/
noncomputable def intervalOfFamily (Θs : Set (α → β)) : IntervalSemantics α β :=
  ⟨lower Θs, upper Θs⟩

@[simp]
theorem lower_singleton (Θ : α → β) (x : α) :
    lower (Set.singleton Θ) x = Θ x := by
  simp [lower]

@[simp]
theorem upper_singleton (Θ : α → β) (x : α) :
    upper (Set.singleton Θ) x = Θ x := by
  simp [upper]

@[simp]
theorem intervalOfFamily_singleton (Θ : α → β) :
    intervalOfFamily (Set.singleton Θ) = ⟨Θ, Θ⟩ := by
  refine IntervalSemantics.ext (s := intervalOfFamily (Set.singleton Θ)) (t := ⟨Θ, Θ⟩) ?_ ?_
  · funext x
    simp [intervalOfFamily]
  · funext x
    simp [intervalOfFamily]

theorem lower_eq_upper_of_subsingleton {Θs : Set (α → β)}
    (hsub : Θs.Subsingleton) (hne : Θs.Nonempty) (x : α) :
    lower Θs x = upper Θs x := by
  have hvals : thetaValues Θs x = {(hne.choose) x} :=
    thetaValues_eq_singleton_of_subsingleton (Θs := Θs) hsub hne x
  simp [lower, upper, hvals]

theorem intervalOfFamily_eq_point_of_subsingleton {Θs : Set (α → β)}
    (hsub : Θs.Subsingleton) (hne : Θs.Nonempty) :
    intervalOfFamily Θs = ⟨hne.choose, hne.choose⟩ := by
  refine IntervalSemantics.ext (s := intervalOfFamily Θs) (t := ⟨hne.choose, hne.choose⟩) ?_ ?_
  · funext x
    have hvals : thetaValues Θs x = {(hne.choose) x} :=
      thetaValues_eq_singleton_of_subsingleton (Θs := Θs) hsub hne x
    simp [intervalOfFamily, lower, hvals]
  · funext x
    have hvals : thetaValues Θs x = {(hne.choose) x} :=
      thetaValues_eq_singleton_of_subsingleton (Θs := Θs) hsub hne x
    simp [intervalOfFamily, upper, hvals]

end CompleteLattice

end ThetaSemantics

end Mettapedia.ProbabilityTheory.Hypercube
