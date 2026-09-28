import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalTreeSubstitution
import Mathlib.Combinatorics.Quiver.Path

/-!
# Finite paths of rule-local derivations

One edge is a complete firing tree at its exact endpoints. Mathlib's free
path construction retains the ordered sequence of these edges. Substitution
acts on every tree, using its existing binder-aware action.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial

open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra

universe u
variable {S : Signature} (R : List (LocalRule S))

/-- The contextual event graph retains each derivation at its endpoints. -/
abbrev derivationQuiver (A : BindingCloneAlgebra.Algebra.{u} S)
    (Γ : Ctx S) (sort : S.Srt) : Quiver (A.substitution.Carrier Γ sort) where
  Hom source target := Tree R A ⟨Γ, sort, source, target⟩

/-- Finite, ordered computations through the presented rule family. -/
abbrev DerivationPath (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ : Ctx S} {sort : S.Srt}
    (source target : A.substitution.Carrier Γ sort) :=
  @Quiver.Path _ (derivationQuiver R A Γ sort) source target

section
variable (A : BindingCloneAlgebra.Algebra.{u} S)

/-- Number of one-step derivations in a finite computation. -/
def pathLength {Γ : Ctx S} {sort : S.Srt}
    {source target : A.substitution.Carrier Γ sort}
    (path : DerivationPath R A source target) : Nat :=
  @Quiver.Path.length _ (derivationQuiver R A Γ sort) _ _ path

/-- Concatenation keeps the authored order of all individual edges. -/
def concatenate {Γ : Ctx S} {sort : S.Srt}
    {first middle last : A.substitution.Carrier Γ sort}
    (left : DerivationPath R A first middle) (right : DerivationPath R A middle last) :
    DerivationPath R A first last :=
  @Quiver.Path.comp _ (derivationQuiver R A Γ sort) _ _ _ left right

/-- A substitution maps each edge through the established tree action. -/
noncomputable def substitutionPrefunctor
    {Γ Δ : Ctx S} (σ : Environment S A.substitution.Carrier Γ Δ)
    (sort : S.Srt) :
    @Prefunctor _ (derivationQuiver R A Γ sort)
      _ (derivationQuiver R A Δ sort) := by
  letI := derivationQuiver R A Γ sort
  letI := derivationQuiver R A Δ sort
  exact {
    obj := fun term => A.substitution.substitute σ term
    map := fun {source target} tree =>
      substTree R A ⟨Γ, sort, source, target⟩ tree σ
        ⟨Δ, sort, A.substitution.substitute σ source,
          A.substitution.substitute σ target⟩ rfl }

/-- Each authored edge is substituted; its place in the history is unchanged. -/
noncomputable def substitutePath
    {Γ Δ : Ctx S} (σ : Environment S A.substitution.Carrier Γ Δ)
    {sort : S.Srt} {source target : A.substitution.Carrier Γ sort}
    (path : DerivationPath R A source target) :
    DerivationPath R A (A.substitution.substitute σ source)
      (A.substitution.substitute σ target) := by
  letI := derivationQuiver R A Γ sort
  letI := derivationQuiver R A Δ sort
  exact (substitutionPrefunctor R A σ sort).mapPath path

theorem substitutePath_length
    {Γ Δ : Ctx S} (σ : Environment S A.substitution.Carrier Γ Δ)
    {sort : S.Srt} {source target : A.substitution.Carrier Γ sort}
    (path : DerivationPath R A source target) :
    pathLength R A (substitutePath R A σ path) = pathLength R A path := by
  let _ := derivationQuiver R A Γ sort
  let _ := derivationQuiver R A Δ sort
  induction path with
  | nil => rfl
  | cons path edge ih =>
      change pathLength R A (substitutePath R A σ path) + 1 = pathLength R A path + 1
      exact congrArg (· + 1) ih

theorem substitutePath_comp
    {Γ Δ : Ctx S} (σ : Environment S A.substitution.Carrier Γ Δ)
    {sort : S.Srt} {first middle last : A.substitution.Carrier Γ sort}
    (left : DerivationPath R A first middle) (right : DerivationPath R A middle last) :
    substitutePath R A σ (concatenate R A left right) =
      concatenate R A (substitutePath R A σ left) (substitutePath R A σ right) := by
  let _ := derivationQuiver R A Γ sort
  let _ := derivationQuiver R A Δ sort
  exact Prefunctor.mapPath_comp (substitutionPrefunctor R A σ sort) left right

end

#print axioms substitutePath
#print axioms substitutePath_length
#print axioms substitutePath_comp

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
