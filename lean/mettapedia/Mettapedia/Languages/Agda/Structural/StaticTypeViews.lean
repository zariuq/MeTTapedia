import Mettapedia.Languages.Agda.Structural.StaticConstructors

/-!
# Recovering finite type annotations from actual rule trees

Formation and type equality expose the finite Set annotation and their actual
term-typing or term-equality child. These are Type-valued views: no witness is
selected from an existential proposition. In particular, type equality cannot
identify different closed level annotations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Statics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory

theorem TypeParameter.code_injective {n : Nat} :
    Function.Injective (TypeParameter.code (n := n)) := by
  intro first second same
  cases first with
  | mk level term =>
    cases second with
    | mk otherLevel otherTerm =>
      cases same
      rfl

structure FormationView (D : Judgment → Type) {n : Nat} (Γ : RawContext n) (A : RawTy n) where
  parameter : TypeParameter n
  boundary : A = parameter.code
  typing : D (typed Γ parameter.term (universeType n parameter.level).code)

structure TypeEqualityView (D : Judgment → Type) {n : Nat} (Γ : RawContext n) (A B : RawTy n) where
  level : Nat
  first : RawTm n
  second : RawTm n
  leftBoundary : A = (TypeParameter.mk level first).code
  rightBoundary : B = (TypeParameter.mk level second).code
  terms : D (termEqual Γ first second (universeType n level).code)

def TypeViews (D : Judgment → Type) : Judgment → Type
  | .type ⟨_, Γ⟩ A => FormationView D Γ A
  | .typeEquality ⟨_, Γ⟩ A B => TypeEqualityView D Γ A B
  | _ => PUnit

def typeViewRule {D : Judgment → Type} {j : Judgment} (shape : RuleShape j)
    (children : Evidence D (premises shape)) : TypeViews D j := by
  cases shape with
  | formation Γ k a =>
      simp only [premises] at children
      exact ⟨⟨k, a⟩, rfl, children 0⟩
  | typeEquality Γ k a b =>
      simp only [premises] at children
      exact ⟨k, a, b, rfl, rfl, children 0⟩
  | empty | extend | sort | «variable» | pi | lambda | application | conversion
    | reflexivity | symmetry | transitivity | equalityConversion | piCongruence
    | applicationCongruence | beta | eta => exact ⟨⟩

noncomputable def Derivation.typeViews {j : Judgment} (tree : Derivation j) : TypeViews Derivation j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial
    (fun _ j _ => TypeViews Derivation j)
    (fun _ _ shape children _ih => typeViewRule shape children) () j tree

noncomputable def Derivation.formationView {n : Nat} {Γ : RawContext n} {A : RawTy n}
    (tree : Derivation (formed Γ A)) : FormationView Derivation Γ A := tree.typeViews

noncomputable def Derivation.typeEqualityView {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    (tree : Derivation (typeEqual Γ A B)) : TypeEqualityView Derivation Γ A B := tree.typeViews

theorem TypeEqualityView.levels_equal {D : Judgment → Type} {n : Nat} {Γ : RawContext n}
    {A B : TypeParameter n} (view : TypeEqualityView D Γ A.code B.code) : A.level = B.level := by
  have first := TypeParameter.code_injective view.leftBoundary
  have second := TypeParameter.code_injective view.rightBoundary
  exact (congrArg TypeParameter.level first).trans (congrArg TypeParameter.level second).symm

theorem Derivation.typeEquality_levels {n : Nat} {Γ : RawContext n} {A B : TypeParameter n}
    (tree : Derivation (typeEqual Γ A.code B.code)) : A.level = B.level := tree.typeEqualityView.levels_equal

def FormationView.parameterTyping {D : Judgment → Type} {n : Nat} {Γ : RawContext n}
    {A : TypeParameter n} (view : FormationView D Γ A.code) :
    D (typed Γ A.term (universeType n A.level).code) := by
  have same := TypeParameter.code_injective view.boundary
  exact same ▸ view.typing

def TypeEqualityView.parameterTerms {D : Judgment → Type} {n : Nat} {Γ : RawContext n}
    {A B : TypeParameter n} (view : TypeEqualityView D Γ A.code B.code) :
    D (termEqual Γ A.term B.term (universeType n A.level).code) := by
  have first := TypeParameter.code_injective view.leftBoundary
  have second := TypeParameter.code_injective view.rightBoundary
  have boundary := congrArg₂ (fun (A B : TypeParameter n) =>
    D (termEqual Γ A.term B.term (universeType n A.level).code)) first second
  exact boundary.mpr view.terms

end Mettapedia.Languages.Agda.Structural.Statics
