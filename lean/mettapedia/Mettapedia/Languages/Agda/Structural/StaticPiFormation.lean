import Mettapedia.Languages.Agda.Structural.StaticTypeViews

/-!
# Formation components of a syntactic Pi

These views invert typing of a term whose raw syntax is a Pi. They retain its
actual domain and codomain formation trees through surrounding conversions.
This is syntactic generation; it is not injectivity of Pi modulo conversion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Statics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory

theorem TypeBody.pi_parameters {n : Nat} {A A' : TypeParameter n} {B B' : TypeBody n}
    (same : B.pi A = B'.pi A') : A = A' ∧ B = B' := by
  cases A with
  | mk level term =>
    cases A' with
    | mk level' term' =>
      cases B with
      | bind body =>
        cases body
        cases B' with
        | bind other => cases other; cases same; exact ⟨rfl, rfl⟩
        | noBind other => cases same
      | noBind body =>
        cases body
        cases B' with
        | bind other => cases same
        | noBind other => cases other; cases same; exact ⟨rfl, rfl⟩

def PiFormation (D : Judgment → Type) : Judgment → Type
  | .type ⟨n, Γ⟩ T => ∀ (A : TypeParameter n) (B : TypeBody n), T = (piType A B).code →
      D (formed Γ A.code) × D (formed (Γ.snoc A.code) B.open.code)
  | .term ⟨n, Γ⟩ _ t => ∀ (A : TypeParameter n) (B : TypeBody n), t.code = B.pi A →
      D (formed Γ A.code) × D (formed (Γ.snoc A.code) B.open.code)
  | _ => PUnit

def piFormationRule {D : Judgment → Type} {j : Judgment} (shape : RuleShape j)
    (children : Evidence D (premises shape))
    (ih : Evidence (PiFormation D) (premises shape)) : PiFormation D j := by
  cases shape <;> simp only [premises] at children ih
  case empty | extend | typeEquality | reflexivity | symmetry | transitivity | equalityConversion
    | piCongruence | applicationCongruence | beta | eta => exact ⟨⟩
  case formation Γ k a =>
    intro A B same
    have parameters := TypeParameter.code_injective same
    exact ih 0 A B (congrArg TypeParameter.term parameters)
  case sort =>
    intro A B same
    cases B <;> cases same
  case «variable» =>
    intro A B same
    cases B <;> cases same
  case pi Γ A B =>
    intro A' B' same
    obtain ⟨rfl, rfl⟩ := TypeBody.pi_parameters same
    exact ⟨children 0, children 1⟩
  case lambda Γ A B body =>
    intro A' B' same
    cases body <;> cases B' <;> cases same
  case application =>
    intro A B same
    cases B <;> cases same
  case conversion => exact ih 0

noncomputable def Derivation.piFormation {j : Judgment} (tree : Derivation j) : PiFormation Derivation j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial
    (fun _ j _ => PiFormation Derivation j)
    (fun _ _ shape children ih => piFormationRule shape children ih) () j tree

noncomputable def Derivation.formationPiParts {n : Nat} {Γ : RawContext n}
    {A : TypeParameter n} {B : TypeBody n} (tree : Derivation (formed Γ (piType A B).code)) :
    Derivation (formed Γ A.code) × Derivation (formed (Γ.snoc A.code) B.open.code) :=
  tree.piFormation A B rfl

end Mettapedia.Languages.Agda.Structural.Statics
