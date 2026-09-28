import Mettapedia.Languages.Agda.Structural.AdministrativeConstructorGeneration

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.BetaPreparation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open Statics (RawTm RawTy RawContext TypeParameter TypeBody)

noncomputable def chainEquality {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    (chain : ConversionChain Γ A B) (formed : CoreDerivation (Statics.formed Γ A)) :
    CoreDerivation (Statics.typeEqual Γ A B) :=
  match chain with
  | .refl _ => formed.typeReflexivity
  | .step equal tail => equal.typeTransitivity (chainEquality tail equal.typeEndpoints.right)

structure ConsTyping {n : Nat} (Γ : RawContext n) (input : RawTy n) (argument : RawTm n)
    (rest : Spine (scope n)) (output : RawTy n) where
  domain : TypeParameter n
  codomain : TypeBody n
  conversions : ConversionChain Γ input (Statics.piType domain codomain).code
  argumentTyped : CoreDerivation (Statics.typed Γ argument domain.code)
  tail : Action Γ (codomain.instantiate argument).code rest output

def ConsGeneration : Judgment → Type
  | .spineAction Γ A es C => ∀ argument rest, es = cons (apply argument) rest → ConsTyping Γ A argument rest C
  | _ => PUnit

def rule {j : Judgment} (shape : RuleShape j)
    (children : Evidence Derivation (premises shape)) (ih : Evidence ConsGeneration (premises shape)) :
    ConsGeneration j := by
  cases shape with
  | prior shape =>
      have children := priorPremiseEvidence children
      have ih := priorPremiseEvidence ih
      cases shape with
      | core | elimination => exact ⟨⟩
      | nil | append => intro argument rest same; cases same
      | cons Γ A B u es C =>
          simp only [SpineStatics.premises] at children
          intro argument rest same
          obtain ⟨rfl, rfl⟩ := cons_apply_injective same
          exact ⟨A, B, .refl _, children 0, children 1⟩
      | inputConversion Γ A' A es B =>
          simp only [SpineStatics.premises] at children ih
          intro argument rest same
          let parts := ih 1 argument rest same
          exact { parts with conversions := .step (children 0) parts.conversions }
      | outputConversion Γ A es B B' =>
          simp only [SpineStatics.premises] at children ih
          intro argument rest same
          let parts := ih 0 argument rest same
          exact { parts with tail := Derivation.outputConversion parts.tail (children 1) }
  | spineRefl | spineSymm | spineTrans | spineCons | spineAppend | spineInputConversion
    | spineOutputConversion | appendEmpty | appendCons | eliminationCongruence
    | emptyElimination | nestedElimination => exact ⟨⟩

noncomputable def consParts {n : Nat} {Γ : RawContext n} {A C : RawTy n} {u : RawTm n}
    {rest : Spine (scope n)} (tree : Action Γ A (cons (apply u) rest) C) : ConsTyping Γ A u rest C :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial (fun _ j _ => ConsGeneration j)
    (fun _ _ shape children ih => rule shape children ih) () _ tree u rest rfl

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.BetaPreparation
