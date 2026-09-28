import Mettapedia.Languages.Agda.Structural.AdministrativeFunctionality
import Mettapedia.Languages.Agda.Structural.AdministrativePiFormation
import Mettapedia.Languages.Agda.Structural.AdministrativeSpineFactorization
import Mettapedia.Languages.Agda.Structural.StaticEndpointRegularity

/-!
# Endpoint regularity for the administrative rule family

Core typing and equality retain their formation and typing endpoints. An
action preserves formation when its input is formed. Spine equality, under
the same explicit input premise, yields both actual actions and formation of
the output. The bundled motive lets append pass the first original child's
output formation to the second child's induction hypothesis.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open Statics (RawTm RawTy RawContext)

structure SpineEndpoints {n : Nat} (Γ : RawContext n) (A : RawTy n)
    (es fs : Spine (scope n)) (B : RawTy n) where
  left : Action Γ A es B
  right : Action Γ A fs B
  outputFormed : CoreDerivation (Statics.formed Γ B)

def EndpointRegularity : Judgment → Type
  | .core j => Statics.EndpointRegularity CoreDerivation j
  | .spineAction Γ A _ B => CoreDerivation (Statics.formed Γ A) → CoreDerivation (Statics.formed Γ B)
  | .spineEquality Γ A es fs B => CoreDerivation (Statics.formed Γ A) → SpineEndpoints Γ A es fs B

noncomputable def endpointRule {j : Judgment} (shape : RuleShape j)
    (children : Evidence Derivation (premises shape))
    (ih : Evidence EndpointRegularity (premises shape)) : EndpointRegularity j := by
  let ops := administrativeOperations
  cases shape with
  | prior shape =>
      have children := priorPremiseEvidence children
      have ih := priorPremiseEvidence ih
      cases shape with
      | core shape =>
          exact Statics.endpointRule ops CoreDerivation.formationPiParts CoreDerivation.formationFunctionality
            shape (SpineStatics.corePremiseEvidence children) (SpineStatics.corePremiseEvidence ih)
      | nil Γ A => exact fun input => input
      | cons Γ A B u es C =>
          simp only [SpineStatics.premises] at children ih
          intro input
          let parts := input.formationPiParts
          exact ih 1 (ops.substituteEvidence parts.2 Γ (Statics.single u)
            (ops.singleSubstitution parts.1 (children 0)))
      | append Γ A es B fs C =>
          simp only [SpineStatics.premises] at children ih
          exact fun input => ih 1 (ih 0 input)
      | inputConversion Γ A' A es B =>
          simp only [SpineStatics.premises] at children ih
          exact fun _ => ih 1 (ih 0).right
      | outputConversion Γ A es B B' =>
          simp only [SpineStatics.premises] at ih
          exact fun _ => (ih 1).right
      | elimination Γ f A es B =>
          simp only [SpineStatics.premises] at ih
          exact ih 1 (ih 0)
  | spineRefl Γ A es B =>
      simp only [premises] at children ih
      exact fun input => ⟨children 0, children 0, ih 0 input⟩
  | spineSymm Γ A es fs B =>
      simp only [premises] at ih
      intro input
      let endpoints := ih 0 input
      exact ⟨endpoints.right, endpoints.left, endpoints.outputFormed⟩
  | spineTrans Γ A es fs gs B =>
      simp only [premises] at ih
      intro input
      let first := ih 0 input
      let second := ih 1 input
      exact ⟨first.left, second.right, first.outputFormed⟩
  | spineCons Γ A B u v es fs C =>
      simp only [premises] at children ih
      intro input
      let parts := input.formationPiParts
      let arguments := ih 0
      let changed := CoreDerivation.formationFunctionality parts.2
        (Statics.EqualSubstitution.single ops parts.1 arguments.left arguments.right (children 0))
      let inputFormed := ops.substituteEvidence parts.2 Γ (Statics.single u)
        (ops.singleSubstitution parts.1 arguments.left)
      let tails := ih 1 inputFormed
      exact ⟨Derivation.cons arguments.left tails.left,
        Derivation.cons arguments.right (Derivation.inputConversion (ops.typeSymmetry changed) tails.right),
        tails.outputFormed⟩
  | spineAppend Γ A es fs B gs hs C =>
      simp only [premises] at ih
      intro input
      let first := ih 0 input
      let second := ih 1 first.outputFormed
      exact ⟨Derivation.append first.left second.left, Derivation.append first.right second.right,
        second.outputFormed⟩
  | spineInputConversion Γ A' A es fs B =>
      simp only [premises] at children ih
      intro _
      let spines := ih 1 (ih 0).right
      exact ⟨Derivation.inputConversion (children 0) spines.left,
        Derivation.inputConversion (children 0) spines.right, spines.outputFormed⟩
  | spineOutputConversion Γ A es fs B B' =>
      simp only [premises] at children ih
      intro input
      let spines := ih 0 input
      exact ⟨Derivation.outputConversion spines.left (children 1),
        Derivation.outputConversion spines.right (children 1), (ih 1).right⟩
  | appendEmpty Γ A es B =>
      simp only [premises] at children ih
      exact fun input => ⟨children 0, Action.dropEmptyAppend (children 0), ih 0 input⟩
  | appendCons Γ A u es fs B =>
      simp only [premises] at children ih
      exact fun input => ⟨children 0, Action.distributeAppend (children 0), ih 0 input⟩
  | eliminationCongruence Γ f g A es fs B =>
      simp only [premises] at children ih
      let heads := ih 0
      let spines := ih 1 heads.formed
      exact ⟨Derivation.elimination heads.left spines.left, Derivation.elimination heads.right spines.right,
        spines.outputFormed⟩
  | emptyElimination Γ f A =>
      simp only [premises] at children ih
      exact ⟨Derivation.elimination (children 0) (Derivation.nil Γ A), children 0, ih 0⟩
  | nestedElimination Γ f A es B fs C =>
      simp only [premises] at children ih
      exact ⟨Derivation.elimination (Derivation.elimination (children 0) (children 1)) (children 2),
        Derivation.elimination (children 0) (Derivation.append (children 1) (children 2)), ih 2 (ih 1 (ih 0))⟩

noncomputable def Derivation.endpointRegularity {j : Judgment} (tree : Derivation j) : EndpointRegularity j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial
    (fun _ j _ => EndpointRegularity j)
    (fun _ _ shape children ih => endpointRule shape children ih) () j tree

noncomputable def CoreDerivation.typingFormation {n : Nat} {Γ : RawContext n} {t : RawTm n} {A : RawTy n}
    (tree : CoreDerivation (Statics.typed Γ t A)) : CoreDerivation (Statics.formed Γ A) := tree.endpointRegularity

noncomputable def CoreDerivation.typeEndpoints {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    (tree : CoreDerivation (Statics.typeEqual Γ A B)) : Statics.TypeEndpoints CoreDerivation Γ A B :=
  tree.endpointRegularity

noncomputable def CoreDerivation.termEndpoints {n : Nat} {Γ : RawContext n} {t u : RawTm n} {A : RawTy n}
    (tree : CoreDerivation (Statics.termEqual Γ t u A)) : Statics.TermEndpoints CoreDerivation Γ t u A :=
  tree.endpointRegularity

noncomputable def Action.outputFormation {n : Nat} {Γ : RawContext n} {A B : RawTy n} {es : Spine (scope n)}
    (tree : Action Γ A es B) (input : CoreDerivation (Statics.formed Γ A)) :
    CoreDerivation (Statics.formed Γ B) := tree.endpointRegularity input

noncomputable def SpineEq.endpoints {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    {es fs : Spine (scope n)} (tree : SpineEq Γ A es fs B)
    (input : CoreDerivation (Statics.formed Γ A)) : SpineEndpoints Γ A es fs B := tree.endpointRegularity input

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics
