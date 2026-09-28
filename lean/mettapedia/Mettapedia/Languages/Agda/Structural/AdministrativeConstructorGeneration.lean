import Mettapedia.Languages.Agda.Structural.AdministrativeTypingGeneration

/-!
# Native origins of lambda, Pi, and universe typing

The views fold arbitrary administrative static trees. Lambda and Pi origins
retain their original formation/body premises and all outer type conversions.
Raw constructor views recover finite Pi parameters and universe boundaries.
They do not identify Pi components modulo conversion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open Statics (RawTm RawTy RawContext TermBody TypeParameter TypeBody)

structure LambdaTyping {n : Nat} (Γ : RawContext n) (body : TermBody n) (output : RawTy n) where
  domain : TypeParameter n
  codomain : TypeBody n
  domainFormed : CoreDerivation (Statics.formed Γ domain.code)
  codomainFormed : CoreDerivation (Statics.formed (Γ.snoc domain.code) codomain.open.code)
  bodyTyped : CoreDerivation (Statics.typed (Γ.snoc domain.code) body.open codomain.open.code)
  conversions : ConversionChain Γ (Statics.piType domain codomain).code output

theorem lambda_injective {n : Nat} {first second : TermBody n}
    (same : first.lambda = second.lambda) : first = second := by
  cases first <;> cases second <;> cases same <;> rfl

def LambdaGeneration : Judgment → Type
  | .core (.term ⟨_, Γ⟩ A t) => ∀ body, t.code = body.lambda → LambdaTyping Γ body A
  | _ => PUnit

def coreLambdaRule {j : Statics.Judgment} (shape : Statics.RuleShape j)
    (children : Evidence CoreDerivation (Statics.premises shape))
    (ih : Evidence (fun j => LambdaGeneration (.core j)) (Statics.premises shape)) :
    LambdaGeneration (.core j) := by
  cases shape <;> simp only [Statics.premises] at children ih
  case empty | extend | formation | typeEquality | reflexivity | symmetry | transitivity
    | equalityConversion | piCongruence | applicationCongruence | beta | eta => exact ⟨⟩
  case sort | «variable» | application => intro body same; cases body <;> cases same
  case pi Γ A B => intro body same; cases B <;> cases body <;> cases same
  case lambda Γ A B original =>
    intro body same
    have boundary := lambda_injective same
    cases boundary
    exact ⟨A, B, children 0, children 1, children 2, .refl _⟩
  case conversion Γ t A B =>
    intro body same
    let parts := ih 0 body same
    exact { parts with conversions := parts.conversions.append (.step (children 1) (.refl B)) }

def lambdaRule {j : Judgment} (shape : RuleShape j)
    (children : Evidence Derivation (premises shape))
    (ih : Evidence LambdaGeneration (premises shape)) : LambdaGeneration j := by
  cases shape with
  | prior shape =>
      have children := priorPremiseEvidence children
      have ih := priorPremiseEvidence ih
      cases shape with
      | core shape =>
          exact coreLambdaRule shape (SpineStatics.corePremiseEvidence children)
            (SpineStatics.corePremiseEvidence ih)
      | nil | cons | append | inputConversion | outputConversion => exact ⟨⟩
      | elimination => intro body same; cases body <;> cases same
  | spineRefl | spineSymm | spineTrans | spineCons | spineAppend | spineInputConversion
    | spineOutputConversion | appendEmpty | appendCons | eliminationCongruence
    | emptyElimination | nestedElimination => exact ⟨⟩

noncomputable def CoreDerivation.lambdaParts {n : Nat} {Γ : RawContext n} {body : TermBody n} {A : RawTy n}
    (tree : CoreDerivation (Statics.typed Γ body.lambda A)) : LambdaTyping Γ body A :=
  (IndexedPolynomial.Fix.eliminate presentation.polynomial (fun _ j _ => LambdaGeneration j)
    (fun _ _ shape children ih => lambdaRule shape children ih) () _ tree) body rfl

structure PiTyping {n : Nat} (Γ : RawContext n) (A : TypeParameter n) (B : TypeBody n)
    (output : RawTy n) where
  domainFormed : CoreDerivation (Statics.formed Γ A.code)
  codomainFormed : CoreDerivation (Statics.formed (Γ.snoc A.code) B.open.code)
  conversions : ConversionChain Γ (Statics.universeType n (max A.level B.level)).code output

def PiGeneration : Judgment → Type
  | .core (.term ⟨_, Γ⟩ output t) => ∀ A B, t.code = B.pi A → PiTyping Γ A B output
  | _ => PUnit

def corePiRule {j : Statics.Judgment} (shape : Statics.RuleShape j)
    (children : Evidence CoreDerivation (Statics.premises shape))
    (ih : Evidence (fun j => PiGeneration (.core j)) (Statics.premises shape)) : PiGeneration (.core j) := by
  cases shape <;> simp only [Statics.premises] at children ih
  case empty | extend | formation | typeEquality | reflexivity | symmetry | transitivity
    | equalityConversion | piCongruence | applicationCongruence | beta | eta => exact ⟨⟩
  case sort | «variable» | application => intro A B same; cases B <;> cases same
  case lambda Γ A B body => intro A' B' same; cases body <;> cases B' <;> cases same
  case pi Γ A B =>
    intro A' B' same
    obtain ⟨rfl, rfl⟩ := Statics.TypeBody.pi_parameters same
    exact ⟨children 0, children 1, .refl _⟩
  case conversion Γ t A B =>
    intro domain codomain same
    let parts := ih 0 domain codomain same
    exact { parts with conversions := parts.conversions.append (.step (children 1) (.refl B)) }

def piRule {j : Judgment} (shape : RuleShape j)
    (children : Evidence Derivation (premises shape))
    (ih : Evidence PiGeneration (premises shape)) : PiGeneration j := by
  cases shape with
  | prior shape =>
      have children := priorPremiseEvidence children
      have ih := priorPremiseEvidence ih
      cases shape with
      | core shape =>
          exact corePiRule shape (SpineStatics.corePremiseEvidence children)
            (SpineStatics.corePremiseEvidence ih)
      | nil | cons | append | inputConversion | outputConversion => exact ⟨⟩
      | elimination => intro A B same; cases B <;> cases same
  | spineRefl | spineSymm | spineTrans | spineCons | spineAppend | spineInputConversion
    | spineOutputConversion | appendEmpty | appendCons | eliminationCongruence
    | emptyElimination | nestedElimination => exact ⟨⟩

noncomputable def CoreDerivation.piTypingParts {n : Nat} {Γ : RawContext n} {A : TypeParameter n} {B : TypeBody n} {T : RawTy n}
    (tree : CoreDerivation (Statics.typed Γ (B.pi A) T)) : PiTyping Γ A B T :=
  (IndexedPolynomial.Fix.eliminate presentation.polynomial (fun _ j _ => PiGeneration j)
    (fun _ _ shape children ih => piRule shape children ih) () _ tree) A B rfl

structure PiBindParameters {n : Nat} (domain : RawTy n) (codomain : RawTy (n + 1)) where
  first : TypeParameter n
  second : TypeParameter (n + 1)
  domainBoundary : domain = first.code
  codomainBoundary : codomain = second.code

structure PiNoBindParameters {n : Nat} (domain codomain : RawTy n) where
  first : TypeParameter n
  second : TypeParameter n
  domainBoundary : domain = first.code
  codomainBoundary : codomain = second.code

structure RawConstructorView {n : Nat} (term : RawTm n) where
  piBind : ∀ domain codomain, term = pi domain codomain → PiBindParameters domain codomain
  piNoBind : ∀ domain codomain, term = piNoAbs domain codomain → PiNoBindParameters domain codomain
  sort : ∀ s, term = sortTerm s → {k : Nat // s = set (levelClosed k)}
  level : ∀ l, term = levelTerm l → False

def ConstructorView : Judgment → Type
  | .core (.term _ _ t) => RawConstructorView t.code
  | _ => PUnit

def coreConstructorRule {j : Statics.Judgment} (shape : Statics.RuleShape j)
    (ih : Evidence (fun j => ConstructorView (.core j)) (Statics.premises shape)) : ConstructorView (.core j) := by
  cases shape <;> simp only [Statics.premises] at ih
  case empty | extend | formation | typeEquality | reflexivity | symmetry | transitivity
    | equalityConversion | piCongruence | applicationCongruence | beta | eta => exact ⟨⟩
  case «variable» | application =>
    exact ⟨(fun _ _ same => by cases same), (fun _ _ same => by cases same),
      (fun _ same => by cases same), fun _ same => by cases same⟩
  case lambda Γ A B body =>
    cases body <;> exact ⟨(fun _ _ same => by cases same), (fun _ _ same => by cases same),
      (fun _ same => by cases same), fun _ same => by cases same⟩
  case sort Γ k =>
    refine ⟨(fun _ _ same => by cases same), (fun _ _ same => by cases same), ?_, fun _ same => by cases same⟩
    intro s same
    cases same
    exact ⟨k, rfl⟩
  case pi Γ A B =>
    cases B with
    | bind body =>
        refine ⟨?_, (fun _ _ same => by cases same), (fun _ same => by cases same), fun _ same => by cases same⟩
        intro domain codomain same
        cases same
        exact ⟨A, body, rfl, rfl⟩
    | noBind body =>
        refine ⟨(fun _ _ same => by cases same), ?_, (fun _ same => by cases same), fun _ same => by cases same⟩
        intro domain codomain same
        cases same
        exact ⟨A, body, rfl, rfl⟩
  case conversion => exact ih 0

def constructorRule {j : Judgment} (shape : RuleShape j)
    (ih : Evidence ConstructorView (premises shape)) : ConstructorView j := by
  cases shape with
  | prior shape =>
      have ih := priorPremiseEvidence ih
      cases shape with
      | core shape => exact coreConstructorRule shape (SpineStatics.corePremiseEvidence ih)
      | nil | cons | append | inputConversion | outputConversion => exact ⟨⟩
      | elimination => exact ⟨(fun _ _ same => by cases same), (fun _ _ same => by cases same),
          (fun _ same => by cases same), fun _ same => by cases same⟩
  | spineRefl | spineSymm | spineTrans | spineCons | spineAppend | spineInputConversion
    | spineOutputConversion | appendEmpty | appendCons | eliminationCongruence
    | emptyElimination | nestedElimination => exact ⟨⟩

noncomputable def CoreDerivation.constructorView {n : Nat} {Γ : RawContext n} {term : RawTm n} {A : RawTy n}
    (tree : CoreDerivation (Statics.typed Γ term A)) : RawConstructorView term :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial (fun _ j _ => ConstructorView j)
    (fun _ _ shape _children ih => constructorRule shape ih) () _ tree

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics
