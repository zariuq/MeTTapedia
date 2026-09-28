import Mettapedia.Languages.Agda.Structural.AdministrativeEndpointRegularity

/-!
# Native generation for elimination typing and conditional actions

Generation traverses the actual enlarged rule trees. Canonical application
and general elimination both expose a typed head and a spine action; outer
term conversions are retained as output conversions of that action.

An empty action yields an ordered chain of actual type-equality receipts or
an empty chain. The latter requires no formation premise. Applying a chain
to existing typing/equality evidence performs the native conversion rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open Statics (RawTm RawTy RawContext)

inductive ConversionChain {n : Nat} (Γ : RawContext n) : RawTy n → RawTy n → Type
  | refl (A : RawTy n) : ConversionChain Γ A A
  | step {A B C : RawTy n} (equal : CoreDerivation (Statics.typeEqual Γ A B))
      (tail : ConversionChain Γ B C) : ConversionChain Γ A C

namespace ConversionChain

def append {n : Nat} {Γ : RawContext n} {A B C : RawTy n}
    (first : ConversionChain Γ A B) (second : ConversionChain Γ B C) : ConversionChain Γ A C :=
  match first with
  | .refl _ => second
  | .step equal tail => .step equal (tail.append second)

noncomputable def typing {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    (chain : ConversionChain Γ A B) {t : RawTm n}
    (typed : CoreDerivation (Statics.typed Γ t A)) : CoreDerivation (Statics.typed Γ t B) :=
  match chain with
  | .refl _ => typed
  | .step equal tail => tail.typing (Derivation.core (.conversion Γ t A _)
      (consEvidence CoreDerivation typed (consEvidence CoreDerivation equal (noEvidence CoreDerivation))))

noncomputable def termEquality {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    (chain : ConversionChain Γ A B) {t u : RawTm n}
    (equal : CoreDerivation (Statics.termEqual Γ t u A)) : CoreDerivation (Statics.termEqual Γ t u B) :=
  match chain with
  | .refl _ => equal
  | .step types tail => tail.termEquality (Derivation.core (.equalityConversion Γ t u A _)
      (consEvidence CoreDerivation equal (consEvidence CoreDerivation types (noEvidence CoreDerivation))))

end ConversionChain

structure EliminationTyping {n : Nat} (Γ : RawContext n) (head : RawTm n)
    (spine : Spine (scope n)) (output : RawTy n) where
  input : RawTy n
  headTyping : CoreDerivation (Statics.typed Γ head input)
  action : Action Γ input spine output

structure ActionTypingView {n : Nat} (Γ : RawContext n) (A : RawTy n)
    (es : Spine (scope n)) (B : RawTy n) where
  nil : es = Structural.nil → ConversionChain Γ A B
  head : ∀ e rest, es = Structural.cons e rest → { u : RawTm n // e = apply u }

def TypingGeneration : Judgment → Type
  | .core (.term ⟨_, Γ⟩ A t) => ∀ head spine, t.code = eliminate head spine → EliminationTyping Γ head spine A
  | .spineAction Γ A es B => ActionTypingView Γ A es B
  | _ => PUnit

theorem eliminate_injective {n : Nat} {f g : RawTm n} {es fs : Spine (scope n)}
    (same : eliminate f es = eliminate g fs) : f = g ∧ es = fs := by
  cases same
  exact ⟨rfl, rfl⟩

def coreTypingGenerationRule {j : Statics.Judgment} (shape : Statics.RuleShape j)
    (children : Evidence CoreDerivation (Statics.premises shape))
    (ih : Evidence (fun j => TypingGeneration (.core j)) (Statics.premises shape)) : TypingGeneration (.core j) := by
  cases shape <;> simp only [Statics.premises] at children ih
  case empty | extend | formation | typeEquality | reflexivity | symmetry | transitivity
    | equalityConversion | piCongruence | applicationCongruence | beta | eta => exact ⟨⟩
  case sort | «variable» => intro head spine same; cases same
  case pi Γ A B => intro head spine same; cases B <;> cases same
  case lambda Γ A B body => intro head spine same; cases body <;> cases same
  case application Γ A B f u =>
    intro head spine same
    obtain ⟨rfl, rfl⟩ := eliminate_injective same
    exact ⟨(Statics.piType A B).code, children 0,
      Derivation.cons (children 1) (Derivation.nil Γ (B.instantiate u).code)⟩
  case conversion Γ t A B =>
    intro head spine same
    let parts := ih 0 head spine same
    exact ⟨parts.input, parts.headTyping, Derivation.outputConversion parts.action (children 1)⟩

def typingGenerationRule {j : Judgment} (shape : RuleShape j)
    (children : Evidence Derivation (premises shape))
    (ih : Evidence TypingGeneration (premises shape)) : TypingGeneration j := by
  cases shape with
  | prior shape =>
      have children := priorPremiseEvidence children
      have ih := priorPremiseEvidence ih
      cases shape with
      | core shape =>
          exact coreTypingGenerationRule shape (SpineStatics.corePremiseEvidence children)
            (SpineStatics.corePremiseEvidence ih)
      | nil Γ A =>
          exact ⟨fun _ => .refl A, fun _ _ same => by cases same⟩
      | cons Γ A B u es C =>
          exact ⟨(fun same => by cases same), fun e rest same => by cases same; exact ⟨u, rfl⟩⟩
      | append => exact ⟨(fun same => by cases same), fun _ _ same => by cases same⟩
      | inputConversion Γ A' A es B =>
          simp only [SpineStatics.premises] at children ih
          exact ⟨fun same => .step (children 0) ((ih 1).nil same), (ih 1).head⟩
      | outputConversion Γ A es B B' =>
          simp only [SpineStatics.premises] at children ih
          exact ⟨fun same => ((ih 0).nil same).append (.step (children 1) (.refl B')), (ih 0).head⟩
      | elimination Γ f A es B =>
          simp only [SpineStatics.premises] at children ih
          intro head spine same
          obtain ⟨rfl, rfl⟩ := eliminate_injective same
          exact ⟨A, children 0, children 1⟩
  | spineRefl | spineSymm | spineTrans | spineCons | spineAppend | spineInputConversion
    | spineOutputConversion | appendEmpty | appendCons | eliminationCongruence
    | emptyElimination | nestedElimination => exact ⟨⟩

noncomputable def Derivation.typingGeneration {j : Judgment} (tree : Derivation j) : TypingGeneration j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial (fun _ j _ => TypingGeneration j)
    (fun _ _ shape children ih => typingGenerationRule shape children ih) () j tree

noncomputable def CoreDerivation.eliminationParts {n : Nat} {Γ : RawContext n}
    {head : RawTm n} {spine : Spine (scope n)} {A : RawTy n}
    (tree : CoreDerivation (Statics.typed Γ (eliminate head spine) A)) : EliminationTyping Γ head spine A :=
  tree.typingGeneration head spine rfl

noncomputable def Action.nilConversion {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    (tree : Action Γ A Structural.nil B) : ConversionChain Γ A B := tree.typingGeneration.nil rfl

noncomputable def Action.appliedHead {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    {e : Elim (scope n)} {rest : Spine (scope n)} (tree : Action Γ A (Structural.cons e rest) B) :
    { u : RawTm n // e = apply u } := tree.typingGeneration.head e rest rfl

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics
