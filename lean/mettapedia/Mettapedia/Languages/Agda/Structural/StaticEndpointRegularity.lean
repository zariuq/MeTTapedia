import Mettapedia.Languages.Agda.Structural.StaticFunctionality
import Mettapedia.Languages.Agda.Structural.StaticPiFormation

/-!
# Endpoint regularity for the canonical structural presentation

Every typing tree yields formation of its type. Type equality yields formation
of both endpoints; term equality yields both typing trees at its displayed
type. Dependent application uses the proved substitution functionality to
transport the right result type. Pi congruence changes the right codomain's
context using the derived identity substitution with conversion.

The algebra states its reusable dependencies explicitly. Its canonical
instance supplies all of them by the earlier rule-tree folds. No endpoint
theorem or preservation result is assumed in that instance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Statics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory

structure TypeEndpoints (D : Judgment → Type) {n : Nat} (Γ : RawContext n) (A B : RawTy n) where
  left : D (formed Γ A)
  right : D (formed Γ B)

structure TermEndpoints (D : Judgment → Type) {n : Nat} (Γ : RawContext n)
    (t u : RawTm n) (A : RawTy n) where
  left : D (typed Γ t A)
  right : D (typed Γ u A)
  formed : D (Statics.formed Γ A)

def EndpointRegularity (D : Judgment → Type) : Judgment → Type
  | .term ⟨_, Γ⟩ A _ => D (formed Γ A)
  | .typeEquality ⟨_, Γ⟩ A B => TypeEndpoints D Γ A B
  | .termEquality ⟨_, Γ⟩ A t u => TermEndpoints D Γ t.code u.code A
  | _ => PUnit

theorem TypeBody.open_level {n : Nat} (B : TypeBody n) : B.open.level = B.level := by
  cases B <;> rfl

def endpointRule {D : Judgment → Type} (ops : EvidenceOperations D)
    (piParts : ∀ {n : Nat} {Γ : RawContext n} {A : TypeParameter n} {B : TypeBody n},
      D (formed Γ (piType A B).code) → D (formed Γ A.code) × D (formed (Γ.snoc A.code) B.open.code))
    (formationCongruence : ∀ {n m : Nat} {Γ : RawContext n} {Δ : RawContext m} {A : RawTy n}
      {σ τ : RawSub n m}, D (formed Γ A) → EqualSubstitution D Γ Δ σ τ →
        D (typeEqual Δ (bind σ A) (bind τ A)))
    {j : Judgment} (shape : RuleShape j) (children : Evidence D (premises shape))
    (ih : Evidence (EndpointRegularity D) (premises shape)) : EndpointRegularity D j := by
  let child := @consEvidence _ D
  let stop := noEvidence D
  cases shape <;> simp only [premises] at children ih
  case empty | extend | formation => exact ⟨⟩
  case sort Γ k => exact ops.universeFormed (children 0) (k + 1)
  case «variable» Γ v => exact (ops.contexts (children 0)).lookup v
  case pi Γ A B => exact ops.universeFormed (ops.contexts (children 0)) (max A.level B.level)
  case lambda => exact ops.piFormed (children 0) (children 1)
  case application Γ A B f a =>
    have parts := piParts (ih 0)
    exact ops.substituteEvidence parts.2 Γ (single a) (ops.singleSubstitution parts.1 (children 1))
  case conversion => exact (ih 1).right
  case typeEquality Γ k a b =>
    exact ⟨ops.build (.formation Γ k a) (child (ih 0).left stop),
      ops.build (.formation Γ k b) (child (ih 0).right stop)⟩
  case reflexivity => exact ⟨children 0, children 0, ih 0⟩
  case symmetry => exact ⟨(ih 0).right, (ih 0).left, (ih 0).formed⟩
  case transitivity => exact ⟨(ih 0).left, (ih 1).right, (ih 0).formed⟩
  case equalityConversion Γ t u A B =>
    exact ⟨ops.build (.conversion Γ t A B) (child (ih 0).left (child (children 1) stop)),
      ops.build (.conversion Γ u A B) (child (ih 0).right (child (children 1) stop)), (ih 1).right⟩
  case piCongruence Γ A A' B B' =>
    have rightCodomain := ops.changeLastFormation (children 0) (ih 1).right (children 1) (ih 2).right
    have domainLevels : A.level = A'.level := (ops.typeViews (children 1)).levels_equal
    have codomainLevels : B.level = B'.level := by
      simpa only [TypeBody.open_level] using (ops.typeViews (children 2)).levels_equal
    refine ⟨ops.build (.pi Γ A B) (child (children 0) (child (ih 2).left stop)), ?_,
      ops.universeFormed (ops.contexts (children 0)) (max A.level B.level)⟩
    simpa only [← domainLevels, ← codomainLevels] using
      ops.build (.pi Γ A' B') (child (ih 1).right (child rightCodomain stop))
  case applicationCongruence Γ A B f g a b =>
    have functions := ih 0
    have arguments := ih 1
    have parts := piParts functions.formed
    have results := formationCongruence parts.2
      (EqualSubstitution.single ops parts.1 arguments.left arguments.right (children 1))
    have right := ops.build (.application Γ A B g b) (child functions.right (child arguments.right stop))
    exact ⟨ops.build (.application Γ A B f a) (child functions.left (child arguments.left stop)),
      ops.build (.conversion Γ (app g b) (B.instantiate b).code (B.instantiate a).code)
        (child right (child (ops.typeSymmetry results) stop)),
      ops.substituteEvidence parts.2 Γ (single a) (ops.singleSubstitution parts.1 arguments.left)⟩
  case beta Γ A B body a =>
    have sub := ops.singleSubstitution (children 0) (children 3)
    have lambda := ops.build (.lambda Γ A B body) (child (children 0) (child (children 1) (child (children 2) stop)))
    exact ⟨ops.build (.application Γ A B body.lambda a) (child lambda (child (children 3) stop)),
      ops.substituteEvidence (children 2) Γ (single a) sub,
      ops.substituteEvidence (children 1) Γ (single a) sub⟩
  case eta => exact ⟨children 2, children 3, ops.piFormed (children 0) (children 1)⟩

noncomputable def Derivation.endpointRegularity {j : Judgment} (tree : Derivation j) :
    EndpointRegularity Derivation j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial
    (fun _ j _ => EndpointRegularity Derivation j)
    (fun _ _ shape children ih => endpointRule canonicalOperations Derivation.formationPiParts
      Derivation.formationFunctionality shape children ih) () j tree

noncomputable def Derivation.typingFormation {n : Nat} {Γ : RawContext n} {t : RawTm n} {A : RawTy n}
    (tree : Derivation (typed Γ t A)) : Derivation (formed Γ A) := tree.endpointRegularity

noncomputable def Derivation.typeEndpoints {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    (tree : Derivation (typeEqual Γ A B)) : TypeEndpoints Derivation Γ A B := tree.endpointRegularity

noncomputable def Derivation.termEndpoints {n : Nat} {Γ : RawContext n} {t u : RawTm n} {A : RawTy n}
    (tree : Derivation (termEqual Γ t u A)) : TermEndpoints Derivation Γ t u A := tree.endpointRegularity

end Mettapedia.Languages.Agda.Structural.Statics
