import Mettapedia.Languages.Agda.Structural.StaticEqualSubstitution
import Mettapedia.Languages.Agda.Structural.StaticLambdaCongruence

/-!
# Equality-respecting substitution for canonical structural statics

The proof follows the authored rule data. Equal typed variable images produce
equal substituted type codes and terms. The lambda case uses the derived beta
and eta construction, while the dependent codomain is compared in the left
extended target context.

The rule algebra is reusable by extensions. Its canonical fixed-point instance
is proved here; an extension must also discharge functionality for its added
typing constructors. In particular this module does not assert functionality
or subject reduction for arbitrary administrative spine typing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Statics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory

def Functionality (D : Judgment → Type) : Judgment → Type
  | .type ⟨n, Γ⟩ A => ∀ {m : Nat} (Δ : RawContext m) (σ τ : RawSub n m),
      EqualSubstitution D Γ Δ σ τ → D (typeEqual Δ (bind σ A) (bind τ A))
  | .term ⟨n, Γ⟩ A t => ∀ {m : Nat} (Δ : RawContext m) (σ τ : RawSub n m),
      EqualSubstitution D Γ Δ σ τ → D (termEqual Δ (bind σ t.code) (bind τ t.code) (bind σ A))
  | _ => PUnit

def functionalityRule {D : Judgment → Type} (ops : EvidenceOperations D)
    {j : Judgment} (shape : RuleShape j) (children : Evidence D (premises shape))
    (ih : Evidence (Functionality D) (premises shape)) : Functionality D j := by
  let child := @consEvidence _ D
  let stop := noEvidence D
  cases shape <;> simp only [premises] at children ih
  case empty | extend | typeEquality | reflexivity | symmetry | transitivity | equalityConversion
    | piCongruence | applicationCongruence | beta | eta => exact ⟨⟩
  case formation Γ k a =>
    intro m Δ σ τ sub
    exact ops.build (.typeEquality Δ k (bind σ a) (bind τ a)) (child (ih 0 Δ σ τ sub) stop)
  case sort Γ k =>
    intro m Δ σ τ sub
    exact ops.build (.reflexivity Δ (universeTerm k) (universeType m (k + 1)).code)
      (child (ops.build (.sort Δ k) (child sub.left.target stop)) stop)
  case «variable» Γ v =>
    intro m Δ σ τ sub
    exact sub.equal v
  case pi Γ A B =>
    intro m Δ σ τ sub
    have domainEq := ih 0 Δ σ τ sub
    have lifted := sub.lift ops (children 0) domainEq
    have codomainEq := ih 1 (Δ.snoc (bind σ A.code)) (Telescope.lift σ) (Telescope.lift τ) lifted
    have domain := ops.substituteEvidence (children 0) Δ σ sub.left
    simpa only [TypeBody.pi_substitute, bind_universeCode, TypeParameter.level_substitute,
      TypeBody.level_substitute] using ops.build (.piCongruence Δ (A.substitute σ) (A.substitute τ)
        (B.substitute σ) (B.substitute τ))
        (child domain (child domainEq (child (by
          simpa only [TypeBody.open_substitute, TypeParameter.code_substitute] using codomainEq) stop)))
  case lambda Γ A B body =>
    intro m Δ σ τ sub
    have domainEq := ih 0 Δ σ τ sub
    have lifted := sub.lift ops (children 0) domainEq
    have codomainEq := ih 1 (Δ.snoc (bind σ A.code)) (Telescope.lift σ) (Telescope.lift τ) lifted
    have bodies := ih 2 (Δ.snoc (bind σ A.code)) (Telescope.lift σ) (Telescope.lift τ) lifted
    have domain := ops.substituteEvidence (children 0) Δ σ sub.left
    have codomain := ops.substituteEvidence (children 1) (Δ.snoc (bind σ A.code)) (Telescope.lift σ) lifted.left
    have left := ops.substituteEvidence (children 2) (Δ.snoc (bind σ A.code)) (Telescope.lift σ) lifted.left
    have right := ops.substituteEvidence (children 2) (Δ.snoc (bind σ A.code)) (Telescope.lift τ) lifted.right
    have rightConverted := ops.build (.conversion (Δ.snoc (bind σ A.code))
      (bind (Telescope.lift τ) body.open) (bind (Telescope.lift τ) B.open.code)
      (bind (Telescope.lift σ) B.open.code))
      (child right (child (ops.typeSymmetry codomainEq) stop))
    simpa only [TermBody.lambda_substitute, ← substitute_piType, TypeParameter.code_substitute] using
      ops.lambdaCongruence (A := A.substitute σ) (B := B.substitute σ)
        (first := body.substitute σ) (second := body.substitute τ) domain
        (by simpa only [TypeBody.open_substitute, TypeParameter.code_substitute] using codomain)
        (by simpa only [TypeBody.open_substitute, TypeParameter.code_substitute, TermBody.open_substitute] using left)
        (by simpa only [TypeBody.open_substitute, TypeParameter.code_substitute, TermBody.open_substitute] using rightConverted)
        (by simpa only [TypeBody.open_substitute, TypeParameter.code_substitute, TermBody.open_substitute] using bodies)
  case application Γ A B f a =>
    intro m Δ σ τ sub
    have functions := ih 0 Δ σ τ sub
    have arguments := ih 1 Δ σ τ sub
    simpa only [bind_app, TypeBody.instantiate_substitute, TypeParameter.code_substitute] using
      ops.build (.applicationCongruence Δ (A.substitute σ) (B.substitute σ)
        (bind σ f) (bind τ f) (bind σ a) (bind τ a))
        (child (by simpa only [← substitute_piType, TypeParameter.code_substitute] using functions)
          (child arguments stop))
  case conversion Γ t A B =>
    intro m Δ σ τ sub
    exact ops.build (.equalityConversion Δ (bind σ t) (bind τ t) (bind σ A) (bind σ B))
      (child (ih 0 Δ σ τ sub)
        (child (ops.substituteEvidence (children 1) Δ σ sub.left) stop))

noncomputable def Derivation.functionality {j : Judgment} (tree : Derivation j) : Functionality Derivation j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial
    (fun _ j _ => Functionality Derivation j)
    (fun _ _ shape children ih => functionalityRule canonicalOperations shape children ih) () j tree

noncomputable def Derivation.formationFunctionality {n m : Nat} {Γ : RawContext n} {Δ : RawContext m}
    {A : RawTy n} {σ τ : RawSub n m} (tree : Derivation (formed Γ A))
    (sub : EqualSubstitution Derivation Γ Δ σ τ) :
    Derivation (typeEqual Δ (bind σ A) (bind τ A)) := tree.functionality Δ σ τ sub

noncomputable def Derivation.typingFunctionality {n m : Nat} {Γ : RawContext n} {Δ : RawContext m}
    {t : RawTm n} {A : RawTy n} {σ τ : RawSub n m} (tree : Derivation (typed Γ t A))
    (sub : EqualSubstitution Derivation Γ Δ σ τ) :
    Derivation (termEqual Δ (bind σ t) (bind τ t) (bind σ A)) := tree.functionality Δ σ τ sub

noncomputable def Derivation.instantiateCongruence {n : Nat} {Γ : RawContext n}
    {A : TypeParameter n} {B : TypeBody n} {u v : RawTm n}
    (domain : Derivation (formed Γ A.code)) (codomain : Derivation (formed (Γ.snoc A.code) B.open.code))
    (left : Derivation (typed Γ u A.code)) (right : Derivation (typed Γ v A.code))
    (equal : Derivation (termEqual Γ u v A.code)) :
    Derivation (typeEqual Γ (B.instantiate u).code (B.instantiate v).code) :=
  codomain.formationFunctionality (EqualSubstitution.single canonicalOperations domain left right equal)

end Mettapedia.Languages.Agda.Structural.Statics
