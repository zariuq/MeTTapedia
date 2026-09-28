import Mettapedia.Languages.Agda.Structural.AdministrativeEvidenceOperations
import Mettapedia.Languages.Agda.Structural.StaticFunctionality

/-!
# Joint functionality of core typing and spine action

Equal typed substitutions induce type equality and term equality in core
formation/typing, and conditional equality between substituted spines in an
action. The cons case uses argument functionality and the original tail's
induction hypothesis. No endpoint regularity or Pi inversion is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open Statics (RawTm RawTy RawContext RawSub TypeParameter TypeBody)

def Functionality (D : Judgment → Type) : Judgment → Type
  | .core j => Statics.Functionality (fun j => D (.core j)) j
  | .spineAction Γ A es B => ∀ {m : Nat} (Δ : RawContext m) (σ τ : RawSub _ m),
      Statics.EqualSubstitution (fun j => D (.core j)) Γ Δ σ τ →
        D (.spineEquality Δ (bind σ A) (bind σ es) (bind τ es) (bind σ B))
  | .spineEquality _ _ _ _ _ => PUnit

noncomputable def functionalityRule {D : Judgment → Type}
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j))
    (ops : Statics.EvidenceOperations (fun j => D (.core j)))
    {j : Judgment} (shape : RuleShape j) (children : Evidence D (premises shape))
    (ih : Evidence (Functionality D) (premises shape)) : Functionality D j := by
  let build {j : Judgment} (shape : RuleShape j) (children : Evidence D (premises shape)) : D j :=
    algebra.act () j ⟨shape, children⟩
  let stop := noEvidence D
  let child := @consEvidence _ D
  cases shape with
  | prior shape =>
      have children := priorPremiseEvidence children
      have ih := priorPremiseEvidence ih
      cases shape with
      | core shape =>
          exact Statics.functionalityRule ops shape (SpineStatics.corePremiseEvidence children)
            (SpineStatics.corePremiseEvidence ih)
      | nil Γ A =>
          intro m Δ σ τ sub
          exact build (.spineRefl Δ (bind σ A) nil (bind σ A))
            (child (build (.prior (.nil Δ (bind σ A))) stop) stop)
      | cons Γ A B u es C =>
          simp only [SpineStatics.premises] at children ih
          intro m Δ σ τ sub
          change D (.spineEquality Δ (bind σ (Statics.piType A B).code)
            (cons (apply (bind σ u)) (bind σ es)) (cons (apply (bind τ u)) (bind τ es)) (bind σ C))
          have inputEquation : (Statics.piType (A.substitute σ) (B.substitute σ)).code =
              bind σ (Statics.piType A B).code :=
            (congrArg Statics.TypeParameter.code (Statics.substitute_piType σ A B).symm).trans
              (Statics.TypeParameter.code_substitute (Statics.piType A B) σ)
          have tailEquation : ((B.substitute σ).instantiate (bind σ u)).code =
              bind σ (B.instantiate u).code :=
            (congrArg Statics.TypeParameter.code (Statics.TypeBody.instantiate_substitute σ B u)).trans
              (Statics.TypeParameter.code_substitute (B.instantiate u) σ)
          have tail : D (.spineEquality Δ ((B.substitute σ).instantiate (bind σ u)).code
              (bind σ es) (bind τ es) (bind σ C)) :=
            (congrArg (fun T => D (.spineEquality Δ T (bind σ es) (bind τ es) (bind σ C))) tailEquation).mpr
              (ih 1 Δ σ τ sub)
          exact (congrArg (fun T => D (.spineEquality Δ T
            (cons (apply (bind σ u)) (bind σ es)) (cons (apply (bind τ u)) (bind τ es)) (bind σ C))) inputEquation).mp
            (build (.spineCons Δ (A.substitute σ) (B.substitute σ)
              (bind σ u) (bind τ u) (bind σ es) (bind τ es) (bind σ C))
              (child (ih 0 Δ σ τ sub) (child tail stop)))
      | append Γ A es B fs C =>
          simp only [SpineStatics.premises] at children ih
          intro m Δ σ τ sub
          exact build (.spineAppend Δ (bind σ A) (bind σ es) (bind τ es)
            (bind σ B) (bind σ fs) (bind τ fs) (bind σ C))
            (child (ih 0 Δ σ τ sub) (child (ih 1 Δ σ τ sub) stop))
      | inputConversion Γ A' A es B =>
          simp only [SpineStatics.premises] at children ih
          intro m Δ σ τ sub
          exact build (.spineInputConversion Δ (bind σ A') (bind σ A) (bind σ es) (bind τ es) (bind σ B))
            (child (ops.substituteEvidence (children 0) Δ σ sub.left) (child (ih 1 Δ σ τ sub) stop))
      | outputConversion Γ A es B B' =>
          simp only [SpineStatics.premises] at children ih
          intro m Δ σ τ sub
          exact build (.spineOutputConversion Δ (bind σ A) (bind σ es) (bind τ es) (bind σ B) (bind σ B'))
            (child (ih 0 Δ σ τ sub) (child (ops.substituteEvidence (children 1) Δ σ sub.left) stop))
      | elimination Γ f A es B =>
          simp only [SpineStatics.premises] at children ih
          intro m Δ σ τ sub
          exact build (.eliminationCongruence Δ (bind σ f) (bind τ f) (bind σ A)
            (bind σ es) (bind τ es) (bind σ B))
            (child (ih 0 Δ σ τ sub) (child (ih 1 Δ σ τ sub) stop))
  | spineRefl | spineSymm | spineTrans | spineCons | spineAppend | spineInputConversion
    | spineOutputConversion | appendEmpty | appendCons | eliminationCongruence | emptyElimination
    | nestedElimination => exact ⟨⟩

noncomputable def Derivation.functionality {j : Judgment} (tree : Derivation j) : Functionality Derivation j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial (fun _ j _ => Functionality Derivation j)
    (fun _ _ shape children ih => functionalityRule algebra administrativeOperations shape children ih) () j tree

noncomputable def CoreDerivation.formationFunctionality {n m : Nat} {Γ : RawContext n} {Δ : RawContext m}
    {A : RawTy n} {σ τ : RawSub n m} (tree : CoreDerivation (Statics.formed Γ A))
    (sub : Statics.EqualSubstitution CoreDerivation Γ Δ σ τ) :
    CoreDerivation (Statics.typeEqual Δ (bind σ A) (bind τ A)) := Derivation.functionality tree Δ σ τ sub

noncomputable def CoreDerivation.typingFunctionality {n m : Nat} {Γ : RawContext n} {Δ : RawContext m}
    {t : RawTm n} {A : RawTy n} {σ τ : RawSub n m} (tree : CoreDerivation (Statics.typed Γ t A))
    (sub : Statics.EqualSubstitution CoreDerivation Γ Δ σ τ) :
    CoreDerivation (Statics.termEqual Δ (bind σ t) (bind τ t) (bind σ A)) := Derivation.functionality tree Δ σ τ sub

noncomputable def Action.functionality {n m : Nat} {Γ : RawContext n} {Δ : RawContext m}
    {A B : RawTy n} {es : Spine (scope n)} {σ τ : RawSub n m} (tree : Action Γ A es B)
    (sub : Statics.EqualSubstitution CoreDerivation Γ Δ σ τ) :
    SpineEq Δ (bind σ A) (bind σ es) (bind τ es) (bind σ B) := Derivation.functionality tree Δ σ τ sub

noncomputable def CoreDerivation.instantiateCongruence {n : Nat} {Γ : RawContext n}
    {A : TypeParameter n} {B : TypeBody n} {u v : RawTm n}
    (domain : CoreDerivation (Statics.formed Γ A.code))
    (codomain : CoreDerivation (Statics.formed (Γ.snoc A.code) B.open.code))
    (left : CoreDerivation (Statics.typed Γ u A.code)) (right : CoreDerivation (Statics.typed Γ v A.code))
    (equal : CoreDerivation (Statics.termEqual Γ u v A.code)) :
    CoreDerivation (Statics.typeEqual Γ (B.instantiate u).code (B.instantiate v).code) :=
  codomain.formationFunctionality (Statics.EqualSubstitution.single administrativeOperations domain left right equal)

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics
