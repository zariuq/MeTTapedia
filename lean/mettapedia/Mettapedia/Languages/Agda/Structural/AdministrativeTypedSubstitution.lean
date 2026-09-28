import Mettapedia.Languages.Agda.Structural.AdministrativeRenaming
import Mettapedia.Languages.Agda.Structural.SpineTypedSubstitution

/-!
# Typed substitution for administrative equality

The actual typed-image record and prior rule algebra are reused. Recursive
substitution transforms all equality children without extracting action
endpoints from a conditional equality.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open Statics (RawTm RawTy RawContext RawSub)

def SubstitutionAction (D : Judgment → Type) : Judgment → Type
  | .core j => Statics.SubstitutionAction (fun j => D (.core j)) j
  | .spineAction Γ A es B => ∀ {m : Nat} (Δ : RawContext m) (σ : RawSub _ m),
      Statics.TypedSubstitution (fun j => D (.core j)) Γ Δ σ →
        D (.spineAction Δ (bind σ A) (bind σ es) (bind σ B))
  | .spineEquality Γ A es fs B => ∀ {m : Nat} (Δ : RawContext m) (σ : RawSub _ m),
      Statics.TypedSubstitution (fun j => D (.core j)) Γ Δ σ →
        D (.spineEquality Δ (bind σ A) (bind σ es) (bind σ fs) (bind σ B))

def toPriorSubstitution {D : Judgment → Type} {j : SpineStatics.CombinedJudgment}
    (value : SubstitutionAction D (mapPrior j)) : SpineStatics.SubstitutionAction (fun j => D (mapPrior j)) j := by
  cases j <;> exact value

def ofPriorSubstitution {D : Judgment → Type} {j : SpineStatics.CombinedJudgment}
    (value : SpineStatics.SubstitutionAction (fun j => D (mapPrior j)) j) : SubstitutionAction D (mapPrior j) := by
  cases j <;> exact value

noncomputable def substituteRule {D : Judgment → Type}
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j))
    (renameEvidence : ∀ {j : Judgment}, D j → RenamingAction D j)
    {j : Judgment} (shape : RuleShape j) (children : Evidence D (premises shape))
    (ih : Evidence (SubstitutionAction D) (premises shape)) : SubstitutionAction D j := by
  let build {j : Judgment} (shape : RuleShape j) (children : Evidence D (premises shape)) : D j :=
    algebra.act () j ⟨shape, children⟩
  let stop := noEvidence D
  let child := @consEvidence _ D
  cases shape <;> simp only [premises] at children ih
  case prior shape =>
    exact ofPriorSubstitution (SpineStatics.substituteRule (priorAlgebra algebra)
      (fun tree => toPriorRenaming (renameEvidence tree)) shape (priorPremiseEvidence children)
      (fun position => toPriorSubstitution (priorPremiseEvidence ih position)))
  case spineRefl Γ A es B =>
    intro m Δ σ sub
    exact build (.spineRefl Δ (bind σ A) (bind σ es) (bind σ B))
      (child (ih 0 Δ σ sub) stop)
  case spineSymm Γ A es fs B =>
    intro m Δ σ sub
    exact build (.spineSymm Δ (bind σ A) (bind σ es) (bind σ fs) (bind σ B))
      (child (ih 0 Δ σ sub) stop)
  case spineTrans Γ A es fs gs B =>
    intro m Δ σ sub
    exact build (.spineTrans Δ (bind σ A) (bind σ es) (bind σ fs)
      (bind σ gs) (bind σ B))
      (child (ih 0 Δ σ sub) (child (ih 1 Δ σ sub) stop))
  case spineCons Γ A B u v es fs C =>
    intro m Δ σ sub
    change D (.spineEquality Δ (bind σ (Statics.piType A B).code)
      (cons (apply (bind σ u)) (bind σ es))
      (cons (apply (bind σ v)) (bind σ fs)) (bind σ C))
    have inputEquation : (Statics.piType (A.substitute σ) (B.substitute σ)).code =
        bind σ (Statics.piType A B).code :=
      (congrArg Statics.TypeParameter.code (Statics.substitute_piType σ A B).symm).trans
        (Statics.TypeParameter.code_substitute (Statics.piType A B) σ)
    have tailEquation : ((B.substitute σ).instantiate (bind σ u)).code =
        bind σ (B.instantiate u).code :=
      (congrArg Statics.TypeParameter.code (Statics.TypeBody.instantiate_substitute σ B u)).trans
        (Statics.TypeParameter.code_substitute (B.instantiate u) σ)
    have tail : D (.spineEquality Δ ((B.substitute σ).instantiate (bind σ u)).code
        (bind σ es) (bind σ fs) (bind σ C)) :=
      (congrArg (fun T => D (.spineEquality Δ T (bind σ es) (bind σ fs) (bind σ C))) tailEquation).mpr
        (ih 1 Δ σ sub)
    exact (congrArg (fun T => D (.spineEquality Δ T
      (cons (apply (bind σ u)) (bind σ es)) (cons (apply (bind σ v)) (bind σ fs)) (bind σ C))) inputEquation).mp
      (build (.spineCons Δ (A.substitute σ) (B.substitute σ)
        (bind σ u) (bind σ v) (bind σ es) (bind σ fs) (bind σ C))
        (child (ih 0 Δ σ sub) (child tail stop)))
  case spineAppend Γ A es fs B gs hs C =>
    intro m Δ σ sub
    exact build (.spineAppend Δ (bind σ A) (bind σ es) (bind σ fs)
      (bind σ B) (bind σ gs) (bind σ hs) (bind σ C))
      (child (ih 0 Δ σ sub) (child (ih 1 Δ σ sub) stop))
  case spineInputConversion Γ A' A es fs B =>
    intro m Δ σ sub
    exact build (.spineInputConversion Δ (bind σ A') (bind σ A)
      (bind σ es) (bind σ fs) (bind σ B))
      (child (ih 0 Δ σ sub) (child (ih 1 Δ σ sub) stop))
  case spineOutputConversion Γ A es fs B B' =>
    intro m Δ σ sub
    exact build (.spineOutputConversion Δ (bind σ A) (bind σ es) (bind σ fs)
      (bind σ B) (bind σ B'))
      (child (ih 0 Δ σ sub) (child (ih 1 Δ σ sub) stop))
  case appendEmpty Γ A es B =>
    intro m Δ σ sub
    exact build (.appendEmpty Δ (bind σ A) (bind σ es) (bind σ B))
      (child (ih 0 Δ σ sub) stop)
  case appendCons Γ A u es fs B =>
    intro m Δ σ sub
    exact build (.appendCons Δ (bind σ A) (bind σ u)
      (bind σ es) (bind σ fs) (bind σ B)) (child (ih 0 Δ σ sub) stop)
  case eliminationCongruence Γ f g A es fs B =>
    intro m Δ σ sub
    exact build (.eliminationCongruence Δ (bind σ f) (bind σ g) (bind σ A)
      (bind σ es) (bind σ fs) (bind σ B))
      (child (ih 0 Δ σ sub) (child (ih 1 Δ σ sub) stop))
  case emptyElimination Γ f A =>
    intro m Δ σ sub
    exact build (.emptyElimination Δ (bind σ f) (bind σ A)) (child (ih 0 Δ σ sub) stop)
  case nestedElimination Γ f A es B fs C =>
    intro m Δ σ sub
    exact build (.nestedElimination Δ (bind σ f) (bind σ A) (bind σ es)
      (bind σ B) (bind σ fs) (bind σ C))
      (child (ih 0 Δ σ sub) (child (ih 1 Δ σ sub) (child (ih 2 Δ σ sub) stop)))

abbrev TypedSubstitution {n m : Nat} (Γ : RawContext n) (Δ : RawContext m) (σ : RawSub n m) :=
  Statics.TypedSubstitution CoreDerivation Γ Δ σ

noncomputable def Derivation.substitution {j : Judgment} (tree : Derivation j) : SubstitutionAction Derivation j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial (fun _ j _ => SubstitutionAction Derivation j)
    (fun _ _ shape children ih => substituteRule algebra Derivation.renaming shape children ih) () j tree

noncomputable def CoreDerivation.substitution {j : Statics.Judgment} (tree : CoreDerivation j) :
    Statics.SubstitutionAction CoreDerivation j := Derivation.substitution tree

noncomputable def Action.substitution {n m : Nat} {Γ : RawContext n} {A B : RawTy n} {es : Spine (scope n)}
    (tree : Action Γ A es B) (Δ : RawContext m) (σ : RawSub n m) (sub : TypedSubstitution Γ Δ σ) :
    Action Δ (bind σ A) (bind σ es) (bind σ B) := Derivation.substitution tree Δ σ sub

noncomputable def SpineEq.substitution {n m : Nat} {Γ : RawContext n} {A B : RawTy n} {es fs : Spine (scope n)}
    (tree : SpineEq Γ A es fs B) (Δ : RawContext m) (σ : RawSub n m) (sub : TypedSubstitution Γ Δ σ) :
    SpineEq Δ (bind σ A) (bind σ es) (bind σ fs) (bind σ B) := Derivation.substitution tree Δ σ sub

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics
