import Mettapedia.Languages.Agda.Structural.AdministrativeStatics

/-!
# Renaming of administrative static derivations

The prior twenty-four cases use their checked algebra. The twelve new cases
transform all recursive children into the enlarged family, keeping equality
at its left substituted type and retaining every conversion premise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open Statics (RawTm RawTy RawContext RawRen)

def RenamingAction (D : Judgment → Type) : Judgment → Type
  | .core j => Statics.RenamingAction (fun j => D (.core j)) j
  | .spineAction Γ A es B => ∀ {m : Nat} (Δ : RawContext m) (ρ : RawRen _ m),
      ρ.Respects Γ Δ → D (.core (Statics.context Δ)) →
        D (.spineAction Δ (bind ρ.asSub A) (bind ρ.asSub es) (bind ρ.asSub B))
  | .spineEquality Γ A es fs B => ∀ {m : Nat} (Δ : RawContext m) (ρ : RawRen _ m),
      ρ.Respects Γ Δ → D (.core (Statics.context Δ)) →
        D (.spineEquality Δ (bind ρ.asSub A) (bind ρ.asSub es) (bind ρ.asSub fs) (bind ρ.asSub B))

def toPriorRenaming {D : Judgment → Type} {j : SpineStatics.CombinedJudgment}
    (value : RenamingAction D (mapPrior j)) : SpineStatics.RenamingAction (fun j => D (mapPrior j)) j := by
  cases j <;> exact value

def ofPriorRenaming {D : Judgment → Type} {j : SpineStatics.CombinedJudgment}
    (value : SpineStatics.RenamingAction (fun j => D (mapPrior j)) j) : RenamingAction D (mapPrior j) := by
  cases j <;> exact value

noncomputable def renameRule {D : Judgment → Type}
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j))
    {j : Judgment} (shape : RuleShape j)
    (ih : Evidence (RenamingAction D) (premises shape)) : RenamingAction D j := by
  let build {j : Judgment} (shape : RuleShape j) (children : Evidence D (premises shape)) : D j :=
    algebra.act () j ⟨shape, children⟩
  let stop := noEvidence D
  let child := @consEvidence _ D
  cases shape <;> simp only [premises] at ih
  case prior shape =>
    exact ofPriorRenaming (SpineStatics.renameRule (priorAlgebra algebra) shape
      (fun position => toPriorRenaming (priorPremiseEvidence ih position)))
  case spineRefl Γ A es B =>
    intro m Δ ρ respects target
    exact build (.spineRefl Δ (bind ρ.asSub A) (bind ρ.asSub es) (bind ρ.asSub B))
      (child (ih 0 Δ ρ respects target) stop)
  case spineSymm Γ A es fs B =>
    intro m Δ ρ respects target
    exact build (.spineSymm Δ (bind ρ.asSub A) (bind ρ.asSub es) (bind ρ.asSub fs) (bind ρ.asSub B))
      (child (ih 0 Δ ρ respects target) stop)
  case spineTrans Γ A es fs gs B =>
    intro m Δ ρ respects target
    exact build (.spineTrans Δ (bind ρ.asSub A) (bind ρ.asSub es) (bind ρ.asSub fs)
      (bind ρ.asSub gs) (bind ρ.asSub B))
      (child (ih 0 Δ ρ respects target) (child (ih 1 Δ ρ respects target) stop))
  case spineCons Γ A B u v es fs C =>
    intro m Δ ρ respects target
    change D (.spineEquality Δ (bind ρ.asSub (Statics.piType A B).code)
      (cons (apply (bind ρ.asSub u)) (bind ρ.asSub es))
      (cons (apply (bind ρ.asSub v)) (bind ρ.asSub fs)) (bind ρ.asSub C))
    have inputEquation : (Statics.piType (A.substitute ρ.asSub) (B.substitute ρ.asSub)).code =
        bind ρ.asSub (Statics.piType A B).code :=
      (congrArg Statics.TypeParameter.code (Statics.substitute_piType ρ.asSub A B).symm).trans
        (Statics.TypeParameter.code_substitute (Statics.piType A B) ρ.asSub)
    have tailEquation : ((B.substitute ρ.asSub).instantiate (bind ρ.asSub u)).code =
        bind ρ.asSub (B.instantiate u).code :=
      (congrArg Statics.TypeParameter.code (Statics.TypeBody.instantiate_substitute ρ.asSub B u)).trans
        (Statics.TypeParameter.code_substitute (B.instantiate u) ρ.asSub)
    have tail : D (.spineEquality Δ ((B.substitute ρ.asSub).instantiate (bind ρ.asSub u)).code
        (bind ρ.asSub es) (bind ρ.asSub fs) (bind ρ.asSub C)) :=
      (congrArg (fun T => D (.spineEquality Δ T (bind ρ.asSub es) (bind ρ.asSub fs) (bind ρ.asSub C))) tailEquation).mpr
        (ih 1 Δ ρ respects target)
    exact (congrArg (fun T => D (.spineEquality Δ T
      (cons (apply (bind ρ.asSub u)) (bind ρ.asSub es)) (cons (apply (bind ρ.asSub v)) (bind ρ.asSub fs)) (bind ρ.asSub C))) inputEquation).mp
      (build (.spineCons Δ (A.substitute ρ.asSub) (B.substitute ρ.asSub)
        (bind ρ.asSub u) (bind ρ.asSub v) (bind ρ.asSub es) (bind ρ.asSub fs) (bind ρ.asSub C))
        (child (ih 0 Δ ρ respects target) (child tail stop)))
  case spineAppend Γ A es fs B gs hs C =>
    intro m Δ ρ respects target
    exact build (.spineAppend Δ (bind ρ.asSub A) (bind ρ.asSub es) (bind ρ.asSub fs)
      (bind ρ.asSub B) (bind ρ.asSub gs) (bind ρ.asSub hs) (bind ρ.asSub C))
      (child (ih 0 Δ ρ respects target) (child (ih 1 Δ ρ respects target) stop))
  case spineInputConversion Γ A' A es fs B =>
    intro m Δ ρ respects target
    exact build (.spineInputConversion Δ (bind ρ.asSub A') (bind ρ.asSub A)
      (bind ρ.asSub es) (bind ρ.asSub fs) (bind ρ.asSub B))
      (child (ih 0 Δ ρ respects target) (child (ih 1 Δ ρ respects target) stop))
  case spineOutputConversion Γ A es fs B B' =>
    intro m Δ ρ respects target
    exact build (.spineOutputConversion Δ (bind ρ.asSub A) (bind ρ.asSub es) (bind ρ.asSub fs)
      (bind ρ.asSub B) (bind ρ.asSub B'))
      (child (ih 0 Δ ρ respects target) (child (ih 1 Δ ρ respects target) stop))
  case appendEmpty Γ A es B =>
    intro m Δ ρ respects target
    exact build (.appendEmpty Δ (bind ρ.asSub A) (bind ρ.asSub es) (bind ρ.asSub B))
      (child (ih 0 Δ ρ respects target) stop)
  case appendCons Γ A u es fs B =>
    intro m Δ ρ respects target
    exact build (.appendCons Δ (bind ρ.asSub A) (bind ρ.asSub u)
      (bind ρ.asSub es) (bind ρ.asSub fs) (bind ρ.asSub B)) (child (ih 0 Δ ρ respects target) stop)
  case eliminationCongruence Γ f g A es fs B =>
    intro m Δ ρ respects target
    exact build (.eliminationCongruence Δ (bind ρ.asSub f) (bind ρ.asSub g) (bind ρ.asSub A)
      (bind ρ.asSub es) (bind ρ.asSub fs) (bind ρ.asSub B))
      (child (ih 0 Δ ρ respects target) (child (ih 1 Δ ρ respects target) stop))
  case emptyElimination Γ f A =>
    intro m Δ ρ respects target
    exact build (.emptyElimination Δ (bind ρ.asSub f) (bind ρ.asSub A)) (child (ih 0 Δ ρ respects target) stop)
  case nestedElimination Γ f A es B fs C =>
    intro m Δ ρ respects target
    exact build (.nestedElimination Δ (bind ρ.asSub f) (bind ρ.asSub A) (bind ρ.asSub es)
      (bind ρ.asSub B) (bind ρ.asSub fs) (bind ρ.asSub C))
      (child (ih 0 Δ ρ respects target) (child (ih 1 Δ ρ respects target) (child (ih 2 Δ ρ respects target) stop)))

noncomputable def Derivation.renaming {j : Judgment} (tree : Derivation j) : RenamingAction Derivation j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial (fun _ j _ => RenamingAction Derivation j)
    (fun _ _ shape _children ih => renameRule algebra shape ih) () j tree

noncomputable def CoreDerivation.renaming {j : Statics.Judgment} (tree : CoreDerivation j) :
    Statics.RenamingAction CoreDerivation j := Derivation.renaming tree

noncomputable def Action.renaming {n m : Nat} {Γ : RawContext n} {A B : RawTy n} {es : Spine (scope n)}
    (tree : Action Γ A es B) (Δ : RawContext m) (ρ : RawRen n m) (respects : ρ.Respects Γ Δ)
    (target : CoreDerivation (Statics.context Δ)) : Action Δ (bind ρ.asSub A) (bind ρ.asSub es) (bind ρ.asSub B) :=
  Derivation.renaming tree Δ ρ respects target

noncomputable def SpineEq.renaming {n m : Nat} {Γ : RawContext n} {A B : RawTy n} {es fs : Spine (scope n)}
    (tree : SpineEq Γ A es fs B) (Δ : RawContext m) (ρ : RawRen n m) (respects : ρ.Respects Γ Δ)
    (target : CoreDerivation (Statics.context Δ)) :
    SpineEq Δ (bind ρ.asSub A) (bind ρ.asSub es) (bind ρ.asSub fs) (bind ρ.asSub B) :=
  Derivation.renaming tree Δ ρ respects target

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics
