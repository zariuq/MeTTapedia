import Mettapedia.Languages.Agda.Structural.SpineRenaming
import Mettapedia.Languages.Agda.Structural.StaticTypedSubstitution

/-!
# Typed substitution for combined spine statics

The substitution record retains source and target context derivations and a
typed image for every variable. The canonical rule algebra is reused through
the actual presentation inclusion. The six additional cases recursively
transform all combined premises, including spine input/output conversion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.SpineStatics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open Statics (RawTm RawTy RawSub RawContext TypeParameter TypeBody)

abbrev TypedSubstitution {n m : Nat} (Γ : RawContext n) (Δ : RawContext m) (σ : RawSub n m) :=
  Statics.TypedSubstitution CoreDerivation Γ Δ σ

def SubstitutionAction (D : CombinedJudgment → Type) : CombinedJudgment → Type
  | .core j => Statics.SubstitutionAction (fun j => D (.core j)) j
  | .spineAction Γ A spine B => ∀ {m : Nat} (Δ : RawContext m) (σ : RawSub _ m),
      Statics.TypedSubstitution (fun j => D (.core j)) Γ Δ σ →
        D (.spineAction Δ (bind σ A) (bind σ spine) (bind σ B))

noncomputable def substituteRule {D : CombinedJudgment → Type}
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j))
    (renameEvidence : ∀ {j : CombinedJudgment}, D j → RenamingAction D j)
    {j : CombinedJudgment} (shape : RuleShape j) (children : Evidence D (premises shape))
    (ih : Evidence (SubstitutionAction D) (premises shape)) : SubstitutionAction D j := by
  let build {j : CombinedJudgment} (shape : RuleShape j) (children : Evidence D (premises shape)) : D j :=
    algebra.act () j ⟨shape, children⟩
  let endChildren := noEvidence D
  let child := @consEvidence _ D
  cases shape <;> simp only [premises] at children ih
  case core shape =>
    exact Statics.substituteRule (canonicalAlgebra algebra) (fun tree => renameEvidence tree)
      shape (corePremiseEvidence children) (corePremiseEvidence ih)
  case nil Γ A =>
    intro m Δ σ sub
    exact build (.nil Δ (bind σ A)) endChildren
  case cons Γ A B argument rest C =>
    intro m Δ σ sub
    change D (.spineAction Δ (bind σ (Statics.piType A B).code)
      (cons (apply (bind σ argument)) (bind σ rest)) (bind σ C))
    have inputEquation : (Statics.piType (A.substitute σ) (B.substitute σ)).code =
        bind σ (Statics.piType A B).code :=
      (congrArg Statics.TypeParameter.code (Statics.substitute_piType σ A B).symm).trans
        (Statics.TypeParameter.code_substitute (Statics.piType A B) σ)
    have tailEquation : ((B.substitute σ).instantiate (bind σ argument)).code =
        bind σ (B.instantiate argument).code :=
      (congrArg Statics.TypeParameter.code (Statics.TypeBody.instantiate_substitute σ B argument)).trans
        (Statics.TypeParameter.code_substitute (B.instantiate argument) σ)
    have tail : D (.spineAction Δ ((B.substitute σ).instantiate (bind σ argument)).code
        (bind σ rest) (bind σ C)) :=
      (congrArg (fun T => D (.spineAction Δ T (bind σ rest) (bind σ C))) tailEquation).mpr
        (ih 1 Δ σ sub)
    exact (congrArg (fun T => D (.spineAction Δ T
      (cons (apply (bind σ argument)) (bind σ rest)) (bind σ C))) inputEquation).mp
      (build (.cons Δ (A.substitute σ) (B.substitute σ)
        (bind σ argument) (bind σ rest) (bind σ C))
        (child (ih 0 Δ σ sub) (child tail endChildren)))
  case append Γ A first B second C =>
    intro m Δ σ sub
    exact build (.append Δ (bind σ A) (bind σ first) (bind σ B) (bind σ second) (bind σ C))
      (child (ih 0 Δ σ sub) (child (ih 1 Δ σ sub) endChildren))
  case inputConversion Γ A' A spine B =>
    intro m Δ σ sub
    exact build (.inputConversion Δ (bind σ A') (bind σ A) (bind σ spine) (bind σ B))
      (child (ih 0 Δ σ sub) (child (ih 1 Δ σ sub) endChildren))
  case outputConversion Γ A spine B B' =>
    intro m Δ σ sub
    exact build (.outputConversion Δ (bind σ A) (bind σ spine) (bind σ B) (bind σ B'))
      (child (ih 0 Δ σ sub) (child (ih 1 Δ σ sub) endChildren))
  case elimination Γ head A spine B =>
    intro m Δ σ sub
    exact build (.elimination Δ (bind σ head) (bind σ A) (bind σ spine) (bind σ B))
      (child (ih 0 Δ σ sub) (child (ih 1 Δ σ sub) endChildren))

/-- Actual variable-image evidence recursively produces actual combined rule trees. -/
noncomputable def Derivation.substitution {j : CombinedJudgment} (tree : Derivation j) :
    SubstitutionAction Derivation j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial
    (fun _ j _ => SubstitutionAction Derivation j)
    (fun _ _ shape children ih => substituteRule
      (IndexedPolynomial.Algebra.initial presentation.polynomial) Derivation.renaming shape children ih)
    () j tree

noncomputable def CoreDerivation.substitution {j : Statics.Judgment} (tree : CoreDerivation j) :
    Statics.SubstitutionAction CoreDerivation j := Derivation.substitution tree

noncomputable def Action.substitution {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    {spine : Spine (scope n)} (tree : Action Γ A spine B)
    {m : Nat} (Δ : RawContext m) (σ : RawSub n m) (sub : TypedSubstitution Γ Δ σ) :
    Action Δ (bind σ A) (bind σ spine) (bind σ B) := Derivation.substitution tree Δ σ sub

@[simp] theorem substitution_nil {n m : Nat} (Γ : RawContext n) (A : RawTy n)
    (Δ : RawContext m) (σ : RawSub n m) (sub : TypedSubstitution Γ Δ σ) :
    Action.substitution (Derivation.nil Γ A) Δ σ sub = Derivation.nil Δ (bind σ A) := rfl

@[simp] theorem substitution_append {n m : Nat} {Γ : RawContext n} {A B C : RawTy n}
    {first second : Spine (scope n)} (left : Action Γ A first B) (right : Action Γ B second C)
    (Δ : RawContext m) (σ : RawSub n m) (sub : TypedSubstitution Γ Δ σ) :
    Action.substitution (Derivation.append left right) Δ σ sub =
      Derivation.append (Action.substitution left Δ σ sub) (Action.substitution right Δ σ sub) := rfl

@[simp] theorem substitution_inputConversion {n m : Nat} {Γ : RawContext n} {A' A B : RawTy n}
    {spine : Spine (scope n)} (equal : CoreDerivation (Statics.typeEqual Γ A' A)) (action : Action Γ A spine B)
    (Δ : RawContext m) (σ : RawSub n m) (sub : TypedSubstitution Γ Δ σ) :
    Action.substitution (Derivation.inputConversion equal action) Δ σ sub =
      Derivation.inputConversion (CoreDerivation.substitution equal Δ σ sub)
        (Action.substitution action Δ σ sub) := rfl

@[simp] theorem substitution_outputConversion {n m : Nat} {Γ : RawContext n} {A B B' : RawTy n}
    {spine : Spine (scope n)} (action : Action Γ A spine B) (equal : CoreDerivation (Statics.typeEqual Γ B B'))
    (Δ : RawContext m) (σ : RawSub n m) (sub : TypedSubstitution Γ Δ σ) :
    Action.substitution (Derivation.outputConversion action equal) Δ σ sub =
      Derivation.outputConversion (Action.substitution action Δ σ sub)
        (CoreDerivation.substitution equal Δ σ sub) := rfl

@[simp] theorem substitution_elimination {n m : Nat} {Γ : RawContext n} {head : RawTm n} {A B : RawTy n}
    {spine : Spine (scope n)} (typedHead : CoreDerivation (Statics.typed Γ head A)) (action : Action Γ A spine B)
    (Δ : RawContext m) (σ : RawSub n m) (sub : TypedSubstitution Γ Δ σ) :
    CoreDerivation.substitution (Derivation.elimination typedHead action) Δ σ sub =
      Derivation.elimination (CoreDerivation.substitution typedHead Δ σ sub)
        (Action.substitution action Δ σ sub) := rfl

end Mettapedia.Languages.Agda.Structural.SpineStatics
