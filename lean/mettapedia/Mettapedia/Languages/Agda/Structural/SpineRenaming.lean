import Mettapedia.Languages.Agda.Structural.SpineStatics
import Mettapedia.Languages.Agda.Structural.StaticRenaming
import Mettapedia.OSLF.Syntax.IndexedRuleAlgebraPullback

/-!
# Admissible renaming for combined spine statics

Canonical cases use the existing rule-renaming algebra pulled back through
the inclusion of presentations. Only the six spine constructors need new
cases. All recursive evidence stays in the combined family, and the target
context's formation evidence is explicitly supplied.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.SpineStatics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open Statics (RawTm RawTy RawContext RawRen TypeParameter TypeBody)

def RenamingAction (D : CombinedJudgment → Type) : CombinedJudgment → Type
  | .core j => Statics.RenamingAction (fun j => D (.core j)) j
  | .spineAction Γ A spine B => ∀ {m : Nat} (Δ : RawContext m) (ρ : RawRen _ m),
      ρ.Respects Γ Δ → D (.core (Statics.context Δ)) →
        D (.spineAction Δ (bind ρ.asSub A) (bind ρ.asSub spine) (bind ρ.asSub B))

/-- Read the same ordered core-tagged premises at their canonical indices. -/
def corePremiseEvidence {D : CombinedJudgment → Type} : {js : List Statics.Judgment} →
    Evidence D (js.map CombinedJudgment.core) → Evidence (fun j => D (.core j)) js
  | [], _ => noEvidence _
  | _ :: _, children => consEvidence _ (children ⟨0, Nat.zero_lt_succ _⟩)
      (corePremiseEvidence (fun position => children position.succ))

abbrev coreRenamingEvidence {D : CombinedJudgment → Type} {js : List Statics.Judgment} :
    Evidence (RenamingAction D) (js.map CombinedJudgment.core) →
      Evidence (Statics.RenamingAction (fun j => D (.core j))) js := corePremiseEvidence

/-- Restrict an actual combined algebra along the cartesian canonical inclusion. -/
noncomputable def canonicalAlgebra {D : CombinedJudgment → Type}
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j)) :
    IndexedPolynomial.Algebra Statics.presentation.polynomial (fun _ j => D (.core j)) :=
  IndexedRuleAlgebraPullback.pullback canonicalHom algebra

noncomputable def renameRule {D : CombinedJudgment → Type}
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j))
    {j : CombinedJudgment} (shape : RuleShape j)
    (ih : Evidence (RenamingAction D) (premises shape)) : RenamingAction D j := by
  let build {j : CombinedJudgment} (shape : RuleShape j) (children : Evidence D (premises shape)) : D j :=
    algebra.act () j ⟨shape, children⟩
  let endChildren := noEvidence D
  let child := @consEvidence _ D
  cases shape <;> simp only [premises] at ih
  case core shape => exact Statics.renameRule (canonicalAlgebra algebra) shape (coreRenamingEvidence ih)
  case nil Γ A =>
    intro m Δ ρ respects target
    exact build (.nil Δ (bind ρ.asSub A)) endChildren
  case cons Γ A B argument rest C =>
    intro m Δ ρ respects target
    change D (.spineAction Δ (bind ρ.asSub (Statics.piType A B).code)
      (cons (apply (bind ρ.asSub argument)) (bind ρ.asSub rest)) (bind ρ.asSub C))
    have inputEquation : (Statics.piType (A.substitute ρ.asSub) (B.substitute ρ.asSub)).code =
        bind ρ.asSub (Statics.piType A B).code :=
      (congrArg Statics.TypeParameter.code (Statics.substitute_piType ρ.asSub A B).symm).trans
        (Statics.TypeParameter.code_substitute (Statics.piType A B) ρ.asSub)
    have tailEquation : ((B.substitute ρ.asSub).instantiate (bind ρ.asSub argument)).code =
        bind ρ.asSub (B.instantiate argument).code :=
      (congrArg Statics.TypeParameter.code (Statics.TypeBody.instantiate_substitute ρ.asSub B argument)).trans
        (Statics.TypeParameter.code_substitute (B.instantiate argument) ρ.asSub)
    have tail : D (.spineAction Δ ((B.substitute ρ.asSub).instantiate (bind ρ.asSub argument)).code
        (bind ρ.asSub rest) (bind ρ.asSub C)) :=
      (congrArg (fun T => D (.spineAction Δ T (bind ρ.asSub rest) (bind ρ.asSub C))) tailEquation).mpr
        (ih 1 Δ ρ respects target)
    exact (congrArg (fun T => D (.spineAction Δ T
      (cons (apply (bind ρ.asSub argument)) (bind ρ.asSub rest)) (bind ρ.asSub C))) inputEquation).mp
      (build (.cons Δ (A.substitute ρ.asSub) (B.substitute ρ.asSub)
        (bind ρ.asSub argument) (bind ρ.asSub rest) (bind ρ.asSub C))
        (child (ih 0 Δ ρ respects target) (child tail endChildren)))
  case append Γ A first B second C =>
    intro m Δ ρ respects target
    exact build (.append Δ (bind ρ.asSub A) (bind ρ.asSub first)
      (bind ρ.asSub B) (bind ρ.asSub second) (bind ρ.asSub C))
      (child (ih 0 Δ ρ respects target) (child (ih 1 Δ ρ respects target) endChildren))
  case inputConversion Γ A' A spine B =>
    intro m Δ ρ respects target
    exact build (.inputConversion Δ (bind ρ.asSub A') (bind ρ.asSub A)
      (bind ρ.asSub spine) (bind ρ.asSub B))
      (child (ih 0 Δ ρ respects target) (child (ih 1 Δ ρ respects target) endChildren))
  case outputConversion Γ A spine B B' =>
    intro m Δ ρ respects target
    exact build (.outputConversion Δ (bind ρ.asSub A) (bind ρ.asSub spine)
      (bind ρ.asSub B) (bind ρ.asSub B'))
      (child (ih 0 Δ ρ respects target) (child (ih 1 Δ ρ respects target) endChildren))
  case elimination Γ head A spine B =>
    intro m Δ ρ respects target
    exact build (.elimination Δ (bind ρ.asSub head) (bind ρ.asSub A)
      (bind ρ.asSub spine) (bind ρ.asSub B))
      (child (ih 0 Δ ρ respects target) (child (ih 1 Δ ρ respects target) endChildren))

/-- Reindex every actual combined derivation, including mutually recursive core premises. -/
noncomputable def Derivation.renaming {j : CombinedJudgment} (tree : Derivation j) :
    RenamingAction Derivation j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial
    (fun _ j _ => RenamingAction Derivation j)
    (fun _ _ shape _children ih => renameRule (IndexedPolynomial.Algebra.initial presentation.polynomial) shape ih)
    () j tree

noncomputable def CoreDerivation.renaming {j : Statics.Judgment} (tree : CoreDerivation j) :
    Statics.RenamingAction CoreDerivation j := Derivation.renaming tree

noncomputable def Action.renaming {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    {spine : Spine (scope n)} (tree : Action Γ A spine B)
    {m : Nat} (Δ : RawContext m) (ρ : RawRen n m) (respects : ρ.Respects Γ Δ)
    (target : CoreDerivation (Statics.context Δ)) :
    Action Δ (bind ρ.asSub A) (bind ρ.asSub spine) (bind ρ.asSub B) :=
  Derivation.renaming tree Δ ρ respects target

@[simp] theorem renaming_nil {n m : Nat} (Γ : RawContext n) (A : RawTy n)
    (Δ : RawContext m) (ρ : RawRen n m) (respects : ρ.Respects Γ Δ)
    (target : CoreDerivation (Statics.context Δ)) :
    Action.renaming (Derivation.nil Γ A) Δ ρ respects target =
      Derivation.nil Δ (bind ρ.asSub A) := rfl

@[simp] theorem renaming_append {n m : Nat} {Γ : RawContext n} {A B C : RawTy n}
    {first second : Spine (scope n)} (left : Action Γ A first B) (right : Action Γ B second C)
    (Δ : RawContext m) (ρ : RawRen n m) (respects : ρ.Respects Γ Δ)
    (target : CoreDerivation (Statics.context Δ)) :
    Action.renaming (Derivation.append left right) Δ ρ respects target =
      Derivation.append (Action.renaming left Δ ρ respects target) (Action.renaming right Δ ρ respects target) := rfl

@[simp] theorem renaming_inputConversion {n m : Nat} {Γ : RawContext n} {A' A B : RawTy n}
    {spine : Spine (scope n)} (equal : CoreDerivation (Statics.typeEqual Γ A' A)) (action : Action Γ A spine B)
    (Δ : RawContext m) (ρ : RawRen n m) (respects : ρ.Respects Γ Δ)
    (target : CoreDerivation (Statics.context Δ)) :
    Action.renaming (Derivation.inputConversion equal action) Δ ρ respects target =
      Derivation.inputConversion (CoreDerivation.renaming equal Δ ρ respects target)
        (Action.renaming action Δ ρ respects target) := rfl

@[simp] theorem renaming_outputConversion {n m : Nat} {Γ : RawContext n} {A B B' : RawTy n}
    {spine : Spine (scope n)} (action : Action Γ A spine B) (equal : CoreDerivation (Statics.typeEqual Γ B B'))
    (Δ : RawContext m) (ρ : RawRen n m) (respects : ρ.Respects Γ Δ)
    (target : CoreDerivation (Statics.context Δ)) :
    Action.renaming (Derivation.outputConversion action equal) Δ ρ respects target =
      Derivation.outputConversion (Action.renaming action Δ ρ respects target)
        (CoreDerivation.renaming equal Δ ρ respects target) := rfl

@[simp] theorem renaming_elimination {n m : Nat} {Γ : RawContext n} {head : RawTm n} {A B : RawTy n}
    {spine : Spine (scope n)} (typedHead : CoreDerivation (Statics.typed Γ head A)) (action : Action Γ A spine B)
    (Δ : RawContext m) (ρ : RawRen n m) (respects : ρ.Respects Γ Δ)
    (target : CoreDerivation (Statics.context Δ)) :
    CoreDerivation.renaming (Derivation.elimination typedHead action) Δ ρ respects target =
      Derivation.elimination (CoreDerivation.renaming typedHead Δ ρ respects target)
        (Action.renaming action Δ ρ respects target) := rfl

end Mettapedia.Languages.Agda.Structural.SpineStatics
