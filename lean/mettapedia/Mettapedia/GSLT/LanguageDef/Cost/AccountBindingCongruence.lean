import Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingLaws

/-!
# The generated equations of an occurrence-local binding account extension

The generating equations retain their complete typed raw expressions as
data.  Their congruence derivations also remain proof-relevant data, including
operator argument positions and every substituted environment value.  Only
the setoid relation takes the existence of such a derivation.

Each generator is proved sound under every genuine over-source clone map
into an independently specified accounted binding clone.  No semantic
quotient or free extension is used to justify its own equations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.AccountBindingCongruence

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open BindingSubstitutionAlgebra
open AccountBindingAlgebra
open FreeBindingTerms
open RawAccountBindingExtension
open RawAccountBindingLaws

universe u

variable {S : Signature} (Q : BindingCloneAlgebra.Algebra.{u} S)
  (accountSort : S.Srt) (base : Over Q)

/-- The concrete, unbounded family of typed defining equations.  Generator
equations expand substitutions only when all environment values are injected
base values.  Arbitrary marked substitutions remain full expression nodes. -/
inductive Equation : {Γ : Ctx S} → {sort : S.Srt} →
    Raw Q accountSort base Γ sort → Raw Q accountSort base Γ sort → Type u where
  | substituteVariable {Γ Δ : Ctx S} {sort : S.Srt}
      (env : Environment S (Raw Q accountSort base) Γ Δ) (v : Var Γ sort) :
      Equation (.substitute env (sourceVariable Q accountSort base v)) (env sort v)
  | genOperation {Γ : Ctx S} {sort : S.Srt} (op : S.Op sort)
      (args : FamilyArgs S base.left.substitution.Carrier (S.arity op) Γ) :
      Equation (.gen (base.left.operation op args))
        (.operation op (genArguments Q accountSort base args))
  | genSubstitute {Γ Δ : Ctx S} {sort : S.Srt}
      (env : Environment S base.left.substitution.Carrier Γ Δ)
      (value : base.left.substitution.Carrier Γ sort) :
      Equation (.gen (base.left.substitution.substitute env value))
        (.substitute (fun s v => .gen (env s v)) (.gen value))
  | substituteIdentity {Γ : Ctx S} {sort : S.Srt}
      (value : Raw Q accountSort base Γ sort) :
      Equation (.substitute (fun _ v => sourceVariable Q accountSort base v) value) value
  | substituteComp {Γ Δ Θ : Ctx S} {sort : S.Srt}
      (first : Environment S (Raw Q accountSort base) Γ Δ)
      (second : Environment S (Raw Q accountSort base) Δ Θ)
      (value : Raw Q accountSort base Γ sort) :
      Equation (.substitute second (.substitute first value))
        (.substitute (fun s v => .substitute second (first s v)) value)
  | substituteOperation {Γ Δ : Ctx S} {sort : S.Srt}
      (env : Environment S (Raw Q accountSort base) Γ Δ)
      (op : S.Op sort) (args : Arguments Q accountSort base (S.arity op) Γ) :
      Equation (.substitute env (.operation op args))
        (.operation op (substituteArguments Q accountSort base env args))
  | accountOne {Γ : Ctx S} {sort : S.Srt} (value : Raw Q accountSort base Γ sort) :
      Equation (.account 1 value) value
  | accountMul {Γ : Ctx S} {sort : S.Srt}
      (first second : SourceAccountSubstitution.Account Q accountSort Γ)
      (value : Raw Q accountSort base Γ sort) :
      Equation (.account (first * second) value) (.account first (.account second value))
  | substituteAccount {Γ Δ : Ctx S} {sort : S.Srt}
      (env : Environment S (Raw Q accountSort base) Γ Δ)
      (word : SourceAccountSubstitution.Account Q accountSort Γ)
      (value : Raw Q accountSort base Γ sort) :
      Equation (.substitute env (.account word value))
        (.account (SourceAccountSubstitution.substitute Q accountSort
          (fun s v => observe Q accountSort base (env s v)) word) (.substitute env value))

/-- Every prospective quotient equation is validated in the independent
target category, using the already proved full-environment binder laws. -/
theorem equation_sound (target : Model Q accountSort)
    (generator : base ⟶ (AccountBindingAlgebra.forget Q accountSort).obj target)
    {Γ : Ctx S} {sort : S.Srt} {left right : Raw Q accountSort base Γ sort}
    (equation : Equation Q accountSort base left right) :
    interpret Q accountSort base target generator left =
      interpret Q accountSort base target generator right := by
  cases equation with
  | substituteVariable env v =>
      exact interpret_substitute_variable Q accountSort base target generator env v
  | genOperation op args =>
      exact interpret_gen_operation Q accountSort base target generator op args
  | genSubstitute env value =>
      exact interpret_gen_substitute Q accountSort base target generator env value
  | substituteIdentity value =>
      exact substitute_identity_sound Q accountSort base target generator _
  | substituteComp first second value =>
      exact substitute_comp_sound Q accountSort base target generator first second value
  | substituteOperation env op args =>
      exact substitute_operation_sound Q accountSort base target generator env op args
  | accountOne value => exact account_one_sound Q accountSort base target generator _
  | accountMul first second value =>
      exact account_mul_sound Q accountSort base target generator first second _
  | substituteAccount env word value =>
      exact substitute_account_sound Q accountSort base target generator env word _

mutual

/-- A generated congruence derivation, kept as data before quotienting.
Substitution congruence retains a derivation for each typed variable value. -/
inductive Derivation : {Γ : Ctx S} → {sort : S.Srt} →
    Raw Q accountSort base Γ sort → Raw Q accountSort base Γ sort → Type u where
  | equation {Γ : Ctx S} {sort : S.Srt} {left right : Raw Q accountSort base Γ sort}
      (witness : Equation Q accountSort base left right) : Derivation left right
  | refl {Γ : Ctx S} {sort : S.Srt} (value : Raw Q accountSort base Γ sort) :
      Derivation value value
  | symm {Γ : Ctx S} {sort : S.Srt} {left right : Raw Q accountSort base Γ sort}
      (witness : Derivation left right) : Derivation right left
  | trans {Γ : Ctx S} {sort : S.Srt} {left middle right : Raw Q accountSort base Γ sort}
      (first : Derivation left middle) (second : Derivation middle right) : Derivation left right
  | operation {Γ : Ctx S} {sort : S.Srt} (op : S.Op sort)
      {left right : Arguments Q accountSort base (S.arity op) Γ}
      (witness : ArgumentDerivation left right) :
      Derivation (.operation op left) (.operation op right)
  | account {Γ : Ctx S} {sort : S.Srt}
      (word : SourceAccountSubstitution.Account Q accountSort Γ)
      {left right : Raw Q accountSort base Γ sort} (witness : Derivation left right) :
      Derivation (.account word left) (.account word right)
  | substitute {Γ Δ : Ctx S} {sort : S.Srt}
      {first second : Environment S (Raw Q accountSort base) Γ Δ}
      {left right : Raw Q accountSort base Γ sort}
      (environments : ∀ s v, Derivation (first s v) (second s v))
      (values : Derivation left right) :
      Derivation (.substitute first left) (.substitute second right)

/-- Ordered, binder-indexed argument congruence; equal source values at
different positions still have separate derivation components. -/
inductive ArgumentDerivation : {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    Arguments Q accountSort base arities Γ → Arguments Q accountSort base arities Γ → Type u where
  | nil {Γ : Ctx S} : ArgumentDerivation (.nil (Γ := Γ)) .nil
  | cons {binders : List S.Srt} {sort : S.Srt}
      {rest : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      {leftHead rightHead : Raw Q accountSort base (binders ++ Γ) sort}
      {leftTail rightTail : Arguments Q accountSort base rest Γ}
      (heads : Derivation leftHead rightHead)
      (tails : ArgumentDerivation leftTail rightTail) :
      ArgumentDerivation (.cons leftHead leftTail) (.cons rightHead rightTail)

end

mutual

theorem derivation_sound (target : Model Q accountSort)
    (generator : base ⟶ (AccountBindingAlgebra.forget Q accountSort).obj target) :
    ∀ {Γ : Ctx S} {sort : S.Srt} {left right : Raw Q accountSort base Γ sort},
      Derivation Q accountSort base left right →
        interpret Q accountSort base target generator left =
          interpret Q accountSort base target generator right
  | _, _, _, _, .equation witness => equation_sound Q accountSort base target generator witness
  | _, _, _, _, .refl _ => rfl
  | _, _, _, _, .symm witness => (derivation_sound target generator witness).symm
  | _, _, _, _, .trans first second =>
      (derivation_sound target generator first).trans (derivation_sound target generator second)
  | _, _, _, _, .operation op witness => congrArg (target.observed.left.operation op)
      (argumentDerivation_sound target generator witness)
  | _, _, _, _, .account word witness => congrArg (target.act word)
      (derivation_sound target generator witness)
  | _, _, _, _, .substitute environments values => by
      apply congrArg₂ target.observed.left.substitution.substitute
      · funext sort v
        exact derivation_sound target generator (environments sort v)
      · exact derivation_sound target generator values

theorem argumentDerivation_sound (target : Model Q accountSort)
    (generator : base ⟶ (AccountBindingAlgebra.forget Q accountSort).obj target) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      {left right : Arguments Q accountSort base arities Γ},
      ArgumentDerivation Q accountSort base left right →
        interpretArguments Q accountSort base target generator left =
          interpretArguments Q accountSort base target generator right
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons heads tails => congrArg₂ FamilyArgs.cons
      (derivation_sound target generator heads) (argumentDerivation_sound target generator tails)

end

/-- The source clone itself is a target with trivial action, observed by its
identity map.  This is only used to validate the immutable source readout. -/
def sourceTarget : Model Q accountSort :=
  AccountBindingAlgebra.pure Q accountSort (Over.mk (𝟙 Q))

def sourceGenerator : base ⟶
    (AccountBindingAlgebra.forget Q accountSort).obj (sourceTarget Q accountSort) := by
  change base ⟶ Over.mk (𝟙 Q)
  exact Over.homMk base.hom (by simp)

/-- Every generated derivation preserves the full source observation. -/
theorem derivation_observe {Γ : Ctx S} {sort : S.Srt}
    {left right : Raw Q accountSort base Γ sort}
    (witness : Derivation Q accountSort base left right) :
    observe Q accountSort base left = observe Q accountSort base right := by
  have sound := derivation_sound Q accountSort base (sourceTarget Q accountSort)
    (sourceGenerator Q accountSort base) witness
  have before := observe_interpret Q accountSort base (sourceTarget Q accountSort)
    (sourceGenerator Q accountSort base) left
  have after := observe_interpret Q accountSort base (sourceTarget Q accountSort)
    (sourceGenerator Q accountSort base) right
  exact before.symm.trans (sound.trans after)

/-- Semantic equality uses existence of an origin-bearing derivation.  The
raw trees and derivations remain separately available; no inverse is alleged. -/
def setoid (Γ : Ctx S) (sort : S.Srt) : Setoid (Raw Q accountSort base Γ sort) where
  r left right := Nonempty (Derivation Q accountSort base left right)
  iseqv :=
    { refl := fun value => ⟨.refl value⟩
      symm := fun ⟨witness⟩ => ⟨.symm witness⟩
      trans := fun ⟨first⟩ ⟨second⟩ => ⟨.trans first second⟩ }

#print axioms equation_sound
#print axioms derivation_sound
#print axioms derivation_observe
#print axioms setoid

end Mettapedia.GSLT.LanguageDef.Cost.AccountBindingCongruence
