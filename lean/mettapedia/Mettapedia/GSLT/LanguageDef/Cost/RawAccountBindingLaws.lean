import Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingExtension

/-!
# Binder lifts and sound equations for relative account expressions

Raw weakening and lifting retain full substitution expressions.  In every
independently specified target accounted clone, interpretation gives its
actual semantic binder lift and substitution.  The equations validated here
are the prospective generators of a quotient; none is imposed merely because
it is wanted, and no quotient or free adjunction is asserted in this module.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingLaws

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open BindingSubstitutionAlgebra
open AccountBindingAlgebra
open FreeBindingTerms
open RawAccountBindingExtension

universe u

variable {S : Signature} (Q : BindingCloneAlgebra.Algebra.{u} S)
  (accountSort : S.Srt) (base : Over Q)

abbrev Raw := Expression Q accountSort base

/-- Weaken by retaining an explicit substitution expression.  Accounts in
the value are transported by the later equations, not silently relabelled. -/
def weaken {Γ : Ctx S} {sort fresh : S.Srt} (value : Raw Q accountSort base Γ sort) :
    Raw Q accountSort base (fresh :: Γ) sort :=
  .substitute (fun _ v => sourceVariable Q accountSort base (.succ v)) value

/-- Lift the entire typed marked environment beneath each declared binder. -/
def liftEnvironment {Γ Δ : Ctx S}
    (env : Environment S (Raw Q accountSort base) Γ Δ) :
    (binders : List S.Srt) →
      Environment S (Raw Q accountSort base) (binders ++ Γ) (binders ++ Δ)
  | [] => env
  | _ :: binders => fun _ v => match v with
    | .zero => sourceVariable Q accountSort base .zero
    | .succ old => weaken Q accountSort base (liftEnvironment env binders _ old)

/-- Substitute each argument under its exact binder prefix. -/
def substituteArguments {Γ Δ : Ctx S}
    (env : Environment S (Raw Q accountSort base) Γ Δ) :
    {arities : List (List S.Srt × S.Srt)} →
      Arguments Q accountSort base arities Γ → Arguments Q accountSort base arities Δ
  | _, .nil => .nil
  | _, .cons (binders := binders) head tail =>
      .cons (.substitute (liftEnvironment Q accountSort base env binders) head)
        (substituteArguments env tail)

variable (target : Model Q accountSort)
  (generator : base ⟶ (AccountBindingAlgebra.forget Q accountSort).obj target)

/-- Interpret the entire environment, preserving every marked value. -/
def interpretedEnvironment {Γ Δ : Ctx S}
    (env : Environment S (Raw Q accountSort base) Γ Δ) :
    Environment S target.observed.left.substitution.Carrier Γ Δ :=
  fun sort v => interpret Q accountSort base target generator (env sort v)

theorem interpret_sourceVariable {Γ : Ctx S} {sort : S.Srt} (v : Var Γ sort) :
    interpret Q accountSort base target generator (sourceVariable Q accountSort base v) =
      target.observed.left.substitution.injectVar v :=
  generator.left.raw.map_variable v

theorem interpret_weaken {Γ : Ctx S} {sort fresh : S.Srt}
    (value : Raw Q accountSort base Γ sort) :
    interpret Q accountSort base target generator
        (weaken Q accountSort base (fresh := fresh) value) =
      target.observed.left.substitution.weaken
        (interpret Q accountSort base target generator value) := by
  change target.observed.left.substitution.substitute
      (fun s v => interpret Q accountSort base target generator
        (sourceVariable Q accountSort base (.succ v)))
      (interpret Q accountSort base target generator value) =
    target.observed.left.substitution.substitute
      (fun _ v => target.observed.left.substitution.injectVar (.succ v))
      (interpret Q accountSort base target generator value)
  apply congrArg (fun env => target.observed.left.substitution.substitute env
    (interpret Q accountSort base target generator value))
  funext sort v
  exact interpret_sourceVariable Q accountSort base target generator (.succ v)

theorem interpret_liftEnvironment {Γ Δ : Ctx S}
    (env : Environment S (Raw Q accountSort base) Γ Δ) :
    ∀ binders,
      interpretedEnvironment Q accountSort base target generator
          (liftEnvironment Q accountSort base env binders) =
        target.observed.left.substitution.liftEnvironment
          (interpretedEnvironment Q accountSort base target generator env) binders
  | [] => rfl
  | _ :: binders => by
      funext sort v
      cases v with
      | zero => exact interpret_sourceVariable Q accountSort base target generator .zero
      | succ old =>
          change interpret Q accountSort base target generator
              (weaken Q accountSort base
                (liftEnvironment Q accountSort base env binders sort old)) =
            target.observed.left.substitution.weaken
              (target.observed.left.substitution.liftEnvironment
                (interpretedEnvironment Q accountSort base target generator env)
                binders sort old)
          exact (interpret_weaken Q accountSort base target generator _).trans
            (congrArg target.observed.left.substitution.weaken
              (congrFun (congrFun
                (interpret_liftEnvironment env binders) sort) old))

theorem interpret_substituteArguments {Γ Δ : Ctx S}
    (env : Environment S (Raw Q accountSort base) Γ Δ) :
    ∀ {arities : List (List S.Srt × S.Srt)}
      (args : Arguments Q accountSort base arities Γ),
      interpretArguments Q accountSort base target generator
          (substituteArguments Q accountSort base env args) =
        target.observed.left.substitution.substituteArgs
          (interpretedEnvironment Q accountSort base target generator env)
          (interpretArguments Q accountSort base target generator args)
  | _, .nil => rfl
  | _, .cons (binders := binders) head tail => by
      change FamilyArgs.cons
          (target.observed.left.substitution.substitute
            (interpretedEnvironment Q accountSort base target generator
              (liftEnvironment Q accountSort base env binders))
            (interpret Q accountSort base target generator head))
          (interpretArguments Q accountSort base target generator
            (substituteArguments Q accountSort base env tail)) =
        FamilyArgs.cons
          (target.observed.left.substitution.substitute
            (target.observed.left.substitution.liftEnvironment
              (interpretedEnvironment Q accountSort base target generator env) binders)
            (interpret Q accountSort base target generator head))
          (target.observed.left.substitution.substituteArgs
            (interpretedEnvironment Q accountSort base target generator env)
            (interpretArguments Q accountSort base target generator tail))
      exact congrArg₂ FamilyArgs.cons
        (congrArg (fun lifted => target.observed.left.substitution.substitute lifted
            (interpret Q accountSort base target generator head))
          (interpret_liftEnvironment Q accountSort base target generator env binders))
        (interpret_substituteArguments env tail)

/-- The source environment of the interpreted values is exactly their raw
source observation.  No source commitment is asserted constant under binders. -/
theorem source_interpretedEnvironment {Γ Δ : Ctx S}
    (env : Environment S (Raw Q accountSort base) Γ Δ) :
    AccountBindingAlgebra.sourceEnvironment Q accountSort target
        (interpretedEnvironment Q accountSort base target generator env) =
      (fun sort v => observe Q accountSort base (env sort v)) := by
  funext sort v
  exact observe_interpret Q accountSort base target generator (env sort v)

theorem substitute_identity_sound {Γ : Ctx S} {sort : S.Srt}
    (value : Raw Q accountSort base Γ sort) :
    interpret Q accountSort base target generator
        (.substitute (fun _ v => sourceVariable Q accountSort base v) value) =
      interpret Q accountSort base target generator value := by
  have envIdentity : interpretedEnvironment Q accountSort base target generator
      (Γ := Γ) (Δ := Γ) (fun _ v => sourceVariable Q accountSort base v) =
        (fun _ v => target.observed.left.substitution.injectVar v) := by
    funext sort v
    exact interpret_sourceVariable Q accountSort base target generator v
  change target.observed.left.substitution.substitute
      (interpretedEnvironment Q accountSort base target generator
        (fun _ v => sourceVariable Q accountSort base v))
      (interpret Q accountSort base target generator value) = _
  rw [envIdentity]
  exact target.observed.left.substitution.substitute_identity _

theorem substitute_comp_sound {Γ Δ Θ : Ctx S} {sort : S.Srt}
    (first : Environment S (Raw Q accountSort base) Γ Δ)
    (second : Environment S (Raw Q accountSort base) Δ Θ)
    (value : Raw Q accountSort base Γ sort) :
    interpret Q accountSort base target generator (.substitute second (.substitute first value)) =
      interpret Q accountSort base target generator
        (.substitute (fun s v => .substitute second (first s v)) value) :=
  target.observed.left.substitution.substitute_comp _ _ _

theorem substitute_operation_sound {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S (Raw Q accountSort base) Γ Δ)
    (op : S.Op sort) (args : Arguments Q accountSort base (S.arity op) Γ) :
    interpret Q accountSort base target generator (.substitute env (.operation op args)) =
      interpret Q accountSort base target generator
        (.operation op (substituteArguments Q accountSort base env args)) := by
  exact (target.observed.left.operation_substitute
    (interpretedEnvironment Q accountSort base target generator env) op
    (interpretArguments Q accountSort base target generator args)).trans
      (congrArg (target.observed.left.operation op)
        (interpret_substituteArguments Q accountSort base target generator env args).symm)

theorem account_one_sound {Γ : Ctx S} {sort : S.Srt}
    (value : Raw Q accountSort base Γ sort) :
    interpret Q accountSort base target generator (.account 1 value) =
      interpret Q accountSort base target generator value := target.act_one _

theorem account_mul_sound {Γ : Ctx S} {sort : S.Srt}
    (first second : SourceAccountSubstitution.Account Q accountSort Γ)
    (value : Raw Q accountSort base Γ sort) :
    interpret Q accountSort base target generator (.account (first * second) value) =
      interpret Q accountSort base target generator (.account first (.account second value)) :=
  target.act_mul first second _

theorem substitute_account_sound {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S (Raw Q accountSort base) Γ Δ)
    (word : SourceAccountSubstitution.Account Q accountSort Γ)
    (value : Raw Q accountSort base Γ sort) :
    interpret Q accountSort base target generator (.substitute env (.account word value)) =
      interpret Q accountSort base target generator
        (.account (SourceAccountSubstitution.substitute Q accountSort
          (fun s v => observe Q accountSort base (env s v)) word)
          (.substitute env value)) := by
  have valid := target.act_substitute
    (interpretedEnvironment Q accountSort base target generator env) word
    (interpret Q accountSort base target generator value)
  change target.observed.left.substitution.substitute
      (interpretedEnvironment Q accountSort base target generator env)
      (target.act word (interpret Q accountSort base target generator value)) =
    target.act (SourceAccountSubstitution.substitute Q accountSort
      (fun s v => observe Q accountSort base (env s v)) word)
      (target.observed.left.substitution.substitute
        (interpretedEnvironment Q accountSort base target generator env)
        (interpret Q accountSort base target generator value))
  apply valid.trans
  apply congrArg (fun transported => target.act transported
    (target.observed.left.substitution.substitute
      (interpretedEnvironment Q accountSort base target generator env)
      (interpret Q accountSort base target generator value)))
  apply congrArg (fun sourceEnv => SourceAccountSubstitution.substitute Q accountSort sourceEnv word)
  exact source_interpretedEnvironment Q accountSort base target generator env

#print axioms interpret_liftEnvironment
#print axioms interpret_substituteArguments
#print axioms substitute_identity_sound
#print axioms substitute_comp_sound
#print axioms substitute_operation_sound
#print axioms substitute_account_sound

end Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingLaws
