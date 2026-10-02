import Mettapedia.OSLF.Syntax.RawRelativeBindingExtension

/-!
# Full binder transport for relative expressions

Each original or added operator receives its entire typed argument vector.
An explicit raw substitution lifts under every argument's exact binder list.
The equations below hold in every independently specified target clone under
every genuine generator morphism, including environments with added nodes.
No quotient or free object is assumed by these soundness proofs.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RawRelativeBindingLaws

open FreeBindingTerms BindingSubstitutionAlgebra SecondOrderContext
open RawRelativeBindingExtension

universe u v

variable {S : Signature} (extension : Object S)
  (base : BindingCloneAlgebra.Algebra.{u} S)

abbrev Raw := Expression extension base

def weaken {Γ : Ctx S} {sort fresh : S.Srt}
    (value : Raw extension base Γ sort) : Raw extension base (fresh :: Γ) sort :=
  .substitute (fun _ index => injectVariable extension base (.succ index)) value

def liftEnvironment {Γ Δ : Ctx S}
    (environment : Environment S (Raw extension base) Γ Δ) :
    (binders : List S.Srt) →
      Environment S (Raw extension base) (binders ++ Γ) (binders ++ Δ)
  | [] => environment
  | _ :: binders => fun _ index => match index with
    | .zero => injectVariable extension base .zero
    | .succ old => weaken extension base (liftEnvironment environment binders _ old)

def substituteArguments {Γ Δ : Ctx S}
    (environment : Environment S (Raw extension base) Γ Δ) :
    {arities : List (List S.Srt × S.Srt)} →
      Arguments extension base arities Γ → Arguments extension base arities Δ
  | _, .nil => .nil
  | _, .cons (binders := binders) head tail =>
      .cons (.substitute (liftEnvironment extension base environment binders) head)
        (substituteArguments environment tail)

variable (target : BindingCloneAlgebra.Algebra.{v} (withMetas S extension.arities))
  (generator : FreeBindingClone.Hom base (restrictAlgebra extension target))

def interpretedEnvironment {Γ Δ : Ctx S}
    (environment : Environment S (Raw extension base) Γ Δ) :
    Environment (withMetas S extension.arities) target.substitution.Carrier Γ Δ :=
  fun sort index => interpret extension base target generator (environment sort index)

theorem interpret_weaken {Γ : Ctx S} {sort fresh : S.Srt}
    (value : Raw extension base Γ sort) :
    interpret extension base target generator (weaken extension base (fresh := fresh) value) =
      target.substitution.weaken (interpret extension base target generator value) := by
  change target.substitution.substitute
      (fun s index => interpret extension base target generator
        (injectVariable extension base (.succ index)))
      (interpret extension base target generator value) =
    target.substitution.substitute (fun _ index => target.substitution.injectVar (.succ index))
      (interpret extension base target generator value)
  apply congrArg (fun environment => target.substitution.substitute environment
    (interpret extension base target generator value))
  funext sort index
  exact interpret_variable extension base target generator (.succ index)

theorem interpret_liftEnvironment {Γ Δ : Ctx S}
    (environment : Environment S (Raw extension base) Γ Δ) :
    ∀ binders,
      interpretedEnvironment extension base target generator
          (liftEnvironment extension base environment binders) =
        target.substitution.liftEnvironment
          (interpretedEnvironment extension base target generator environment) binders
  | [] => rfl
  | _ :: binders => by
      funext sort index
      cases index with
      | zero => exact interpret_variable extension base target generator .zero
      | succ old =>
          change interpret extension base target generator
              (weaken extension base (liftEnvironment extension base environment binders sort old)) =
            target.substitution.weaken
              (target.substitution.liftEnvironment
                (interpretedEnvironment extension base target generator environment) binders sort old)
          exact (interpret_weaken extension base target generator _).trans
            (congrArg target.substitution.weaken
              (congrFun (congrFun (interpret_liftEnvironment environment binders) sort) old))

theorem interpret_substituteArguments {Γ Δ : Ctx S}
    (environment : Environment S (Raw extension base) Γ Δ) :
    ∀ {arities : List (List S.Srt × S.Srt)}
      (arguments : Arguments extension base arities Γ),
      interpretArguments extension base target generator
          (substituteArguments extension base environment arguments) =
        target.substitution.substituteArgs
          (interpretedEnvironment extension base target generator environment)
          (interpretArguments extension base target generator arguments)
  | _, .nil => rfl
  | _, .cons (binders := binders) head tail => by
      change FamilyArgs.cons
          (target.substitution.substitute
            (interpretedEnvironment extension base target generator
              (liftEnvironment extension base environment binders))
            (interpret extension base target generator head))
          (interpretArguments extension base target generator
            (substituteArguments extension base environment tail)) =
        FamilyArgs.cons
          (target.substitution.substitute
            (target.substitution.liftEnvironment
              (interpretedEnvironment extension base target generator environment) binders)
            (interpret extension base target generator head))
          (target.substitution.substituteArgs
            (interpretedEnvironment extension base target generator environment)
            (interpretArguments extension base target generator tail))
      exact congrArg₂ FamilyArgs.cons
        (congrArg (fun lifted => target.substitution.substitute lifted
            (interpret extension base target generator head))
          (interpret_liftEnvironment extension base target generator environment binders))
        (interpret_substituteArguments environment tail)

theorem substitute_identity_sound {Γ : Ctx S} {sort : S.Srt}
    (value : Raw extension base Γ sort) :
    interpret extension base target generator
        (.substitute (fun _ index => injectVariable extension base index) value) =
      interpret extension base target generator value := by
  have identity : interpretedEnvironment extension base target generator
      (Γ := Γ) (Δ := Γ) (fun _ index => injectVariable extension base index) =
        (fun _ index => target.substitution.injectVar index) := by
    funext sort index
    exact interpret_variable extension base target generator index
  change target.substitution.substitute
      (interpretedEnvironment extension base target generator
        (fun _ index => injectVariable extension base index))
      (interpret extension base target generator value) = _
  rw [identity]
  exact target.substitution.substitute_identity _

theorem substitute_comp_sound {Γ Δ Θ : Ctx S} {sort : S.Srt}
    (first : Environment S (Raw extension base) Γ Δ)
    (second : Environment S (Raw extension base) Δ Θ)
    (value : Raw extension base Γ sort) :
    interpret extension base target generator (.substitute second (.substitute first value)) =
      interpret extension base target generator
        (.substitute (fun sort index => .substitute second (first sort index)) value) :=
  target.substitution.substitute_comp _ _ _

/-- This includes every added operator, rather than proving substitution
compatibility only for the original signature. -/
theorem substitute_operation_sound {Γ Δ : Ctx S} {sort : S.Srt}
    (environment : Environment S (Raw extension base) Γ Δ)
    (operator : (withMetas S extension.arities).Op sort)
    (arguments : Arguments extension base ((withMetas S extension.arities).arity operator) Γ) :
    interpret extension base target generator (.substitute environment (.operation operator arguments)) =
      interpret extension base target generator
        (.operation operator (substituteArguments extension base environment arguments)) := by
  exact (target.operation_substitute
    (interpretedEnvironment extension base target generator environment) operator
    (interpretArguments extension base target generator arguments)).trans
      (congrArg (target.operation operator)
        (interpret_substituteArguments extension base target generator environment arguments).symm)

end Mettapedia.OSLF.Binding.RawRelativeBindingLaws
