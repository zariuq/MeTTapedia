import Mettapedia.OSLF.Syntax.RawRelativeBindingLaws
import Mettapedia.OSLF.Syntax.BindingFirstOrderFamilyTransport

/-!
# Generated congruence for a relative binding extension

Generator equations preserve the supplied clone's actual operations and
substitution. The clone equations use every extended operator and whole raw
environment values. Extra first-order equations enter at their canonical
variable instances; substitution congruence supplies all other instances.

Every generator and congruence derivation is checked in an independently
specified target satisfying the extra equations. The derivations and raw
expressions remain data, separate from their later quotient classes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RelativeBindingCongruence

open FreeBindingTerms BindingSubstitutionAlgebra SecondOrderContext
open RawRelativeBindingExtension RawRelativeBindingLaws

universe u v

variable {S : Signature} (extension : Object S)
  (base : BindingCloneAlgebra.Algebra.{u} S)
  (family : EqAxiom (withMetas S extension.arities) [] → Prop)

inductive Equation : {Γ : Ctx S} → {sort : S.Srt} →
    Raw extension base Γ sort → Raw extension base Γ sort → Type u where
  | substituteVariable {Γ Δ : Ctx S} {sort : S.Srt}
      (environment : Environment S (Raw extension base) Γ Δ) (index : Var Γ sort) :
      Equation (.substitute environment (injectVariable extension base index)) (environment sort index)
  | genOperation {Γ : Ctx S} {sort : S.Srt} (operator : S.Op sort)
      (arguments : FamilyArgs S base.substitution.Carrier (S.arity operator) Γ) :
      Equation (.gen (base.operation operator arguments))
        (.operation (.inl operator) (genArguments extension base arguments))
  | genSubstitute {Γ Δ : Ctx S} {sort : S.Srt}
      (environment : Environment S base.substitution.Carrier Γ Δ)
      (value : base.substitution.Carrier Γ sort) :
      Equation (.gen (base.substitution.substitute environment value))
        (.substitute (fun sort index => .gen (environment sort index)) (.gen value))
  | substituteIdentity {Γ : Ctx S} {sort : S.Srt} (value : Raw extension base Γ sort) :
      Equation (.substitute (fun _ index => injectVariable extension base index) value) value
  | substituteComp {Γ Δ Θ : Ctx S} {sort : S.Srt}
      (first : Environment S (Raw extension base) Γ Δ)
      (second : Environment S (Raw extension base) Δ Θ) (value : Raw extension base Γ sort) :
      Equation (.substitute second (.substitute first value))
        (.substitute (fun sort index => .substitute second (first sort index)) value)
  | substituteOperation {Γ Δ : Ctx S} {sort : S.Srt}
      (environment : Environment S (Raw extension base) Γ Δ)
      (operator : (withMetas S extension.arities).Op sort)
      (arguments : Arguments extension base ((withMetas S extension.arities).arity operator) Γ) :
      Equation (.substitute environment (.operation operator arguments))
        (.operation operator (substituteArguments extension base environment arguments))
  | declared (equation : EqAxiom (withMetas S extension.arities) []) (admitted : family equation) :
      Equation (ofTerm extension base (BaseEquation.ofEmptySchema equation).left)
        (ofTerm extension base (BaseEquation.ofEmptySchema equation).right)

theorem equation_sound
    (target : BindingCloneAlgebra.Algebra.{v} (withMetas S extension.arities))
    (satisfaction : BindingEquationFamilyModel.Satisfies target family)
    (generator : FreeBindingClone.Hom base (restrictAlgebra extension target))
    {Γ : Ctx S} {sort : S.Srt} {left right : Raw extension base Γ sort}
    (equation : Equation extension base family left right) :
    interpret extension base target generator left =
      interpret extension base target generator right := by
  cases equation with
  | substituteVariable environment index =>
      exact interpret_substitute_variable extension base target generator environment index
  | genOperation operator arguments =>
      exact interpret_gen_operation extension base target generator operator arguments
  | genSubstitute environment value =>
      exact interpret_gen_substitute extension base target generator environment value
  | substituteIdentity value => exact substitute_identity_sound extension base target generator _
  | substituteComp first second value =>
      exact substitute_comp_sound extension base target generator first second value
  | substituteOperation environment operator arguments =>
      exact substitute_operation_sound extension base target generator environment operator arguments
  | declared equation admitted =>
      exact (interpret_ofTerm extension base target generator _).trans
        ((BindingFirstOrderFamilyTransport.canonical_of_contextual target satisfaction equation admitted).trans
          (interpret_ofTerm extension base target generator _).symm)

mutual

inductive Derivation : {Γ : Ctx S} → {sort : S.Srt} →
    Raw extension base Γ sort → Raw extension base Γ sort → Type u where
  | equation {Γ : Ctx S} {sort : S.Srt} {left right : Raw extension base Γ sort}
      (witness : Equation extension base family left right) : Derivation left right
  | refl {Γ : Ctx S} {sort : S.Srt} (value : Raw extension base Γ sort) : Derivation value value
  | symm {Γ : Ctx S} {sort : S.Srt} {left right : Raw extension base Γ sort}
      (witness : Derivation left right) : Derivation right left
  | trans {Γ : Ctx S} {sort : S.Srt} {left middle right : Raw extension base Γ sort}
      (first : Derivation left middle) (second : Derivation middle right) : Derivation left right
  | operation {Γ : Ctx S} {sort : S.Srt}
      (operator : (withMetas S extension.arities).Op sort)
      {left right : Arguments extension base ((withMetas S extension.arities).arity operator) Γ}
      (witness : ArgumentDerivation left right) :
      Derivation (.operation operator left) (.operation operator right)
  | substitute {Γ Δ : Ctx S} {sort : S.Srt}
      {first second : Environment S (Raw extension base) Γ Δ}
      {left right : Raw extension base Γ sort}
      (environments : ∀ sort index, Derivation (first sort index) (second sort index))
      (values : Derivation left right) :
      Derivation (.substitute first left) (.substitute second right)

inductive ArgumentDerivation : {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    Arguments extension base arities Γ → Arguments extension base arities Γ → Type u where
  | nil {Γ : Ctx S} : ArgumentDerivation (.nil (Γ := Γ)) .nil
  | cons {binders : List S.Srt} {sort : S.Srt}
      {rest : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      {leftHead rightHead : Raw extension base (binders ++ Γ) sort}
      {leftTail rightTail : Arguments extension base rest Γ}
      (heads : Derivation leftHead rightHead) (tails : ArgumentDerivation leftTail rightTail) :
      ArgumentDerivation (.cons leftHead leftTail) (.cons rightHead rightTail)

end

mutual

theorem derivation_sound
    (target : BindingCloneAlgebra.Algebra.{v} (withMetas S extension.arities))
    (satisfaction : BindingEquationFamilyModel.Satisfies target family)
    (generator : FreeBindingClone.Hom base (restrictAlgebra extension target)) :
    ∀ {Γ : Ctx S} {sort : S.Srt} {left right : Raw extension base Γ sort},
      Derivation extension base family left right →
        interpret extension base target generator left = interpret extension base target generator right
  | _, _, _, _, .equation witness => equation_sound extension base family target satisfaction generator witness
  | _, _, _, _, .refl _ => rfl
  | _, _, _, _, .symm witness => (derivation_sound target satisfaction generator witness).symm
  | _, _, _, _, .trans first second =>
      (derivation_sound target satisfaction generator first).trans
        (derivation_sound target satisfaction generator second)
  | _, _, _, _, .operation operator witness => congrArg (target.operation operator)
      (argumentDerivation_sound target satisfaction generator witness)
  | _, _, _, _, .substitute environments values => by
      apply congrArg₂ target.substitution.substitute
      · funext sort index
        exact derivation_sound target satisfaction generator (environments sort index)
      · exact derivation_sound target satisfaction generator values

theorem argumentDerivation_sound
    (target : BindingCloneAlgebra.Algebra.{v} (withMetas S extension.arities))
    (satisfaction : BindingEquationFamilyModel.Satisfies target family)
    (generator : FreeBindingClone.Hom base (restrictAlgebra extension target)) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      {left right : Arguments extension base arities Γ},
      ArgumentDerivation extension base family left right →
        interpretArguments extension base target generator left =
          interpretArguments extension base target generator right
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons heads tails =>
      congrArg₂ FamilyArgs.cons (derivation_sound target satisfaction generator heads)
        (argumentDerivation_sound target satisfaction generator tails)

end

def setoid (Γ : Ctx S) (sort : S.Srt) : Setoid (Raw extension base Γ sort) where
  r left right := Nonempty (Derivation extension base family left right)
  iseqv :=
    { refl := fun value => ⟨.refl value⟩
      symm := fun ⟨witness⟩ => ⟨.symm witness⟩
      trans := fun ⟨first⟩ ⟨second⟩ => ⟨.trans first second⟩ }

end Mettapedia.OSLF.Binding.RelativeBindingCongruence
