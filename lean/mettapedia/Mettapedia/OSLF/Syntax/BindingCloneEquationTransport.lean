import Mettapedia.OSLF.Syntax.BindingEquationInterpretation

/-!
# First-order equation instances in arbitrary target environments

A full clone morphism preserves the interpretation of every ordinary scoped
term. A source equation between such interpretations therefore holds after
any target substitution, including values outside the morphism's image.
This does not assert satisfaction for arbitrary target metavariable bodies:
the transported equation has ordinary term variables.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingCloneEquationTransport

open FreeBindingClone BindingCloneFoldSubstitution BindingSubstitutionAlgebra

universe u v

variable {S : Signature}
  {A : BindingCloneAlgebra.Algebra.{u} S} {B : BindingCloneAlgebra.Algebra.{v} S}

/-- Initiality identifies the composite source fold with the target fold. -/
theorem interpret_naturality (h : FreeBindingClone.Hom A B)
    {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) :
    h.raw.map (interpret A term) = interpret B term := by
  exact congrArg (fun arrow : FreeBindingClone.Hom (BindingCloneAlgebra.terms S) B =>
    arrow.raw.map term) (FreeBindingClone.hom_unique B
      (FreeBindingClone.Hom.comp (FreeBindingClone.interpretHom A) h))

/-- A source term equation holds under every target substitution. Target
environment values need not be images of source elements. -/
theorem target_environment_equation (h : FreeBindingClone.Hom A B)
    {Γ Δ : Ctx S} {sort : S.Srt} {left right : Term S Γ sort}
    (sourceEquation : interpret A left = interpret A right)
    (env : Environment S B.substitution.Carrier Γ Δ) :
    B.substitution.substitute env (interpret B left) =
      B.substitution.substitute env (interpret B right) := by
  apply congrArg (B.substitution.substitute env)
  exact (interpret_naturality h left).symm.trans
    ((congrArg h.raw.map sourceEquation).trans (interpret_naturality h right))

/-- Every proved ordinary-term instance of an authored source equation
transports, then admits arbitrary target substitution values. This is
stronger than restricting the target environment to mapped source values. -/
theorem target_environment_eqClosure (h : FreeBindingClone.Hom A B)
    {M : List (MetaArity S)} {equations : List (EqAxiom S M)}
    (satisfies : BindingEquationInterpretation.Satisfies A equations)
    {Γ Δ : Ctx S} {sort : S.Srt} {left right : Term S Γ sort}
    (equation : EqClosure equations left right)
    (env : Environment S B.substitution.Carrier Γ Δ) :
    B.substitution.substitute env (interpret B left) =
      B.substitution.substitute env (interpret B right) :=
  target_environment_equation h
    (BindingEquationInterpretation.interpret_eqClosure A satisfies equation) env

end Mettapedia.OSLF.Binding.BindingCloneEquationTransport
