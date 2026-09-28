import Mettapedia.OSLF.Syntax.BindingSubstitutionAlgebra

/-!
# Binding operators over a semantic substitution algebra

An algebra of a binding signature needs more than raw constructors and more
than a clone. Its operations must commute with simultaneous substitution,
using the environment lifted beneath each argument's declared binders.
The actual intrinsically scoped terms satisfy this law, by the existing
`bindArgs` case and the proved semantic/syntactic lift comparison.

This is a model interface for the terms rung. Semantic metavariable
valuations, equation satisfaction, and the free equational quotient remain
to be constructed; no quotient universal property is assumed here.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingCloneAlgebra

open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.FreeBindingTerms

universe u

variable {S : Signature}

/-- A clone with every authored binding operator, satisfying the standard
substitution compatibility law at all contexts and argument binder lists. -/
structure Algebra (S : Signature) where
  substitution : BindingSubstitutionAlgebra.Algebra.{u} S
  operation : {Γ : Ctx S} → {s : S.Srt} → (o : S.Op s) →
    FamilyArgs S substitution.Carrier (S.arity o) Γ →
      substitution.Carrier Γ s
  operation_substitute : ∀ {Γ Δ : Ctx S} {s : S.Srt}
    (env : Environment S substitution.Carrier Γ Δ)
    (o : S.Op s)
    (args : FamilyArgs S substitution.Carrier (S.arity o) Γ),
    substitution.substitute env (operation o args) =
      operation o (substitution.substituteArgs env args)

/-- Forget semantic substitution while retaining the same constructor
interpretation, so the raw initial fold applies to this stronger model. -/
def Algebra.toRaw (A : Algebra.{u} S) : FreeBindingTerms.Algebra.{u} S where
  Carrier := A.substitution.Carrier
  injectVar := A.substitution.injectVar
  operation := A.operation

/-- The argument packaging map is compatible with `bindArgs` for an
arbitrary semantic argument vector in the actual term algebra. -/
theorem familyToSyntax_substituteArgs {Γ Δ : Ctx S}
    (sigma : Sub S Γ Δ) :
    ∀ {arity : List (List S.Srt × S.Srt)}
      (args : FamilyArgs S (Term S) arity Γ),
      (FreeBindingTerms.terms.familyToSyntax S)
        ((BindingSubstitutionAlgebra.terms S).substituteArgs sigma args) =
      bindArgs sigma ((FreeBindingTerms.terms.familyToSyntax S) args)
  | _, .nil => rfl
  | _, .cons (bs := binders) head tail => by
      simp only [FreeBindingTerms.terms.familyToSyntax,
        BindingSubstitutionAlgebra.Algebra.substituteArgs, bindArgs]
      rw [terms_liftEnvironment_eq_liftSub sigma binders]
      exact congrArg (Args.cons (bind (liftSub sigma binders) head))
        (familyToSyntax_substituteArgs sigma tail)

/-- The existing term constructors, clone substitution and binding lifts
form an actual binding-clone algebra. -/
def terms (S : Signature) : Algebra S where
  substitution := BindingSubstitutionAlgebra.terms S
  operation := fun o args => Term.op o
    ((FreeBindingTerms.terms.familyToSyntax S) args)
  operation_substitute := by
    intro Γ Δ s sigma o args
    change bind sigma (Term.op o ((FreeBindingTerms.terms.familyToSyntax S) args)) =
      Term.op o ((FreeBindingTerms.terms.familyToSyntax S)
        ((BindingSubstitutionAlgebra.terms S).substituteArgs sigma args))
    change Term.op o (bindArgs sigma
      ((FreeBindingTerms.terms.familyToSyntax S) args)) =
      Term.op o ((FreeBindingTerms.terms.familyToSyntax S)
        ((BindingSubstitutionAlgebra.terms S).substituteArgs sigma args))
    exact congrArg (Term.op o) (familyToSyntax_substituteArgs sigma args).symm

end Mettapedia.OSLF.Binding.BindingCloneAlgebra
