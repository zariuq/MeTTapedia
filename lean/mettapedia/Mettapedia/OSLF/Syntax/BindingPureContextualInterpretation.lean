import Mettapedia.OSLF.Syntax.BindingCloneFoldSubstitution
import Mettapedia.OSLF.Syntax.SemanticContextualMetavariables

/-!
# Pure schemas at arbitrary semantic environments

An embedded ordinary term has no metavariable operators. Its contextual
interpretation is the free binding fold followed by substitution of the full
ordinary semantic environment. The separate ambient environment remains
available, but cannot affect an embedded term without metavariables.

The argument proof retains every declared binding prefix and uses the actual
semantic lift of the supplied environment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingPureContextualInterpretation

open BindingSubstitutionAlgebra FreeBindingTerms SemanticContextualMetavariables

universe u

variable {S : Signature} (algebra : BindingCloneAlgebra.Algebra.{u} S)

mutual

theorem interpret_embed {Θ Ξ Γ : Ctx S}
    (bodies : Valuation (M := []) algebra Θ)
    (ambient : Environment S algebra.substitution.Carrier Θ Γ)
    (ordinary : Environment S algebra.substitution.Carrier Ξ Γ) :
    ∀ {sort : S.Srt} (value : Term S Ξ sort),
      interpretSchema algebra bodies ambient ordinary (embed (M := []) value) =
        algebra.substitution.substitute ordinary
          (BindingCloneFoldSubstitution.interpret algebra value)
  | _, .var position => (algebra.substitution.substitute_var ordinary position).symm
  | _, .op operator arguments => by
      change algebra.operation operator (interpretArgs algebra bodies ambient ordinary
          (embedArgs arguments)) =
        algebra.substitution.substitute ordinary
          (algebra.operation operator (BindingCloneFoldSubstitution.interpretArgs algebra arguments))
      rw [algebra.operation_substitute]
      exact congrArg (algebra.operation operator)
        (interpretArgs_embed bodies ambient ordinary arguments)

theorem interpretArgs_embed {Θ Ξ Γ : Ctx S}
    (bodies : Valuation (M := []) algebra Θ)
    (ambient : Environment S algebra.substitution.Carrier Θ Γ)
    (ordinary : Environment S algebra.substitution.Carrier Ξ Γ) :
    ∀ {arity : List (List S.Srt × S.Srt)} (values : Args S arity Ξ),
      interpretArgs algebra bodies ambient ordinary (embedArgs (M := []) values) =
        algebra.substitution.substituteArgs ordinary
          (BindingCloneFoldSubstitution.interpretArgs algebra values)
  | _, .nil => rfl
  | _, .cons (bs := binders) head tail => by
      change FamilyArgs.cons
          (interpretSchema algebra bodies (weakenEnvironment algebra binders ambient)
            (algebra.substitution.liftEnvironment ordinary binders) (embed head))
          (interpretArgs algebra bodies ambient ordinary (embedArgs tail)) =
        FamilyArgs.cons
          (algebra.substitution.substitute (algebra.substitution.liftEnvironment ordinary binders)
            (BindingCloneFoldSubstitution.interpret algebra head))
          (algebra.substitution.substituteArgs ordinary
            (BindingCloneFoldSubstitution.interpretArgs algebra tail))
      exact congrArg₂ FamilyArgs.cons
        (interpret_embed bodies (weakenEnvironment algebra binders ambient)
          (algebra.substitution.liftEnvironment ordinary binders) head)
        (interpretArgs_embed bodies ambient ordinary tail)

end

end Mettapedia.OSLF.Binding.BindingPureContextualInterpretation
