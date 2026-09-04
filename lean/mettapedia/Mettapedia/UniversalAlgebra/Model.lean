import Mettapedia.UniversalAlgebra.Signature

/-!
# Models and evaluation of universal-algebra terms
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

universe u v

variable {S : Signature.{u}}

/-- An interpretation of every operation of `S` on a carrier. -/
structure Model (S : Signature.{u}) (Carrier : Type v) : Type (max u v) where
  interpret : (operation : S.Operation) →
    (Fin (S.arity operation) → Carrier) → Carrier

/-- Evaluation of a term under a variable valuation. -/
def Term.evaluate {Carrier : Type v} (model : Model S Carrier)
    (valuation : Nat → Carrier) : Term S → Carrier
  | .var index => valuation index
  | .op operation arguments =>
      model.interpret operation (fun i => (arguments i).evaluate model valuation)

theorem Term.evaluate_subst {Carrier : Type v} (model : Model S Carrier)
    (valuation : Nat → Carrier) (substitution : Nat → Term S) :
    ∀ term : Term S,
      (term.subst substitution).evaluate model valuation =
        term.evaluate model (fun index =>
          (substitution index).evaluate model valuation)
  | .var _ => rfl
  | .op operation arguments => by
      simp only [Term.subst_op, Term.evaluate]
      exact congrArg (model.interpret operation)
        (funext fun i => Term.evaluate_subst model valuation substitution (arguments i))

end Mettapedia.UniversalAlgebra
