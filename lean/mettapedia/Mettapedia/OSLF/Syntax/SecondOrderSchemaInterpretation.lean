import Mettapedia.OSLF.Syntax.SecondOrderBindingAlgebraMap

/-!
# Authored schemas in an extended binding signature

Schema inclusion and its interpretation laws are independent of equation
closure, quotient categories and their semantic soundness.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FreeBindingTerms

variable {S : Signature} {M : List (MetaArity S)}

mutual

/-- Include a source schema in an ambient second-order context, retaining
each authored metavariable position and every binder. -/
def liftSchema (X : Object S) :
    {Γ : Ctx S} → {sort : S.Srt} →
      Term (withMetas S M) Γ sort →
      Term (withMetas (withMetas S X.arities) M) Γ sort
  | _, _, .var index => .var index
  | _, _, .op (Sum.inl op) args =>
      .op (Sum.inl (Sum.inl op)) (liftSchemaArgs X args)
  | _, _, .op (Sum.inr (.mk index)) args =>
      .op (Sum.inr (MetaOp.mk (S := withMetas S X.arities) index))
        (liftSchemaArgs X args)

/-- The schema inclusion acts under every argument's binder list. -/
def liftSchemaArgs (X : Object S) :
    {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
      Args (withMetas S M) arities Γ →
      Args (withMetas (withMetas S X.arities) M) arities Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail =>
      .cons (liftSchema X head) (liftSchemaArgs X tail)

end

/-- On nonbinding metavariable arguments, the semantic argument environment
is exactly the syntactic simultaneous substitution. -/
theorem argsEnvironment_toSyntax (X : Object S) :
    ∀ {dependencies : List S.Srt} {Γ : Ctx S}
      (args : FamilyArgs S (restrictedSubstitution X).Carrier
        (dependencies.map (fun sort => ([], sort))) Γ),
      BindingEquationalModels.argsEnvironment (termAlgebra X) args =
        argsToSub (toSyntax X args)
  | [], _, .nil => by
      funext sort index
      exact nomatch index
  | _ :: _, _, .cons _head tail => by
      funext sort index
      cases index with
      | zero => rfl
      | succ old => exact congrFun (congrFun (argsEnvironment_toSyntax X tail) sort) old

mutual

/-- Interpreting an authored schema in the ambient syntactic binding algebra
is its concrete lifted instance. The equation holds for open dependency
contexts, not only for closed or first-order equations. -/
theorem interpretSchema_liftSchema (X : Object S)
    (valuation : BindingEquationalModels.MetaValuation (termAlgebra X) M) :
    ∀ {Γ : Ctx S} {sort : S.Srt}
      (term : Term (withMetas S M) Γ sort),
      BindingEquationInterpretation.interpretSchema
        (termAlgebra X) valuation term =
      instantiate valuation (liftSchema X term)
  | _, _, .var _ => rfl
  | _, _, .op (Sum.inl op) args => by
      change Term.op (S := withMetas S X.arities) (Sum.inl op)
        (toSyntax X
          (BindingEquationInterpretation.interpretSchemaArgs
            (termAlgebra X) valuation args)) =
        Term.op (S := withMetas S X.arities) (Sum.inl op)
          (instantiateArgs valuation (liftSchemaArgs X args))
      exact congrArg
        (Term.op (S := withMetas S X.arities) (Sum.inl op))
        (interpretSchemaArgs_liftSchema X valuation args)
  | _, _, .op (Sum.inr (.mk index)) args => by
      change bind
        (BindingEquationalModels.argsEnvironment (termAlgebra X)
          (BindingEquationInterpretation.interpretSchemaArgs
            (termAlgebra X) valuation args))
        (valuation index) =
        bind (argsToSub (instantiateArgs valuation (liftSchemaArgs X args)))
          (valuation index)
      have sameEnvironment :
          BindingEquationalModels.argsEnvironment (termAlgebra X)
            (BindingEquationInterpretation.interpretSchemaArgs
              (termAlgebra X) valuation args) =
          argsToSub (instantiateArgs valuation (liftSchemaArgs X args)) := by
        calc
          _ = argsToSub (toSyntax X
                (BindingEquationInterpretation.interpretSchemaArgs
                  (termAlgebra X) valuation args)) :=
            argsEnvironment_toSyntax X _
          _ = _ := congrArg argsToSub
            (interpretSchemaArgs_liftSchema X valuation args)
      exact congrArg (fun environment => bind environment (valuation index))
        sameEnvironment

/-- The schema comparison acts in every argument of an authored operator,
including a body in the extended context of its binders. -/
theorem interpretSchemaArgs_liftSchema (X : Object S)
    (valuation : BindingEquationalModels.MetaValuation (termAlgebra X) M) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : Args (withMetas S M) arities Γ),
      toSyntax X
        (BindingEquationInterpretation.interpretSchemaArgs
          (termAlgebra X) valuation args) =
      instantiateArgs valuation (liftSchemaArgs X args)
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      exact congrArg₂ Args.cons
        (interpretSchema_liftSchema X valuation head)
        (interpretSchemaArgs_liftSchema X valuation tail)

end

/-- Include every component of an authored higher-order equation at a
second-order context without changing its schema metavariable declarations. -/
def liftEquation (X : Object S) (equation : EqAxiom S M) :
    EqAxiom (withMetas S X.arities) M where
  ctx := equation.ctx
  sort := equation.sort
  lhs := liftSchema X equation.lhs
  rhs := liftSchema X equation.rhs

/-- A second-order assignment commutes with a concrete instance of any
authored schema, including metavariable applications in binding contexts. -/
theorem instInto_liftSchema_instance {X Y : Object S}
    (assignment : X ⟶ Y)
    (valuation : BindingEquationalModels.MetaValuation (termAlgebra Y) M)
    {Γ : Ctx S} {sort : S.Srt}
    (schema : Term (withMetas S M) Γ sort) :
    instInto assignment (instantiate valuation (liftSchema Y schema)) =
      instantiate (fun k => instInto assignment (valuation k))
        (liftSchema X schema) := by
  rw [← interpretSchema_liftSchema Y valuation schema,
    ← interpretSchema_liftSchema X
      (fun k => instInto assignment (valuation k)) schema]
  exact interpretSchema_instInto assignment valuation schema


end Mettapedia.OSLF.Binding.SecondOrderContext
