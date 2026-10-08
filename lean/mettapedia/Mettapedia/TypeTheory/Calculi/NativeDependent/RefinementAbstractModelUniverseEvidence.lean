import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModelUniverseReadout

/-!
# Retained dependent sections after changing the semantic carriers

Two independently supplied generated certificates extract the same complete
section from the authored evaluator, before and after the carrier change.
The supplied context and type are retained; no equality of certificate trees
or choice of a new data witness is required.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract.Derivation

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualCwfUniverseLift
open Mettapedia.TypeTheory.ContextualPredicateModelScopeUniverseLift

universe a c s t m p uc vs wt ms ps
variable {S : Symbols.{a}} {D : Signature S} {C : CwfWithTerminal.{c,s,t,m}}

theorem termSection_carrierLift
    (model : Contextual.Interpretation.QualifiedModel.{a,c,s,t,m,p} D C) {n : Nat}
    {raw : ContextExpr S n} {term : TermExpr S n} {type : TypeExpr S n}
    (first second : Derivation D (.term raw term type))
    (Γ : ModelScope C model.localModel n) (A : C.toCwf.Ty Γ.1)
    (contextRead : model.data.evaluateContext raw = some Γ)
    (typeRead : model.data.evaluateType Γ type = some A) :
    (termSection (model.carrierLift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}).data
      model.carrierLift.realization model.carrierLift.products_substitution
      model.carrierLift.products_beta model.carrierLift.products_eta second
      (liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} Γ) (ULift.up A)
      (model.data.evaluateContext_carrierLift raw Γ contextRead)
      (model.data.evaluateType_carrierLift type Γ A typeRead)).down =
      termSection model.data model.realization model.products_substitution
        model.products_beta model.products_eta first Γ A contextRead typeRead := by
  let lifted := model.carrierLift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}
  have read := model.data.evaluateTerm_carrierLift.{a,c,s,t,m,p,uc,vs,wt,ms,ps} term Γ _
    (termSection_readout model.data model.realization model.products_substitution
      model.products_beta model.products_eta first Γ A contextRead typeRead)
  have exactSection := termSection_unique lifted.data lifted.realization
    lifted.products_substitution lifted.products_beta lifted.products_eta
    second (liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} Γ) (ULift.up A)
    (model.data.evaluateContext_carrierLift raw Γ contextRead)
    (model.data.evaluateType_carrierLift type Γ A typeRead) (ULift.up
      (termSection model.data model.realization model.products_substitution
        model.products_beta model.products_eta first Γ A contextRead typeRead)) read
  exact congrArg ULift.down exactSection

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract.Derivation
