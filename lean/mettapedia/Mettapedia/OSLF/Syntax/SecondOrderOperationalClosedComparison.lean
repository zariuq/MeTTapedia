import Mettapedia.OSLF.Syntax.SecondOrderEquationModelNaturality
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalClosedInterpretation

/-!
# Scoped premise functions over authored equation contexts

The quotient binding models carry the same scoped function interpretation as
the original binding clone. Reindexing an authored metavariable context maps
both endpoints of a binder-local operational premise through that function
object. Its premise remains a request for firing evidence, not an equation of
the endpoint programs.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.BinderLocalPremise
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalClosedInterpretation
open Mettapedia.OSLF.Binding.MultiBinderPresheaf
open Mettapedia.GSLT.LanguageDef.MultiSortedClone

/-- Contextual equation-class substitution preserves both chosen function
endpoints of an authored premise under any list of local binders. -/
theorem authoredPremiseFunctions_contextMap
    (S : Signature) {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    {X Y : EquationContexts (authoredEquationPresentation S equations)}
    (assignment : X ⟶ Y)
    {Ξ Γ : Ctx S}
    (valuation : Valuation (M := M)
      (authoredEquationModelAt S equations Y.as).algebra Γ)
    (close : Environment S
      (authoredEquationModelAt S equations Y.as).algebra.substitution.Carrier
      Ξ Γ)
    (premise : LocalStepPremise (withMetas S M) Ξ) :
    let h := authoredEquationModelMapQuot S equations assignment
    premiseFunctions (authoredEquationModelAt S equations X.as).algebra
        (mapValuation h valuation)
        (fun sort var => h.raw.map (close sort var)) premise =
      ((mapScopedFunctions h premise.binders premise.sort).app
          (Opposite.op
            (ContextObject.ofList
              (authoredEquationModelAt S equations Y.as).algebra.substitution.toClone
              Γ))
          (premiseFunctions
            (authoredEquationModelAt S equations Y.as).algebra
            valuation close premise).1,
        (mapScopedFunctions h premise.binders premise.sort).app
          (Opposite.op
            (ContextObject.ofList
              (authoredEquationModelAt S equations Y.as).algebra.substitution.toClone
              Γ))
          (premiseFunctions
            (authoredEquationModelAt S equations Y.as).algebra
            valuation close premise).2) := by
  exact premiseFunctions_map
    (authoredEquationModelMapQuot S equations assignment)
    valuation close premise

end Mettapedia.OSLF.Binding.SecondOrderContext

#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredPremiseFunctions_contextMap
