import Mettapedia.OSLF.Syntax.SecondOrderAuthoredEquationPresentation
import Mettapedia.OSLF.Syntax.PatternSubstEquation

/-!
# A binder-dependent authored equation in second-order contexts

The explicit-substitution presentation has a metavariable that depends on the
variable bound by the substitution former. This instance checks that the
general equation-context construction accepts the authored schema with that
dependency, rather than merely accepting empty metavariable lists.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext.PatternControl

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.PatternPresentation
open Mettapedia.OSLF.Binding.PatternSubst

/-- The actual explicit-substitution equation in every ambient second-order
context. Its binder-dependent body and nullary replacement keep their authored
declaration positions. -/
def presentation : EquationPresentation patSig substMetas :=
  authoredEquationPresentation patSig patE

theorem equation_count : patE.length = 1 := rfl

/-- The concrete binder-dependent instance remains a generator of the
equation closure after free contextual metavariables are adjoined. -/
theorem scoped_instance (X : Object patSig)
    (valuation : BindingEquationalModels.MetaValuation
      (termAlgebra X) substMetas) :
    EqClosure (presentation.axioms X)
      (instantiate valuation (liftSchema X substLhs))
      (instantiate valuation (liftSchema X substRhs)) := by
  change EqClosure [liftEquation X substAxiom]
    (instantiate valuation (liftSchema X substLhs))
    (instantiate valuation (liftSchema X substRhs))
  have generated := EqClosure.ax_closed
    [liftEquation X substAxiom] (⟨0, by decide⟩ : Fin 1)
    valuation (fun _ v => Term.var v)
  simpa [substAxiom, liftEquation, bind_id] using generated

/-- The same binder-dependent redex instance commutes with any contextual
metavariable assignment. -/
theorem scoped_instance_transport {X Y : Object patSig}
    (assignment : X ⟶ Y)
    (valuation : BindingEquationalModels.MetaValuation
      (termAlgebra Y) substMetas) :
    instInto assignment (instantiate valuation (liftSchema Y substLhs)) =
      instantiate (fun k => instInto assignment (valuation k))
        (liftSchema X substLhs) :=
  instInto_liftSchema_instance assignment valuation substLhs

/-- The authored binder-dependent equation has the same universal
interpretation property at the equation-context rung as the general theorem. -/
noncomputable def universal (D : Type*) [Category D] :
    (EquationContexts presentation ⥤ D) ≌
      LawfulEquationInterpretation presentation D :=
  equationUniversalEquivalence presentation D

end Mettapedia.OSLF.Binding.SecondOrderContext.PatternControl

#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.PatternControl.scoped_instance
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.PatternControl.universal
