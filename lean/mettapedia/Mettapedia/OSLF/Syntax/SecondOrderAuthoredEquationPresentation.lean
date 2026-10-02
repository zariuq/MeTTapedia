import Mettapedia.OSLF.Syntax.SecondOrderSchemaInterpretation
import Mettapedia.OSLF.Syntax.SecondOrderContextualSchemaInterpretation
import Mettapedia.OSLF.Syntax.SecondOrderEquationUniversal

/-!
# Authored higher-order equations in second-order contexts

The source signature's operators and schema metavariables are kept distinct
when a second-order context is adjoined. The interpretation comparison below
identifies concrete instances of the lifted schema with the existing semantic
binding-clone interpretation. This includes schema metavariable applications
and arguments under binders.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FreeBindingTerms

variable {S : Signature} {M : List (MetaArity S)}

/-- A complete list of authored higher-order equations generates a stable
second-order quotient. The proof checks each actual lifted schema generator;
stability of the congruence follows from the separate closure theorem. -/
def authoredEquationPresentation (S : Signature)
    {M : List (MetaArity S)} (equations : List (EqAxiom S M)) :
    EquationPresentation S M where
  axioms := fun X => equations.map (liftEquation X)
  generator_substitute := by
    intro X Y assignment index Θ Γ valuation ambient
    let sourceIndex : Fin equations.length :=
      ⟨index.val, by simpa using index.isLt⟩
    let targetIndex : Fin (equations.map (liftEquation X)).length :=
      ⟨sourceIndex.val, by simp⟩
    have getY :
        (equations.map (liftEquation Y)).get index =
          liftEquation Y (equations.get sourceIndex) := by
      change (equations.map (liftEquation Y))[sourceIndex.val] =
        liftEquation Y (equations[sourceIndex.val])
      simp
    have getX :
        (equations.map (liftEquation X)).get targetIndex =
          liftEquation X (equations.get sourceIndex) := by
      change (equations.map (liftEquation X))[sourceIndex.val] =
        liftEquation X (equations[sourceIndex.val])
      simp
    rw [getY]
    intro ordinary
    have generated : ∀ env : Sub (withMetas S X.arities)
        ((equations.map (liftEquation X)).get targetIndex).ctx Γ,
        EqClosure (equations.map (liftEquation X))
          (ContextualAssignment.instantiate (fun k => instInto assignment (valuation k))
            (fun s v => instInto assignment (ambient s v)) env
            ((equations.map (liftEquation X)).get targetIndex).lhs)
          (ContextualAssignment.instantiate (fun k => instInto assignment (valuation k))
            (fun s v => instInto assignment (ambient s v)) env
            ((equations.map (liftEquation X)).get targetIndex).rhs) :=
      fun env => EqClosure.ax (E := equations.map (liftEquation X)) targetIndex
        (fun k => instInto assignment (valuation k))
        (fun s v => instInto assignment (ambient s v)) env
    rw [getX] at generated
    change EqClosure (equations.map (liftEquation X))
      (instInto assignment
        (ContextualAssignment.instantiate valuation ambient ordinary
          (liftSchema Y (equations.get sourceIndex).lhs)))
      (instInto assignment
        (ContextualAssignment.instantiate valuation ambient ordinary
          (liftSchema Y (equations.get sourceIndex).rhs)))
    rw [instInto_contextual_liftSchema_instance assignment valuation ambient ordinary
      (equations.get sourceIndex).lhs,
      instInto_contextual_liftSchema_instance assignment valuation ambient ordinary
        (equations.get sourceIndex).rhs]
    simpa only [liftEquation] using
      generated (fun s v => instInto assignment (ordinary s v))

/-- The equation-context universal property now applies to the actual
authored higher-order equation list, including maps between interpretations.
This classifies equations and contextual substitution; the operational and
chosen closed-structure extensions are separate obligations. -/
noncomputable def authoredEquationUniversalEquivalence
    (S : Signature) {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (D : Type*) [Category D] :
    (EquationContexts (authoredEquationPresentation S equations) ⥤ D) ≌
      LawfulEquationInterpretation
        (authoredEquationPresentation S equations) D :=
  equationUniversalEquivalence
    (authoredEquationPresentation S equations) D

end Mettapedia.OSLF.Binding.SecondOrderContext

#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredEquationPresentation
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredEquationUniversalEquivalence
