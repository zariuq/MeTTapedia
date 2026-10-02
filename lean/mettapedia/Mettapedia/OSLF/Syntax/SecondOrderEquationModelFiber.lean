import Mettapedia.OSLF.Syntax.SecondOrderBindingModelRestriction
import Mettapedia.OSLF.Syntax.SecondOrderEquationLexCompletion
import Mettapedia.OSLF.Syntax.FreeBindingEquationModel

/-!
# Binding equation models over contextual equation classes

At each second-order context, the quotient by lifted authored equations is
an actual binding-clone model of the original language. Its carrier is the
same equation-class term family represented by arrows of the quotient
context category. This identifies the categorical term object with the
existing free binding-equation semantics.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FreeBindingTerms

variable {S : Signature} {M : List (MetaArity S)}

universe u u₁ u₂

/-- At every ambient second-order context, the actual equation quotient is
a semantic model of the original authored binding equations. -/
noncomputable def authoredEquationModelAt (S : Signature)
    {M : List (MetaArity S)}
    (equations : List (EqAxiom S M)) (X : Object S) :
    FreeBindingEquationModel.Model equations where
  algebra := restrictAlgebra X
    (BindingEquationQuotientModel.algebra
      ((authoredEquationPresentation S equations).axioms X))
  satisfies := by
    intro index Θ Γ body ambient ordinary
    let sourceIndex : Fin
        ((authoredEquationPresentation S equations).axioms X).length :=
      ⟨index.val, by simp [authoredEquationPresentation]⟩
    have selected :
        ((authoredEquationPresentation S equations).axioms X).get
          sourceIndex = liftEquation X (equations.get index) := by
      change (equations.map (liftEquation X))[index.val] =
        liftEquation X (equations[index.val])
      simp
    have valid := (BindingEquationQuotientModel.algebra_satisfies
      ((authoredEquationPresentation S equations).axioms X)) sourceIndex
        (Γ := Θ) (Δ := Γ) body ambient
    rw [selected] at valid
    have atInstance := valid ordinary
    simp only [liftEquation] at atInstance
    rw [← interpretContextualSchema_restrictAlgebra X
      (BindingEquationQuotientModel.algebra
        ((authoredEquationPresentation S equations).axioms X))
      body ambient ordinary (equations.get index).lhs,
      ← interpretContextualSchema_restrictAlgebra X
      (BindingEquationQuotientModel.algebra
        ((authoredEquationPresentation S equations).axioms X))
      body ambient ordinary (equations.get index).rhs] at atInstance
    exact atInstance

end Mettapedia.OSLF.Binding.SecondOrderContext

#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredEquationModelAt
