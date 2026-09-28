import Mettapedia.OSLF.Syntax.SecondOrderEquationUniversal
import Mettapedia.OSLF.Syntax.MonoidEquationRung

/-!
# The authored monoid equations in second-order contexts

The source's three ordered equations have no schema metavariables. Removing
that empty layer gives exactly the same written equations in the
second-order-context quotient. The equation-context universal property thus
applies to the actual authored monoid presentation, not a replacement list.
This does not yet classify the complete operational language.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext.MonoidControl

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.MonoidEquationRung

/-- The authored association and two unit equations, with their original
positions, carried into second-order metavariable contexts. -/
def presentation : EquationPresentation sig [] :=
  emptySchemaPresentation monoidE

theorem equation_count : monoidE.length = 3 := rfl

/-- No equation side, context, sort or declaration position is lost by the
empty-schema conversion used in the classifier's equation rung. -/
theorem authored_roundtrip :
    (monoidE.map BaseEquation.ofEmptySchema).map
      BaseEquation.toEmptySchema = monoidE :=
  emptySchemaList_roundtrip monoidE

/-- Lawful interpretations of the authored monoid equations, including their
natural maps, are equivalent to functors out of its equation contexts in any
target category. This is the equation rung of the Chapter 7 classifier. -/
noncomputable def universal (D : Type*) [Category D] :
    (EquationContexts presentation ⥤ D) ≌
      LawfulEquationInterpretation presentation D :=
  equationUniversalEquivalence presentation D

end Mettapedia.OSLF.Binding.SecondOrderContext.MonoidControl

#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.MonoidControl.authored_roundtrip
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.MonoidControl.universal
