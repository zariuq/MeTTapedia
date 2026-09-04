import Mettapedia.UniversalAlgebra.ConservativeExtension
import Mettapedia.UniversalAlgebra.Instances.Monoid

/-!
# Conservative and non-conservative monoid equation extensions

Concrete positive and negative controls for the generic conservative-extension
criterion.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.Monoid

open Mettapedia.UniversalAlgebra

/-- Extend the monoid equations by the already-derived equation
`(1 * x) * 1 = x`. -/
def derivedExtension : EquationSystem signature :=
  equationSystem.extend [(mul (mul one x) one, x)]

/-- The derived extension proves exactly the same equations as the original
monoid system. -/
theorem derivedExtension_sameConsequences :
    EquationSystem.SameConsequences derivedExtension equationSystem := by
  apply EquationSystem.extend_sameConsequences
  intro equation equationMem
  simp only [List.mem_singleton] at equationMem
  subst equation
  exact one_mul_mul_one

/-- Extend the monoid equations by identifying two distinct variables. -/
def collapsingExtension : EquationSystem signature :=
  equationSystem.extend [((Term.var 0 : Term signature), Term.var 1)]

/-- Negative control: the collapsing equation is genuinely new, so this
extension does not preserve the monoid consequence relation. -/
theorem collapsingExtension_not_sameConsequences :
    ¬ EquationSystem.SameConsequences collapsingExtension equationSystem :=
  EquationSystem.extend_not_sameConsequences_of_not_consequence
    equationSystem ((Term.var 0 : Term signature), Term.var 1)
    distinct_variables_not_consequence

end Mettapedia.UniversalAlgebra.Monoid
