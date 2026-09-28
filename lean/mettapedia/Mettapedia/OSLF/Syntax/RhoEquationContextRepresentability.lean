import Mettapedia.OSLF.Syntax.BindingEquationOperationRepresentable
import Mettapedia.OSLF.Syntax.RhoSourceEquationModel

/-!
# The Chapter 7 rho name presheaf in the equation context category

The full source equation presentation, including name reflection, has its
name-sort operations represented by the singleton-name context in its
quotient clone. The inclusion of ACU equations into that presentation is a
proper quotient even at the categorical level: its context functor is not
faithful because name reflection identifies two distinct substitution
arrows.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoEquationContextRepresentability

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSourceEquationModel
open Mettapedia.OSLF.Binding.BindingEquationExtension

/-- The Chapter 7 name-sort program presheaf is pulled back from the
representable singleton-name context of the complete equation quotient. -/
noncomputable def sourceNameYonedaIso :=
  termQAsPulledYonedaIso rhoSourceE Srt.nm

/-- The exact source reflection equation makes the ACU-to-source comparison
nonfaithful on name-context substitution arrows. -/
theorem acu_to_source_context_not_faithful :
    ¬ (comparisonContextFunctor acu_in_source).Faithful := by
  intro faithful
  apply acu_to_source_not_injective
  intro first second sameImages
  let clone := (BindingEquationQuotientModel.algebra rhoE).substitution.toClone
  let context : ContextObject clone := ContextObject.ofList clone [Srt.nm]
  let firstArrow : context ⟶ context := clone.operationAsSingletonMorphism first
  let secondArrow : context ⟶ context := clone.operationAsSingletonMorphism second
  have arrowsEqual : firstArrow = secondArrow := by
    apply faithful.map_injective
    funext i
    refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) i
    exact sameImages
  exact congrFun arrowsEqual (0 : Fin 1)

end Mettapedia.OSLF.Binding.RhoEquationContextRepresentability
