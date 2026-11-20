import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSemantics

/-!
# Substituting derivations for stored hypotheses

Every hypothesis of an application derivation may be replaced by a derivation
over another knowledge base, at its declared caller interpretation. This is
proved on the two actual DTL constructors, retaining the proof term.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSemantics

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)

theorem Derives.cut (judgmentTag arrowTag : Nat) (data base : Data) (source baseSource : Subst rowSig)
    (deriveHypothesis : ∀ value ∈ hypotheses data source, Derives judgmentTag arrowTag base baseSource value)
    {value : Tm} (derivation : Derives judgmentTag arrowTag data source value) :
    Derives judgmentTag arrowTag base baseSource value := by
  induction derivation with
  | hypothesis assumed => exact deriveHypothesis _ assumed
  | apply _ _ major minor => exact .apply major minor

#print axioms Derives.cut

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSemantics
