import Mettapedia.Logic.HOL.HenkinInstitution
import Mettapedia.Logic.HOL.StandardAxiomProperties

/-!
# Extensional HOL derivability inside the Henkin institution

This module connects the proof-theoretic and model-theoretic faces of the
fixed-base, varying-constant institution.  Its models include the semantic
function-extensionality property required by the extensional derivation
calculus; consequently a finite derivation from a theory is a semantic
consequence in the institution.

Choice, infinity, and excluded middle are not implicit in this result.  They
remain formulas or theory extensions whose model properties must be supplied
separately.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.HenkinInstitution

open CategoryTheory
open scoped CategoryTheory

universe u

/-- Soundness of the extensional HOL calculus, expressed as institution
consequence.  This is the proof-theory/semantics seam for the fixed-base
institution. -/
theorem provable_entails {Base : Type u} {signature : Signature Base}
    {theory : ClosedTheorySet signature.Const}
    {conclusion : ClosedFormula signature.Const}
    (derivation : ClosedTheorySet.Provable theory conclusion) :
    (institution Base).Entails signature theory conclusion := by
  intro wrappedModel modelsTheory
  let semanticModel :=
    (show CategoryTheory.Discrete (Model signature) from wrappedModel).as
  exact StandardAxiomProperties.provable_sound_of_models
    semanticModel.henkin semanticModel.functionsRespectEqv theory
    (by
      intro formula membership
      exact modelsTheory formula membership)
    derivation

/-- The proof-theoretic closure of a theory is contained in its semantic
closure.  Completeness is deliberately a separate theorem with its own
Henkin-construction hypotheses. -/
theorem provable_mem_semanticConsequence {Base : Type u}
    {signature : Signature Base} {theory : ClosedTheorySet signature.Const}
    {conclusion : ClosedFormula signature.Const}
    (derivation : ClosedTheorySet.Provable theory conclusion) :
    conclusion ∈ (institution Base).semanticConsequence signature theory :=
  provable_entails derivation

#print axioms provable_entails
#print axioms provable_mem_semanticConsequence

end Mettapedia.Logic.HOL.HenkinInstitution
