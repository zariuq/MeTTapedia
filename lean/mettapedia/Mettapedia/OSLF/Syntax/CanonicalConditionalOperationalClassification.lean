import Mettapedia.OSLF.Syntax.CanonicalConditionalRuleFrames
import Mettapedia.OSLF.Syntax.IndexedOperationalPresentationCategory

/-!
# Universal rule interpretation for canonical conditional reductions

The exact authored rule-frame polynomial is an object of the general category
of indexed operational presentations. Its free model interprets each complete
conditional firing as a constructor tree. The relative fold is unique for
every target rule algebra and every cartesian presentation interpretation.

This classifies the raw operational rule component. Integrating the authored
binding clone, equations, collection semantics, and a local-binder premise
carrier into a single classifying theory remains a separate construction.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CanonicalConditionalOperationalClassification

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Binding.CanonicalConditionalRuleFrames
open Mettapedia.OSLF.Binding.IndexedRulePresentationCategory
open Mettapedia.OSLF.Binding.IndexedOperationalPresentationCategory

/-- The canonical `LanguageDef` rules, including ordered nonrecursive
evidence and recursively addressed congruence premises, as an object of the
general rule-presentation category. -/
def authoredRules (base : BasePremiseEvaluator) (lang : LanguageDef) :
    Presentation Unit where
  Judgment := fun _ => Judgment
  rules := (authoredPresentation base lang).polynomial

/-- The proof-relevant free operational model of those actual authored
conditional rules. -/
def freeAuthoredRules (base : BasePremiseEvaluator) (lang : LanguageDef) :
    Equipped Unit :=
  free (authoredRules base lang)

/-- An interpretation of all retained authored firing histories is uniquely
determined by a cartesian rule-presentation map into the target model. -/
noncomputable def authoredFreeHomEquiv
    (base : BasePremiseEvaluator) (lang : LanguageDef)
    (target : Equipped Unit) :
    (freeAuthoredRules base lang ⟶ target) ≃
      (authoredRules base lang ⟶ target.presentation) :=
  freeHomEquiv (authoredRules base lang) target

/-- The source-specific operational interpretation really has the universal
extension and uniqueness law, rather than only an object-level assignment. -/
theorem authored_interpretation_unique
    (base : BasePremiseEvaluator) (lang : LanguageDef)
    {target : Equipped Unit}
    (interpretation : freeAuthoredRules base lang ⟶ target) :
    lift target interpretation.presentation = interpretation :=
  lift_unique interpretation

/-- The existing executable interpreter reaches an endpoint exactly when the
free operational model has evidence at the corresponding indexed judgment. -/
theorem executable_iff_free_evidence
    (base : BasePremiseEvaluator) (lang : LanguageDef)
    (fuel : Nat) (source target : Pattern) :
    target ∈ rewriteAt base lang fuel source ↔
      Nonempty ((freeAuthoredRules base lang).model.carrier ()
        (fuel, source, target)) :=
  mem_rewriteAt_iff_derivation base lang fuel source target

#print axioms authoredFreeHomEquiv
#print axioms authored_interpretation_unique
#print axioms executable_iff_free_evidence

end Mettapedia.OSLF.Binding.CanonicalConditionalOperationalClassification
