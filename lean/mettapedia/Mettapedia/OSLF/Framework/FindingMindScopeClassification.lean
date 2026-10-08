import Mettapedia.OSLF.Framework.FindingMindNativeInteraction
import Mettapedia.TypeTheory.PresheafEventTruthClassification

/-!
# Sieve-valued scope classification for an actual rho interaction

The actual occurrence scope opens after a real observer-context arrow.
Its generic truth classification is the name readout followed by the
scope characteristic map. The possible-event classifier records a future
target certificate before the current world has an admitted event.
Present falsehood alone therefore cannot replace this native predicate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FindingMindScopeClassification

open _root_.CategoryTheory _root_.CategoryTheory.Functor
open Mettapedia.GSLT.Topos
open Mettapedia.GSLT.Topos.PresheafPredicateGenericTruth
open FindingMindNativeInteraction

/-- The existing scoped event comprehension is classified by the composed
actual name map and sieve-valued scope classifier. -/
theorem event_scope_truth :
    (truthPredicate Stages).preimage (eventName ≫ chiOfSubfunctor names openScope) =
      openScope.preimage eventName :=
  events.scope_truth_preimage eventName openScope

theorem event_scope_classification_unique :
    ∃! arrow : totalOfPredicate events.events (openScope.preimage eventName) ⟶ totalTruth Stages,
      IsStronglyCartesian (presheafPredicateProjection Stages) arrow.base arrow :=
  events.scope_cartesian_classification eventName openScope

theorem scoped_erasure_has_exact_classified_range :
    Subfunctor.range (events.scopeErasure eventName openScope) =
      (truthPredicate Stages).preimage (eventName ≫ chiOfSubfunctor names openScope) := by
  rw [events.scopeErasure_range, event_scope_truth]

/-- The supported possible event is independently the existential image
of the actual scoped event's target specification. -/
theorem scoped_possible_truth :
    (truthPredicate Stages).preimage
      (chiOfSubfunctor states
        (((support postcondition).preimage scopedEvents.target).image scopedEvents.source)) =
      support (scopedEvents.certificates postcondition) :=
  scopedEvents.certificate_truth_preimage postcondition

def possible : Subfunctor states := support (scopedEvents.certificates postcondition)

noncomputable def possibleClassifier : states ⟶ omegaFunctor (C := Stages) :=
  chiOfSubfunctor states possible

noncomputable def initialSieve : Sieve (world 0).unop :=
  possibleClassifier.app (world 0) source

/-- An actual future certificate belongs to the classifier's earlier sieve. -/
theorem classifier_contains_future : initialSieve.arrows (advance 0).unop := by
  change Nonempty ((scopedEvents.certificates postcondition).obj ⟨world 1, source⟩)
  exact ⟨openedCertificate⟩

/-- The same classifier does not assert an admitted event at the present world. -/
theorem classifier_excludes_present : ¬ initialSieve.arrows (𝟙 (world 0).unop) := by
  change ¬ Nonempty ((scopedEvents.certificates postcondition).obj ⟨world 0, source⟩)
  exact no_scoped_certificate_initial

/-- Actual future possibility differs from both perpetual failure and
unqualified present truth, even at one fixed runtime source. -/
theorem possible_sieve_is_proper : initialSieve ≠ ⊥ ∧ initialSieve ≠ ⊤ := by
  constructor
  · intro same
    have future := classifier_contains_future
    rw [same] at future
    exact future
  · intro same
    apply classifier_excludes_present
    rw [same]
    trivial

theorem present_failure_is_not_perpetual_failure :
    (source ∈ possible.obj (world 0) ↔ source ∈ (⊥ : Subfunctor states).obj (world 0)) ∧
      possible ≠ ⊥ := by
  constructor
  · exact iff_of_false no_scoped_certificate_initial (by intro impossible; exact impossible)
  · intro same
    have future : source ∈ possible.obj (world 1) := ⟨openedCertificate⟩
    rw [same] at future
    exact future

/-- Complete Cartesian classification concerns the same supported event
predicate as the native receipt, without claiming to select its witness. -/
theorem possible_classification_unique :
    ∃! arrow : totalOfPredicate states possible ⟶ totalTruth Stages,
      IsStronglyCartesian (presheafPredicateProjection Stages) arrow.base arrow :=
  scopedEvents.certificate_cartesian_classification postcondition

end Mettapedia.OSLF.Framework.FindingMindScopeClassification
