import Mettapedia.GSLT.Core.LooseRelationPredicateTransformers
import Mettapedia.GSLT.LanguageDef.GSLTILSemanticPredicateInstitution

/-!
# Predicate-institution shadow of the route equipment

The proof-relevant route equipment and the semantic predicate institution are
not competing universal structures.  This module proves their exact overlap.

An institutional signature translation acts by inverse image along a tight
term map.  The companion of that map is a represented loose route, and both
its existential and universal predicate transformers are exactly the same
inverse image.  General loose routes retain more information: branching
separates the two predicate transformers, while duplicate route witnesses are
invisible even when the visible support is a total function.

Consequently the predicate institution is a logical shadow of the represented
route layer.  It transports sentence truth and consequence, but it cannot by
itself supply proof identity or an executable representation license.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.PredicateEquipmentBridge

open CategoryTheory
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.LooseRelationPredicateTransformers
open Mettapedia.GSLT.LanguageDef.GSLTIL.SemanticPredicateInstitution
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

universe u

/-! ## Exact overlap on tight translations -/

/-- Sentence translation in the semantic predicate institution is both the
may and must transformer of the companion of the same tight term map. -/
theorem institution_transport_eq_companion_pullbacks
    {source target : (ModallyCoveredTheory.{u})ᵒᵖ}
    (translation : source ⟶ target)
    (predicate : Set (SemanticTerm source.unop.theory)) :
    predicateSentence.map translation predicate =
        mayPullback
          (companion
            translation.unop.toCoveredTranslation.toOperational.mapSemantic)
          predicate ∧
      predicateSentence.map translation predicate =
        mustPullback
          (companion
            translation.unop.toCoveredTranslation.toOperational.mapSemantic)
          predicate := by
  constructor
  · exact (mayPullback_eq_preimage
      (Representation.companionSelf
        translation.unop.toCoveredTranslation.toOperational.mapSemantic)
      predicate).symm
  · exact (mustPullback_eq_preimage
      (Representation.companionSelf
        translation.unop.toCoveredTranslation.toOperational.mapSemantic)
      predicate).symm

/-- Any exactly represented loose route likewise has one predicate action,
namely inverse image along its uniquely determined executable map. -/
theorem represented_route_has_single_predicate_action
    {Source Target : Type u} {route : Loose Source Target}
    (representation : Representation route) (predicate : Set Target) :
    mayPullback route predicate =
        Set.preimage representation.map predicate ∧
      mustPullback route predicate =
        Set.preimage representation.map predicate :=
  ⟨mayPullback_eq_preimage representation predicate,
    mustPullback_eq_preimage representation predicate⟩

/-! ## Strict boundaries -/

/-- The branching Boolean route can reach the selected true point. -/
theorem choice_may_reach_true :
    () ∈ mayPullback Canary.choice ({true} : Set Bool) := by
  exact ⟨true, ⟨Unit.unit⟩, Set.mem_singleton true⟩

/-- The same route does not universally land at true because it also reaches
false. -/
theorem choice_not_must_reach_true :
    () ∉ mustPullback Canary.choice ({true} : Set Bool) := by
  intro allTargets
  have falseMember := allTargets false ⟨Unit.unit⟩
  exact Bool.false_ne_true (Set.mem_singleton_iff.mp falseMember)

/-- A branching loose route has no single functional predicate reindexing:
its existential and universal readings are observably different. -/
theorem branching_route_has_distinct_predicate_actions :
    mayPullback Canary.choice ({true} : Set Bool) ≠
      mustPullback Canary.choice ({true} : Set Bool) := by
  intro equalPullbacks
  apply choice_not_must_reach_true
  rw [← equalPullbacks]
  exact choice_may_reach_true

/-- Conversely, a total single-valued predicate action still does not earn an
execution license when its visible fibre retains duplicate witnesses. -/
theorem functional_predicate_action_does_not_imply_representation :
    (∀ predicate : Set Unit,
      mayPullback
          Mettapedia.GSLT.LooseRelationPredicateTransformers.Canary.twoWitnesses
          predicate =
        mustPullback
          Mettapedia.GSLT.LooseRelationPredicateTransformers.Canary.twoWitnesses
          predicate) ∧
      ¬ Nonempty
        (Representation
          Mettapedia.GSLT.LooseRelationPredicateTransformers.Canary.twoWitnesses) :=
  Mettapedia.GSLT.LooseRelationPredicateTransformers.Canary.predicate_functional_but_not_proof_representable

/-- Even the complete family of existential predicate transformers determines
only propositional support, not proof-relevant route fibres. -/
theorem predicate_action_determines_exactly_support
    {Source Target : Type u} (first second : Loose Source Target) :
    (∀ predicate : Set Target,
      mayPullback first predicate = mayPullback second predicate) ↔
      ∀ source target,
        support first source target ↔ support second source target :=
  all_mayPullback_eq_iff_same_support first second

#print axioms institution_transport_eq_companion_pullbacks
#print axioms represented_route_has_single_predicate_action
#print axioms branching_route_has_distinct_predicate_actions
#print axioms functional_predicate_action_does_not_imply_representation
#print axioms predicate_action_determines_exactly_support

end Mettapedia.GSLT.LanguageDef.GSLTIL.PredicateEquipmentBridge
