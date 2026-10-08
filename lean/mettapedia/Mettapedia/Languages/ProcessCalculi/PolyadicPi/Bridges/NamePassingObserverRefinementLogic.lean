import Mettapedia.TypeTheory.PresheafNativeRefinementCells
import Mettapedia.TypeTheory.PresheafNativePropositionRestriction
import Mettapedia.TypeTheory.PresheafNativePredicateLogicalRestriction
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverNativeImage

/-!
# Native propositions and refinements on admitted observer origins

The equivalence retaining each authored protocol client and its supplied
source elaboration gives full future coverage. Its canonical ordinary
native proposition comparison is invertible, and chosen predicate
comprehension and quantified judgments commute with the same native theory
action. These judgments range over this retained observer image.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverRefinementLogic

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open ContextualLocalUniverses NativeLocalTypeFormers NativeLocalTheoryRestriction NativeLocalTheoryTransformation
open PresheafNativePropositionReadout PresheafNativePredicateQuantifierSubstitution
open NamePassingObserverFunctor NamePassingObserverNativeImage

theorem observer_future_coverage :
    LogicalTransport.LiftsRestrictions observerEquivalence.functor :=
  PresheafNativePredicateLogicalRestriction.equivalence_lifts observerEquivalence.functor

noncomputable def propositionDisplay (P : RetainedScopeᵒᵖ ⥤ Type) :
    (⟨restrict observerEquivalence.functor (nativeOmega P)⟩ :
      TypeOver (nativeLocalModel SourceScope).toCwf (observerEquivalence.functor.op ⋙ P)) ≅
        ⟨nativeOmega (observerEquivalence.functor.op ⋙ P)⟩ :=
  PresheafNativePropositionRestriction.displayIso observerEquivalence.functor P

theorem propositionDisplay_canonical (P : RetainedScopeᵒᵖ ⥤ Type) :
    (propositionDisplay P).hom =
      PresheafNativePropositionRestriction.displayComparison observerEquivalence.functor P :=
  PresheafNativePropositionRestriction.displayIso_hom observerEquivalence.functor P

noncomputable def refinementDisplay (P : RetainedScopeᵒᵖ ⥤ Type)
    (A : NativeType P) (selected : Subfunctor (totalSpace A.decoded)) :
    (⟨restrict observerEquivalence.functor (PresheafNativeStableRefinement.chosen A selected)⟩ :
      TypeOver (nativeLocalModel SourceScope).toCwf (observerEquivalence.functor.op ⋙ P)) ≅
        ⟨PresheafNativeStableRefinement.chosen (restrict observerEquivalence.functor A)
          (PresheafNativeRefinementRestriction.predicate observerEquivalence.functor A selected)⟩ :=
  PresheafNativeRefinementRestriction.displayComparison observerEquivalence.functor A selected

theorem proposition_readout (P : RetainedScopeᵒᵖ ⥤ Type) (selected : Subfunctor P) :
    nativeHolds (PresheafNativePropositionRestriction.termAction observerEquivalence.functor
      (nativeQuote selected)) = LogicalTransport.restrictPredicate observerEquivalence.functor selected := by
  rw [PresheafNativePropositionRestriction.quote_action, nativeHolds_nativeQuote]

theorem universal_rule (P : RetainedScopeᵒᵖ ⥤ Type) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    LogicalTransport.restrictPredicate observerEquivalence.functor (nativeForall A selected) =
      nativeForall (restrict observerEquivalence.functor A)
        (PresheafNativeRefinementRestriction.predicate observerEquivalence.functor A selected) :=
  PresheafNativePredicateLogicalRestriction.forall_restriction_eq
    observerEquivalence.functor observer_future_coverage A selected

theorem existential_rule (P : RetainedScopeᵒᵖ ⥤ Type) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    LogicalTransport.restrictPredicate observerEquivalence.functor (nativeExists A selected) =
      nativeExists (restrict observerEquivalence.functor A)
        (PresheafNativeRefinementRestriction.predicate observerEquivalence.functor A selected) :=
  PresheafNativePredicateLogicalRestriction.exists_restriction observerEquivalence.functor A selected

theorem implication_rule (P : RetainedScopeᵒᵖ ⥤ Type) (A : NativeType P)
    (first second : Subfunctor (totalSpace A.decoded)) :
    PresheafNativeRefinementRestriction.predicate observerEquivalence.functor A (first ⇨ second) =
      PresheafNativeRefinementRestriction.predicate observerEquivalence.functor A first ⇨
        PresheafNativeRefinementRestriction.predicate observerEquivalence.functor A second :=
  PresheafNativePredicateLogicalRestriction.predicate_implication_eq
    observerEquivalence.functor observer_future_coverage A first second

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverRefinementLogic
