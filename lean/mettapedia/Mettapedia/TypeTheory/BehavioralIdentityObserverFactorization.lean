import Mettapedia.GSLT.Logic.ObserverRefinement
import Mettapedia.TypeTheory.EqualityFamilyObserverFactorization

/-!
# Behavioral identity and dependent-family descent

Refining an observer may split behavioral identity classes.  Forgetting the
extra distinctions therefore gives a canonical map from fine classes to
coarse classes.  This module connects that operational fact to dependent type
theory's family-factorization criterion.

If the observer refinement adds no genuine atom or label, the class map is
injective and preserves every anchored equality family.  If the class map
merges fine behavioral classes, it cannot preserve the fine equality family.
Thus observer-relative behavioral identity may be used as an extensional
readout, but it does not manufacture intensional identity evidence and does
not support arbitrary dependent elimination back into distinctions it erased.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BehavioralIdentityObserverFactorization

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.EqualityFamilyObserverFactorization

universe uS uAtomCoarse uLabelCoarse uAtomFine uLabelFine

variable {S : GSLT.{uS}}
variable
  {coarse : System.{uAtomCoarse, uLabelCoarse} S}
  {fine : System.{uAtomFine, uLabelFine} S}

/-- A refinement that merely renames all atoms and labels preserves equality
fibres between behavioral classes. -/
def equalityFamilyFactorizationOfSurjective
    (refinement : ObserverRefinement coarse fine)
    (atomSurjective : Function.Surjective refinement.mapAtom)
    (labelSurjective : Function.Surjective refinement.mapLabel) :
    EqualityFamilyFactorization refinement.classMap :=
  EqualityFamilyFactorization.ofInjective
    (refinement.classMap_injective_of_surjective
      atomSurjective labelSurjective)

/-- All equality families anchored at fine behavioral classes descend through
the observer refinement exactly when the refinement does not merge fine classes. -/
theorem allAnchoredFactorizations_iff_classMap_injective
    (refinement : ObserverRefinement coarse fine) :
    (∀ anchor,
        Nonempty
          (FamilyFactorization refinement.classMap
            (fun state => PLift (anchor = state)))) ↔
      Function.Injective refinement.classMap :=
  EqualityFamilyFactorization.all_anchored_nonempty_iff_injective
    refinement.classMap

/-- Surjectivity on atoms and labels is a sufficient operational certificate
for every anchored behavioral-identity family to descend. -/
theorem allAnchoredFactorizationsOfSurjective
    (refinement : ObserverRefinement coarse fine)
    (atomSurjective : Function.Surjective refinement.mapAtom)
    (labelSurjective : Function.Surjective refinement.mapLabel) :
    ∀ anchor,
      Nonempty
        (FamilyFactorization refinement.classMap
          (fun state => PLift (anchor = state))) :=
  (allAnchoredFactorizations_iff_classMap_injective refinement).2
    (refinement.classMap_injective_of_surjective
      atomSurjective labelSurjective)

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.GSLT.HennessyMilner.ObserverRefinementCanary

/-- Identity refinement preserves the equality family on fine behavioral classes. -/
def identityRefinementPreservesEquality :
    EqualityFamilyFactorization
      (ObserverRefinement.id fine).classMap :=
  equalityFamilyFactorizationOfSurjective
    (ObserverRefinement.id fine)
    Function.surjective_id Function.surjective_id

/-- The strict coarse/fine canary merges two fine classes, so it cannot
preserve their equality fibres. -/
theorem coarseRefinementDoesNotPreserveFineEquality :
    ¬ Nonempty (EqualityFamilyFactorization refinement.classMap) := by
  rw [EqualityFamilyFactorization.nonempty_iff_injective]
  exact refinement_not_injective

/-- Equivalently, at least one family anchored at a fine identity class fails
to descend through this lawful coarse observation. -/
theorem someAnchoredFineIdentityFamilyDoesNotDescend :
    ¬ (∀ anchor,
        Nonempty
          (FamilyFactorization refinement.classMap
            (fun state => PLift (anchor = state)))) := by
  rw [allAnchoredFactorizations_iff_classMap_injective]
  exact refinement_not_injective

end Canary

#print axioms equalityFamilyFactorizationOfSurjective
#print axioms allAnchoredFactorizations_iff_classMap_injective
#print axioms allAnchoredFactorizationsOfSurjective
#print axioms Canary.identityRefinementPreservesEquality
#print axioms Canary.coarseRefinementDoesNotPreserveFineEquality
#print axioms Canary.someAnchoredFineIdentityFamilyDoesNotDescend

end Mettapedia.TypeTheory.BehavioralIdentityObserverFactorization
