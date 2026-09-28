import Mettapedia.Languages.Agda.Adequacy.StaticAdmission
import Mettapedia.Languages.Agda.StaticSpecification.Examples

/-!
# Controls for source derivations entering structural statics

These examples translate actual source proof trees, including typed beta and
eta, an ordered two-argument elimination, and different dependent substitution
images. Distinct source proofs of a sort keep distinct roots after translation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.ForwardControls

open Structural.Statics
open StaticSpecification.Examples

def identityTyping := typingForward closedIdentityTyping
def betaEquality := termEqualityForward closedBeta
def etaEquality := termEqualityForward closedEta
def orderedApplicationTyping := typingForward orderedSpineResult

def olderImageTyping := formationForward substitutedOlderType
def newestImageTyping := formationForward substitutedNewestType

noncomputable def olderSubstitution := admittedSubstitution olderTypeSubstitution
noncomputable def newestSubstitution := admittedSubstitution newestTypeSubstitution

theorem different_admitted_substitutions : olderSubstitution.val ≠ newestSubstitution.val := by
  intro same
  have images := congrFun (congrFun same Structural.Srt.term) (embedVar (0 : Fin 1))
  change Mettapedia.OSLF.Binding.Term.var (.succ .zero) =
    (Mettapedia.OSLF.Binding.Term.var .zero : Structural.Tm (Structural.scope 2)) at images
  cases images

theorem different_translated_type_images :
    embedTy (.el 0 (.var (1 : Fin 2))) ≠ embedTy (.el 0 (.var (0 : Fin 2))) := by
  intro same
  exact distinct_type_images (embedTy_injective same)

theorem beta_retains_nontrivial_endpoints :
    embedTerm (closedIdentity.app (.sort 0)) ≠ embedTerm (.sort (n := 0) 0) := by
  intro same
  exact beta_is_not_raw_equality (embedTerm_injective same)

theorem translated_derivations_remain_distinct :
    typingForward directSortTyping ≠ typingForward detouredSortTyping := by
  intro same
  change Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll _ _ =
    Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll _ _ at same
  have root := (Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll.inj same).1
  cases root

end Mettapedia.Languages.Agda.StaticAdequacy.ForwardControls
