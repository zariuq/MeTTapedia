import Mettapedia.Languages.MeTTa.PureKernel.Universe.IntrinsicMILNativeLiftingSearch
import Mettapedia.Languages.MeTTa.Prime.NativeRelationalSearchNIKSelection

/-!
# NIK selection for generic higher-order native relation liftings

The generic higher-order hypothesis recursion now supplies the exact capability
objects consumed by request-local maximal-native selection.  This module checks
the three honest outcomes:

* finite nondeterministic lifting selects exhaustive native search;
* functional lifting selects the stronger direct realization over the same
  complete proof-occurrence contract;
* an infinitary strictly-positive lifting cannot enter the finite-search request
  fibre.

The examples use native polynomial List, but the selection theorem depends only
on the declared lifting capabilities, not on a List-specific dispatcher.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeLiftedHypothesisNIKSelection

open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission
open Mettapedia.Languages.MeTTa.PureKernel.Universe
open Mettapedia.Languages.MeTTa.PureKernel.Universe.RelationalInternalLanguage.Semantic
open Mettapedia.Languages.MeTTa.PureKernel.Universe.IntrinsicMILNativeSearch
open Mettapedia.Languages.MeTTa.PureKernel.Universe.IntrinsicMILNativeLiftingSearch
open Mettapedia.Languages.MeTTa.PureKernel.Universe.IntrinsicMILNativeLiftingSearch.Canary
open Mettapedia.Languages.MeTTa.Prime.NativeRelationalSearchNIKSelection
open Mettapedia.TypeTheory.IndexedPolynomial

/-! ## One revision model shared by both exact requests -/

def dependencies : DependencySystem where
  Revision := Bool
  Dependency := Unit
  Value := Bool
  read revision _ := revision

/-! ## Finite nondeterministic lifted hypothesis -/

noncomputable def branchingFamily :=
  finiteOnlyFamily liftedChoiceProvider

noncomputable def branchingAdmission :=
  admitStrongestAt branchingFamily
    (finiteOnlyRequest liftedChoiceProvider)
    (finiteOnlySelection liftedChoiceProvider)
    dependencies false

noncomputable def activeBranching : branchingAdmission.Active false :=
  branchingAdmission.activate (dependencies.sameDependencies_refl false)

noncomputable def activeBranchingRun :
    BranchCarrier (BranchSort.list BranchSort.input) →
      NativeSearchReceipt liftedChoice.denote :=
  activeBranching.run

/-- The provider was derived by recursion over generic higher-order syntax;
NIK selects finite search and retains both branches. -/
theorem generic_branching_lift_selects_complete_search :
    (activeBranchingRun ListExample.singletonUnit).face = .finiteSearch ∧
      (activeBranchingRun ListExample.singletonUnit).result.answers.card = 2 := by
  constructor
  · rfl
  · change (liftedChoiceProvider.run ListExample.singletonUnit).answers.card = 2
    exact generic_list_lifting_retains_two_occurrences

/-! ## Functionally represented lifted hypothesis -/

noncomputable def directFamily :=
  representedFamily liftedToggleProvider liftedToggleRepresentation

noncomputable def directAdmission :=
  admitStrongestAt directFamily
    (completeSearchRequest liftedToggleProvider liftedToggleRepresentation)
    (directSelection liftedToggleProvider liftedToggleRepresentation)
    dependencies false

noncomputable def activeDirect : directAdmission.Active false :=
  directAdmission.activate (dependencies.sameDependencies_refl false)

noncomputable def activeDirectRun :
    DirectCarrier (DirectSort.list DirectSort.atom) →
      NativeSearchReceipt liftedToggle.denote :=
  activeDirect.run

/-- Over the same complete-result contract, functional representation earns
the direct face and the resulting proof bag remains complete. -/
theorem generic_functional_lift_selects_direct :
    (activeDirectRun (ListExample.ofList [false])).face = .directMap ∧
      RelationalEvidence.AnswerBag.Complete
        (activeDirectRun (ListExample.ofList [false])).result.answers := by
  constructor
  · rfl
  · exact directAdmission.refinement.preservesMeaning _ trivial

/-- Currentness is part of the capability request: changing the selected
dependency does not trigger a weaker hidden route. -/
theorem changed_revision_prevents_generic_lifted_selection :
    ¬ Nonempty (directAdmission.Active true) := by
  rintro ⟨active⟩
  have changed := active.current ()
  simp [dependencies] at changed

/-! ## Refusing boundary -/

/-- A strictly-positive but infinitary data former can have a lawful
compositional relator while lacking the finite capability required by this NIK
request. -/
theorem infinitary_positive_lifting_has_no_finite_nik_capability :
    ¬ Nonempty
      (FiniteSearchLifting (fun Object : Type => Nat → Object)
        readerLifting.{0}) :=
  compositional_lifting_does_not_imply_finite_search

#print axioms generic_branching_lift_selects_complete_search
#print axioms generic_functional_lift_selects_direct
#print axioms changed_revision_prevents_generic_lifted_selection
#print axioms infinitary_positive_lifting_has_no_finite_nik_capability

end Mettapedia.Languages.MeTTa.Prime.NativeLiftedHypothesisNIKSelection
