import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftWAlgebra
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftAbstraction
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftIdentity
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualHypersetFamilyClosureControls
import Mettapedia.TypeTheory.ContextualSmallFamilyWiderControls

/-!
# Nonconstant and separating controls for actual upper type formers

The material family acquires a cyclic member at a later world, and its
body genuinely depends on the selected member. Full products distinguish
present answers from future availability. W trees retain every future
branch across the universe lift; infinitely many original trees remain
distinct even where every present branch agrees.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftFamilyControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open HostChoiceContextualSetSiteLift HostChoiceContextualSetSiteLiftFamilies
open HostChoiceContextualSetSiteLiftProducts HostChoiceContextualSetSiteLiftIdentity
open HostChoiceContextualHypersetFamilyClosure HostChoiceContextualHypersetModel
open HostChoiceContextualHypersetFamilyClosureControls
open HostChoiceContextualHypersetModelControls.Infinite
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretationControls
open PowerClassPresheafDescent.Controls

noncomputable abbrev raisedPoint (stage : ℕ) : (ContextualFutureSiteLift.base parameters).Elements :=
  ⟨ULift.up (world stage), PUnit.unit⟩

theorem upper_dependent_body_sets_distinct :
    (upperBodyMap growingParent singletonBody).app (ULift.up (world 1))
        ⟨PUnit.unit, memberUp growingParent (raisedPoint 1) (emptyCode (world 1))⟩ ≠
      (upperBodyMap growingParent singletonBody).app (ULift.up (world 1))
        ⟨PUnit.unit, memberUp growingParent (raisedPoint 1) loopArgument⟩ := by
  intro same
  have first := upperBodyMap_forward growingParent singletonBody (raisedPoint 1) (ULift.up (emptyCode (world 1)))
  have second := upperBodyMap_forward growingParent singletonBody (raisedPoint 1) (ULift.up loopArgument)
  exact dependent_body_sets_distinct (embedding_injective
    (ULift.up (world 1)) (first.symm.trans (same.trans second)))

theorem upper_every_present_argument_has_answer :
    ∀ argument : (upperDomain growingParent).obj (raisedPoint 0),
      Nonempty ((upperBody growingParent selectedEmptyBody).obj ⟨raisedPoint 0, argument⟩) := by
  intro argument
  obtain ⟨original, rfl⟩ := (domainEquiv growingParent (raisedPoint 0)).surjective argument
  exact ⟨bodyEquiv growingParent selectedEmptyBody ⟨raisedPoint 0, original⟩
    (ULift.up (presentAnswer original.down))⟩

theorem upper_complete_product_empty :
    ¬ Nonempty ((Pi.upper growingParent selectedEmptyBody).obj (raisedPoint 0)) := by
  rintro ⟨term⟩
  exact complete_product_empty ⟨(Pi.equiv growingParent selectedEmptyBody (raisedPoint 0)).symm term⟩

theorem present_answers_do_not_supply_upper_product :
    (∀ argument : (upperDomain growingParent).obj (raisedPoint 0),
      Nonempty ((upperBody growingParent selectedEmptyBody).obj ⟨raisedPoint 0, argument⟩)) ∧
      ¬ Nonempty ((Pi.upper growingParent selectedEmptyBody).obj (raisedPoint 0)) :=
  ⟨upper_every_present_argument_has_answer, upper_complete_product_empty⟩

noncomputable def raisedSingletonProduct : (Pi.upper growingParent singletonBody).obj (raisedPoint 0) :=
  (Pi.forward growingParent singletonBody).app (raisedPoint 0) (singletonProduct (point (world 0)))

theorem actual_upper_product_inhabited : Nonempty ((Pi.upper growingParent singletonBody).obj (raisedPoint 0)) :=
  ⟨raisedSingletonProduct⟩

noncomputable def raisedLeaf (stage : ℕ) :
    (HostChoiceContextualSetSiteLiftW.upper growingParent (argumentReading growingParent)).obj (raisedPoint stage) :=
  (HostChoiceContextualSetSiteLiftW.forward growingParent (argumentReading growingParent)).app (raisedPoint stage)
    (emptyPositionLeaf (point (world stage)))

theorem actual_upper_argument_dependent_W_inhabited (stage : ℕ) :
    Nonempty ((HostChoiceContextualSetSiteLiftW.upper growingParent (argumentReading growingParent)).obj
      (raisedPoint stage)) := ⟨raisedLeaf stage⟩

theorem actual_upper_singleton_positions_admit_no_W (stage : ℕ) :
    ¬ Nonempty ((HostChoiceContextualSetSiteLiftW.upper growingParent singletonBody).obj (raisedPoint stage)) := by
  rintro ⟨tree⟩
  exact singleton_positions_admit_no_W (point (world stage))
    ⟨(HostChoiceContextualSetSiteLiftW.equiv growingParent singletonBody (raisedPoint stage)).symm tree⟩

theorem old_members_distinct : (emptyCode (world 1) : input.obj (point (world 1))) ≠ loopArgument := by
  intro same
  have values := congrArg ((argumentReading growingParent).app (world 1) ∘ fun argument =>
    (⟨PUnit.unit, argument⟩ : (comprehension growingParent).obj (world 1))) same
  exact loop_ne_empty (world 1) (loopArgument_value.symm.trans (values.symm.trans (emptyCode_value _)))

theorem upper_off_diagonal_empty :
    ¬ Nonempty ((ContextualSmallFamilyIdentity.witnessFamily (upperDomain growingParent)).obj
      ⟨(raisedPoint 1).1, ⟨⟨PUnit.unit, memberUp growingParent (raisedPoint 1) (emptyCode (world 1))⟩,
        memberUp growingParent (raisedPoint 1) loopArgument⟩⟩) := by
  apply ContextualSmallFamilyIdentity.offDiagonal_empty
  intro same
  have recovered := congrArg (memberDown growingParent (raisedPoint 1)) same
  exact old_members_distinct ((member_down_up growingParent (raisedPoint 1) (emptyCode (world 1))).symm.trans
    (recovered.trans (member_down_up growingParent (raisedPoint 1) loopArgument)))

namespace InfiniteTrees

open ContextualSmallFamilyUniverseControls ContextualSmallFamilyTypeFormerControls
open ContextualSmallFamilyWControls

abbrev point : (ContextualFutureSiteLift.base ContextualSmallFamilyUniverseControls.parameters).Elements :=
  ⟨ULift.up 0, HSet.quineAtom⟩

noncomputable def raised (bound : ℕ) :=
  (ContextualFutureSiteWCones.equiv cyclicSmall growingPositions point).symm (futureBranchTree bound)

theorem infinitely_many_preserved_whole_future_trees : Function.Injective raised := by
  intro first second same
  apply infinitely_many_whole_future_trees
  exact (ContextualFutureSiteWCones.equiv cyclicSmall growingPositions point).symm.injective same

theorem present_branch_equality_does_not_license_tree_identification :
    (∀ position,
      (ContextualSmallFamilyWAlgebra.destructorValue cyclicSmall growingPositions
        (parameter 0 HSet.quineAtom) (futureBranchTree 0)).2.app
          (ContextualSmallFamilyUniverse.root 0) (𝟙 _) position =
      (ContextualSmallFamilyWAlgebra.destructorValue cyclicSmall growingPositions
        (parameter 0 HSet.quineAtom) (futureBranchTree 1)).2.app
          (ContextualSmallFamilyUniverse.root 0) (𝟙 _) position) ∧ raised 0 ≠ raised 1 :=
  ⟨all_present_branches_agree 0 1, fun same => Nat.zero_ne_one (infinitely_many_preserved_whole_future_trees same)⟩

end InfiniteTrees

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftFamilyControls
