import Mettapedia.TypeTheory.ContextualSmallFamilyWiderInitiality
import Mettapedia.TypeTheory.ContextualSmallFamilyWControls

/-!
# Wider W consumers retaining material parameters and future trees

The consumer has arbitrary material values and the varying original-bound
W carrier. Its algebra reconstructs complete future trees from the branch
values. The fold retains the original material parameter and actual tree;
new future positions distinguish results despite identical present branches.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWiderControls

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyUniverseControls ContextualSmallFamilyTypeFormerControls
open ContextualSmallFamilyWControls ContextualSmallFamilyWTypes

noncomputable def wideTarget : parameters.Elements ⥤ Type 1 where
  obj point := HSet.{0} × WAt cyclicSmall growingPositions point
  map step := TypeCat.ofHom fun value => ⟨value.1, wMap cyclicSmall growingPositions step value.2⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    exact Prod.ext rfl (wMap_id cyclicSmall growingPositions point value.2)
  map_comp first later := by
    apply ConcreteCategory.hom_ext
    intro value
    exact Prod.ext rfl (wMap_comp cyclicSmall growingPositions first later value.2)

def treeProjection : WiderPresheafDependentFunctions.Hom wideTarget (w cyclicSmall growingPositions) where
  app _ value := value.2
  naturality _ _ := rfl

noncomputable def retainParameter : WiderPresheafDependentFunctions.Hom (w cyclicSmall growingPositions) wideTarget where
  app point tree := ⟨point.2, tree⟩
  naturality {_first _second} step _tree := Prod.ext step.2 rfl

noncomputable def wideAlgebra : ContextualSmallFamilyWiderAlgebra.Algebra cyclicSmall growingPositions
    (target := wideTarget) where
  app point node := ⟨point.2, ContextualSmallFamilyWiderAlgebra.constructorValue cyclicSmall growingPositions point
    (ContextualSmallFamilyWiderAction.mapValue cyclicSmall growingPositions treeProjection point node)⟩
  naturality {first second} step node := by
    apply Prod.ext step.2
    exact (ContextualSmallFamilyWiderConstructor.constructor_natural cyclicSmall growingPositions step
      (ContextualSmallFamilyWiderAction.mapValue cyclicSmall growingPositions treeProjection first node)).trans
      (congrArg (ContextualSmallFamilyWiderAlgebra.constructorValue cyclicSmall growingPositions second)
        (ContextualSmallFamilyWiderAction.mapValue_natural cyclicSmall growingPositions treeProjection step node))

theorem whole_branch_reconstruction (point : parameters.Elements)
    (node : ContextualSmallFamilyWiderPolynomial.At cyclicSmall growingPositions
      (w cyclicSmall growingPositions) point) :
    ContextualSmallFamilyWiderAction.mapValue cyclicSmall growingPositions treeProjection point
      (ContextualSmallFamilyWiderAction.mapValue cyclicSmall growingPositions retainParameter point node) = node := by
  rcases node with ⟨label, branches⟩
  apply congrArg (Sigma.mk label)
  apply WiderContextualWAlgebras.Branches.ext
  intro future arrow position
  rfl

theorem retaining_constructor_law (point : parameters.Elements)
    (node : ContextualSmallFamilyWiderPolynomial.At cyclicSmall growingPositions
      (w cyclicSmall growingPositions) point) :
    retainParameter.app point
      (ContextualSmallFamilyWiderAlgebra.constructorValue cyclicSmall growingPositions point node) =
      wideAlgebra.app point
        (ContextualSmallFamilyWiderAction.mapValue cyclicSmall growingPositions retainParameter point node) := by
  apply Prod.ext rfl
  exact (congrArg (ContextualSmallFamilyWiderAlgebra.constructorValue cyclicSmall growingPositions point)
    (whole_branch_reconstruction point node)).symm

theorem wider_fold_whole :
    ContextualSmallFamilyWiderRecursion.foldMap cyclicSmall growingPositions wideAlgebra = retainParameter :=
  (ContextualSmallFamilyWiderInitiality.fold_unique cyclicSmall growingPositions wideAlgebra retainParameter
    retaining_constructor_law).symm

theorem wider_fold_value (point : parameters.Elements) (tree : WAt cyclicSmall growingPositions point) :
    ContextualSmallFamilyWiderAlgebra.foldValue cyclicSmall growingPositions wideAlgebra point tree = ⟨point.2, tree⟩ :=
  congrArg (fun operation => operation.app point tree) wider_fold_whole

theorem wider_consumer_has_no_original_small_cover {I : Type}
    (reading : I → wideTarget.obj (parameter 0 HSet.quineAtom)) : ¬ Function.Surjective reading := by
  intro covers
  apply parameter_object_has_no_small_cover (fun receipt => (reading receipt).1)
  intro material
  obtain ⟨receipt, same⟩ := covers ⟨material, zeroLeaf (parameter 0 HSet.quineAtom)⟩
  exact ⟨receipt, congrArg Prod.fst same⟩

theorem arbitrary_parameter_retained (stage : Nat) (material : HSet.{0}) :
    (ContextualSmallFamilyWiderAlgebra.foldValue cyclicSmall growingPositions wideAlgebra
      (parameter stage material) (zeroLeaf (parameter stage material))).1 = material :=
  congrArg Prod.fst (wider_fold_value (parameter stage material) (zeroLeaf (parameter stage material)))

theorem wider_fold_retains_complete_future (bound : Nat) :
    ContextualSmallFamilyWiderAlgebra.foldValue cyclicSmall growingPositions wideAlgebra
      (parameter 0 HSet.quineAtom) (futureBranchTree bound) = ⟨HSet.quineAtom, futureBranchTree bound⟩ :=
  wider_fold_value (parameter 0 HSet.quineAtom) (futureBranchTree bound)

theorem infinitely_many_wider_fold_results : Function.Injective fun bound =>
    ContextualSmallFamilyWiderAlgebra.foldValue cyclicSmall growingPositions wideAlgebra
      (parameter 0 HSet.quineAtom) (futureBranchTree bound) := by
  intro first second same
  apply infinitely_many_whole_future_trees
  exact (congrArg Prod.snd (wider_fold_retains_complete_future first)).symm.trans
    ((congrArg Prod.snd same).trans (congrArg Prod.snd (wider_fold_retains_complete_future second)))

theorem all_present_branches_miss_wider_fold_difference :
    (∀ position,
      (ContextualSmallFamilyWAlgebra.destructorValue cyclicSmall growingPositions
        (parameter 0 HSet.quineAtom) (futureBranchTree 0)).2.app
          (ContextualSmallFamilyUniverse.root 0) (𝟙 _) position =
      (ContextualSmallFamilyWAlgebra.destructorValue cyclicSmall growingPositions
        (parameter 0 HSet.quineAtom) (futureBranchTree 1)).2.app
          (ContextualSmallFamilyUniverse.root 0) (𝟙 _) position) ∧
    ContextualSmallFamilyWiderAlgebra.foldValue cyclicSmall growingPositions wideAlgebra
        (parameter 0 HSet.quineAtom) (futureBranchTree 0) ≠
      ContextualSmallFamilyWiderAlgebra.foldValue cyclicSmall growingPositions wideAlgebra
        (parameter 0 HSet.quineAtom) (futureBranchTree 1) := by
  refine ⟨all_present_branches_agree 0 1, ?_⟩
  intro same
  exact Nat.zero_ne_one (infinitely_many_wider_fold_results same)

end Mettapedia.TypeTheory.ContextualSmallFamilyWiderControls
