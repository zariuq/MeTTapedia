import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphWReadout
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyControls

/-!
# Varying labelled W trees and discriminating material controls

Both labels and branches grow at every natural stage. Terminal trees
with cyclic versus terminal label bodies have different material values;
different positive native labels have equal readings. A branching tree
retains its actual children and is separated from a terminal tree even
when their label bodies agree. Native folds can still inspect the labels
that this material observer identifies.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphWReadoutControls

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualWTypes

abbrev shape : Nat ⥤ Type := {
  obj stage := Fin (stage+1) × Bool
  map {_ _} arrival := TypeCat.ofHom fun label =>
    ⟨Fin.castLE (Nat.succ_le_succ (leOfHom arrival)) label.1, label.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl }

def position : shape.Elements ⥤ Type where
  obj point := {_index : Fin (point.1+1) // point.2.2 = true}
  map {_first _second} step := TypeCat.ofHom fun index =>
    ⟨Fin.castLE (Nat.succ_le_succ (leOfHom step.1)) index.val,
      (congrArg Prod.snd step.2).symm.trans index.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def shapeReading : NaturalHom shape (values Nat) where
  app stage label := ContextualGraphFamilyBodyControls.material stage label.1
  naturality _ _ := rfl

def positionReading : NaturalHom (total position) (values Nat) where
  app stage receipt := ContextualGraphFamilyBodyControls.material stage receipt.2.val
  naturality _ _ := rfl

def leaf (stage : Nat) (index : Fin (stage+1)) : (family shape position).obj stage :=
  sup shape position ⟨index, false⟩
    (fun _ _ branch => Bool.noConfusion branch.property)
    (fun _ _ _ _ branch => Bool.noConfusion branch.property)

theorem leaf_natural {first second : Nat} (arrival : first ⟶ second) (index : Fin (first+1)) :
    (family shape position).map arrival (leaf first index) =
      leaf second (Fin.castLE (Nat.succ_le_succ (leOfHom arrival)) index) := by
  apply Subtype.ext
  apply RawTree.sup_eq_of_cast rfl
  intro future arrow branch
  exact Bool.noConfusion branch.property

def starBranches (stage : Nat) (index : Fin (stage+1)) :
    Branches shape position (family shape position) ⟨index, true⟩ where
  app future _ branch := leaf future branch.val
  naturality _ _ _ later branch := leaf_natural later branch.val

def star (stage : Nat) (index : Fin (stage+1)) : (family shape position).obj stage :=
  (treeAlgebra shape position).make stage ⟨index, true⟩ (starBranches stage index)

theorem star_natural {first second : Nat} (arrival : first ⟶ second) (index : Fin (first+1)) :
    (family shape position).map arrival (star first index) =
      star second (Fin.castLE (Nat.succ_le_succ (leOfHom arrival)) index) := by
  apply Subtype.ext
  apply RawTree.sup_eq_of_cast rfl
  intro future arrow branch
  rfl

def read (stage : Nat) (tree : (family shape position).obj stage) : Value Nat stage :=
  (ContextualGraphWReadout.reading shape position shapeReading positionReading).app stage tree

def branchCollection (stage : Nat) (tree : (family shape position).obj stage) : Value Nat stage :=
  (ContextualGraphWReadout.branchCollection shape position shapeReading positionReading).app stage tree

def noLeafMember {stage : Nat} (index : Fin (stage+1)) (element : Value Nat stage)
    (proof : Member element (branchCollection stage (leaf stage index))) : Empty :=
  Bool.noConfusion (ContextualGraphFamilyBodyComparison.memberDecode
    (ContextualGraphWBranchSpan.branches shape position)
    (ContextualGraphWReadout.branchReading shape position shapeReading positionReading)
    ⟨stage, leaf stage index⟩ element proof).1.property

def leafCollectionsEqual (stage : Nat) (first second : Fin (stage+1)) :
    Equal (branchCollection stage (leaf stage first)) (branchCollection stage (leaf stage second)) := by
  apply extensionality
  · intro future arrival element proof
    have natural := (ContextualGraphWReadout.branchCollection shape position shapeReading positionReading).naturality arrival (leaf stage first)
    change move Nat arrival (branchCollection stage (leaf stage first)) = _ at natural
    rw [natural, leaf_natural] at proof
    exact Empty.elim (noLeafMember _ element proof)
  · intro future arrival element proof
    have natural := (ContextualGraphWReadout.branchCollection shape position shapeReading positionReading).naturality arrival (leaf stage second)
    change move Nat arrival (branchCollection stage (leaf stage second)) = _ at natural
    rw [natural, leaf_natural] at proof
    exact Empty.elim (noLeafMember _ element proof)

def positiveLeavesMatch : Equal (read 2 (leaf 2 ⟨1, by decide⟩)) (read 2 (leaf 2 ⟨2, by decide⟩)) :=
  (ContextualGraphWReadout.unfold shape position shapeReading positionReading _).trans
    ((ContextualGraphOrderedPairs.orderedPairCongr
      (ContextualGraphFamilyBodyControls.terminalEquality 2 ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide) (by decide))
      (leafCollectionsEqual 2 _ _)).trans
        (ContextualGraphWReadout.unfold shape position shapeReading positionReading _).symm)

theorem terminal_results_distinguished :
    ¬ Nonempty (Equal (read 1 (leaf 1 ⟨0, by decide⟩)) (read 1 (leaf 1 ⟨1, by decide⟩))) := by
  rintro ⟨same⟩
  have labels := ContextualGraphWReadout.reflectLabel shape position shapeReading positionReading same
  exact (by decide : ¬ (1 : Nat) = 0)
    (ContextualGraphFamilyBodyControls.matching_preserves_zero 1 ⟨0, by decide⟩ ⟨1, by decide⟩ labels rfl)

theorem native_positive_leaves_distinct : leaf 2 ⟨1, by decide⟩ ≠ leaf 2 ⟨2, by decide⟩ := by
  intro same
  have indices := congrArg (fun tree => (ContextualGraphWBranchSpan.label shape position tree).1.val) same
  exact (by decide : ¬ (1 : Nat) = 2) indices

def starMember (stage : Nat) (index branch : Fin (stage+1)) :
    Member ((ContextualGraphWReadout.branchReading shape position shapeReading positionReading).app stage
      ⟨star stage index, ⟨branch, rfl⟩⟩) (branchCollection stage (star stage index)) :=
  ContextualGraphFamilyBodyComparison.memberIntro (ContextualGraphWBranchSpan.branches shape position)
    (ContextualGraphWReadout.branchReading shape position shapeReading positionReading)
    ⟨stage, star stage index⟩ _ ⟨branch, rfl⟩ (Equal.refl _)

theorem branches_distinguish_same_label :
    ¬ Nonempty (Equal (read 0 (star 0 ⟨0, by decide⟩)) (read 0 (leaf 0 ⟨0, by decide⟩))) := by
  rintro ⟨same⟩
  have collections := ContextualGraphPolynomialReadout.reflectCollection
    (ContextualGraphWBranchSpan.branches shape position)
    (ContextualGraphWReadout.labels shape position shapeReading)
    (ContextualGraphWReadout.arguments shape position positionReading)
    (ContextualGraphWBranchSpan.childMap shape position) same
  exact Empty.elim (noLeafMember _ _ (Member.transportParent collections (starMember 0 ⟨0, by decide⟩ ⟨0, by decide⟩)))

theorem branches_grow_at_every_stage (stage : Nat) :
    ¬ ∃ earlier : position.obj ⟨stage, (⟨⟨0, Nat.succ_pos _⟩, true⟩ : shape.obj stage)⟩,
      (position.map (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.argumentMap shape
        (homOfLE (Nat.le_succ stage)) ⟨⟨0, Nat.succ_pos _⟩, true⟩) earlier).val.val = stage+1 := by
  rintro ⟨earlier, same⟩
  exact (Nat.ne_of_lt earlier.val.isLt) same

def starSection : (family shape position).sections :=
  ⟨fun stage => star stage ⟨0, Nat.succ_pos _⟩,
    fun {_ _} arrival => star_natural arrival _⟩

def wholeStarReading : (values Nat).sections :=
  ContextualGraphWReadout.sectionReading shape position shapeReading positionReading starSection

/-- This algebra reads retained native labels, including distinctions
that the material label observer intentionally identifies. -/
def indexTarget : Nat ⥤ Type where
  obj _ := Nat
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def indexAlgebra : Algebra shape position indexTarget where
  make _ label _ := label.1.val
  naturality _ _ _ _ _ := rfl

theorem fold_leaf (stage : Nat) (index : Fin (stage+1)) :
    fold shape position indexAlgebra (leaf stage index) = index.val :=
  fold_beta shape position indexAlgebra ⟨index, false⟩
    { app := fun _ _ branch => Bool.noConfusion branch.property
      naturality := fun _ _ _ _ branch => Bool.noConfusion branch.property }

theorem material_matching_does_not_license_arbitrary_fold :
    Nonempty (Equal (read 2 (leaf 2 ⟨1, by decide⟩)) (read 2 (leaf 2 ⟨2, by decide⟩))) ∧
      fold shape position indexAlgebra (leaf 2 ⟨1, by decide⟩) ≠
        fold shape position indexAlgebra (leaf 2 ⟨2, by decide⟩) := by
  refine ⟨⟨positiveLeavesMatch⟩, ?_⟩
  rw [fold_leaf, fold_leaf]
  change (1 : Nat) ≠ 2
  decide

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphWReadoutControls
