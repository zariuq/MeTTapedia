import Mettapedia.TypeTheory.PresheafNativeRefinementRestriction

/-!
# Refinement cells of the actual native theory action

A theory transformation transports selected witnesses along the existing
complete native evidence cell. The resulting refinement cell has its
forgetting square, identity and vertical-composition laws, and commutes with
the restriction comparison on the chosen native sum/truth presentation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.PresheafNativeRefinementCells

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice
open DisplayedPresheafCwf DisplayedPresheafTheoryRestriction
open DisplayedPresheafTheoryRestrictionAction DisplayedPresheafTheoryTransformation
open DisplayedPresheafTheoryTransformationCoherence
open ContextualLocalUniverses NativeLocalTypeFormers
open NativeLocalTheoryRestriction NativeLocalTheoryTransformation NativeLocalDisplayComparisons
open PresheafNativeLogicalAction PresheafNativeLogicalCells PresheafNativeRefinementRestriction

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {F G H : C ⥤ D} {P : Dᵒᵖ ⥤ Type u}

local instance decodedCategory (P : Dᵒᵖ ⥤ Type u) :
    Category.{u} ((presheafCwf.{u, u, u} D).Ty P) :=
  inferInstanceAs (Category.{u} (DisplayedFamily.{u, u, u, u} P))

attribute [local irreducible] NativeLocalTypeFormers.sigma PresheafNativeStableRefinement.chosen

/-- The actual complete native evidence cell respects each restricted
predicate by the original predicate's naturality. -/
theorem predicate_cell (change : F ⟶ G) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    predicate G A selected ≤ (predicate F A selected).preimage (completeCell change P A) := by
  intro world value belongs
  have square := ConcreteCategory.congr_hom (NatTrans.congr_app
    (totalEvidenceMap_square change P A.decoded) world) value
  change (totalComparison F P A.decoded).hom.app world
      ((completeCell change P A).app world value) ∈ selected.obj (F.op.obj world)
  change (totalComparison F P A.decoded).hom.app world
      ((completeCell change P A).app world value) =
    (totalSpace A.decoded).map ((NatTrans.op change).app world)
      ((totalComparison G P A.decoded).hom.app world value) at square
  rw [square]
  exact selected.map ((NatTrans.op change).app world) belongs

/-- The selected cell uses the actual complete theory cell on the
original inhabitant and introduces its earned target membership. -/
noncomputable def cell (change : F ⟶ G) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    totalSpace (PresheafNativeStableRefinement.chosen (restrict G A)
      (predicate G A selected)).decoded ⟶
        totalSpace (PresheafNativeStableRefinement.chosen (restrict F A)
          (predicate F A selected)).decoded :=
  PresheafNativeStableRefinement.introComplete (restrict F A) (predicate F A selected)
    (PresheafNativeStableRefinement.forgetComplete (restrict G A)
      (predicate G A selected) ≫ completeCell change P A)
    (fun world value => predicate_cell change A selected world
      (PresheafNativeStableRefinement.forgetComplete_satisfies (restrict G A)
        (predicate G A selected) world value))

theorem cell_forget (change : F ⟶ G) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    cell change A selected ≫
        PresheafNativeStableRefinement.forgetComplete (restrict F A) (predicate F A selected) =
      PresheafNativeStableRefinement.forgetComplete (restrict G A) (predicate G A selected) ≫
        completeCell change P A :=
  PresheafNativeStableRefinement.complete_beta _ _ _ _

theorem cell_identity (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    cell (𝟙 F) A selected = 𝟙 _ := by
  apply (cancel_mono (PresheafNativeStableRefinement.forgetComplete
    (restrict F A) (predicate F A selected))).mp
  rw [cell_forget, completeCell_decodes, totalEvidenceMap_identity]
  ext world value
  rfl

theorem cell_composition (first : F ⟶ G) (second : G ⟶ H)
    (A : NativeType P) (selected : Subfunctor (totalSpace A.decoded)) :
    cell (first ≫ second) A selected = cell second A selected ≫ cell first A selected := by
  apply (cancel_mono (PresheafNativeStableRefinement.forgetComplete
    (restrict F A) (predicate F A selected))).mp
  rw [cell_forget, Category.assoc, cell_forget, ← Category.assoc, cell_forget,
    completeCell_decodes, completeCell_decodes, completeCell_decodes,
    totalEvidenceMap_composition, Category.assoc]

private theorem totalRestriction_map (route : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    {A B : DisplayedFamily P} (operation : A ⟶ B) :
    (totalRestriction route P).map operation =
      totalHom ((restrictionFunctor route P).map operation) := by
  ext world value
  rfl

theorem completeCell_naturality (change : F ⟶ G) (A B : NativeType P)
    (operation : A.decoded ⟶ B.decoded) :
    totalHom ((restrictionFunctor G P).map operation) ≫ completeCell change P B =
      completeCell change P A ≫ totalHom ((restrictionFunctor F P).map operation) := by
  have natural := totalEvidenceMap_naturality change P operation
  rw [totalRestriction_map, totalRestriction_map] at natural
  exact natural

private theorem selection_paste {K : Type*} [Category K]
    {X X' Y Y' A B : K} (sourceComparison : X ⟶ X') (targetComparison : Y ⟶ Y')
    (sourceForget : X' ⟶ A) (targetForget : Y' ⟶ B)
    (sourceOperation : X ⟶ A) (targetOperation : Y ⟶ B)
    (evidenceCell : A ⟶ B) (selectedCell : X' ⟶ Y') (actualCell : X ⟶ Y)
    [Mono targetForget]
    (sourceSquare : sourceComparison ≫ sourceForget = sourceOperation)
    (targetSquare : targetComparison ≫ targetForget = targetOperation)
    (selectedSquare : selectedCell ≫ targetForget = sourceForget ≫ evidenceCell)
    (naturalSquare : sourceOperation ≫ evidenceCell = actualCell ≫ targetOperation) :
    sourceComparison ≫ selectedCell = actualCell ≫ targetComparison := by
  apply (cancel_mono targetForget).mp
  rw [Category.assoc, selectedSquare, ← Category.assoc, sourceSquare,
    Category.assoc, targetSquare]
  exact naturalSquare

/-- Selected native refinements commute with the actual corrected
contextual action before and after the chosen presentation is rebuilt. -/
theorem cell_square (change : F ⟶ G) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    (displayComparison G A selected).hom.substitution ≫ cell change A selected =
      completeCell change P (PresheafNativeStableRefinement.chosen A selected) ≫
        (displayComparison F A selected).hom.substitution := by
  let operation := (PresheafNativeStableRefinement.decodeIso A selected).hom ≫
    PresheafNativePredicateRefinement.forgetFamily A.decoded selected
  have sourceSquare := (forget_complete_square G A selected).trans
    (action_forget_total G A selected)
  have targetSquare := (forget_complete_square F A selected).trans
    (action_forget_total F A selected)
  exact selection_paste _ _ _ _ _ _ _ _ _ sourceSquare targetSquare
    (cell_forget change A selected)
    (completeCell_naturality change (PresheafNativeStableRefinement.chosen A selected) A operation)

end Mettapedia.TypeTheory.PresheafNativeRefinementCells
