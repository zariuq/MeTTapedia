import Mettapedia.GSLT.Core.LambdaTheoryStructuredTwoCategories
import Mettapedia.CategoryTheory.PredicateDoctrineClosed
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.Data.Bool.Basic

/-!
# Strict structured-theory controls

The Boolean order is a finite-limit and cartesian closed theory. Its
identity and constant-top maps preserve both structures. Their natural
transformation is noninvertible, and fixes a top-provided structure.
Changing just one endpoint map fails strict square commutation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.LambdaTheoryStructuredControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Bicategory
open scoped _root_.CategoryTheory.SemilatticeInf
open scoped Mettapedia.CategoryTheory.PredicateDoctrine.HeytingClosed
open Mettapedia.CategoryTheory

def boolTheory : LambdaTheory.{0,0} where
  Obj := Bool
  instCategory := inferInstance
  instCartesianMonoidal := inferInstance
  instMonoidalClosed := inferInstance
  instHasFiniteLimits := inferInstance

def topFunctor : Bool ⥤ Bool := (Functor.const Bool).obj true
def bottomFunctor : Bool ⥤ Bool := (Functor.const Bool).obj false

private def bottomTopAdjunction : bottomFunctor ⊣ topFunctor :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun _ _ => {
      toFun := fun _ => homOfLE le_top
      invFun := fun _ => homOfLE bot_le
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }
    homEquiv_naturality_left_symm := by intros; apply Subsingleton.elim
    homEquiv_naturality_right := by intros; apply Subsingleton.elim }

instance top_preservesFiniteLimits : PreservesFiniteLimits topFunctor := by
  let : PreservesLimitsOfSize.{0,0} topFunctor :=
    bottomTopAdjunction.rightAdjoint_preservesLimits
  infer_instance

instance top_preservesExponentials : MonoidalClosedFunctor topFunctor where
  comparison_iso domain := by
    suffices ∀ codomain : Bool,
        IsIso ((expComparison topFunctor domain).natTrans.app codomain) from
      NatIso.isIso_of_isIso_app _
    intro codomain
    have same : (expComparison topFunctor domain).natTrans.app codomain = (𝟙 true) :=
      Subsingleton.elim _ _
    rw [same]
    infer_instance

def topMap : boolTheory ⟶ boolTheory where
  functor := topFunctor
  preservesFiniteLimits := top_preservesFiniteLimits
  preservesExponentials := top_preservesExponentials

def grow : (𝟙 boolTheory : boolTheory ⟶ boolTheory) ⟶ topMap :=
  show (Functor.id Bool) ⟶ topFunctor from {
    app _ := homOfLE le_top
    naturality := by intros; apply Subsingleton.elim }

theorem grow_is_not_invertible : ¬ IsIso grow := by
  intro invertible
  let backward : topMap ⟶ (𝟙 boolTheory) :=
    @inv (boolTheory ⟶ boolTheory) (LambdaTheory.homCategory boolTheory boolTheory)
      (𝟙 boolTheory) topMap grow invertible
  let impossibleArrow : (true : Bool) ⟶ false := backward.app false
  exact (not_le_of_gt Bool.false_lt_true) impossibleArrow.le

def topStructure : LambdaTheory.StructuredOver boolTheory := ⟨boolTheory, topMap⟩

def fixedIdentity : topStructure ⟶ topStructure := 𝟙 topStructure

def fixedTop : topStructure ⟶ topStructure where
  hom := topMap
  comm := by
    apply LambdaTheoryMap.ext
    rfl

def fixedGrow : fixedIdentity ⟶ fixedTop where
  hom := grow
  fixed := by
    apply heq_of_eq
    apply NatTrans.ext
    funext object
    change (grow.app true : true ⟶ true) = 𝟙 true
    apply Subsingleton.elim

theorem fixedGrow_component_false :
    fixedGrow.hom.app false = homOfLE (show false ≤ true from le_top) := rfl

theorem structure_component_is_identity (object : boolTheory.Obj) :
    fixedGrow.hom.app (topStructure.leg.functor.obj object) = 𝟙 true := by
  change (grow.app true : true ⟶ true) = 𝟙 true
  apply Subsingleton.elim

theorem fixed_two_cell_still_noninvertible : ¬ IsIso fixedGrow := by
  intro invertible
  let backward : fixedTop ⟶ fixedIdentity :=
    @inv (topStructure ⟶ topStructure) (StrictTwoCoslice.homCategory topStructure topStructure)
      fixedIdentity fixedTop fixedGrow invertible
  let impossibleArrow : (true : Bool) ⟶ false := backward.hom.app false
  exact (not_le_of_gt Bool.false_lt_true) impossibleArrow.le

def identityStructure : LambdaTheory.Structured.{0,0} := ⟨boolTheory, boolTheory, 𝟙 boolTheory⟩

def identitySquare : identityStructure ⟶ identityStructure := 𝟙 identityStructure

def topSquare : identityStructure ⟶ identityStructure where
  left := topMap
  right := topMap
  comm := by
    change (𝟙 boolTheory) ≫ topMap = topMap ≫ (𝟙 boolTheory)
    rw [_root_.CategoryTheory.Category.id_comp, _root_.CategoryTheory.Category.comp_id]

def squareGrow : identitySquare ⟶ topSquare where
  left := grow
  right := grow
  compatible := (StrictTwoWhiskering.left_unit grow).trans
    (StrictTwoWhiskering.right_unit grow).symm

theorem squareGrow_retains_both_components :
    squareGrow.left.app false = homOfLE (show false ≤ true from le_top) ∧
    squareGrow.right.app false = homOfLE (show false ≤ true from le_top) := ⟨rfl, rfl⟩

/-- Independently valid closed maps need not form a structure-preserving square. -/
theorem no_mixed_square : ¬ ∃ square : identityStructure ⟶ identityStructure,
    square.left = 𝟙 boolTheory ∧ square.right = topMap := by
  rintro ⟨square, left, right⟩
  have commute := square.comm
  rw [left, right] at commute
  have objects := congrArg (fun map : boolTheory ⟶ boolTheory => map.functor.obj false) commute
  change true = false at objects
  exact Bool.noConfusion objects

theorem actual_top_commutation :
    identityStructure.arrow ≫ topSquare.right = topSquare.left ≫ identityStructure.arrow :=
  topSquare.comm

/-- Composition retains the nonidentity endpoint map at both ends. -/
theorem top_square_composition_false :
    ((topSquare ≫ topSquare).left.functor.obj false) = true ∧
    ((topSquare ≫ topSquare).right.functor.obj false) = true := ⟨rfl, rfl⟩

end Mettapedia.GSLT.Core.LambdaTheoryStructuredControls
